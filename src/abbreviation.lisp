;;;; abbreviation.lisp -- abbreviations declared by a .system file
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; Only a system's primitive symbols, axioms and rules are trusted. Every
;;; other symbol is an abbreviation that stands for an expression in
;;; earlier symbols, and the kernel only ever sees the expansion:
;;;
;;;   (:abbreviation (.and ?A ?B) (.neg (.to ?A (.neg ?B))))
;;;   (:abbreviation (.le ?s ?t) (.exists ?z (.eq (+ ?s ?z) ?t)))
;;;   (:abbreviation (.exists1 ?x ?A)
;;;     (.exists ?x (.and ?A (.forall ?u (.to (@subst ?x ?u ?A) (.eq ?u ?x))))))
;;;
;;; Written input -- a proof, a formula, a rule's pattern -- is expanded
;;; where it enters the kernel (NAMED->DB, and rule admission in
;;; system-spec.lisp), so (.and A B) and (.neg (.to A (.neg B))) are the
;;; same formula and no FOLD/UNFOLD axiom is needed. A function defined by
;;; description is an abbreviation too, NAME(x) := (.iota y A(x, y))
;;; (function-definition.lisp). Theorems and their citations are
;;; abbreviations of proof figures in the same sense (k-proof.lisp).
;;;
;;; Expansion works on the written form, with named binders:
;;;   - the arguments replace the head's parameters (?A, ?B, ...); a
;;;     parameter in a binder slot, such as .exists1's ?x, takes the
;;;     variable written there, which then binds as the body says;
;;;   - every other binder of the body (?z, ?u above, or a concrete v2 in
;;;     a defining formula) is renamed to a fresh variable first, so it
;;;     can capture nothing in the arguments;
;;;   - (@subst x t A) in the body is then computed, unless it still holds
;;;     pattern variables (inside a rule's pattern, where the matcher
;;;     computes it);
;;;   - the result is expanded again, so a body may use abbreviations
;;;     declared before it. A body cannot use its own head or a later
;;;     one, so expansion terminates.
;;; Fresh variables are %n above every %n in the input (or ?ABBREVn in a
;;; pattern). They only ever occur as bound variables, which NAMED->DB
;;; turns into nameless indices, so which n is chosen never matters.
;;;
;;; The kernel stores the expansion; an entry's ORIGIN keeps the text as
;;; written, and that is what is shown. (Folding an expansion back is
;;; ambiguous: every (.to (.neg A) B) would read as (.or A B).)

(defun proper-list-p (x)
  "T iff X is a proper (NIL-terminated, finite) list."
  (and (listp x) (handler-case (list-length x) (error () nil)) t))

(defun abbreviation-table (ledger)
  "Alist head -> (PARAMETERS . BODY) for LEDGER's abbreviations."
  (mapcar (lambda (e)
            (destructuring-bind (head-pattern body) (entry-payload e)
              (list* (car head-pattern) (cdr head-pattern) body)))
          (entries-of-kind 'abbreviation ledger)))

(defun abbreviation-head-p (sym ledger)
  "T iff SYM is the head of one of LEDGER's abbreviations (contextual ones
included)."
  (and (symbolp sym) sym
       (some (lambda (e) (eq (car (first (entry-payload e))) sym))
             (append (entries-of-kind 'abbreviation ledger)
                     (entries-of-kind 'contextual-abbreviation ledger)))))

(defun next-abbrev-index (&rest trees)
  "1 + the largest n such that ?ABBREVn occurs in TREES (0 if none)."
  (let ((best -1))
    (labels ((walk (x)
               (cond ((consp x) (walk (car x)) (walk (cdr x)))
                     ((and (symbolp x) x)
                      (let ((s (symbol-name x)))
                        (when (and (> (length s) 7) (string= (subseq s 0 7) "?ABBREV")
                                   (every #'digit-char-p (subseq s 7)))
                          (setf best (max best (parse-integer s :start 7)))))))))
      (walk trees))
    (1+ best)))

(defun rename-body-binders (body parameters fresh &optional descriptions)
  "BODY with the variable of every binder that is not one of PARAMETERS
renamed to (FUNCALL FRESH), within its scope. DESCRIPTIONS, a
CONTEXTUAL-TABLE, makes a description (.iota v A) count as a binder of v
over A too."
  (flet ((binder-p (x) (or (named-binder-p x) (description-binder-p x descriptions))))
    (cond
      ((and (binder-p body) (not (member (second body) parameters :test #'eq)))
       (let ((new (funcall fresh)))
         (list* (first body) new
                (rename-body-binders (substitute-named (second body) new (cddr body))
                                     parameters fresh descriptions))))
      ((binder-p body)
       (list* (first body) (second body)
              (rename-body-binders (cddr body) parameters fresh descriptions)))
      ((consp body) (cons (rename-body-binders (car body) parameters fresh descriptions)
                          (rename-body-binders (cdr body) parameters fresh descriptions)))
      (t body))))

(defun description-binder-p (x table)
  "T iff X is a description (HEAD v ...) of contextual TABLE whose first
argument, a symbol, is a variable its definition binds (as .iota binds
its v)."
  (let ((def (and table (description-p x table))))
    (and def (second x) (symbolp (second x))
         (let ((param (first (second def))) (bound nil))
           (labels ((walk (y) (when (consp y)
                                (when (named-binder-p y) (push (second y) bound))
                                (walk (car y)) (walk (cdr y)))))
             (walk (cddr def)))
           (and (member param bound :test #'eq) t)))))

(defun compute-substitutions (x)
  "X with each (@subst v t A) whose arguments hold no pattern variable
replaced by A with t for the free occurrences of v (innermost first)."
  (cond
    ((atom x) x)
    (t (let ((x (cons (compute-substitutions (car x)) (compute-substitutions (cdr x)))))
         (if (and (eq (car x) '@subst) (= (length x) 4)
                  (null (template-free-pattern-vars (cdr x))))
             (destructuring-bind (v term a) (cdr x)
               (substitute-named v term a))
             x)))))

(defun expand-abbreviations (x ledger &key pattern)
  "X, written with named binders, with every abbreviation expanded (see
above). PATTERN true means X is a rule's pattern: fresh variables are
then pattern variables ?ABBREVn."
  (let ((table (abbreviation-table ledger))
        (descriptions (contextual-table ledger)))
    (if (null table)
        x
        ;; Fresh means above every name of that kind in X and in every
        ;; stored body: a body is stored expanded, so it may already hold
        ;; ?ABBREVn (or %n) binders of its own, and renaming one binder to
        ;; a name another binder of the same body uses would capture.
        (let ((counter (if pattern
                           (next-abbrev-index x table)
                           (next-fresh-index x table))))
          (labels ((fresh ()
                     (prog1 (if pattern
                                (intern (format nil "?ABBREV~D" counter) :ledger-kernel)
                                (fresh-var counter))
                       (incf counter)))
                   (expand (x)
                     (let ((def (and (consp x) (symbolp (car x))
                                     (assoc (car x) table :test #'eq))))
                       (cond
                         ((and def (proper-list-p (cdr x)) (= (length (cdr x)) (length (second def))))
                          (destructuring-bind (parameters . body) (cdr def)
                            (let* ((args (mapcar #'expand (cdr x)))
                                   (body (rename-body-binders body parameters #'fresh descriptions))
                                   (body (sublis (mapcar #'cons parameters args) body)))
                              (expand (compute-substitutions body)))))
                         ((consp x) (cons (expand (car x)) (expand (cdr x))))
                         (t x)))))
            (expand x))))))

(defun check-abbreviation-declaration (head-pattern body ledger)
  "Signal an error unless (:abbreviation HEAD-PATTERN BODY) is admissible:
the head a symbol the ledger has never used, applied to distinct pattern
variables; the body's other pattern variables only bound in it; and every
abbreviation it uses declared before it."
  (flet ((fail (fmt &rest args)
           (error "(:abbreviation ~S ...): ~?" head-pattern fmt args)))
    (unless (and (consp head-pattern) (symbolp (car head-pattern)) (listp (cdr head-pattern)))
      (fail "the head must be (SYMBOL ?PARAMETER...)."))
    (let ((head (car head-pattern)) (parameters (cdr head-pattern)))
      (unless (and (fresh-symbol-name-p head ledger)
                   (not (member head '(.to .eq .neg .forall) :test #'eq))
                   (not (symbol-used-in-ledger-p head ledger)))
        (fail "~S is not a fresh symbol." head))
      (unless (and (every #'pat-var-p parameters)
                   (= (length parameters) (length (remove-duplicates parameters))))
        (fail "the parameters must be distinct pattern variables."))
      (let ((bound (let ((acc nil))
                     (labels ((walk (x) (when (consp x)
                                          (when (or (named-binder-p x)
                                                    (description-binder-p x (contextual-table ledger)))
                                            (push (second x) acc))
                                          (walk (car x)) (walk (cdr x)))))
                       (walk body))
                     acc)))
        (dolist (v (template-free-pattern-vars body))
          (unless (or (member v parameters) (member v bound))
            (fail "~S in the body is neither a parameter nor bound there." v))))
      (labels ((heads (x) (when (consp x)
                            (when (and (symbolp (car x)) (eq (car x) head))
                              (fail "the body uses ~S itself." head))
                            (heads (car x)) (heads (cdr x)))))
        (heads body)))))

;;; --- Contextual abbreviations: descriptions, as in Principia *14 -----------
;;;
;;; A description (.iota x A), "the x such that A", is an incomplete
;;; symbol: it is not a term of the system, and means something only in
;;; the formula around it. *14.01, with the narrowest scope:
;;;
;;;   (:contextual-abbreviation (.iota ?x ?A) (?psi ?b)
;;;     (.exists ?b (.and (.forall ?x (.iff ?A (.eq ?x ?b))) (?psi ?b))))
;;;
;;; An atomic formula psi(T) holding a description T becomes the body,
;;; with ?x and ?A from T, ?b a fresh variable, and (?psi ?b) the atomic
;;; formula with that occurrence of T replaced by b. Which formulas are
;;; atomic is read off the system's formation rules: a head whose wff?
;;; formation rule asks (wff? ...) of an argument is a connective, and that
;;; argument is a formula position; anything else in a formula position
;;; is atomic. Descriptions are found outermost first, left to right; one
;;; nested in another's A is expanded inside A, where its own narrowest
;;; scope is. A function defined by description, NAME(x) := (.iota y A),
;;; is first expanded to the description, then eliminated the same way.
;;; With existence and uniqueness proved, the scope does not matter
;;; (*14.3); without them, the expansion just says what it says.

(defun contextual-table (ledger)
  "Alist head -> (PARAMETERS PLACEHOLDER . BODY) for LEDGER's contextual
abbreviations."
  (mapcar (lambda (e)
            (destructuring-bind (head-pattern placeholder body) (entry-payload e)
              (list* (car head-pattern) (cdr head-pattern) placeholder body)))
          (entries-of-kind 'contextual-abbreviation ledger)))

(defun formula-argument-positions (head ledger)
  "The 1-based argument positions of HEAD that hold formulas, according to
LEDGER's wff? formation rules, or NIL if HEAD forms an atomic formula."
  (dolist (e (entries-of-kind 'wff? ledger) nil)
    (destructuring-bind (name conditions result) (entry-payload e)
      (declare (ignore name))
      (let ((form (second result)))
        (when (and (consp form) (eq (car form) head))
          (let ((wff-vars (loop for c in conditions
                                when (and (consp c) (eq (car c) 'wff?)) collect (second c))))
            (return (loop for arg in (cdr form) for i from 1
                          when (member arg wff-vars :test #'eq) collect i))))))))

(defun description-p (x table)
  "The table entry if X is a description (HEAD arg...) of TABLE, else NIL."
  (and (consp x) (symbolp (car x))
       (let ((def (assoc (car x) table :test #'eq)))
         (and def (proper-list-p (cdr x)) (= (length (cdr x)) (length (second def))) def))))

(defun first-description-path (x table)
  "The path (list of argument indices) to the first outermost description
among the arguments of atomic formula X, or NIL."
  (labels ((search-in (y path)
             (cond ((description-p y table) (reverse path))
                   ((and (consp y) (proper-list-p y))
                    (loop for arg in (cdr y) for i from 1
                          do (let ((p (search-in arg (cons i path))))
                               (when p (return p)))))
                   (t nil))))
    (and (consp x) (proper-list-p x)
         (loop for arg in (cdr x) for i from 1
               do (let ((p (search-in arg (list i))))
                    (when p (return p)))))))

(defun subtree-at (x path)
  (if (null path) x (subtree-at (nth (car path) x) (cdr path))))

(defun replace-at (x path new)
  "X with the subtree at PATH replaced by NEW (a copy along the path only)."
  (if (null path)
      new
      (loop for item in x for i from 0
            collect (if (= i (car path)) (replace-at item (cdr path) new) item))))

(defun mentions-any-head-p (x heads)
  (cond ((consp x) (or (and (symbolp (car x)) (member (car x) heads :test #'eq))
                       (mentions-any-head-p (car x) heads)
                       (mentions-any-head-p (cdr x) heads)))
        (t nil)))

(defun expand-descriptions-in-formula (formula ledger table counter-cell)
  "FORMULA (written, named binders, ordinary abbreviations expanded) with
every description eliminated (see above). COUNTER-CELL is a cons whose
car is the next fresh %n."
  (labels ((fresh () (prog1 (fresh-var (car counter-cell)) (incf (car counter-cell))))
           (walk (f)
             (let ((positions (and (consp f) (symbolp (car f))
                                   (formula-argument-positions (car f) ledger))))
               (cond
                 ((not (consp f)) f)
                 (positions
                  (loop for item in f for i from 0
                        collect (if (member i positions) (walk item) item)))
                 (t (atomic f)))))
           (atomic (psi)
             (let ((path (first-description-path psi table)))
               (if (null path)
                   psi
                   (let* ((desc (subtree-at psi path))
                          (def (description-p desc table)))
                     (destructuring-bind (parameters placeholder . body) (cdr def)
                       (let* ((b (fresh))
                              (body (rename-body-binders body (append parameters (list (second placeholder)))
                                                         #'fresh))
                              (body (sublis (list (cons (second placeholder) b)) body))
                              (psi-b (replace-at psi path b))
                              (body (subst psi-b (list (first placeholder) b) body :test #'equal))
                              (body (sublis (mapcar #'cons parameters (cdr desc)) body)))
                         (walk (compute-substitutions body)))))))))
    (walk formula)))

(defun expand-descriptions (x ledger)
  "X with descriptions eliminated wherever a formula stands: in each line
of a proof (its formula, and the formulas of a citation's :INST), or in X
itself when it is a formula. A description standing alone, as a term,
is left as it is -- it is not a term."
  (let ((table (contextual-table ledger)))
    (if (or (null table) (not (mentions-any-head-p x (mapcar #'car table))))
        x
        (let ((counter (list (next-fresh-index x table))))
          (labels ((formula (f) (expand-descriptions-in-formula f ledger table counter))
                   (line-p (l) (and (consp l) (proper-list-p l) (= (length l) 4)
                                    (member (third l) '(:hyp :axiom :ir :th :th-ded))))
                   (inst-items (items)
                     (mapcar (lambda (item)
                               (cond ((and (consp item) (= (length item) 3)) ; (P (x) body)
                                      (list (first item) (second item) (formula (third item))))
                                     ((and (consp item) (= (length item) 2)
                                           (atomic-wff-symbol-p (first item) ledger))
                                      (list (first item) (formula (second item))))
                                     (t item)))
                             items))
                   (line (l)
                     (destructuring-bind (num f role by) l
                       (list num (formula f) role
                             (if (and (consp by) (member :inst by))
                                 (let ((after nil))
                                   (mapcar (lambda (a) (prog1 (if (and after (listp a)) (inst-items a) a)
                                                         (setf after (eq a :inst))))
                                           by))
                                 by)))))
            (cond
              ((line-p x) (line x))
              ((and (proper-list-p x) x (every #'line-p x)) (mapcar #'line x))
              ((description-p x table) x)
              (t (formula x))))))))

(defun check-contextual-abbreviation (head-pattern placeholder body ledger)
  "Signal an error unless (:contextual-abbreviation HEAD-PATTERN
PLACEHOLDER BODY) is admissible: a fresh head over distinct pattern
variables, a placeholder (?psi ?b) of two other pattern variables, used
in BODY, whose ?b BODY binds."
  (flet ((fail (fmt &rest args)
           (error "(:contextual-abbreviation ~S ...): ~?" head-pattern fmt args)))
    (check-abbreviation-declaration head-pattern
                                    (subst (second placeholder) placeholder body :test #'equal)
                                    ledger)
    (unless (and (consp placeholder) (= (length placeholder) 2)
                 (every #'pat-var-p placeholder)
                 (not (intersection placeholder (cdr head-pattern))))
      (fail "the placeholder must be (?PSI ?B), two pattern variables not in the head."))
    (unless (occurs-symbol-p (first placeholder) body)
      (fail "the body does not use ~S." placeholder))))
