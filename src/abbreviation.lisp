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
  "T iff SYM is the head of one of LEDGER's abbreviations."
  (and (symbolp sym) sym
       (some (lambda (e) (eq (car (first (entry-payload e))) sym))
             (entries-of-kind 'abbreviation ledger))))

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

(defun rename-body-binders (body parameters fresh)
  "BODY with the variable of every binder that is not one of PARAMETERS
renamed to (FUNCALL FRESH), within its scope."
  (cond
    ((and (named-binder-p body) (not (member (second body) parameters :test #'eq)))
     (let ((new (funcall fresh)))
       (list (first body) new
             (rename-body-binders (substitute-named (second body) new (third body)) parameters fresh))))
    ((named-binder-p body)
     (list (first body) (second body) (rename-body-binders (third body) parameters fresh)))
    ((consp body) (cons (rename-body-binders (car body) parameters fresh)
                        (rename-body-binders (cdr body) parameters fresh)))
    (t body)))

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
  (let ((table (abbreviation-table ledger)))
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
                                   (body (rename-body-binders body parameters #'fresh))
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
                   (not (member head '(.to .eq .neg .forall .iota) :test #'eq))
                   (not (symbol-used-in-ledger-p head ledger)))
        (fail "~S is not a fresh symbol." head))
      (unless (and (every #'pat-var-p parameters)
                   (= (length parameters) (length (remove-duplicates parameters))))
        (fail "the parameters must be distinct pattern variables."))
      (let ((bound (let ((acc nil))
                     (labels ((walk (x) (when (consp x)
                                          (when (named-binder-p x) (push (second x) acc))
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
