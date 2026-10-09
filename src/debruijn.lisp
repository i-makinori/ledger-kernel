;;;; debruijn.lisp -- bound variables as de Bruijn indices (machine B)
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; Inside the kernel a bound variable has no name. A binder is written
;;; (Q BODY) -- two elements, where the surface syntax has (Q x BODY) --
;;; and an occurrence of the variable it binds is (:BV n), n being the
;;; number of binders between the occurrence and its own binder (the de
;;; Bruijn index; 0 = the nearest).
;;;
;;;   surface   (.forall v0 (.forall v1 (.eq v0 v1)))
;;;   kernel    (.forall (.forall (.eq (:bv 1) (:bv 0))))
;;;
;;; Consequences:
;;;   - alpha-equivalent formulas are EQUAL, so every comparison in the
;;;     kernel (hypotheses, conclusions, memoization keys) is modulo
;;;     renaming of bound variables;
;;;   - substituting a term for a free variable is plain replacement of a
;;;     symbol: a bound variable is not a symbol, so it cannot capture;
;;;   - free variables keep their names: they are the ones that mean
;;;     something (a fixed but arbitrary object, a witness, a parameter).
;;;
;;; The conversion happens once, where data enters the kernel
;;; (CHECK-K-PROOF, CHECK-AND-EXTEND, JUDGEMENT?, ...): NAMED->DB is
;;; idempotent, so passing kernel data back through it changes nothing.
;;; Stored entries keep the surface text in their ORIGIN, for display and
;;; for saving; the kernel only ever reads the converted PAYLOAD.
;;;
;;; Opening a binder. The rules in a .system file are written with named
;;; binders, e.g. III.1 is (.to (.forall ?x ?A) (@subst ?x ?t ?A)). To
;;; match (.forall ?x ?A) against a kernel formula (.forall BODY), the
;;; matcher OPENS BODY with a variable: it replaces the index that points
;;; at this binder by that variable, and matches ?A against the result.
;;; The variable is either the one ?x is already bound to (Gen: the x
;;; being generalized, which must then not occur in BODY), or a FRESH
;;; variable %0, %1, ... that occurs nowhere in the rule application.
;;; Fresh variables are determined by the input alone (the next number
;;; above every %n already present), never by a counter or other hidden
;;; state, so re-verifying the same proof always makes the same choices.

;;; --- Shapes -------------------------------------------------------------

(defun bvar (n) (list :bv n))

(defun bvar-p (x)
  "T iff X is a bound-variable occurrence (:BV n)."
  (and (consp x) (eq (car x) :bv)
       (consp (cdr x)) (integerp (cadr x)) (>= (cadr x) 0)
       (null (cddr x))))

(defun binder-head-p (x)
  (and (symbolp x) (member x (binder-heads) :test #'eq)))

(defun db-binder-p (x)
  "T iff X is a kernel binder (Q BODY)."
  (and (consp x) (binder-head-p (car x))
       (consp (cdr x)) (null (cddr x))))

(defun named-binder-p (x)
  "T iff X is a surface binder (Q v BODY) with V a symbol."
  (and (consp x) (symbolp (car x)) (binder-head-p (car x))
       (consp (cdr x)) (consp (cddr x)) (null (cdddr x))
       (second x) (symbolp (second x))))

;;; --- Fresh variables %0, %1, ... ----------------------------------------

(defun fresh-var-index (sym)
  "N if SYM is the fresh variable %N, else NIL."
  (and (symbolp sym)
       (let ((s (symbol-name sym)))
         (and (> (length s) 1)
              (char= (char s 0) #\%)
              (loop for i from 1 below (length s) always (digit-char-p (char s i)))
              (parse-integer s :start 1)))))

(defun fresh-var-name-p (sym)
  (and (fresh-var-index sym) t))

(defun fresh-var (n)
  "The fresh variable %N."
  (intern (format nil "%~D" n) :ledger-kernel))

(defun next-fresh-index (&rest trees)
  "1 + the largest N such that %N occurs in TREES (0 if none): %N and
everything above it is fresh for TREES."
  (let ((best -1))
    (labels ((walk (x)
               (cond ((consp x) (walk (car x)) (walk (cdr x)))
                     (t (let ((n (fresh-var-index x)))
                          (when (and n (> n best)) (setf best n)))))))
      (walk trees))
    (1+ best)))

;;; --- Bound-variable names ?BV1, ?BV2, ... -------------------------------
;;;
;;; The one name a bound variable is shown and written with, in a theorem
;;; as in a rule (system-spec.lisp): "bound variable n". It has the shape
;;; of a pattern variable, so it can never be a declared symbol, and it is
;;; accepted as the variable of a binder in any input.

(defun bound-pattern-variable (n)
  "The name ?BVn."
  (intern (format nil "?BV~D" n) :ledger-kernel))

(defun bound-pattern-variable-name-p (sym)
  "T iff SYM is a bound-variable name ?BVn (n = 1, 2, ...)."
  (and (symbolp sym)
       (let ((s (symbol-name sym)))
         (and (> (length s) 3) (string= (subseq s 0 3) "?BV")
              (every #'digit-char-p (subseq s 3))
              (char/= (char s 3) #\0)))))

;;; --- Surface <-> kernel ---------------------------------------------------

(defun named->db (x ledger &key (expand t))
  "Convert every surface binder (Q v BODY) in X whose V is a variable of
LEDGER into (Q BODY') with V's occurrences replaced by indices. Anything
else is left alone, so the function is idempotent and can be applied to a
whole proof line (numbers, roles and rule names pass through). A binder
whose V is not a variable is not converted, and fails the formation
rules later as it always did.
EXPAND NIL skips abbreviation expansion; only for display, where an
entry is shown as written."
  (labels ((conv (x env)
             (cond
               ((symbolp x)
                (let ((pos (position x env :test #'eq)))
                  (if pos (bvar pos) x)))
               ((and (named-binder-p x)
                     (or (variable-p (second x) ledger)
                         (bound-pattern-variable-name-p (second x))))
                (list (first x) (conv (third x) (cons (second x) env))))
               ((consp x) (cons (conv (car x) env) (conv (cdr x) env)))
               (t x))))
    ;; Abbreviations are expanded first, so the kernel only ever sees a
    ;; system's primitive symbols (abbreviation.lisp).
    (conv (if expand (expand-abbreviations x ledger) x) nil)))

(defun contains-raw-index-p (x)
  "T iff X contains a (:BV ...) form. Written input must name its bound
variables: NAMED->DB passes a raw index through unchanged, where an
enclosing binder captures it, so the kernel would check something other
than the text stored and shown -- (.forall v0 (.eq v0 (:bv 0))) would be
admitted as forall x. x = x. The entry points for written input (CHECK-K-PROOF,
CHECK-AND-EXTEND, CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT, JUDGEMENT?) refuse
it; data already in kernel form never goes back through them."
  (and (consp x)
       (or (eq (car x) :bv)
           (contains-raw-index-p (car x))
           (contains-raw-index-p (cdr x)))))

(defun named->db-proof (raw-proof ledger)
  "NAMED->DB applied to every line of RAW-PROOF (formula and BY)."
  (named->db raw-proof ledger))

(defun pattern->db (pat)
  "As NAMED->DB, for a rule pattern: a binder whose variable is a concrete
symbol, e.g. (.forall z ...) in a defining axiom, is converted; a binder
over a pattern variable, (.forall ?x ?A), is kept, because the matcher
opens it (MATCH-TEMPLATE). A pattern binder is not counted in the
indices of the concrete binders around it: by the time the matcher is
inside it, the concrete side has been opened, which removes one level."
  (labels ((conv (x env)
             (cond
               ((pat-var-p x) x)
               ((symbolp x)
                (let ((pos (position x env :test #'eq)))
                  (if pos (bvar pos) x)))
               ((and (named-binder-p x) (not (pat-var-p (second x))))
                (list (first x) (conv (third x) (cons (second x) env))))
               ((named-binder-p x)
                (list (first x) (second x) (conv (third x) env)))
               ((consp x) (cons (conv (car x) env) (conv (cdr x) env)))
               (t x))))
    (conv pat nil)))

;;; --- Opening and closing ----------------------------------------------

(defun db-open (body term)
  "BODY, the inside of a binder, with the index pointing at that binder
replaced by TERM (a locally closed term, e.g. a variable) and every index
pointing further out lowered by one."
  (labels ((walk (x depth)
             (cond
               ((bvar-p x)
                (let ((i (second x)))
                  (cond ((= i depth) term)
                        ((> i depth) (bvar (1- i)))
                        (t x))))
               ((db-binder-p x) (list (first x) (walk (second x) (1+ depth))))
               ((consp x) (cons (walk (car x) depth) (walk (cdr x) depth)))
               (t x))))
    (walk body 0)))

(defun db-close (expr var)
  "The inverse of DB-OPEN: EXPR with the variable VAR turned into the
index of a new binder around it, and every index already pointing
outside EXPR raised by one. (Q (DB-CLOSE E v)) is \"Q v. E\"."
  (labels ((walk (x depth)
             (cond
               ((eq x var) (bvar depth))
               ((bvar-p x)
                (if (>= (second x) depth) (bvar (1+ (second x))) x))
               ((db-binder-p x) (list (first x) (walk (second x) (1+ depth))))
               ((consp x) (cons (walk (car x) depth) (walk (cdr x) depth)))
               (t x))))
    (walk expr 0)))

(defun locally-closed-p (x)
  "T iff every index in X points at a binder inside X."
  (labels ((walk (x depth)
             (cond
               ((bvar-p x) (< (second x) depth))
               ((db-binder-p x) (walk (second x) (1+ depth)))
               ((consp x) (and (walk (car x) depth) (walk (cdr x) depth)))
               (t t))))
    (walk x 0)))

(defun occurs-symbol-p (sym x)
  "T iff the symbol SYM occurs anywhere in X. In kernel form every symbol
occurrence of a variable is a free occurrence."
  (cond ((eq sym x) t)
        ((consp x) (or (occurs-symbol-p sym (car x)) (occurs-symbol-p sym (cdr x))))
        (t nil)))

;;; --- Back to the surface (for display only) -----------------------------

(defun db->bv-named (x &optional (start 1))
  "Kernel form X with its binders named ?BV<start>, ?BV<start+1>, ... in
order of appearance (a preorder walk), for display. Distinct binders get
distinct names, so nothing is shadowed and NAMED->DB gives back X. A
rule's own binders over pattern variables, (Q ?x P), are left as they
are and not counted."
  (let ((n (1- start)))
    (labels ((conv (x env)
               (cond
                 ((bvar-p x) (or (nth (second x) env) x))
                 ((db-binder-p x)
                  (let ((v (bound-pattern-variable (incf n))))
                    (list (first x) v (conv (second x) (cons v env)))))
                 ((consp x) (cons (conv (car x) env) (conv (cdr x) env)))
                 (t x))))
      (conv x nil))))

(defun db->named (x ledger)
  "A surface form of kernel form X, naming each binder with the first
declared variable of LEDGER that is neither free in its body nor the name
of an enclosing binder (a fresh %n if the declared ones run out). For
display; the kernel never reads the result."
  (let ((candidates (sigma-variable-symbols ledger)))
    (labels ((pick (body outer)
               (or (find-if (lambda (v) (and (not (member v outer :test #'eq))
                                             (not (occurs-symbol-p v body))))
                            candidates)
                   (fresh-var (next-fresh-index body outer))))
             (conv (x env)
               (cond
                 ((bvar-p x) (or (nth (second x) env) x))
                 ((db-binder-p x)
                  (let ((v (pick (second x) env)))
                    (list (first x) v (conv (second x) (cons v env)))))
                 ((consp x) (cons (conv (car x) env) (conv (cdr x) env)))
                 (t x))))
      (conv x nil))))

(defun substitute-named (var term form)
  "Surface-syntax substitution: FORM with TERM replacing the free
occurrences of VAR, stopping under a binder that rebinds VAR. Not
capture-avoiding. Only for tools that build surface text (a proof, a
pattern) which the kernel then converts and checks; the kernel itself
substitutes with SUBSTITUTE-WFF on kernel form."
  (cond
    ((eq form var) term)
    ((named-binder-p form)
     (if (eq (second form) var)
         form
         (list (first form) (second form) (substitute-named var term (third form)))))
    ((consp form) (cons (substitute-named var term (car form)) (substitute-named var term (cdr form))))
    (t form)))
