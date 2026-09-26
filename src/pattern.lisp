;;;; pattern.lisp -- Section 1: pattern matching
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 1. Pattern matching
;;; ---------------------------------------------------------------------
;;;
;;; A pattern variable is any symbol whose name begins with "?" (e.g. ?A,
;;; ?x, ?t). Matching produces an alist of (pat-var . value) bindings, or
;;; the distinguished value +FAIL+ if no consistent match exists. NIL is a
;;; legitimate "matched, zero bindings" result, so it must not be
;;; conflated with failure -- hence the dedicated sentinel.

(defconstant +fail+ '+fail+)

(defun match-fail-p (x) (eq x +fail+))

(defun pat-var-p (x)
  (and (symbolp x)
       (> (length (symbol-name x)) 1)
       (char= (char (symbol-name x) 0) #\?)))

(defun lookup-binding (var binds)
  (assoc var binds :test #'eq))

(defun template-free-pattern-vars (pat)
  "All pattern variables occurring anywhere in PAT."
  (cond ((pat-var-p pat) (list pat))
        ((consp pat) (union (template-free-pattern-vars (car pat))
                             (template-free-pattern-vars (cdr pat))
                             :test #'eq))
        (t nil)))

(defun meta-constructor-p (sym)
  "Alist entry (@name . function) for meta-forms that EXPAND to a value
(e.g. @subst) rather than testing a boolean (e.g. @subst-ok?), or NIL if
SYM names none. META-CONSTRUCTORS-TABLE (section 4) builds the table
fresh on every call rather than caching it in a special variable."
  (assoc sym (meta-constructors-table) :test #'eq))

(defun instantiate-with-binds (pat binds)
  "Replace every pattern variable in PAT with its binding. A pattern
variable with no binding is left as-is (caller's responsibility to check
completeness first)."
  (cond
    ((pat-var-p pat)
     (let ((b (lookup-binding pat binds)))
       (if b (cdr b) pat)))
    ((consp pat)
     (cons (instantiate-with-binds (car pat) binds)
           (instantiate-with-binds (cdr pat) binds)))
    (t pat)))

(defun match-template (pat expr &optional (binds nil))
  "Match PAT against EXPR, extending BINDS. Returns an alist of bindings,
or +FAIL+. A repeated pattern variable must match consistently (EQUAL)
across occurrences.

PAT may contain an embedded meta-constructor call, e.g. (@subst ?x ?t
?A) inside axiom III.1's conclusion pattern. Such a node is evaluated --
not structurally matched -- once ALL of its arguments are already ground
under BINDS (typically because an earlier part of the same template
bound them, matched left-to-right, or they were seeded in beforehand as
an axiom's extra parameter). If some argument is still a free pattern
variable at this point, matching FAILS outright rather than trying to
unify/back-solve it: the caller must supply it from outside (see
CHECK-K-AXIOM-LINE's EXTRA-ARGS) instead of the matcher guessing it."
  (cond
    ((match-fail-p binds) +fail+)
    ((pat-var-p pat)
     (let ((existing (lookup-binding pat binds)))
       (if existing
           (if (equal (cdr existing) expr) binds +fail+)
           (cons (cons pat expr) binds))))
    ((and (consp pat) (meta-constructor-p (car pat)))
     (let ((inst-args (mapcar (lambda (a) (instantiate-with-binds a binds)) (cdr pat))))
       (if (some #'template-free-pattern-vars inst-args)
           +fail+
           (let ((value (apply (cdr (meta-constructor-p (car pat))) inst-args)))
             (match-template value expr binds)))))
    ((and (consp pat) (consp expr))
     (let ((b1 (match-template (car pat) (car expr) binds)))
       (if (match-fail-p b1) +fail+
           (match-template (cdr pat) (cdr expr) b1))))
    ((and (null pat) (null expr)) binds)
    ((equal pat expr) binds)
    (t +fail+)))

;;; A predicate schema symbol P (see PREDICATE-SCHEMA-ARITY) is bound to a
;;; LAMBDA BINDING, (:LAMBDA (x1 ... xn) BODY): "the formula BODY, with
;;; x1..xn as its argument places". An occurrence (P t1 ... tn) then
;;; instantiates to BODY with t1..tn substituted simultaneously for
;;; x1..xn (SCHEMA-BETA). This substitution does not rename bound
;;; variables to avoid capture; it does not have to, because an
;;; instantiated proof is always re-verified in full (see
;;; TRY-DERIVED-ENTRY), so an instance where capture would matter is
;;; simply rejected.

(defun lambda-binding-p (x)
  (and (consp x) (eq (car x) :lambda) (= (length x) 3) (listp (second x))))

(defun schema-beta (lam args)
  "Apply the lambda binding LAM to ARGS (see above). Returns NIL if the
number of arguments does not match."
  (destructuring-bind (params body) (cdr lam)
    (and (= (length params) (length args))
         (substitute-wff-multi params args body))))

(defun distinct-variables-p (xs ledger)
  (and (every (lambda (x) (and (symbolp x) (variable-p x ledger))) xs)
       (= (length xs) (length (remove-duplicates xs :test #'eq)))))

(defun match-schema-atoms (pat expr ledger &optional (binds nil))
  "Like MATCH-TEMPLATE, but the pattern variables are declared ATOMIC-WFF
SYMBOLS (A, B, C, ... per Sigma) rather than ?-prefixed symbols. This is
the matcher used for a :DERIVED entry's own stored proof, whose schema
hypotheses/conclusion were written using bare atomic-wff symbols as
schema placeholders. Declared VARIABLE symbols (v0, v1, ...) are
deliberately NOT treated as schema placeholders here: a schema's own
bound/generalized variables are always written as concrete literals,
matched structurally as-is."
  (cond
    ((match-fail-p binds) +fail+)
    ((and (symbolp pat) (atomic-wff-symbol-p pat ledger))
     (let ((existing (lookup-binding pat binds)))
       (if existing
           (if (equal (cdr existing) expr) binds +fail+)
           (cons (cons pat expr) binds))))
    ;; (P t1 ... tn) for a predicate schema symbol P. Already bound: the
    ;; instance must be EXPR exactly. Unbound: bound here only when the
    ;; arguments are distinct variables (the higher-order "pattern" case,
    ;; where the solution is unique: P := (lambda (t1..tn) EXPR));
    ;; otherwise matching fails and the citation must supply P via :INST.
    ((and (consp pat) (predicate-schema-arity (car pat) ledger))
     (let ((existing (lookup-binding (car pat) binds))
           (args (instantiate-schema-atoms (cdr pat) binds)))
       (cond
         ((/= (length args) (predicate-schema-arity (car pat) ledger)) +fail+)
         (existing
          (if (and (lambda-binding-p (cdr existing))
                   (equal (schema-beta (cdr existing) args) expr))
              binds
              +fail+))
         ((distinct-variables-p args ledger)
          (cons (cons (car pat) (list :lambda args expr)) binds))
         (t +fail+))))
    ((and (consp pat) (consp expr))
     (let ((b1 (match-schema-atoms (car pat) (car expr) ledger binds)))
       (if (match-fail-p b1) +fail+
           (match-schema-atoms (cdr pat) (cdr expr) ledger b1))))
    ((and (null pat) (null expr)) binds)
    ((equal pat expr) binds)
    (t +fail+)))

(defun instantiate-schema-atoms (template binds)
  "Substitute bound atomic-wff schema symbols throughout TEMPLATE using
BINDS (an alist produced by MATCH-SCHEMA-ATOMS). An unbound schema atom
is left as-is."
  (cond
    ((and (symbolp template) (lookup-binding template binds)) (cdr (lookup-binding template binds)))
    ;; (P t1 ... tn) with P bound to a lambda binding: beta-reduce, after
    ;; instantiating the arguments themselves.
    ((and (consp template) (symbolp (car template))
          (let ((b (lookup-binding (car template) binds)))
            (and b (lambda-binding-p (cdr b)))))
     (let ((args (instantiate-schema-atoms (cdr template) binds)))
       (or (and (listp args)
                (schema-beta (cdr (lookup-binding (car template) binds)) args))
           template)))
    ((consp template) (cons (instantiate-schema-atoms (car template) binds)
                             (instantiate-schema-atoms (cdr template) binds)))
    (t template)))
