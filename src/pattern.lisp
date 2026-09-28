;;;; pattern.lisp -- pattern matching and instantiation

(in-package :ledger-kernel)

;;; Pattern variables are symbols named ?... (?A, ?x). Matching returns an
;;; alist of (pat-var . value) or the sentinel +FAIL+; NIL cannot signal
;;; failure because it is the valid "matched, no bindings" result.

(defconstant +fail+ '+fail+)

(defun match-fail-p (x) (eq x +fail+))

(defun pat-var-p (x)
  "T iff X is a pattern variable (a symbol named ?...)."
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
  "Entry (@name . function) for a meta-constructor SYM (a meta-form that
computes a value, like @subst), or NIL."
  (assoc sym (meta-constructors-table) :test #'eq))

(defun instantiate-with-binds (pat binds)
  "Replace bound pattern variables in PAT; unbound ones are left as-is.
A pattern binder (Q ?x P) whose ?x is bound to a variable v becomes the
kernel binder (Q (DB-CLOSE P' v)) -- e.g. IOTA's (.iota ?x ?A)."
  (cond
    ((pat-var-p pat)
     (let ((b (lookup-binding pat binds)))
       (if b (cdr b) pat)))
    ((pattern-binder-p pat)
     (let ((b (lookup-binding (second pat) binds)))
       (if (and b (cdr b) (symbolp (cdr b)))
           (list (first pat) (db-close (instantiate-with-binds (third pat) binds) (cdr b)))
           (cons (first pat) (instantiate-with-binds (cdr pat) binds)))))
    ((named-binder-p pat) (instantiate-with-binds (pattern->db pat) binds))
    ((consp pat)
     (cons (instantiate-with-binds (car pat) binds)
           (instantiate-with-binds (cdr pat) binds)))
    (t pat)))

;;; --- Fresh variables in bindings ---------------------------------------
;;;
;;; Opening a binder needs a variable that occurs nowhere else in the rule
;;; application (debruijn.lisp). The first one is chosen above every %n in
;;; the inputs; the caller records that in the bindings under the key
;;; :NEXT-FRESH (SEED-FRESH), and each opening takes the next one. The
;;; choice depends only on the inputs, so a re-check repeats it exactly.

(defun seed-fresh (binds &rest trees)
  "BINDS with :NEXT-FRESH set above every %n in TREES and in BINDS."
  (acons :next-fresh (apply #'next-fresh-index binds trees) binds))

(defun take-fresh (binds &rest trees)
  "(VALUES v new-binds): the next fresh variable and BINDS advanced past
it. Without a seed, falls back to what TREES and BINDS contain."
  (let ((n (or (cdr (assoc :next-fresh binds))
               (apply #'next-fresh-index binds trees))))
    (values (fresh-var n) (acons :next-fresh (1+ n) binds))))

(defun pattern-binder-p (pat)
  "T iff PAT is a binder over a pattern variable, (Q ?x P)."
  (and (named-binder-p pat) (pat-var-p (second pat))))

(defun match-template (pat expr &optional (binds nil))
  "Match PAT against EXPR, extending BINDS; returns bindings or +FAIL+.
A repeated pattern variable must match EQUAL values, and a pattern
variable only ever binds a locally closed value (never a bare index).
An embedded meta-constructor call, e.g. (@subst ?x ?t ?A), is evaluated
and its value matched; if any argument is still unbound at that point
(matching is left to right) the match fails rather than solving for it,
so such arguments must be supplied up front (e.g. an axiom's extra
arguments).

A pattern binder (Q ?x P) matches a kernel binder (Q BODY) by opening
BODY: if ?x is already bound to a variable v (Gen's x), v must not occur
in BODY and P is matched against BODY opened with v; otherwise ?x is
bound to a fresh variable (TAKE-FRESH) and BODY is opened with that."
  (cond
    ((match-fail-p binds) +fail+)
    ((pat-var-p pat)
     (let ((existing (lookup-binding pat binds)))
       (cond (existing (if (equal (cdr existing) expr) binds +fail+))
             ((or (atom expr) (locally-closed-p expr)) (cons (cons pat expr) binds))
             (t +fail+))))
    ((atom pat) (if (equal pat expr) binds +fail+))
    ((pattern-binder-p pat)
     (if (and (db-binder-p expr) (eq (first pat) (first expr)))
         (let* ((x (second pat))
                (body (second expr))
                (existing (lookup-binding x binds)))
           (if existing
               (let ((v (cdr existing)))
                 (if (and v (symbolp v) (not (occurs-symbol-p v body)))
                     (match-template (third pat) (db-open body v) binds)
                     +fail+))
               (multiple-value-bind (f b1) (take-fresh binds expr)
                 (match-template (third pat) (db-open body f) (cons (cons x f) b1)))))
         +fail+))
    ;; A binder over a concrete variable, e.g. in a defining axiom:
    ;; convert it and match structurally.
    ((named-binder-p pat) (match-template (pattern->db pat) expr binds))
    ((meta-constructor-p (car pat))
     (let ((inst-args (mapcar (lambda (a) (instantiate-with-binds a binds)) (cdr pat))))
       (if (some #'template-free-pattern-vars inst-args)
           +fail+
           (let ((value (apply (cdr (meta-constructor-p (car pat))) inst-args)))
             (match-template value expr binds)))))
    ((consp expr)
     (let ((b1 (match-template (car pat) (car expr) binds)))
       (if (match-fail-p b1) +fail+
           (match-template (cdr pat) (cdr expr) b1))))
    (t +fail+)))

;;; A predicate schema symbol P is bound to a lambda binding
;;; (:LAMBDA (x1 ... xn) BODY); (P t1 ... tn) instantiates to BODY with
;;; t1..tn substituted simultaneously for x1..xn (SCHEMA-BETA). Stored
;;; proofs are in kernel form, so BODY has no named binders to capture
;;; with; and an instantiated proof is re-verified in full anyway
;;; (TRY-DERIVED-ENTRY).

(defun lambda-binding-p (x)
  "T iff X has the shape (:LAMBDA params body)."
  (and (consp x) (eq (car x) :lambda) (= (length x) 3) (listp (second x))))

(defun schema-beta (lam args)
  "Beta-reduce lambda binding LAM applied to ARGS; NIL on arity mismatch."
  (destructuring-bind (params body) (cdr lam)
    (and (= (length params) (length args))
         (substitute-wff-multi params args body))))

(defun distinct-variables-p (xs ledger)
  "T iff XS are pairwise distinct declared variables."
  (and (every (lambda (x) (and (symbolp x) (variable-p x ledger))) xs)
       (= (length xs) (length (remove-duplicates xs :test #'eq)))))

(defun match-schema-atoms (pat expr ledger &optional (binds nil))
  "Like MATCH-TEMPLATE, for a derived entry's stored schema: the pattern
variables are the declared atomic-wff symbols (A, B, ...) and predicate
schema symbols. Declared object variables are matched literally.
Both sides are kernel forms; a binder on both sides is opened with the
same fresh variable, so a schema under it sees a variable, not an index:
(P (:bv 0)) against (.in (:bv 0) v1) becomes (P %n) against (.in %n v1).
An atomic symbol can therefore never capture a bound variable: its value
would contain %n, which the instantiated proof cannot turn back into the
binder, and the final comparison fails. Dependence on a bound variable is
written with a predicate schema and its argument, P(x)."
  (cond
    ((match-fail-p binds) +fail+)
    ((and (symbolp pat) (atomic-wff-symbol-p pat ledger))
     (let ((existing (lookup-binding pat binds)))
       (cond (existing (if (equal (cdr existing) expr) binds +fail+))
             ((locally-closed-p expr) (cons (cons pat expr) binds))
             (t +fail+))))
    ((db-binder-p pat)
     (if (and (db-binder-p expr) (eq (first pat) (first expr)))
         (multiple-value-bind (f b1) (take-fresh binds pat expr)
           (match-schema-atoms (db-open (second pat) f) (db-open (second expr) f) ledger b1))
         +fail+))
    ;; (P t1 ... tn), P a predicate schema. If P is bound, its beta
    ;; instance must equal EXPR. If unbound, bind P := (lambda (t1..tn)
    ;; EXPR) only when the ti are distinct variables (then the solution is
    ;; unique); otherwise fail, and the citation must give P via :INST.
    ((and (consp pat) (predicate-schema-arity (car pat) ledger))
     (let ((existing (lookup-binding (car pat) binds))
           (args (instantiate-schema-atoms (cdr pat) binds)))
       (cond
         ((/= (length args) (predicate-schema-arity (car pat) ledger)) +fail+)
         ((not (locally-closed-p expr)) +fail+)
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

(defun instantiate-schema-atoms (template binds &optional next)
  "Instantiate TEMPLATE under BINDS from MATCH-SCHEMA-ATOMS, beta-reducing
predicate-schema applications. Unbound schema symbols are left as-is.
A binder is opened with a fresh variable (numbered from NEXT, by default
BINDS' :NEXT-FRESH), instantiated inside, and closed again, so the terms
substituted for a schema's arguments are always locally closed."
  (let ((next (or next
                  (cdr (assoc :next-fresh binds))
                  (next-fresh-index template binds))))
    (labels ((inst (x)
               (cond
                 ((and (symbolp x) x (not (keywordp x)) (lookup-binding x binds))
                  (cdr (lookup-binding x binds)))
                 ((db-binder-p x)
                  (let ((g (fresh-var next)))
                    (list (first x)
                          (db-close (instantiate-schema-atoms (db-open (second x) g) binds (1+ next)) g))))
                 ;; (P t1 ... tn), P bound to a lambda: instantiate args, beta-reduce.
                 ((and (consp x) (symbolp (car x))
                       (let ((b (lookup-binding (car x) binds)))
                         (and b (lambda-binding-p (cdr b)))))
                  (let ((args (mapcar #'inst (cdr x))))
                    (or (schema-beta (cdr (lookup-binding (car x) binds)) args)
                        x)))
                 ((consp x) (cons (inst (car x)) (inst (cdr x))))
                 (t x))))
      (inst template))))
