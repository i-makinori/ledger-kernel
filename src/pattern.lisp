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
  "Replace bound pattern variables in PAT; unbound ones are left as-is."
  (cond
    ((pat-var-p pat)
     (let ((b (lookup-binding pat binds)))
       (if b (cdr b) pat)))
    ((consp pat)
     (cons (instantiate-with-binds (car pat) binds)
           (instantiate-with-binds (cdr pat) binds)))
    (t pat)))

(defun match-template (pat expr &optional (binds nil))
  "Match PAT against EXPR, extending BINDS; returns bindings or +FAIL+.
A repeated pattern variable must match EQUAL values. An embedded
meta-constructor call, e.g. (@subst ?x ?t ?A), is evaluated and its value
matched; if any argument is still unbound at that point (matching is
left to right) the match fails rather than solving for it, so such
arguments must be supplied up front (e.g. an axiom's extra arguments)."
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

;;; A predicate schema symbol P is bound to a lambda binding
;;; (:LAMBDA (x1 ... xn) BODY); (P t1 ... tn) instantiates to BODY with
;;; t1..tn substituted simultaneously for x1..xn (SCHEMA-BETA). This is
;;; not capture-avoiding; that is safe because an instantiated proof is
;;; always re-verified in full (TRY-DERIVED-ENTRY), which rejects any
;;; instance where capture matters.

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
schema symbols. Declared object variables are matched literally."
  (cond
    ((match-fail-p binds) +fail+)
    ((and (symbolp pat) (atomic-wff-symbol-p pat ledger))
     (let ((existing (lookup-binding pat binds)))
       (if existing
           (if (equal (cdr existing) expr) binds +fail+)
           (cons (cons pat expr) binds))))
    ;; (P t1 ... tn), P a predicate schema. If P is bound, its beta
    ;; instance must equal EXPR. If unbound, bind P := (lambda (t1..tn)
    ;; EXPR) only when the ti are distinct variables (then the solution is
    ;; unique); otherwise fail, and the citation must give P via :INST.
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
  "Instantiate TEMPLATE under BINDS from MATCH-SCHEMA-ATOMS, beta-reducing
predicate-schema applications. Unbound schema symbols are left as-is."
  (cond
    ((and (symbolp template) (lookup-binding template binds)) (cdr (lookup-binding template binds)))
    ;; (P t1 ... tn), P bound to a lambda: instantiate args, beta-reduce.
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
