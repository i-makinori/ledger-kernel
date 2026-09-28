;;;; meta.lisp -- meta predicates (@...? side conditions) and
;;;; meta-constructors (@subst): free variables and substitution,
;;;; on kernel (de Bruijn) formulas.

(in-package :ledger-kernel)

;;; Kernel formulas are in de Bruijn form (debruijn.lisp): a bound
;;; variable is an index, never a symbol. So "the free variables" are just
;;; the variable symbols that occur, and substitution is plain replacement
;;; -- neither needs to know where the binders are.

(defun %free-vars (expr ledger)
  "The variables (declared, or fresh %n) occurring in kernel form EXPR."
  (let ((acc nil))
    (labels ((walk (x)
               (cond ((consp x) (walk (car x)) (walk (cdr x)))
                     ((and x (symbolp x) (variable-p x ledger)) (pushnew x acc :test #'eq)))))
      (walk expr))
    (nreverse acc)))

(defun free-vars-wff (wff ledger)
  "The free variables of WFF (surface or kernel form)."
  (%free-vars (named->db wff ledger) ledger))

(defun meta-not-free-in? (ledger open-hyps var wff)
  "@not-free-in?: T iff VAR is not free in WFF (kernel form; a surface
form is converted first)."
  (declare (ignore open-hyps))
  (not (occurs-symbol-p var (named->db wff ledger))))

(defun meta-not-free-in-dependencies? (ledger open-hyps var)
  "@not-free-in-dependencies?: Gen's restriction. T iff VAR is free in
none of OPEN-HYPS, the hypotheses open at this point of the current proof."
  (every (lambda (hyp-wff) (meta-not-free-in? ledger nil var hyp-wff)) open-hyps))

(defun substitute-wff (var term wff)
  "Kernel form WFF with TERM replacing the variable VAR. Every occurrence
of the symbol VAR is free (bound ones are indices), and TERM is locally
closed, so this is capture-free by construction."
  (cond
    ((eq wff var) term)
    ((consp wff) (cons (substitute-wff var term (car wff)) (substitute-wff var term (cdr wff))))
    (t wff)))

(defun meta-subst-ok? (ledger open-hyps var term wff)
  "@subst-ok?: T iff substituting TERM for VAR in WFF can capture nothing.
In kernel form that is a property of the shapes alone: TERM and WFF are
locally closed (no index points outside them) and VAR is a symbol.
It holds for every formula the kernel builds; it is checked anyway, so
that a bug in the conversion or in opening binders is caught here
instead of silently admitting a captured instance."
  (declare (ignore ledger open-hyps))
  (and (symbolp var) var
       (locally-closed-p term)
       (locally-closed-p wff)))

(defun meta-subst (ledger var term wff)
  "SUBSTITUTE-WFF with the meta-predicate calling convention."
  (declare (ignore ledger))
  (substitute-wff var term wff))

(defun substitute-wff-multi (vars terms wff)
  "Simultaneously substitute TERMS for VARS in WFF (used by SCHEMA-BETA).
Goes through fresh gensyms so that one term's variables are never
rewritten by a later substitution."
  (let ((temps (mapcar (lambda (v) (gensym (symbol-name v))) vars)))
    (let ((swapped (reduce (lambda (w pair) (substitute-wff (car pair) (cdr pair) w))
                            (mapcar #'cons vars temps) :initial-value wff)))
      (reduce (lambda (w pair) (substitute-wff (car pair) (cdr pair) w))
              (mapcar #'cons temps terms) :initial-value swapped))))

(defun meta-substitutes? (ledger open-hyps var term wff result)
  "@substitutes?: T iff RESULT = WFF with TERM substituted for VAR.
A side condition checked after matching, not an embedded @subst evaluated
during it, so that RESULT can be bound structurally before TERM is known
(e.g. a witness variable supplied only as an extra parameter)."
  (declare (ignore ledger open-hyps))
  (equal (substitute-wff var term wff) result))

(defun meta-predicates-table ()
  "Alist of @-tagged side conditions to their functions."
  (list (cons '@not-free-in? #'meta-not-free-in?)
        (cons '@not-free-in-dependencies? #'meta-not-free-in-dependencies?)
        (cons '@subst-ok? #'meta-subst-ok?)
        (cons '@substitutes? #'meta-substitutes?)))

(defun meta-constructors-table ()
  "Alist of @-tagged meta-constructors to their functions."
  (list (cons '@subst (lambda (var term wff) (substitute-wff var term wff)))))
