;;;; meta.lisp -- meta predicates (@...? side conditions) and
;;;; meta-constructors (@subst): free variables and substitution.

(in-package :ledger-kernel)

(defun free-vars-wff (wff ledger)
  "Declared variables (per LEDGER's signature) occurring in WFF outside
any binder for them."
  (labels ((walk (form bound)
             (cond
               ((and (symbolp form) (variable-p form ledger) (not (member form bound :test #'eq)))
                (list form))
               ((symbolp form) nil)
               ((and (consp form) (member (car form) (binder-heads) :test #'eq))
                (let ((x (second form)) (body (third form)))
                  (walk body (cons x bound))))
               ((consp form)
                (union (walk (car form) bound) (walk (cdr form) bound) :test #'eq))
               (t nil))))
    (walk wff nil)))

(defun meta-not-free-in? (ledger open-hyps var wff)
  "@not-free-in?: T iff VAR is not free in WFF."
  (declare (ignore open-hyps))
  (not (member var (free-vars-wff wff ledger) :test #'eq)))

(defun meta-not-free-in-dependencies? (ledger open-hyps var)
  "@not-free-in-dependencies?: Gen's restriction. T iff VAR is free in
none of OPEN-HYPS, the hypotheses open at this point of the current proof."
  (every (lambda (hyp-wff) (meta-not-free-in? ledger nil var hyp-wff)) open-hyps))

(defun count-bound-occurrences (var wff)
  "Number of binders for VAR in WFF."
  (labels ((walk (form)
             (cond
               ((and (consp form) (member (car form) (binder-heads) :test #'eq))
                (+ (if (eq (second form) var) 1 0) (walk (third form))))
               ((consp form) (+ (walk (car form)) (walk (cdr form))))
               (t 0))))
    (walk wff)))

(defun substitute-wff (var term wff)
  "WFF with TERM replacing the free occurrences of VAR. Not
capture-avoiding: guard with @subst-ok? where capture matters."
  (cond
    ((eq wff var) term)
    ((and (consp wff) (member (car wff) (binder-heads) :test #'eq))
     (if (eq (second wff) var)
         wff ;; VAR is shadowed: stop
         (list (first wff) (second wff) (substitute-wff var term (third wff)))))
    ((consp wff) (cons (substitute-wff var term (car wff)) (substitute-wff var term (cdr wff))))
    (t wff)))

(defun meta-subst-ok? (ledger open-hyps var term wff)
  "@subst-ok?: T iff substituting TERM for VAR in WFF captures nothing.
Fails if any binder not shadowing VAR binds a free variable of TERM
(conservatively, even when VAR does not occur beneath it)."
  (declare (ignore open-hyps))
  (let ((before (count-bound-occurrences var wff))
        (term-vars (free-vars-wff term ledger)))
    (declare (ignore before))
    (labels ((walk (form)
               (cond
                 ((eq form var) t)
                 ((and (consp form) (member (car form) (binder-heads) :test #'eq))
                  (if (eq (second form) var)
                      t ;; shadowed: no substitution below
                      (and (not (member (second form) term-vars :test #'eq))
                           (walk (third form)))))
                 ((consp form) (and (walk (car form)) (walk (cdr form))))
                 (t t))))
      (walk wff))))

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
