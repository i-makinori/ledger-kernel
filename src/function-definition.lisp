;;;; function-definition.lisp -- DEFINE-FUNCTION-BY-DESCRIPTION
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; Definition by description. Given ledger theorems
;;;   EXISTENCE:   forall x1..xn. exists y. A(x1,...,xn,y)
;;;   UNIQUENESS:  forall x1..xn. forall y. forall y2.
;;;                  (A(...,y) -> (A(...,y2) -> y=y2))
;;; this admits a new n-ary function symbol NAME as an ABBREVIATION
;;; (abbreviation.lisp):
;;;   NAME(x1,...,xn)  :=  (.iota y A(x1,...,xn,y))      "the y such that A"
;;; and the theorem NAME-DEF, A(x1,...,xn, NAME(x1,...,xn)). Nothing is
;;; added as an axiom or a rule: NAME is expanded before the kernel sees
;;; it, the description at each atomic formula as in Principia *14.01
;;; (see 00-connectives.system), and NAME-DEF is an ordinary checked
;;; theorem (cite it with :inst to use it at other arguments).
;;;
;;; NAME-DEF is proved as in Principia *14: with Phi(c) = forall y (A <-> y = c),
;;;   - existence and uniqueness give  exists c Phi(c)        (th-desc-proper)
;;;   - Phi(c) |- A(c), by III.1 at c and c = c
;;;   - Phi(c) |- A(c) <-> A(NAME(x)), built along A: at each atomic
;;;     formula by th-desc-atomic, through not, -> and forall by
;;;     th-iff-neg, th-iff-imp and th-iff-forall
;;;   - so Phi(c) -> A(NAME(x)) (the auxiliary TH-DED NAME-DEF.S1), and
;;;     exists-elimination closes it.
;;; The lemmas are those of 07-quantifier-schemas.ledger, which must be
;;; loaded. In this first version every atomic formula of A holds Y at
;;; most once, and A holds no other description.

(defun rename-many (pairs form)
  "Substitute each (OLD . NEW) of PAIRS into FORM, in order. Order does not
matter because callers only use fresh NEW symbols that do not occur in FORM."
  (dolist (p pairs form) (setf form (subst (cdr p) (car p) form))))

;;; Checked beforehand (CHECK-DEFINITION-SHAPE), so that the abbreviation
;;; means what it says:
;;;   - NAME is a symbol the ledger has never used, so it gets one meaning.
;;;   - The free variables of A are among X1..Xn, Y: NAME(x) is a term in
;;;     x alone. (A free parameter z would leave z free in NAME's
;;;     expansion, behind the reader's back.)
;;;   - X1..Xn, Y, Y2 are distinct declared variables, Y2 does not occur
;;;     in A, and none of them is the variable of a binder inside A, so
;;;     the plain renamings below (Y to Y2, Xi to ?Xi) change exactly the
;;;     free occurrences and capture nothing.

(defun binder-variables-named (form)
  "The variables of the surface binders (Q v BODY) anywhere in FORM."
  (let ((acc nil))
    (labels ((walk (x)
               (when (consp x)
                 (when (named-binder-p x) (pushnew (second x) acc :test #'eq))
                 (walk (car x))
                 (walk (cdr x)))))
      (walk form))
    acc))

(defun check-definition-shape (ledger name arg-vars y-var y2-var a-formula)
  "Signal an error unless NAME, ARG-VARS, Y-VAR, Y2-VAR and A-FORMULA meet
the conditions above."
  (flet ((fail (fmt &rest args)
           (error "DEFINE-FUNCTION-BY-DESCRIPTION: ~?" fmt args)))
    (unless (and (fresh-symbol-name-p name ledger)
                 (not (symbol-used-in-ledger-p name ledger)))
      (fail "~S is not a fresh symbol (already used in the ledger, or ~
             reserved); a second definition of a symbol is refused." name))
    (unless (listp arg-vars)
      (fail "ARG-VARS ~S is not a list." arg-vars))
    (let ((all (append arg-vars (list y-var y2-var))))
      (unless (distinct-variables-p all ledger)
        (fail "ARG-VARS, Y-VAR and Y2-VAR ~S must be distinct declared variables." all))
      (unless (judgement? 'wff? a-formula ledger)
        (fail "A-FORMULA ~S is not a well-formed formula." a-formula))
      (let ((extra (set-difference (free-vars-wff a-formula ledger)
                                   (cons y-var arg-vars) :test #'eq)))
        (when extra
          (fail "A-FORMULA has free variables ~S that are neither arguments ~
                 nor Y-VAR; NAME could not depend on them." extra)))
      (when (occurs-symbol-p y2-var a-formula)
        (fail "Y2-VAR ~S occurs in A-FORMULA." y2-var))
      (let ((clash (intersection (binder-variables-named a-formula) all :test #'eq)))
        (when clash
          (fail "A-FORMULA binds ~S, which is also an argument, Y-VAR or ~
                 Y2-VAR; rename the bound variable." clash))))))

(defun forall-prefix (vars body)
  "(.forall v1 (.forall v2 ... BODY))."
  (if (null vars) body (list '.forall (car vars) (forall-prefix (cdr vars) body))))

(defun strip-foralls-proof (start formula vars cited)
  "Lines numbered from START that take FORMULA = forall VARS. B (proved at
line CITED) to B by III.1 with each variable itself and MP. Returns
(VALUES lines last-line-number B)."
  (let ((lines nil) (n start) (at cited) (f formula))
    (dolist (v vars (values (nreverse lines) at f))
      (let ((body (third f)))
        (push (list n (list '.to f body) :axiom (list 'III.1 v)) lines)
        (push (list (1+ n) body :ir (list 'MP n at)) lines)
        (setf at (1+ n) n (+ n 2) f body)))))

;;; --- NAME-DEF along the structure of A ------------------------------------

(defparameter *description-lemmas*
  '(th-iff-refl th-iff-mp th-iff-mpr th-iff-sym th-iff-neg th-iff-imp th-iff-forall
    th-desc-proper th-desc-atomic th-exists-elim)
  "The ledger lemmas the NAME-DEF proof cites.")

(defun count-symbol (sym x)
  (cond ((eq sym x) 1)
        ((consp x) (+ (count-symbol sym (car x)) (count-symbol sym (cdr x))))
        (t 0)))

(defun description-witness-variable (ledger avoid)
  "A declared variable, not among AVOID nor V0..V3 (the variables of the
description lemmas), for the witness c of the NAME-DEF proof."
  (or (find-if (lambda (v) (not (member v (append avoid '(v0 v1 v2 v3)) :test #'eq)))
               (sigma-variable-symbols ledger))
      (error "DEFINE-FUNCTION-BY-DESCRIPTION: no declared variable is left ~
              for the witness of the NAME-DEF proof; declare one more.")))

(defun description-iff-lines (f y c term hyp-line a-prim ledger counter)
  "Lines proving (.iff F[c/y] F[TERM/y]) under the hypothesis at HYP-LINE,
Phi(c) = forall y (A-PRIM <-> y = c); F is a subformula of A-PRIM, with
only primitive connectives. COUNTER is a cons whose car is the next line
number. Returns (VALUES lines line-of-the-iff)."
  (let ((lines nil))
    (labels ((emit (formula role by)
               (let ((n (car counter)))
                 (incf (car counter))
                 (push (list n formula role by) lines)
                 n))
             (fc (g) (substitute-named y c g))
             (fn (g) (substitute-named y term g))
             (iff (a b) (list '.iff a b))
             (build (g)
               (cond
                 ((not (occurs-symbol-p y g))
                  (emit (iff g g) :th '(th-iff-refl)))
                 ((and (consp g) (eq (car g) '.neg))
                  (let* ((h (second g))
                         (k (build h))
                         (n (emit (list '.to (iff (fc h) (fn h)) (iff (fc g) (fn g)))
                                  :th-ded '(th-iff-neg))))
                    (emit (iff (fc g) (fn g)) :ir (list 'mp n k))))
                 ((and (consp g) (eq (car g) '.to))
                  (let* ((a (second g)) (b (third g))
                         (ka (build a))
                         (kb (build b))
                         (n (emit (list '.to (iff (fc b) (fn b)) (iff (fc g) (fn g)))
                                  :th-ded (list 'th-iff-imp ka))))
                    (emit (iff (fc g) (fn g)) :ir (list 'mp n kb))))
                 ((and (consp g) (eq (car g) '.forall))
                  (let* ((z (second g)) (h (third g))
                         (k (build h))
                         (gen (emit (list '.forall z (iff (fc h) (fn h))) :ir (list 'gen k z)))
                         (n (emit (list '.to (list '.forall z (iff (fc h) (fn h))) (iff (fc g) (fn g)))
                                  :th-ded (list 'th-iff-forall
                                                :inst (list (list 'p (list z) (fc h))
                                                            (list 'q (list z) (fn h)))))))
                    (emit (iff (fc g) (fn g)) :ir (list 'mp n gen))))
                 ((and (consp g) (symbolp (car g)) (formula-argument-positions (car g) ledger))
                  (error "DEFINE-FUNCTION-BY-DESCRIPTION: ~S is formed by ~S, which is ~
                          not a primitive connective (.neg, .to, .forall) of this ~
                          first version." g (car g)))
                 ((> (count-symbol y g) 1)
                  (error "DEFINE-FUNCTION-BY-DESCRIPTION: the atomic formula ~S holds ~
                          ~S more than once; this first version supports one ~
                          description per atomic formula." g y))
                 (t
                  ;; th-desc-atomic: Phi(c) |- (exists b (Phi(b) and g[b])) <-> g[c],
                  ;; the left side being g[TERM] written out.
                  (let* ((k (emit (iff (fn g) (fc g)) :th
                                  (list 'th-desc-atomic hyp-line
                                        :inst (list (list 'p (list y) a-prim)
                                                    (list 'q (list y) g)
                                                    (list 'v1 c)))))
                         (n (emit (list '.to (iff (fn g) (fc g)) (iff (fc g) (fn g))) :th '(th-iff-sym))))
                    (emit (iff (fc g) (fn g)) :ir (list 'mp n k)))))))
      (let ((last (build f)))
        (values (nreverse lines) last)))))

(defun description-s1-proof (y c term a-formula a-prim def-formula ledger)
  "The proof of Phi(c) |- A[TERM/y], Phi(c) = forall y (A <-> y = c), its
hypothesis at line 0."
  (let* ((phi (list '.forall y (list '.iff a-prim (list '.eq y c))))
         (ac (substitute-named y c a-prim))
         (cc (list '.eq c c))
         (head (list (list 0 phi :hyp nil)
                     (list 1 (list '.to phi (list '.iff ac cc)) :axiom (list 'III.1 c))
                     (list 2 (list '.iff ac cc) :ir '(mp 1 0))
                     (list 3 cc :axiom '(IV.1))
                     (list 4 (list '.to (list '.iff ac cc) (list '.to cc ac)) :th '(th-iff-mpr))
                     (list 5 (list '.to cc ac) :ir '(mp 4 2))
                     (list 6 ac :ir '(mp 5 3))))
         (counter (list 7)))
    (declare (ignore a-formula))
    (multiple-value-bind (iff-lines at) (description-iff-lines a-prim y c term 0 a-prim ledger counter)
      (let* ((n (car counter))
             (an (substitute-named y term a-prim)))
        (values (append head iff-lines
                        (list (list n (list '.to (list '.iff ac an) (list '.to ac an)) :th '(th-iff-mp))
                              (list (+ n 1) (list '.to ac an) :ir (list 'mp n at))
                              (list (+ n 2) def-formula :ir (list 'mp (+ n 1) 6))))
                phi)))))

(defun define-function-by-description (ledger name arg-vars y-var y2-var a-formula
                                        existence-name uniqueness-name)
  "Admit function symbol NAME defined by A-FORMULA, after checking
EXISTENCE-NAME and UNIQUENESS-NAME: the abbreviation NAME(x) := the y
such that A, and the theorem NAME-DEF (with its auxiliary TH-DED
NAME-DEF.S1). ARG-VARS are A-FORMULA's argument variables, Y-VAR its
output variable; Y2-VAR is a distinct variable used only to state
uniqueness."
  (check-definition-shape ledger name arg-vars y-var y2-var a-formula)
  (let ((missing (remove-if (lambda (n) (derived-rule-name-taken-p n ledger)) *description-lemmas*)))
    (when missing
      (error "DEFINE-FUNCTION-BY-DESCRIPTION: the ledger lacks ~S; load ~
              hilbert-library/07-quantifier-schemas.ledger (and what it needs) first."
             missing)))
  (let ((a-prim (expand-abbreviations a-formula ledger)))
    (when (mentions-any-head-p a-prim (mapcar #'car (contextual-table ledger)))
      (error "DEFINE-FUNCTION-BY-DESCRIPTION: A-FORMULA ~S holds a description; ~
              this first version does not define by one." a-formula))
    (let* ((expected-existence (forall-prefix arg-vars (list '.exists y-var a-formula)))
           (a-at-y2 (rename-many (list (cons y-var y2-var)) a-formula))
           (uniqueness-body (list '.forall y-var
                                  (list '.forall y2-var
                                        (list '.to a-formula (list '.to a-at-y2 (list '.eq y-var y2-var))))))
           (expected-uniqueness (forall-prefix arg-vars uniqueness-body)))
      (unless (eq t (check-k-proof (list (list 0 expected-existence :th (list existence-name))) ledger))
        (error "DEFINE-FUNCTION-BY-DESCRIPTION: ~S does not establish the ~
                required existence schema~%  ~S" existence-name expected-existence))
      (unless (eq t (check-k-proof (list (list 0 expected-uniqueness :th (list uniqueness-name))) ledger))
        (error "DEFINE-FUNCTION-BY-DESCRIPTION: ~S does not establish the ~
                required uniqueness schema~%  ~S" uniqueness-name expected-uniqueness))
      (let* ((pkg (symbol-package name))
             (schema-xs (loop for i from 1 to (length arg-vars)
                               collect (intern (format nil "?X~D" i) pkg)))
             (schema-y (intern "?Y" pkg))
             (schema-a (rename-many (append (mapcar #'cons arg-vars schema-xs) (list (cons y-var schema-y)))
                                     a-formula))
             (ledger (bootstrap-kernel-from-spec
                      (list (list :abbreviation (cons name schema-xs) (list '.iota schema-y schema-a)))
                      :ledger ledger
                      ;; Lets LEDGER-COMMANDS save this as a command that
                      ;; replays, and re-checks, through this function.
                      :origin-note (list :by-description
                                         (list :define-function-by-description name arg-vars y-var y2-var
                                               a-formula existence-name uniqueness-name))))
             (def-name (intern (format nil "~A-DEF" (symbol-name name)) pkg))
             (s1-name (intern (format nil "~A-DEF.S1" (symbol-name name)) pkg))
             (term (cons name arg-vars))
             (def-formula (substitute-named y-var term a-formula))
             (c (description-witness-variable
                 ledger (list* y-var y2-var (append arg-vars (binder-variables-named a-prim))))))
        (when (occurs-symbol-p c a-prim)
          (error "DEFINE-FUNCTION-BY-DESCRIPTION: internal: witness ~S occurs in A." c))
        ;; NAME-DEF.S1: Phi(c) |- A(NAME(x)).
        (multiple-value-bind (s1-proof phi)
            (description-s1-proof y-var c term a-formula a-prim def-formula ledger)
          (setf ledger (admit-deduction ledger s1-name phi s1-proof (silent-log)
                                        (list :by-description t)))
          ;; NAME-DEF: strip the foralls off both theorems; exists c Phi(c);
          ;; then exists-elimination through NAME-DEF.S1.
          (multiple-value-bind (ex-lines ex-at) (strip-foralls-proof 2 expected-existence arg-vars 0)
            (multiple-value-bind (un-lines un-at)
                (strip-foralls-proof (+ 2 (length ex-lines)) expected-uniqueness arg-vars 1)
              (let ((n (+ 2 (length ex-lines) (length un-lines))))
                (admit-theorem ledger def-name
                               (append (list (list 0 expected-existence :th (list existence-name))
                                             (list 1 expected-uniqueness :th (list uniqueness-name)))
                                       ex-lines un-lines
                                       (list (list n (list '.exists c (list '.forall y-var (list '.iff a-formula (list '.eq y-var c))))
                                                   :th (list 'th-desc-proper ex-at un-at
                                                             :inst (list (list 'p (list y-var) a-prim))))
                                             (list (+ n 1) (list '.to phi def-formula) :th-ded (list s1-name))
                                             (list (+ n 2) (list '.forall c (list '.to phi def-formula))
                                                   :ir (list 'gen (+ n 1) c))
                                             (list (+ n 3) def-formula
                                                   :th (list 'th-exists-elim n (+ n 2) :inst (list (list 'v1 c))))))
                               (silent-log)
                               (list :by-description))))))))))
