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
;;; and the theorem NAME-DEF, A(x1,...,xn, NAME(x1,...,xn)), proved by the
;;; IOTA rule from the two theorems. Nothing is added as an axiom: NAME is
;;; expanded before the kernel sees it, and NAME-DEF is an ordinary checked
;;; theorem (cite it with :inst to use it at other arguments).

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

(defun define-function-by-description (ledger name arg-vars y-var y2-var a-formula
                                        existence-name uniqueness-name)
  "Admit function symbol NAME defined by A-FORMULA, after checking
EXISTENCE-NAME and UNIQUENESS-NAME: the abbreviation NAME(x) := the y
such that A, and the theorem NAME-DEF. ARG-VARS are A-FORMULA's argument
variables, Y-VAR its output variable; Y2-VAR is a distinct variable used
only to state uniqueness."
  (check-definition-shape ledger name arg-vars y-var y2-var a-formula)
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
           (def-formula (substitute-named y-var (cons name arg-vars) a-formula)))
      ;; NAME-DEF: strip the foralls off both theorems, then IOTA.
      (multiple-value-bind (ex-lines ex-at) (strip-foralls-proof 2 expected-existence arg-vars 0)
        (multiple-value-bind (un-lines un-at)
            (strip-foralls-proof (+ 2 (length ex-lines)) expected-uniqueness arg-vars 1)
          (admit-theorem ledger def-name
                         (append (list (list 0 expected-existence :th (list existence-name))
                                       (list 1 expected-uniqueness :th (list uniqueness-name)))
                                 ex-lines un-lines
                                 (list (list (+ 2 (length ex-lines) (length un-lines))
                                             def-formula :ir (list 'IOTA ex-at un-at))))
                         (silent-log)
                         (list :by-description)))))))
