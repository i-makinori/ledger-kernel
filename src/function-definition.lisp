;;;; function-definition.lisp -- DEFINE-FUNCTION-BY-DESCRIPTION
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; Definition by description. Given ledger theorems
;;;   EXISTENCE:   forall x1..xn. exists y. A(x1,...,xn,y)
;;;   UNIQUENESS:  forall x1..xn. forall y. forall y2.
;;;                  (A(...,y) -> (A(...,y2) -> y=y2))
;;; this admits a new n-ary function symbol NAME with the defining axiom
;;;   A(x1,...,xn, NAME(x1,...,xn)).
;;; Given existence and uniqueness, such a definition is a conservative
;;; extension -- a standard metatheorem that this kernel does not itself
;;; prove. What IS checked: both cited theorems are re-checked by
;;; CHECK-K-PROOF against the exact formulas built from A-FORMULA, and a
;;; mismatch is an error. The symbol and axiom are then admitted as
;;; :PRIMITIVE entries through BOOTSTRAP-KERNEL-FROM-SPEC.

(defun rename-many (pairs form)
  "Substitute each (OLD . NEW) of PAIRS into FORM, in order. Order does not
matter because callers only use fresh NEW symbols that do not occur in FORM."
  (dolist (p pairs form) (setf form (subst (cdr p) (car p) form))))

;;; The metatheorem needs more than the two theorems; these are checked
;;; too (CHECK-DEFINITION-SHAPE), since each one's failure admits a
;;; contradiction:
;;;   - NAME is a symbol the ledger has never used. Reusing a function
;;;     symbol (S, +, an earlier definition) adds a second defining axiom
;;;     for it: with A(x,y) := y = x, S(x) = x, so (S zero) = zero.
;;;   - The free variables of A are among X1..Xn, Y. A free parameter z
;;;     makes existence and uniqueness hold for each z separately, but
;;;     the axiom A(x, NAME(x)) then fixes one value for every z: with
;;;     A(y) := y = z, NAME = z for all z, so (S zero) = zero.
;;;   - X1..Xn, Y, Y2 are distinct declared variables, Y2 does not occur
;;;     in A, and none of them is the variable of a binder inside A, so
;;;     the plain renamings below (Y to Y2, Xi to ?Xi) change exactly the
;;;     free occurrences and capture nothing.

(defun symbol-used-in-ledger-p (sym ledger)
  "T iff SYM occurs anywhere in the payload of an entry of LEDGER."
  (some (lambda (e) (occurs-symbol-p sym (entry-payload e)))
        (treap-values-below (ledger-all ledger) (ledger-bound ledger))))

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

(defun define-function-by-description (ledger name arg-vars y-var y2-var a-formula
                                        existence-name uniqueness-name)
  "Admit function symbol NAME defined by A-FORMULA, after checking
EXISTENCE-NAME and UNIQUENESS-NAME. ARG-VARS are A-FORMULA's argument
variables, Y-VAR its output variable; Y2-VAR is a distinct variable used
only to state uniqueness."
  (check-definition-shape ledger name arg-vars y-var y2-var a-formula)
  (let* ((expected-existence
           (let ((body (list '.exists y-var a-formula)))
             (dolist (v (reverse arg-vars) body) (setf body (list '.forall v body)))))
         (a-at-y2 (rename-many (list (cons y-var y2-var)) a-formula))
         (expected-uniqueness
           (let ((body (list '.forall y-var
                              (list '.forall y2-var
                                    (list '.to a-formula (list '.to a-at-y2 (list '.eq y-var y2-var)))))))
             (dolist (v (reverse arg-vars) body) (setf body (list '.forall v body))))))
    (unless (eq t (check-k-proof (list (list 0 expected-existence :th (list existence-name))) ledger))
      (error "DEFINE-FUNCTION-BY-DESCRIPTION: ~S does not establish the ~
              required existence schema~%  ~S" existence-name expected-existence))
    (unless (eq t (check-k-proof (list (list 0 expected-uniqueness :th (list uniqueness-name))) ledger))
      (error "DEFINE-FUNCTION-BY-DESCRIPTION: ~S does not establish the ~
              required uniqueness schema~%  ~S" uniqueness-name expected-uniqueness))
    (let* ((schema-xs (loop for i from 1 to (length arg-vars)
                             collect (intern (format nil "?X~D" i) (symbol-package name))))
           (schema-y (intern "?Y" (symbol-package name)))
           (schema-a (rename-many (append (mapcar #'cons arg-vars schema-xs) (list (cons y-var schema-y)))
                                   a-formula))
           (schema-a-at-name (substitute-named schema-y (cons name schema-xs) schema-a))
           (term-cmd (list :term-formation
                            (intern (format nil "~A-TERM" (symbol-name name)) (symbol-package name))
                            (mapcar (lambda (x) (list 'term? x)) schema-xs)
                            (list 'term? (cons name schema-xs))))
           (def-cmd (list :axiom
                           (intern (format nil "~A-DEF" (symbol-name name)) (symbol-package name))
                           (mapcar (lambda (x) (list 'term? x)) schema-xs)
                           (list nil schema-a-at-name))))
      (bootstrap-kernel-from-spec
       (list term-cmd def-cmd)
       :ledger ledger
       ;; Lets LEDGER-COMMANDS save this as a command that replays, and
       ;; re-checks, through this function.
       :origin-note (list :by-description
                          (list :define-function-by-description name arg-vars y-var y2-var
                                a-formula existence-name uniqueness-name))))))
