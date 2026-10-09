;;;; peano-library-tests.lisp -- 00-peano-order.system and the generated
;;;; 08-arithmetic and 09-order ledgers (tools/generate-arithmetic-ledger.lisp)
;;;;
;;;; 10-division.ledger is left out until the generator is redone for
;;;; descriptions as contextual abbreviations: it uses div-s, mod-s and
;;;; beta as terms, which a description no longer is.

(in-package :ledger-kernel)

(defun peano-library-ledger ()
  "FOL + connectives + Peano arithmetic + order, and the modules 01-06, 08-09."
  (let ((l nil))
    (dolist (f '("00-classical-fol-equality.system" "00-connectives.system"
                 "00-peano-arithmetic.system" "00-peano-order.system"))
      (setf l (bootstrap-kernel-from-spec-file (library-path f) :ledger l)))
    (dolist (f '("01-propositional-core.ledger" "02-predicate-core.ledger"
                 "03-equality-core.ledger" "04-peano-arithmetic.ledger"
                 "05-classical-logic.ledger" "06-connectives.ledger"
                 "08-arithmetic.ledger" "09-order.ledger")
               l)
      (setf l (read-ledger-from-file (library-path f) :ledger l)))))

(defparameter *peano-laws*
  '((th-add-comm (.forall x1 (.forall x2 (.eq (+ x1 x2) (+ x2 x1)))))
    (th-add-assoc (.forall x1 (.forall x2 (.forall x3 (.eq (+ (+ x1 x2) x3) (+ x1 (+ x2 x3)))))))
    (th-add-cancel-r (.forall x1 (.forall x2 (.forall x3 (.to (.eq (+ x1 x3) (+ x2 x3)) (.eq x1 x2))))))
    (th-mul-comm (.forall x1 (.forall x2 (.eq (* x1 x2) (* x2 x1)))))
    (th-mul-assoc (.forall x1 (.forall x2 (.forall x3 (.eq (* (* x1 x2) x3) (* x1 (* x2 x3)))))))
    (th-mul-distrib-l (.forall x1 (.forall x2 (.forall x3 (.eq (* x1 (+ x2 x3)) (+ (* x1 x2) (* x1 x3)))))))
    (th-le-trans (.forall x1 (.forall x2 (.forall x3 (.to (.le x1 x2) (.to (.le x2 x3) (.le x1 x3)))))))
    (th-le-antisym (.forall x1 (.forall x2 (.to (.le x1 x2) (.to (.le x2 x1) (.eq x1 x2))))))
    (th-le-total (.forall x1 (.forall x2 (.or (.le x1 x2) (.le x2 x1)))))
    (th-zero-or-succ (.forall x1 (.or (.eq x1 zero) (.exists x4 (.eq x1 (s x4)))))))
  "Some of the closed laws of 08-09, as they must be stated.")

(defun test-peano-laws (ledger)
  (dolist (law *peano-laws*)
    (expect (format nil "~(~A~) is a theorem, stated as documented" (first law))
            (check-k-proof `((0 ,(second law) :th (,(first law)))) ledger) t))
  (let ((comm (second (assoc 'th-add-comm *peano-laws*))))
    (expect "using a law: 1 + 2 = 2 + 1 by instantiating th-add-comm with III.1"
            (check-k-proof
             `((0 ,comm :th (th-add-comm))
               (1 (.to ,comm (.forall x2 (.eq (+ (s zero) x2) (+ x2 (s zero))))) :axiom (iii.1 (s zero)))
               (2 (.forall x2 (.eq (+ (s zero) x2) (+ x2 (s zero)))) :ir (mp 1 0))
               (3 (.to (.forall x2 (.eq (+ (s zero) x2) (+ x2 (s zero))))
                       (.eq (+ (s zero) (s (s zero))) (+ (s (s zero)) (s zero))))
                  :axiom (iii.1 (s (s zero))))
               (4 (.eq (+ (s zero) (s (s zero))) (+ (s (s zero)) (s zero))) :ir (mp 3 2)))
             ledger)
            t))
  (expect "Attack: citing th-le-antisym as if x <= y alone gave x = y -- must reject"
          (check-k-proof '((0 (.forall x1 (.forall x2 (.to (.le x1 x2) (.eq x1 x2))))
                            :th (th-le-antisym)))
                         ledger)
          nil)
  (expect "Attack: capturing instantiation of a closed law (x2 into forall x2) -- must reject"
          (check-k-proof '((0 (.forall x1 (.forall x2 (.eq (+ x1 x2) (+ x2 x1)))) :th (th-add-comm))
                           (1 (.to (.forall x1 (.forall x2 (.eq (+ x1 x2) (+ x2 x1))))
                                   (.forall x2 (.eq (+ x2 x2) (+ x2 x2))))
                            :axiom (iii.1 x2)))
                         ledger)
          nil)
  (expect "s <= t is exists z (s + z = t), whatever z is called"
          (same-formula-p ledger '(.le v0 v1) '(.exists v2 (.eq (+ v0 v2) v1))) t)
  (expect "Attack: an expansion whose bound variable is free in the terms is a different formula"
          (same-formula-p ledger '(.le v0 v1) '(.exists v0 (.eq (+ v0 v0) v1))) nil)
  ledger)

(defun run-peano-library-self-tests ()
  "The generated arithmetic and order libraries load (every proof
re-verified) and their laws can be cited."
  (let ((ledger (peano-library-ledger)))
    (test-peano-laws ledger)
    (expect "every TH-DED of the arithmetic libraries is expanded into a real, checked proof"
            (every #'deduction-entry-expanded-p (entries-of-kind 'th-ded ledger)) t))
  (format t "~%Peano library self-tests complete.~%"))
