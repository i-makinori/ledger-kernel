;;;; arithmetic-tests.lisp -- Section 13: equality and Peano arithmetic tests
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 13. Regression tests for equality (IV.1-IV.4) and Peano arithmetic
;;;     (Section 7.5, bootstrap-kernel :arithmetic t)
;;; ---------------------------------------------------------------------
;;;
;;; These run against their OWN, separately-bootstrapped arithmetic-
;;; enabled ledger (BOOTSTRAP-KERNEL :ARITHMETIC T) rather than threading
;;; through RUN-SELF-TESTS' main LEDGER chain: :ARITHMETIC's extra
;;; vocabulary/axioms are one specific theory's business, not the generic
;;; kernel's, so every other self-test above continues to run against the
;;; exact same plain kernel it always has.

(defun test-equality-axioms (ledger)
  "IV.1 (reflexivity), IV.2 (Leibniz), IV.3 (symmetry), IV.4
(transitivity). Does not grow the ledger."
  (expect "IV.1: zero = zero" (check-k-proof '((0 (.eq zero zero) :axiom (IV.1))) ledger) t)
  (expect "IV.1: v0 = v0" (check-k-proof '((0 (.eq v0 v0) :axiom (IV.1))) ledger) t)
  (expect "IV.3: v0=v1 -> v1=v0"
          (check-k-proof '((0 (.to (.eq v0 v1) (.eq v1 v0)) :axiom (IV.3))) ledger) t)
  (expect "IV.4: v0=v1 -> (v1=v2 -> v0=v2)"
          (check-k-proof '((0 (.to (.eq v0 v1) (.to (.eq v1 v2) (.eq v0 v2))) :axiom (IV.4))) ledger)
          t)
  (expect "IV.2 (Leibniz), single-occurrence use: v0=v1 -> (forall v2(v2=v0) -> forall v2(v2=v1))"
          (check-k-proof '((0 (.to (.eq v0 v1)
                                   (.to (.forall v2 (.eq v2 v0)) (.forall v2 (.eq v2 v1))))
                               :axiom (IV.2)))
                          ledger)
          t)
  ledger)

(defun test-peano-axioms (ledger)
  "P1-P2 (successor), P4-P7 (recursive +/*), P8-P10 (congruence), and one
instantiation of P3 (induction). Does not grow the ledger."
  (expect "P1: S(v0) =/= 0" (check-k-proof '((0 (.neg (.eq (S v0) zero)) :axiom (P1))) ledger) t)
  (expect "P2: S(v0)=S(v1) -> v0=v1"
          (check-k-proof '((0 (.to (.eq (S v0) (S v1)) (.eq v0 v1)) :axiom (P2))) ledger) t)
  (expect "P4: v0+0 = v0" (check-k-proof '((0 (.eq (+ v0 zero) v0) :axiom (P4))) ledger) t)
  (expect "P5: v0+S(v1) = S(v0+v1)"
          (check-k-proof '((0 (.eq (+ v0 (S v1)) (S (+ v0 v1))) :axiom (P5))) ledger) t)
  (expect "P6: v0*0 = 0" (check-k-proof '((0 (.eq (* v0 zero) zero) :axiom (P6))) ledger) t)
  (expect "P7: v0*S(v1) = (v0*v1)+v0"
          (check-k-proof '((0 (.eq (* v0 (S v1)) (+ (* v0 v1) v0)) :axiom (P7))) ledger) t)
  (expect "P8: v0=v1 -> S(v0)=S(v1)"
          (check-k-proof '((0 (.to (.eq v0 v1) (.eq (S v0) (S v1))) :axiom (P8))) ledger) t)
  (expect "P9: v0=v1 -> (v2=v3 -> v0+v2=v1+v3)"
          (check-k-proof '((0 (.to (.eq v0 v1) (.to (.eq v2 v3) (.eq (+ v0 v2) (+ v1 v3)))) :axiom (P9)))
                          ledger)
          t)
  (expect "P3, instantiated at A(x):=(0+x=x): well-typed and accepted"
          (check-k-proof `((0 (.to (.eq (+ zero zero) zero)
                                   (.to (.forall v0 (.to (.eq (+ zero v0) v0) (.eq (+ zero (S v0)) (S v0))))
                                        (.forall v0 (.eq (+ zero v0) v0))))
                               :axiom (P3 v0 (.eq (+ zero v0) v0))))
                          ledger)
          t)
  ledger)

(defun test-peano-induction-proof (ledger)
  "End to end: PROVE 0+x=x by genuine induction (P3), not just check that
P3's schema type-checks -- a base case (P4), a step case discharged via
CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT (chaining IV.4/P5/P8, no expansion),
GEN, then one MP against the P3 instance itself. Grows the ledger by
three entries (the base fact, the step-case TH-DED lemma, and the final
induction theorem)."
  (let* ((base-proof '((0 (.eq (+ zero zero) zero) :axiom (P4))))
         (ledger (check-and-extend ledger 'th 'th-zero-plus-zero base-proof))
         (step-hyp '(.eq (+ zero v0) v0))
         (step-proof '((0 (.eq (+ zero v0) v0) :hyp nil)
                       (1 (.eq (+ zero (S v0)) (S (+ zero v0))) :axiom (P5))
                       (2 (.to (.eq (+ zero v0) v0) (.eq (S (+ zero v0)) (S v0))) :axiom (P8))
                       (3 (.eq (S (+ zero v0)) (S v0)) :ir (MP 2 0))
                       (4 (.to (.eq (+ zero (S v0)) (S (+ zero v0)))
                               (.to (.eq (S (+ zero v0)) (S v0))
                                    (.eq (+ zero (S v0)) (S v0))))
                          :axiom (IV.4))
                       (5 (.to (.eq (S (+ zero v0)) (S v0)) (.eq (+ zero (S v0)) (S v0)))
                          :ir (MP 4 1))
                       (6 (.eq (+ zero (S v0)) (S v0)) :ir (MP 5 3)))))
    (expect "step-case ND proof (0+v0=v0 |- 0+S(v0)=S(v0)) checks"
            (check-k-proof step-proof ledger) t)
    (let* ((ledger (check-and-extend-by-deduction-direct
                    ledger 'th-zero-plus-step step-hyp step-proof))
           (step-concl (list '.to step-hyp (proof-conclusion step-proof)))
           (full-proof
             `((0 ,step-concl :th-ded (th-zero-plus-step))
               (1 (.forall v0 ,step-concl) :ir (Gen 0 v0))
               (2 (.to (.eq (+ zero zero) zero)
                       (.to (.forall v0 ,step-concl) (.forall v0 (.eq (+ zero v0) v0))))
                  :axiom (P3 v0 (.eq (+ zero v0) v0)))
               (3 (.eq (+ zero zero) zero) :th-ded (th-zero-plus-zero))
               (4 (.to (.forall v0 ,step-concl) (.forall v0 (.eq (+ zero v0) v0))) :ir (MP 2 3))
               (5 (.forall v0 (.eq (+ zero v0) v0)) :ir (MP 4 1)))))
      (expect "full induction proof of forall v0 (0+v0=v0) checks"
              (check-k-proof full-proof ledger) t)
      (let ((ledger (check-and-extend ledger 'th 'th-zero-plus-identity full-proof)))
        (expect "TH-ZERO-PLUS-IDENTITY is a real, re-citable ledger theorem"
                (check-k-proof '((0 (.forall v0 (.eq (+ zero v0) v0)) :th (th-zero-plus-identity))) ledger)
                t)
        ledger))))

(defun run-arithmetic-self-tests ()
  "As RUN-SELF-TESTS, but against a BOOTSTRAP-KERNEL :ARITHMETIC T ledger
-- equality theory and Peano arithmetic, Sections 7.5/13."
  (let* ((ledger (bootstrap-kernel :arithmetic t))
         (ledger (test-equality-axioms ledger))
         (ledger (test-peano-axioms ledger))
         (ledger (test-peano-induction-proof ledger)))
    (declare (ignorable ledger))
    (format t "~%Arithmetic self-tests complete.~%")))
