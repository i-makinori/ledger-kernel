;;;; classical-logic-tests.lisp -- Section 14: classical propositional completeness lemmas
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 14. Classical propositional completeness lemmas (II.4 and friends)
;;; ---------------------------------------------------------------------
;;;
;;; Re-derives, in-memory, exactly the chain also persisted as
;;; hilbert-library/05-classical-logic.ledger: TH-EX-FALSO, TH-DNEG-ELIM,
;;; TH-DNEG-INTRO, and the reductio ladder TH-RAA-S1/TH-RAA-S3/TH-RAA
;;; ending in TH-NEG-IMPL. These are the handful of classical facts
;;; Kalmar's completeness construction (tactics layer, on top of this
;;; kernel) needs and that are NOT reachable from {II.1,II.2,II.3} within
;;; any practical proof-search budget -- see BOOTSTRAP-AXIOMS' comment on
;;; II.4 for why that axiom exists at all despite being, in principle,
;;; redundant.

(defun test-classical-logic (ledger)
  ;; TH-IDENTITY (A -> A) isn't part of BOOTSTRAP-KERNEL itself -- it
  ;; only exists as the first line of hilbert-library/01-propositional-
  ;; core.ledger -- but TH-DNEG-ELIM and TH-RAA-S3 below cite it, so it
  ;; is re-derived here too, exactly as that file defines it.
  (let ((ledger (check-and-extend-by-deduction-direct
                 ledger 'th-identity 'a '((0 a :hyp nil)))))
  (let ((ledger (check-and-extend-by-deduction-direct
                 ledger 'th-ex-falso '(.neg a)
                 '((0 (.neg a) :hyp nil)
                   (1 (.to (.neg a) (.to (.neg b) (.neg a))) :axiom (II.1))
                   (2 (.to (.neg b) (.neg a)) :ir (MP 1 0))
                   (3 (.to (.to (.neg b) (.neg a)) (.to a b)) :axiom (II.3))
                   (4 (.to a b) :ir (MP 3 2))))))
    (expect "TH-EX-FALSO: not-a |- (a -> b), any b"
            (check-k-proof '((0 (.neg C) :hyp nil)
                              (1 (.to (.neg C) (.to C D)) :th-ded (th-ex-falso))
                              (2 (.to C D) :ir (MP 1 0)))
                            ledger)
            t)
    (let ((ledger (check-and-extend-by-deduction-direct
                   ledger 'th-dneg-elim '(.neg (.neg a))
                   '((0 (.neg (.neg a)) :hyp nil)
                     (1 (.to a a) :th-ded (th-identity))
                     (2 (.to (.to a a) (.to (.to (.neg a) a) a)) :axiom (II.4))
                     (3 (.to (.to (.neg a) a) a) :ir (MP 2 1))
                     (4 (.to (.neg (.neg a)) (.to (.neg a) a)) :th-ded (th-ex-falso))
                     (5 (.to (.neg a) a) :ir (MP 4 0))
                     (6 a :ir (MP 3 5))))))
      (expect "TH-DNEG-ELIM: not-not-C |- C"
              (check-k-proof '((0 (.neg (.neg C)) :hyp nil)
                                (1 (.to (.neg (.neg C)) C) :th-ded (th-dneg-elim))
                                (2 C :ir (MP 1 0)))
                              ledger)
              t)
      (let ((ledger (check-and-extend
                     ledger 'th 'th-dneg-intro
                     '((0 (.to (.neg (.neg (.neg a))) (.neg a)) :th-ded (th-dneg-elim))
                       (1 (.to (.to (.neg (.neg (.neg a))) (.neg a)) (.to a (.neg (.neg a)))) :axiom (II.3))
                       (2 (.to a (.neg (.neg a))) :ir (MP 1 0))))))
        (expect "TH-DNEG-INTRO: C |- not-not-C"
                (check-k-proof '((0 C :hyp nil)
                                  (1 (.to C (.neg (.neg C))) :th-ded (th-dneg-intro))
                                  (2 (.neg (.neg C)) :ir (MP 1 0)))
                                ledger)
                t)
        (let* ((ledger (check-and-extend-by-deduction-direct
                        ledger 'th-raa-s1 'a
                        '((0 (.to a b) :hyp nil)
                          (1 (.to a (.neg b)) :hyp nil)
                          (2 a :hyp nil)
                          (3 b :ir (MP 0 2))
                          (4 (.neg b) :ir (MP 1 2))
                          (5 (.to (.neg b) (.to b (.neg a))) :th-ded (th-ex-falso))
                          (6 (.to b (.neg a)) :ir (MP 5 4))
                          (7 (.neg a) :ir (MP 6 3)))))
               (ledger (check-and-extend-by-deduction-direct
                        ledger 'th-raa-s3 '(.to a (.neg b))
                        '((0 (.to a b) :hyp nil)
                          (1 (.to a (.neg b)) :hyp nil)
                          (2 (.to a (.neg a)) :th-ded (th-raa-s1 0 1))
                          (3 (.to (.neg a) (.neg a)) :th-ded (th-identity))
                          (4 (.to (.to a (.neg a)) (.to (.to (.neg a) (.neg a)) (.neg a))) :axiom (II.4))
                          (5 (.to (.to (.neg a) (.neg a)) (.neg a)) :ir (MP 4 2))
                          (6 (.neg a) :ir (MP 5 3)))))
               (ledger (check-and-extend-by-deduction-direct
                        ledger 'th-raa '(.to a b)
                        '((0 (.to a b) :hyp nil)
                          (1 (.to (.to a (.neg b)) (.neg a)) :th-ded (th-raa-s3 0))))))
          (expect "TH-RAA: (C->D) |- ((C-> not-D) -> not-C), fully closed"
                  (check-k-proof '((0 (.to (.to C D) (.to (.to C (.neg D)) (.neg C))) :th-ded (th-raa))) ledger)
                  t)
          (let* ((ledger (check-and-extend-by-deduction-direct
                          ledger 'th-mp-flip '(.to a c)
                          '((0 a :hyp nil)
                            (1 (.to a c) :hyp nil)
                            (2 c :ir (MP 1 0)))))
                 (ledger (check-and-extend-by-deduction-direct
                          ledger 'th-neg-impl '(.neg c)
                          '((0 a :hyp nil)
                            (1 (.neg c) :hyp nil)
                            (2 (.to (.to a c) c) :th-ded (th-mp-flip 0))
                            (3 (.to (.neg c) (.to (.to a c) (.neg c))) :axiom (II.1))
                            (4 (.to (.to a c) (.neg c)) :ir (MP 3 1))
                            (5 (.to (.to (.to a c) c) (.to (.to (.to a c) (.neg c)) (.neg (.to a c)))) :th-ded (th-raa))
                            (6 (.to (.to (.to a c) (.neg c)) (.neg (.to a c))) :ir (MP 5 2))
                            (7 (.neg (.to a c)) :ir (MP 6 4))))))
            (expect "TH-NEG-IMPL: C, not-D |- not(C->D)"
                    (check-k-proof '((0 C :hyp nil)
                                      (1 (.neg D) :hyp nil)
                                      (2 (.to (.neg D) (.neg (.to C D))) :th-ded (th-neg-impl 0))
                                      (3 (.neg (.to C D)) :ir (MP 2 1)))
                                    ledger)
                    t)
            ledger)))))))

(defun run-classical-logic-self-tests ()
  "As RUN-SELF-TESTS, but exercising the classical completeness lemmas
built on top of a plain (non-arithmetic) BOOTSTRAP-KERNEL -- Section 14."
  (let* ((ledger (bootstrap-kernel))
         (ledger (test-classical-logic ledger)))
    (declare (ignorable ledger))
    (format t "~%Classical-logic self-tests complete.~%")))
