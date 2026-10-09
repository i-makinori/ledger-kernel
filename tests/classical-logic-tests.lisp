;;;; classical-logic-tests.lisp -- Section 14: classical propositional lemmas
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 14. Classical propositional lemmas from II.1-3 alone
;;; ---------------------------------------------------------------------
;;;
;;; hilbert-library/01-propositional-core.ledger and
;;; 05-classical-logic.ledger derive, from Lukasiewicz's axioms II.1-3 and
;;; MP only: ex falso, double negation (both ways), modus tollens, the
;;; case split TH-CASE-SPLIT (formerly the extra axiom II.4), reductio
;;; and TH-NEG-IMPL. These tests load both files and use the results at
;;; other formulas than the ones they were proved at.

(defun classical-logic-ledger (ledger)
  "LEDGER with 01-propositional-core and 05-classical-logic loaded."
  (reduce (lambda (l f) (read-ledger-from-file (library-path f) :ledger l))
          '("01-propositional-core.ledger" "05-classical-logic.ledger")
          :initial-value ledger))

(defun axioms-cited-in-ledger (ledger)
  "The names of the axioms cited by :AXIOM lines in the stored proofs of
LEDGER's TH / TH-DED entries."
  (let ((acc nil))
    (dolist (e (treap-values-below (ledger-all ledger) nil) acc)
      (let ((proof (case (entry-kind e)
                     (th (second (entry-payload e)))
                     (th-ded (third (entry-payload e))))))
        (dolist (line proof)
          (when (eq (third line) :axiom)
            (pushnew (car (fourth line)) acc :test #'eq)))))))

(defun test-classical-logic (ledger)
  (let ((ledger (classical-logic-ledger ledger)))
    (expect "01 and 05 cite no axiom other than II.1-3, and III.1-2 for the existential quantifier"
            (subsetp (axioms-cited-in-ledger ledger) '(ii.1 ii.2 ii.3 iii.1 iii.2))
            t)
    (expect "III.3 and EXISTS-ELIM are no longer primitive"
            (and (notany (lambda (e) (eq (first (entry-payload e)) 'iii.3)) (entries-of-kind 'axiom ledger))
                 (notany (lambda (e) (eq (first (entry-payload e)) 'exists-elim)) (entries-of-kind 'irule ledger)))
            t)
    (expect "exists x A is the formula not forall x not A"
            (equal (named->db '(.exists v0 (.eq v0 v1)) ledger)
                   (named->db '(.neg (.forall v2 (.neg (.eq v2 v1)))) ledger))
            t)
    (expect "TH-EXISTS-INTRO: (v1 = v1) -> exists v0 (v0 = v1), with P and t given by :inst"
            (check-k-proof '((0 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1)))
                                :th (th-exists-intro :inst ((p (v0) (.eq v0 v1)) (v1 v1)))))
                           ledger)
            t)
    (expect "Attack: TH-EXISTS-INTRO with the wrong term -- must reject"
            (check-k-proof '((0 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1)))
                                :th (th-exists-intro :inst ((p (v0) (.eq v0 v1)) (v1 v2)))))
                           ledger)
            nil)
    (expect "II.4 is not an axiom of the base system any more"
            (check-k-proof '((0 (.to (.to C D) (.to (.to (.neg C) D) D)) :axiom (II.4))) ledger)
            nil)
    (expect "TH-EX-FALSO: not-a |- (a -> b), any b"
            (check-k-proof '((0 (.neg C) :hyp nil)
                              (1 (.to (.neg C) (.to C D)) :th-ded (th-ex-falso))
                              (2 (.to C D) :ir (MP 1 0)))
                            ledger)
            t)
    (expect "TH-DNEG-ELIM: not-not-C |- C"
            (check-k-proof '((0 (.neg (.neg C)) :hyp nil)
                              (1 (.to (.neg (.neg C)) C) :th-ded (th-dneg-elim))
                              (2 C :ir (MP 1 0)))
                            ledger)
            t)
    (expect "TH-DNEG-INTRO: C |- not-not-C"
            (check-k-proof '((0 C :hyp nil)
                              (1 (.to C (.neg (.neg C))) :th (th-dneg-intro))
                              (2 (.neg (.neg C)) :ir (MP 1 0)))
                            ledger)
            t)
    (expect "TH-MODUS-TOLLENS: (C -> D) -> (not-D -> not-C)"
            (check-k-proof '((0 (.to (.to C D) (.to (.neg D) (.neg C))) :th-ded (th-modus-tollens)))
                            ledger)
            t)
    (expect "TH-CASE-SPLIT: (C -> D) -> ((not-C -> D) -> D), the former axiom II.4"
            (check-k-proof '((0 (.to (.to C D) (.to (.to (.neg C) D) D)) :th-ded (th-case-split)))
                            ledger)
            t)
    (expect "TH-CASE-SPLIT at compound formulas"
            (check-k-proof '((0 (.to (.to (.eq v0 v1) (.neg A))
                                     (.to (.to (.neg (.eq v0 v1)) (.neg A)) (.neg A)))
                                :th-ded (th-case-split)))
                            ledger)
            t)
    (expect "Attack: TH-CASE-SPLIT without the negated branch -- must reject"
            (check-k-proof '((0 (.to (.to C D) (.to (.to C D) D)) :th-ded (th-case-split))) ledger)
            nil)
    (expect "TH-RAA: (C->D) |- ((C-> not-D) -> not-C), fully closed"
            (check-k-proof '((0 (.to (.to C D) (.to (.to C (.neg D)) (.neg C))) :th-ded (th-raa))) ledger)
            t)
    (expect "TH-NEG-IMPL: C, not-D |- not(C->D)"
            (check-k-proof '((0 C :hyp nil)
                              (1 (.neg D) :hyp nil)
                              (2 (.to (.neg D) (.neg (.to C D))) :th-ded (th-neg-impl 0))
                              (3 (.neg (.to C D)) :ir (MP 2 1)))
                            ledger)
            t)
    ledger))

(defun run-classical-logic-self-tests ()
  "Section 14: the classical lemmas of 01 and 05 on top of plain
first-order logic, derived from II.1-3 alone."
  (let* ((ledger (fol-kernel))
         (ledger (test-classical-logic ledger)))
    (declare (ignorable ledger))
    (format t "~%Classical-logic self-tests complete.~%")))
