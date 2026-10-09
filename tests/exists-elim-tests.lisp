;;;; exists-elim-tests.lisp -- Section 21: EXISTS-ELIM tests
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 21. EXISTS-ELIM: genuine existential elimination
;;; ---------------------------------------------------------------------
;;;
;;; III.3 could only ever INTRODUCE a .EXISTS-headed formula (from a
;;; concrete witness); there was no way to go the other direction and
;;; actually USE an already-proven (.exists ?x ?A) for anything besides
;;; citing it as IOTA's own existence premise. EXISTS-ELIM (Mendelson's
;;; Rule C) closes that gap: given (.exists ?x ?A) and a proof that SOME
;;; already-established formula Ac implies C, where Ac is verified (via
;;; the new @substitutes? meta-predicate) to equal A with x instantiated
;;; to a fresh witness variable w, concludes C outright.

(defun test-exists-elim (ledger)
  "The positive case (from exists v0(v0=v1), conclude v1=v1 by
instantiating the witness to a fresh v2 and immediately discarding it via
K/II.1 -- so, exactly like the EVEN-IND wiring test in Section 20, this
exercises the MECHANISM, not a deep fact), plus four attacks: the wrong-
Ac case (@substitutes? itself catches a citer's mismatched substitution
instance), and the three freshness violations (witness free in Gamma,
free in A, free in the conclusion C)."
  (expect "positive: from exists v0(v0=v1), conclude v1=v1 via witness v2"
          (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :hyp nil)
                            (1 (.eq v1 v1) :axiom (IV.1))
                            (2 (.to (.eq v1 v1) (.to (.eq v2 v1) (.eq v1 v1))) :axiom (II.1))
                            (3 (.to (.eq v2 v1) (.eq v1 v1)) :ir (MP 2 1))
                            (5 (.forall v2 (.to (.eq v2 v1) (.eq v1 v1))) :ir (gen 3 v2))
                            (4 (.eq v1 v1) :th (th-exists-elim 0 5 :inst ((v1 v2)))))
                          ledger)
          t)
  (expect "Attack: witness v2 free in an open hypothesis (Gamma) -- must reject"
          (check-k-proof '((0 (.eq v2 v3) :hyp nil)
                            (1 (.exists v0 (.eq v0 v1)) :hyp nil)
                            (2 (.eq v1 v1) :axiom (IV.1))
                            (3 (.to (.eq v1 v1) (.to (.eq v2 v1) (.eq v1 v1))) :axiom (II.1))
                            (4 (.to (.eq v2 v1) (.eq v1 v1)) :ir (MP 3 2))
                            (6 (.forall v2 (.to (.eq v2 v1) (.eq v1 v1))) :ir (gen 4 v2))
                            (5 (.eq v1 v1) :th (th-exists-elim 1 6 :inst ((v1 v2)))))
                          ledger)
          nil)
  (expect "Attack: witness v2 already free in A itself -- must reject"
          (check-k-proof '((0 (.exists v0 (.eq v0 v2)) :hyp nil)
                            (1 (.eq v1 v1) :axiom (IV.1))
                            (2 (.to (.eq v1 v1) (.to (.eq v2 v2) (.eq v1 v1))) :axiom (II.1))
                            (3 (.to (.eq v2 v2) (.eq v1 v1)) :ir (MP 2 1))
                            (5 (.forall v2 (.to (.eq v2 v2) (.eq v1 v1))) :ir (gen 3 v2))
                            (4 (.eq v1 v1) :th (th-exists-elim 0 5 :inst ((v1 v2)))))
                          ledger)
          nil)
  (expect "Attack: the cited antecedent does NOT actually equal A[w/x] -- must reject"
          (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :hyp nil)
                            (1 (.eq v1 v1) :axiom (IV.1))
                            (2 (.to (.eq v1 v1) (.to (.eq v2 v3) (.eq v1 v1))) :axiom (II.1))
                            (3 (.to (.eq v2 v3) (.eq v1 v1)) :ir (MP 2 1))
                            (5 (.forall v2 (.to (.eq v2 v3) (.eq v1 v1))) :ir (gen 3 v2))
                            (4 (.eq v1 v1) :th (th-exists-elim 0 5 :inst ((v1 v2)))))
                          ledger)
          nil)
  (let ((selfimp-proof '((0 (.to (.to (.eq v2 v1) (.to (.to (.eq v2 v1) (.eq v2 v1)) (.eq v2 v1)))
                                 (.to (.to (.eq v2 v1) (.to (.eq v2 v1) (.eq v2 v1))) (.to (.eq v2 v1) (.eq v2 v1))))
                             :axiom (II.2))
                          (1 (.to (.eq v2 v1) (.to (.to (.eq v2 v1) (.eq v2 v1)) (.eq v2 v1))) :axiom (II.1))
                          (2 (.to (.to (.eq v2 v1) (.to (.eq v2 v1) (.eq v2 v1))) (.to (.eq v2 v1) (.eq v2 v1)))
                             :ir (MP 0 1))
                          (3 (.to (.eq v2 v1) (.to (.eq v2 v1) (.eq v2 v1))) :axiom (II.1))
                          (4 (.to (.eq v2 v1) (.eq v2 v1)) :ir (MP 2 3)))))
    (expect "Attack setup: the self-implication (v2=v1)->(v2=v1) itself checks (S/K derivation)"
            (check-k-proof selfimp-proof ledger) t)
    (expect "Attack: witness v2 leaks into the CONCLUSION C itself -- must reject"
            (check-k-proof (append '((0 (.exists v0 (.eq v0 v1)) :hyp nil)) selfimp-proof
                                    '((6 (.forall v2 (.to (.eq v2 v1) (.eq v2 v1))) :ir (gen 4 v2))
                                      (5 (.eq v2 v1) :th (th-exists-elim 0 6 :inst ((v1 v2))))))
                            ledger)
            nil))
  ledger)

(defun run-exists-elim-self-tests ()
  "Section 21: existential elimination, now the derived theorem
TH-EXISTS-ELIM of 05-classical-logic.ledger (cited after a Gen on the
witness) -- the positive case plus four attacks, each still refused."
  (let* ((ledger (classical-logic-ledger (fol-kernel)))
         (ledger (test-exists-elim ledger)))
    (declare (ignorable ledger))
    (format t "~%EXISTS-ELIM self-tests complete.~%")))
