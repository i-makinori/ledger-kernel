;;;; iota-tests.lisp -- Section 19: IOTA and III.3 tests
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 19. IOTA (definite description): formation, III.3 (existential
;;;     generalization), a worked uniqueness derivation, and the IOTA
;;;     irule itself -- plus attack tests.
;;;
;;; What this gives you: given (a) a proof of (.exists ?x ?A) and (b) a
;;; proof that "any two things satisfying A are equal" (curried, since
;;; there is no AND connective: (.forall ?y (.forall ?z (.to A[y/x] (.to
;;; A[z/x] (.eq ?y ?z)))))), the IOTA irule concludes A[(.iota ?x ?A)/?x]
;;; -- the iota-term itself satisfies A. Concretely worked below: from
;;; exists v0(v0=v1) and "any two things equal to v1 are equal to each
;;; other", conclude (.iota v0 (.eq v0 v1)) = v1 -- i.e. "the x such that
;;; x=v1" behaves exactly as v1 itself does, without ever requiring v1 be
;;; produced as a syntactically distinguished witness.
;;;
;;; What this deliberately still does NOT give you (see Section 7's own
;;; commentary on III.3/IOTA for the reasoning): no general definitional
;;; mechanism that lets you write "let y := the x such that A(x)" and
;;; have y become a fresh, reusable name -- every use of (.iota ?x ?A)
;;; must independently re-cite BOTH an existence and a uniqueness proof
;;; for that exact A; no total/junk-value convention for when uniqueness
;;; fails (this kernel simply never lets you apply IOTA without proving
;;; it first, sidestepping the question rather than answering it); and
;;; still no full existential ELIMINATION/instantiation rule (III.3 only
;;; ever INTRODUCES .EXISTS from a witness, it never lets you extract one
;;; back out of an already-proven .EXISTS).

(defun test-iota-formation (ledger)
  "(.iota x A) forms as a TERM (via ITOA-TERM) but never as a WFF -- it is
a description of AN OBJECT ('the x such that A'), not a proposition."
  (expect "(.iota v0 (.eq v0 v1)) is a term" (judgement? 'term? '(.iota v0 (.eq v0 v1)) ledger) t)
  (expect "(.iota v0 (.eq v0 v1)) is NOT a wff" (judgement? 'wff? '(.iota v0 (.eq v0 v1)) ledger) nil)
  (expect "(.eq (.iota v0 (.eq v0 v1)) v1) IS a wff (iota-term used as an ordinary term argument)"
          (judgement? 'wff? '(.eq (.iota v0 (.eq v0 v1)) v1) ledger) t)
  ledger)

(defun test-axiom-iii3 (ledger)
  "III.3: A[t/x] -> exists x. A, unconditional (no Gen-style freshness
side condition -- see its own commentary in BOOTSTRAP-AXIOMS for why
that's sound). EXTRA-PARAM-PATTERNS are (?x ?A ?t), NOT just (?t) like
III.1 -- ?x/?A must be supplied directly since the binder here sits in
the CONSEQUENT while @subst sits in the ANTECEDENT (MATCH-TEMPLATE
processes antecedent before consequent, so ?x/?A can't be left to bind
structurally the way III.1's own (.forall ?x ?A) antecedent does)."
  (expect "III.3: v1=v1 -> exists v0(v0=v1)"
          (check-k-proof '((0 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1))) :axiom (III.3 v0 (.eq v0 v1) v1))) ledger)
          t)
  (let ((ledger (check-and-extend ledger 'th 'th-exists-v0-eq-v1
                                   '((0 (.eq v1 v1) :axiom (IV.1))
                                     (1 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1))) :axiom (III.3 v0 (.eq v0 v1) v1))
                                     (2 (.exists v0 (.eq v0 v1)) :ir (MP 1 0)))
                                   (silent-log))))
    (expect "TH-EXISTS-V0-EQ-V1 is a real, re-citable ledger theorem"
            (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :th (th-exists-v0-eq-v1))) ledger) t)
    (expect "Attack: III.3 with a MISMATCHED extra-arg t (v2 instead of v1) -- must reject"
            (check-k-proof '((0 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1))) :axiom (III.3 v0 (.eq v0 v1) v2))) ledger)
            nil)
    ledger))

(defun test-iota-irule (ledger)
  "The full worked example: derive UNIQ-FULL (any two things equal to v1
are equal to each other, i.e. |- forall v2 forall v3 (v2=v1 -> (v3=v1 ->
v2=v3))) via the same multi-step deduction-theorem-direct chaining
pattern 05-classical-logic.ledger already uses for TH-RAA, then cite it
alongside TH-EXISTS-V0-EQ-V1 as IOTA's two premises to conclude
(.iota v0 (.eq v0 v1)) = v1."
  (let* ((inner '((0 (.eq v2 v1) :hyp nil)
                  (1 (.eq v3 v1) :hyp nil)
                  (2 (.to (.eq v3 v1) (.eq v1 v3)) :axiom (IV.3))
                  (3 (.eq v1 v3) :ir (MP 2 1))
                  (4 (.to (.eq v2 v1) (.to (.eq v1 v3) (.eq v2 v3))) :axiom (IV.4))
                  (5 (.to (.eq v1 v3) (.eq v2 v3)) :ir (MP 4 0))
                  (6 (.eq v2 v3) :ir (MP 5 3))))
         (ledger (check-and-extend-by-deduction-direct ledger 'uniq-step1 '(.eq v3 v1) inner (silent-log)))
         (step2 '((0 (.eq v2 v1) :hyp nil)
                  (1 (.to (.eq v3 v1) (.eq v2 v3)) :th-ded (uniq-step1 0))))
         (ledger (check-and-extend-by-deduction-direct ledger 'uniq-step2 '(.eq v2 v1) step2 (silent-log)))
         (ledger (check-and-extend ledger 'th 'uniq-gen-v3
                                    '((0 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))) :th-ded (uniq-step2))
                                      (1 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3)))) :ir (Gen 0 v3)))
                                    (silent-log)))
         (ledger (check-and-extend ledger 'th 'uniq-full
                                    '((0 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3)))) :th (uniq-gen-v3))
                                      (1 (.forall v2 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))))) :ir (Gen 0 v2)))
                                    (silent-log))))
    (expect "UNIQ-FULL is a real, re-citable ledger theorem (any two things =v1 are equal)"
            (check-k-proof '((0 (.forall v2 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))))) :th (uniq-full))) ledger)
            t)
    (expect "IOTA: from exists v0(v0=v1) and uniq-full, conclude (iota v0 (v0=v1)) = v1"
            (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :th (th-exists-v0-eq-v1))
                              (1 (.forall v2 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))))) :th (uniq-full))
                              (2 (.eq (.iota v0 (.eq v0 v1)) v1) :ir (IOTA 0 1)))
                            ledger)
            t)
    (expect "Attack: IOTA citing the SAME line twice (existence as both premises) -- must reject"
            (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :th (th-exists-v0-eq-v1))
                              (1 (.eq (.iota v0 (.eq v0 v1)) v1) :ir (IOTA 0 0)))
                            ledger)
            nil)
    (expect "Attack: IOTA with existence/uniqueness premises SWAPPED -- must reject"
            (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :th (th-exists-v0-eq-v1))
                              (1 (.forall v2 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))))) :th (uniq-full))
                              (2 (.eq (.iota v0 (.eq v0 v1)) v1) :ir (IOTA 1 0)))
                            ledger)
            nil)
    (expect "Attack: IOTA citing a uniqueness formula about a DIFFERENT A than the existence line -- must reject"
            (check-k-proof '((0 (.exists v0 (.eq v0 v5)) :hyp nil)
                              (1 (.forall v2 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))))) :th (uniq-full))
                              (2 (.eq (.iota v0 (.eq v0 v5)) v1) :ir (IOTA 0 1)))
                            ledger)
            nil)
    (let* ((A '(.to (.eq v0 v4) (.forall v4 (.eq v0 v4))))
           (existence (list '.exists 'v0 A))
           (uniqueness '(.forall v2 (.forall v3
                         (.to (.to (.eq v2 v4) (.forall v4 (.eq v2 v4)))
                              (.to (.to (.eq v3 v4) (.forall v4 (.eq v3 v4)))
                                   (.eq v2 v3)))))))
      (expect "Attack (capture-avoidance): IOTA where substituting the iota-term would capture a
free variable under a nested same-named binder inside A -- @subst-ok? must block it"
              (check-k-proof (list (list 0 existence :hyp nil)
                                    (list 1 uniqueness :hyp nil)
                                    (list 2 (list '.to (list '.eq (list '.iota 'v0 A) 'v4)
                                                  (list '.forall 'v4 (list '.eq (list '.iota 'v0 A) 'v4)))
                                          :ir '(IOTA 0 1)))
                              ledger)
              nil))
    ledger))

(defun run-iota-self-tests ()
  "Section 19: IOTA formation, III.3, the worked uniqueness-chain example,
and attack tests."
  (let* ((ledger (fol-kernel))
         (ledger (test-iota-formation ledger))
         (ledger (test-axiom-iii3 ledger))
         (ledger (test-iota-irule ledger)))
    (declare (ignorable ledger))
    (format t "~%IOTA self-tests complete.~%")))
