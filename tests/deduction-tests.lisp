;;;; deduction-tests.lisp -- Sections 11-11.5: Deduction Theorem tests
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun test-deduction-theorem-direct (ledger)
  "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT (Section 11.5) end to end: the same
basic MP discharge as TEST-DEDUCTION-THEOREM, but confirming (a) NO
expansion ever happens -- the stored proof is exactly RAW-PROOF, unchanged
size -- and (b) the GEN edge case @DEDUCTION cannot avoid (documented in
Section 11's header, and in Section 11.5's own header) is genuinely fixed
here, not merely papered over: a proof where Gen generalizes a variable
BEFORE the hypothesis being discharged is even introduced, where that
variable IS free in the hypothesis, so @DEDUCTION's own per-line
Case-4 construction spuriously rejects it, while CHECK-AND-EXTEND-BY-
DEDUCTION-DIRECT -- never touching CHECK-K-PROOF's own already-correct,
order-sensitive OPEN-HYPS tracking -- correctly accepts it. Grows the
ledger by two entries."
  (let* ((mp-proof '((0 A :hyp nil)
                      (1 (.to A B) :hyp nil)
                      (2 B :ir (MP 1 0))))
         (ledger (check-and-extend-by-deduction-direct ledger 'th-direct-mp-demo '(.to A B) mp-proof)))
    (expect "TH-DIRECT-MP-DEMO is a real, re-citable ledger theorem (citing Gamma=A as C)"
            (check-k-proof '((0 C :hyp nil)
                              (1 (.to (.to C D) D) :th-ded (th-direct-mp-demo 0)))
                            ledger)
            t)
    (expect "Attack: citing it with mismatched C<>D halves -- must reject"
            (check-k-proof '((0 C :hyp nil)
                              (1 (.to (.to C D) E) :th-ded (th-direct-mp-demo 0)))
                            ledger)
            nil)
    (expect "Attack (regression for the earlier caught bug): omitting the ~
             required Gamma premise (A) entirely -- must reject, since ~
             (.to (.to C D) D) is NOT a tautology on its own"
            (check-k-proof '((0 (.to (.to C D) D) :th-ded (th-direct-mp-demo))) ledger)
            nil)
    (expect "No expansion happened: the stored proof is exactly RAW-PROOF's own 3 lines"
            (= (length (third (entry-payload (car (entries-of-kind 'th-ded ledger))))) 3)
            t)
    ;; The GEN edge case, made concrete: H = (v0 .eq v1), with v0 free in
    ;; H. Line 1 generalizes v0 -- legally, since at that point OPEN-HYPS
    ;; is just {(v4 .eq v1)}, which does not mention v0 -- BEFORE H itself
    ;; is introduced at line 2. @DEDUCTION's Case 4 would still rebuild
    ;; "H -> (forall v0 (v4 .eq v1))" via axiom III.2 for that line, which
    ;; demands v0 not free in H -- false here -- so it must reject the
    ;; result even though the underlying mathematics is perfectly sound.
    (let* ((h '(.eq v0 v1))
           (edge-proof '((0 (.eq v4 v1) :hyp nil)
                         (1 (.forall v0 (.eq v4 v1)) :ir (Gen 0 v0))
                         (2 (.eq v0 v1) :hyp nil)
                         (3 (.to (.forall v0 (.eq v4 v1)) (.eq v4 v1)) :axiom (III.1 v4))
                         (4 (.eq v4 v1) :ir (MP 3 1)))))
      (expect "Sanity: the edge-case proof itself checks (Gamma,H |- PHI)"
              (check-k-proof edge-proof ledger) t)
      (let ((ledger (check-and-extend-by-deduction-direct ledger 'th-edge-case-fixed h edge-proof)))
        (expect "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT correctly admits it (citing Gamma=(.eq v4 v1))"
                (check-k-proof '((0 (.eq v4 v1) :hyp nil)
                                  (1 (.to (.eq v0 v1) (.eq v4 v1)) :th-ded (th-edge-case-fixed 0)))
                                ledger)
                t)
        ledger))))
