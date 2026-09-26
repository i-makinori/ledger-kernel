;;;; deduction-tests.lisp -- Sections 11-11.5: Deduction Theorem tests
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun test-deduction-theorem (ledger)
  "@DEDUCTION end to end: discharging TWICE over the ordinary MP proof of
A, (.to A B) |- B recovers the fully closed combinator theorem
A -> ((.to A B) -> B); discharging over a GEN-based proof (both the
self-generalizing case, where the discharged hypothesis is itself the
formula being generalized over vacuously, and the case where GEN cites a
DIFFERENT, still-open hypothesis) recovers the corresponding
quantified theorems -- all admitted and re-citable as real ledger
THEOREMs (not just in-memory raw-proofs); plus the one remaining
documented rejection path (a :TH line). Grows the ledger by four
entries."
  (let* ((mp-proof '((0 A :hyp nil)
                      (1 (.to A B) :hyp nil)
                      (2 B :ir (MP 1 0))))
         (discharge-1 (@deduction '(.to A B) mp-proof)))
    (expect "Sanity: the plain MP proof itself still checks"
            (check-k-proof mp-proof ledger) t)
    (expect "After discharging (.to A B): A |- (.to A B) -> B"
            (check-k-proof discharge-1 ledger) t)
    (expect "...and its conclusion is exactly that"
            (equal (proof-conclusion discharge-1) '(.to (.to A B) B)) t)
    (let ((discharge-2 (@deduction 'A discharge-1)))
      (expect "After discharging A too: |- A -> ((.to A B) -> B), no open hyps left"
              (check-k-proof discharge-2 ledger) t)
      (expect "...and its conclusion is exactly that"
              (equal (proof-conclusion discharge-2) '(.to A (.to (.to A B) B))) t)
      (let ((ledger (check-and-extend-by-deduction
                     (check-and-extend-by-deduction ledger 'th 'th-deduction-demo-step1
                                                     '(.to A B) mp-proof)
                     'th 'th-deduction-demo 'A discharge-1)))
        (expect "TH-DEDUCTION-DEMO is now a real, re-citable ledger theorem"
                (check-k-proof '((0 (.to C (.to (.to C D) D)) :th (th-deduction-demo))) ledger)
                t)
        (expect "Attack: citing it with mismatched A<>B halves -- must reject"
                (check-k-proof '((0 (.to C (.to (.to D D) D)) :th (th-deduction-demo))) ledger)
                nil)
        (expect "@DEDUCTION rejects a :TH line (out of scope, see section header)"
                (handler-case (progn (@deduction 'A `((0 A :hyp nil)
                                                        (1 (.to A B) :th (my-ax1))))
                                      nil)
                  (error () t))
                t)
        (let* ((gen-self-proof '((0 A :hyp nil) (1 (.forall v0 A) :ir (Gen 0 v0))))
               (gen-self-discharge (@deduction 'A gen-self-proof)))
          (expect "Sanity: the vacuous-Gen proof itself still checks (A |- forall v0 A)"
                  (check-k-proof gen-self-proof ledger) t)
          (expect "Case 4 (GEN) on the SELF-discharged hypothesis: |- A -> (forall v0 A)"
                  (check-k-proof gen-self-discharge ledger) t)
          (expect "...and its conclusion is exactly that"
                  (equal (proof-conclusion gen-self-discharge) '(.to A (.forall v0 A))) t)
          (let ((ledger (check-and-extend-by-deduction ledger 'th 'th-gen-self-discharge
                                                         'A gen-self-proof)))
            (expect "TH-GEN-SELF-DISCHARGE is a real, re-citable ledger theorem"
                    (check-k-proof '((0 (.to C (.forall v0 C)) :th (th-gen-self-discharge))) ledger)
                    t)
            (let* ((gen-other-proof '((0 A :hyp nil) (1 B :hyp nil)
                                       (2 (.forall v0 B) :ir (Gen 1 v0))))
                   (gen-other-discharge-1 (@deduction 'A gen-other-proof)))
              (expect "Case 4 (GEN) discharging a hyp OTHER than the one GEN cites: A |- B still open"
                      (check-k-proof gen-other-discharge-1 ledger) t)
              (expect "...and its conclusion is exactly that (A -> forall v0 B), with B still open"
                      (equal (proof-conclusion gen-other-discharge-1) '(.to A (.forall v0 B))) t)
              (let* ((gen-other-discharge-2 (@deduction 'B gen-other-discharge-1)))
                (expect "Discharging B too closes it: |- B -> (A -> forall v0 B)"
                        (check-k-proof gen-other-discharge-2 ledger) t)
                (let ((ledger (check-and-extend-by-deduction ledger 'th 'th-gen-other-discharge
                                                              'B gen-other-discharge-1)))
                  (expect "TH-GEN-OTHER-DISCHARGE is a real, re-citable ledger theorem"
                          (check-k-proof '((0 (.to C (.to D (.forall v0 C))) :th (th-gen-other-discharge)))
                                          ledger)
                          t)
                  ledger)))))))))

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
      (expect "@DEDUCTION genuinely fails here -- the documented edge case, concretely demonstrated"
              (check-k-proof (@deduction h edge-proof) ledger) nil)
      (let ((ledger (check-and-extend-by-deduction-direct ledger 'th-edge-case-fixed h edge-proof)))
        (expect "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT correctly admits it (citing Gamma=(.eq v4 v1))"
                (check-k-proof '((0 (.eq v4 v1) :hyp nil)
                                  (1 (.to (.eq v0 v1) (.eq v4 v1)) :th-ded (th-edge-case-fixed 0)))
                                ledger)
                t)
        ledger))))
