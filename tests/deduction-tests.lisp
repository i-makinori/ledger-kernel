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

;;; --- The Deduction Theorem as a declared meta-theorem -------------------

(defun fol-spec-variant (&key (drop-meta-theorem nil) (unrestricted-gen nil) (extra nil))
  "A ledger from 00-classical-fol-equality.system's directives, changed:
DROP-META-THEOREM removes the (:meta-theorem deduction ...) directive,
UNRESTRICTED-GEN replaces Gen by one without its open-hypothesis
restriction, and EXTRA directives are appended."
  (let ((spec (read-system-spec-from-file (library-path "00-classical-fol-equality.system"))))
    (when drop-meta-theorem
      (setf spec (remove :meta-theorem spec :key #'car)))
    (when unrestricted-gen
      (setf spec (mapcar (lambda (cmd)
                           (if (and (eq (car cmd) :irule) (eq (second cmd) 'gen))
                               '(:irule Gen ((var? ?x) (wff? ?A)) ((?A) (?x) :=> (.forall ?x ?A)))
                               cmd))
                         spec)))
    (bootstrap-kernel-from-spec (append spec extra))))

(defun test-deduction-meta-theorem ()
  "TH-DED is admitted only when the system declares the Deduction Theorem
and every line of the proof is covered by one of its cases."
  (flet ((admitted-p (thunk)
           (handler-case (progn (funcall thunk) t) (error () nil))))
    (let ((no-dt (fol-spec-variant :drop-meta-theorem t)))
      (expect "Attack: a system that declares no Deduction Theorem cannot admit TH-DED"
              (admitted-p (lambda ()
                            (check-and-extend-by-deduction-direct no-dt 'th-id-no-dt 'a '((0 a :hyp nil)))))
              nil)
      (expect "... while ordinary theorems are still admitted there"
              (admitted-p (lambda ()
                            (check-and-extend no-dt 'th 'th-k-no-dt
                                              '((0 (.to A (.to B A)) :axiom (II.1))))))
              t))
    (let ((loose (fol-spec-variant :unrestricted-gen t))
          (proof '((0 (.eq v0 v1) :hyp nil)
                   (1 (.forall v0 (.eq v0 v1)) :ir (Gen 0 v0)))))
      (expect "with an unrestricted Gen, v0 = v1 |- forall v0 (v0 = v1) is a valid proof line by line"
              (check-k-proof proof loose) t)
      (expect "Attack: ... but its discharge, v0 = v1 -> forall v0 (v0 = v1), is refused by the Gen case"
              (admitted-p (lambda ()
                            (check-and-extend-by-deduction-direct loose 'th-bad-gen '(.eq v0 v1) proof)))
              nil)
      (expect "Gen of a line that does not depend on H is covered by :independent, even with v1 free in H"
              (admitted-p (lambda ()
                            (check-and-extend-by-deduction-direct
                             loose 'th-gen-indep '(.eq v1 v2)
                             '((0 (.eq v1 v1) :axiom (IV.1))
                               (1 (.forall v1 (.eq v1 v1)) :ir (Gen 0 v1))
                               (2 (.eq v1 v2) :hyp nil)
                               (3 (.to (.forall v1 (.eq v1 v1)) (.to (.eq v1 v2) (.forall v1 (.eq v1 v1)))) :axiom (II.1))
                               (4 (.to (.eq v1 v2) (.forall v1 (.eq v1 v1))) :ir (MP 3 1))
                               (5 (.forall v1 (.eq v1 v1)) :ir (MP 4 2))))))
              t))
    ;; An irule with no Deduction Theorem case: usable in proofs, but no
    ;; line made by it from H can be discharged -- directly or through a
    ;; cited theorem.
    (let* ((l (fol-spec-variant :extra '((:irule DUP ((wff? ?A)) ((?A) nil :=> ?A)))))
           (l (check-and-extend l 'th 'th-dup '((0 A :hyp nil) (1 A :ir (DUP 0))))))
      (expect "an irule without a case is usable in an ordinary proof"
              (check-k-proof '((0 B :hyp nil) (1 B :ir (DUP 0))) l) t)
      (expect "Attack: discharging H through an irule with no case -- refused"
              (admitted-p (lambda ()
                            (check-and-extend-by-deduction-direct
                             l 'th-dup-direct 'b '((0 B :hyp nil) (1 B :ir (DUP 0))))))
              nil)
      (expect "Attack: ... and through a theorem whose proof uses it -- refused"
              (admitted-p (lambda ()
                            (check-and-extend-by-deduction-direct
                             l 'th-dup-cited 'b '((0 B :hyp nil) (1 B :th (th-dup 0))))))
              nil)
      (expect "the same theorem cited from a line that does not depend on H is fine"
              (admitted-p (lambda ()
                            (check-and-extend-by-deduction-direct
                             l 'th-dup-indep 'b '((0 A :hyp nil) (1 A :th (th-dup 0)) (2 B :hyp nil)))))
              t))
    (let ((l (fol-kernel)))
      (expect "the declared :DISCHARGE writes H -> PHI as (.to H PHI)"
              (discharge-formula 'a 'b l) '(.to a b))
      (expect "Attack: a second :DISCHARGE declaration -- must error"
              (admitted-p (lambda ()
                            (bootstrap-kernel-from-spec
                             '((:meta-theorem deduction (:discharge (@vdash ?H ?A) (.to ?A ?H))))
                             :ledger l)))
              nil)
      (expect "Attack: an unknown meta-theorem -- must error"
              (admitted-p (lambda ()
                            (bootstrap-kernel-from-spec '((:meta-theorem cut-elimination)) :ledger l)))
              nil))))

(defun test-deduction-expansion ()
  "With proof templates for its cases, a TH-DED is also built as a real
proof of Gamma |- H -> PHI and checked; without one (IOTA), or with a
wrong one, its case is trusted and the entry says so."
  (let* ((l (classical-logic-ledger (fol-kernel)))
         (l (check-and-extend-by-deduction-direct
             l 'th-exp-test '(.forall v0 (.eq v0 v1))
             '((0 (.eq v2 v2) :hyp nil)
               (1 (.forall v0 (.eq v0 v1)) :hyp nil)
               (2 (.to (.forall v0 (.eq v0 v1)) (.eq v3 v1)) :axiom (III.1 v3))
               (3 (.eq v3 v1) :ir (MP 2 1))
               (4 (.forall v3 (.eq v3 v1)) :ir (Gen 3 v3))
               (5 (.to (.eq v3 v1) (.neg (.neg (.eq v3 v1)))) :th (th-dneg-intro))
               (6 (.neg (.neg (.eq v3 v1))) :ir (MP 5 3)))))
         (e (first (last (entries-of-kind 'th-ded l))))
         (expanded (expand-deduction-entry e l)))
    (expect "a TH-DED through MP, Gen and a cited theorem is admitted as expanded"
            (deduction-entry-expanded-p e) t)
    (expect "its expansion is an ordinary proof of Gamma |- H -> PHI ..."
            (and expanded
                 (%check-k-proof expanded (entries-upto (entry-k e) l))   ; kernel form
                 (equal (proof-conclusion expanded)
                        (named->db '(.to (.forall v0 (.eq v0 v1)) (.neg (.neg (.eq v3 v1)))) l)))
            t)
    (expect "... whose only hypothesis is Gamma, H discharged"
            (equal (proof-hypotheses expanded) (list (named->db '(.eq v2 v2) l)))
            t)
    (expect "... and which cites no TH-DED that depends on H (the Deduction Theorem is not used)"
            (notany (lambda (line) (and (eq (third line) :hyp)
                                        (equal (second line) (named->db '(.forall v0 (.eq v0 v1)) l))))
                    expanded)
            t))
  ;; A wrong template: MP's written with II.1 in place of II.2.
  (let* ((spec (mapcar (lambda (cmd)
                         (if (eq (car cmd) :meta-theorem)
                             (subst '(II.1) '(II.2) cmd :test #'equal)
                             cmd))
                       (read-system-spec-from-file (library-path "00-classical-fol-equality.system"))))
         (l (bootstrap-kernel-from-spec spec))
         (l (check-and-extend-by-deduction-direct
             l 'th-exp-bad 'a '((0 (.to a b) :hyp nil) (1 a :hyp nil) (2 b :ir (MP 0 1)))))
         (e (first (last (entries-of-kind 'th-ded l)))))
    (expect "Attack: a wrong proof template does not pass for an expansion"
            (deduction-entry-expanded-p e) nil)))
