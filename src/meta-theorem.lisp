;;;; meta-theorem.lisp -- meta-theorems declared by a .system file
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; A meta-theorem is a fact about the proofs of a system, not a formula
;;; of it. Whether it holds depends on the system's rules, so the kernel
;;; does not assume any: a .system file states the ones it relies on,
;;; with the matching rules that say when each applies, and a system that
;;; states none simply cannot use them. The only one so far is the
;;; Deduction Theorem (deduction.lisp):
;;;
;;;   (:meta-theorem deduction
;;;     (:discharge (@vdash ?H ?A) (.to ?H ?A))
;;;     (:case NAME CONDITIONS (PREMISE-PATTERNS EXTRA-PATTERNS :=> CONCLUSION))
;;;     ...)
;;;
;;; (@VDASH H A) is the meta-level statement "line A of the proof, which
;;; depends on the hypothesis H being discharged, becomes Gamma |- H -> A".
;;; :DISCHARGE says how that is written as a formula of the system. Each
;;; :CASE is a matching rule, checked like an inference rule (type
;;; conditions and side conditions included), for one way a line can
;;; arise:
;;;   NAME = an irule name   -- a line made by that irule from lines that
;;;                             depend on H, e.g. Gen with ?x not free in ?H;
;;;   NAME = :ASSUMPTION     -- a :HYP line that is H itself;
;;;   NAME = :INDEPENDENT    -- a line that does not depend on H.
;;; A line made by an irule with no case cannot be discharged, so a rule
;;; such as an unrestricted Gen keeps Gamma, P(x) |- forall x P(x) from
;;; becoming Gamma |- P(x) -> forall x P(x).
;;;
;;; Both kinds of entry are :PRIMITIVE and trusted like axioms: a case
;;; claims that the textbook induction step for that rule goes through in
;;; this system. What the kernel checks is that every line of every
;;; discharged proof is covered by a case whose conditions hold.

(defun deduction-discharge-entry (ledger)
  "The DEDUCTION-DISCHARGE entry of LEDGER (the first, if several), or NIL
when the system assumes no Deduction Theorem."
  (first (entries-of-kind 'deduction-discharge ledger)))

(defun discharge-formula (hyp conclusion ledger)
  "The formula Gamma |- HYP -> CONCLUSION is written as in LEDGER's system,
per its :DISCHARGE declaration, or NIL if it has none."
  (let ((e (deduction-discharge-entry ledger)))
    (when e
      (destructuring-bind (vdash-pattern formula-pattern) (entry-payload e)
        (let ((binds (match-template vdash-pattern (list '@vdash hyp conclusion))))
          (and (not (match-fail-p binds))
               (instantiate-with-binds formula-pattern binds)))))))

(defun deduction-case-holds-p (case-name hyp premises extras conclusion ledger open-hyps)
  "T iff some DEDUCTION-CASE entry named CASE-NAME matches (@VDASH HYP P)
for each P in PREMISES, EXTRAS against its extra patterns and
(@VDASH HYP CONCLUSION), with its conditions holding."
  (let ((premise-sequents (mapcar (lambda (p) (list '@vdash hyp p)) premises))
        (conclusion-sequent (list '@vdash hyp conclusion)))
    (some (lambda (entry)
            (destructuring-bind (name conditions form) (entry-payload entry)
              (and (eq name case-name)
                   (destructuring-bind (premise-pats extra-pats arrow concl-pat) form
                     (declare (ignore arrow))
                     (and (= (length premise-pats) (length premise-sequents))
                          (= (length extra-pats) (length extras))
                          (let* ((b0 (seed-fresh nil premise-sequents extras conclusion-sequent))
                                 (b1 (match-templates-seq premise-pats premise-sequents b0))
                                 (b2 (match-templates-seq extra-pats extras b1))
                                 (b3 (match-template concl-pat conclusion-sequent b2)))
                            (and (not (match-fail-p b3))
                                 (nth-value 1 (check-conditions conditions b3 ledger nil open-hyps)))))))))
          (entries-of-kind 'deduction-case ledger))))
