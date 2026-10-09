;;;; deduction.lisp -- admitting H -> PHI by the Deduction Theorem (TH-DED)

(in-package :ledger-kernel)

;;; The Deduction Theorem is trusted as a meta-theorem instead of being
;;; compiled into an explicit K/S proof of H -> PHI, which grows about
;;; threefold per discharge. (A proof-transforming version is kept in
;;; backup/_backup_deduction-transform.lisp.)
;;;
;;; Checked: RAW-PROOF, a proof of Gamma,H |- PHI with H as one of its :HYP
;;; lines, is verified unchanged by CHECK-K-PROOF. Gen's restriction
;;; (@not-free-in-dependencies?) there forbids generalizing a variable free
;;; in any hypothesis open at that line, which is exactly the Deduction
;;; Theorem's side condition; a Gen before H's :HYP line is correctly not
;;; constrained by H.
;;;
;;; Trusted: only the step "a checked proof of Gamma,H |- PHI yields
;;; Gamma |- H -> PHI", proved once by the textbook induction over HYP,
;;; axiom, MP and Gen. A bug here could admit an unsound entry, but every
;;; later citation still re-verifies the stored, unexpanded RAW-PROOF
;;; (TRY-DEDUCTION-ENTRY).
;;;
;;; Scope: the textbook induction covers :HYP, :AXIOM and :IR (MP, Gen)
;;; lines. A line citing a derived entry (TH, TH-DED) with cited lines
;;; S1..Sn and conclusion PSI is covered by one more case: the entry's
;;; stored proof, instantiated, is itself a checked proof of S1..Sn |- PSI
;;; whose Gen steps respect S1..Sn, so by induction on ledger order
;;; |- S1 -> ... -> Sn -> PSI, and Gamma |- H -> PSI follows from the
;;; Gamma |- H -> Si by propositional steps alone. (This extension is the
;;; argument written here; it has not been mechanically checked.)

(defun check-and-extend-by-deduction-direct (ledger name hyp-formula raw-proof &optional (log (silent-log)))
  "Admit (.to HYP-FORMULA PHI), PHI being RAW-PROOF's conclusion, as
TH-DED entry NAME. Other hypotheses of RAW-PROOF stay undischarged and
must be supplied when the entry is cited. Returns the new ledger."
  (when (derived-rule-name-taken-p name ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: the name ~S is already ~
            used by an existing TH/TH-DED entry -- refused ~
            to avoid an ambiguous or shadowing citation." name))
  (when (contains-raw-index-p (list hyp-formula raw-proof))
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: ~S contains a raw ~
            (:bv n); write bound variables by name." name))
  (unless (judgement? 'wff? hyp-formula ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: HYP-FORMULA ~S is not a ~
            well-formed formula." hyp-formula))
  (let ((db-hyp (named->db hyp-formula ledger))
        (db-proof (named->db-proof raw-proof ledger)))
    (unless (member db-hyp (proof-hypotheses db-proof) :test #'equal)
      (log-admission-result log name nil)
      (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: HYP-FORMULA ~S does not ~
              occur as one of RAW-PROOF's own :HYP lines -- nothing would be ~
              discharged." hyp-formula))
    (unless (%check-k-proof db-proof ledger log)
      (log-admission-result log name nil)
      (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: proof of ~S rejected." name))
    (log-admission-result log name t)
    ;; Kernel form in the payload, the text as written in the ORIGIN.
    (ledger-append ledger 'th-ded (list name db-hyp db-proof)
                   (list :derived-by-deduction hyp-formula raw-proof))))
