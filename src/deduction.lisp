;;;; deduction.lisp -- Sections 11-11.5: the Deduction Theorem
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 11.5. CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT -- trusting the Deduction
;;;       Theorem itself, instead of compiling it away
;;; ---------------------------------------------------------------------
;;;
;;; @DEDUCTION (above) treats the Deduction Theorem as something that must
;;; be COMPILED: it rewrites RAW-PROOF into a brand-new, K/S-only raw-proof
;;; of (HYP-FORMULA -> PHI) with no open hypotheses left, so CHECK-AND-
;;; EXTEND never has to know anything special happened -- but every line
;;; of the original proof gets replaced by ~3 new ones, and this compounds
;;; multiplicatively over repeated discharges (5 lines -> 17 -> 53 -> 161
;;; across three successive discharges of one small syllogism -- see the
;;; session's own diagnostic run). The other honest option, discussed at
;;; length before this section exists to realize it: treat the Deduction
;;; Theorem itself as a TRUSTED meta-mathematical fact -- established once,
;;; here, never re-derived per use -- and admit (HYP-FORMULA -> PHI)
;;; directly from a CHECKED proof of Gamma,HYP-FORMULA |- PHI, without ever
;;; materializing an expanded K,S-only proof of the implication at all.
;;;
;;; WHY THIS IS SOUND, using only machinery CHECK-K-PROOF already has:
;;;
;;;   RAW-PROOF here is an ordinary ND-style raw-proof (:HYP/:AXIOM/
;;;   :IR(MP)/:IR(GEN) lines, exactly what CHECK-K-PROOF already knows how
;;;   to verify) with HYP-FORMULA as one of its own :HYP lines. CHECK-AND-
;;;   EXTEND-BY-DEDUCTION-DIRECT calls CHECK-K-PROOF on it UNCHANGED -- no
;;;   transformation, no expansion. GEN's own Verallgemeinerungsverbot
;;;   (META-NOT-FREE-IN-DEPENDENCIES?, Section 5) already checks, line by
;;;   line as CHECK-K-PROOF walks the proof top-down, that a generalized
;;;   variable is free in none of the hypotheses OPEN AT THAT POINT -- and
;;;   that is EXACTLY the side condition the Deduction Theorem requires
;;;   (Mendelson's formulation: no Gen on a variable free in a hypothesis
;;;   the generalized line actually depends on). Because OPEN-HYPS only
;;;   ever contains :HYP lines strictly earlier in the linear proof, a Gen
;;;   line that comes BEFORE HYP-FORMULA's own :HYP line is automatically,
;;;   correctly unconstrained by HYP-FORMULA -- there is no coarser,
;;;   blanket "check every Gen against HYP-FORMULA regardless of order"
;;;   approximation here, unlike @DEDUCTION's per-line Case 4 (see its own
;;;   "GEN's KNOWN EDGE CASE" commentary above), which reconstructs H -> B
;;;   for EVERY line uniformly and so can spuriously demand X not free in H
;;;   even when the original Gen came before H was ever introduced. TEST-
;;;   DEDUCTION-THEOREM-DIRECT below constructs exactly that scenario and
;;;   confirms @DEDUCTION rejects it while this function accepts it.
;;;
;;;   The ONE thing that is trusted rather than checked, here, is the
;;;   bridge itself: "a checked proof of Gamma,H |- PHI, with Gen already
;;;   honoring Gamma as open-hyps, justifies asserting Gamma |- H -> PHI."
;;;   That is a fixed fact about THIS proof system, established once by
;;;   the classical Deduction Theorem argument (structural induction on
;;;   the same four cases @DEDUCTION's own construction embodies -- HYP,
;;;   weakening, MP, Gen -- which is precisely why that construction is
;;;   always POSSIBLE, whatever its cost); it is never re-derived inside
;;;   this function, the same way ADMIT-PRIMITIVE's axioms are trusted
;;;   once at bootstrap rather than re-proven on every citation.
;;;
;;;   Everything else stays LCF-style, checked, never taken on faith: the
;;;   stored payload is (NAME HYP-FORMULA RAW-PROOF) -- the ORIGINAL,
;;;   small, unexpanded proof -- and TRY-DEDUCTION-ENTRY (Section 6) fully
;;;   re-verifies an instantiated copy of it via CHECK-K-PROOF from a fresh
;;;   OPEN-HYPS every single time the resulting :TH-DED entry is cited. A
;;;   bug in the one trusted bridging step above could make this function
;;;   admit an unsound (.to HYP-FORMULA PHI); it can never make a later
;;;   citation of an already-admitted entry go unverified.
;;;
;;; SCOPE: identical to @DEDUCTION's -- RAW-PROOF's lines may be :HYP,
;;; :AXIOM, or :IR citing MP or GEN; a line citing an existing ITH/TH/
;;; DEF-ABBREV/TH-DED entry is out of scope (CHECK-K-PROOF would still
;;; verify such a proof directly since it is not @DEDUCTION-transformed at
;;; all, but the Deduction Theorem's own textbook proof only inducts on
;;; HYP/AXIOM/MP/GEN, so citing a derived rule mid-proof is not covered by
;;; the trusted bridging step here either -- this function does not special-
;;; case or forbid it, but nothing has verified the bridge is sound in that
;;; case, so it is simply not something to rely on).

(defun check-and-extend-by-deduction-direct (ledger name hyp-formula raw-proof &optional (log (silent-log)))
  "Admit (.to HYP-FORMULA PHI), where PHI is RAW-PROOF's own conclusion, as
a new :TH-DED/NAME ledger entry -- by trusting the Deduction Theorem
itself (see the section header above), never by constructing an explicit
K,S-only expansion the way CHECK-AND-EXTEND-BY-DEDUCTION/@DEDUCTION do.
RAW-PROOF must be an ordinary :HYP/:AXIOM/:IR(MP)/:IR(GEN) raw-proof
containing HYP-FORMULA as one of its own :HYP lines; it is checked EXACTLY
as it stands, via CHECK-K-PROOF, with no transformation at all. RAW-PROOF
may have OTHER open hypotheses (Gamma) besides HYP-FORMULA -- they are NOT
discharged, and remain genuine required premises that a later citation of
this entry must still supply (see TRY-DEDUCTION-ENTRY). Returns the NEW
ledger."
  (when (derived-rule-name-taken-p name ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: the name ~S is already ~
            used by an existing ITH/TH/DEF-ABBREV/TH-DED entry -- refused ~
            to avoid an ambiguous or shadowing citation." name))
  (unless (judgement? 'wff? hyp-formula ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: HYP-FORMULA ~S is not a ~
            well-formed formula." hyp-formula))
  (unless (member hyp-formula (proof-hypotheses raw-proof) :test #'equal)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: HYP-FORMULA ~S does not ~
            occur as one of RAW-PROOF's own :HYP lines -- nothing would be ~
            discharged." hyp-formula))
  (unless (check-k-proof raw-proof ledger log)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: proof of ~S rejected." name))
  (log-admission-result log name t)
  (ledger-append ledger 'th-ded (list name hyp-formula raw-proof)
                 (list :derived-by-deduction hyp-formula raw-proof)))
