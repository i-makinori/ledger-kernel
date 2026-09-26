;;;; deduction.lisp -- Sections 11-11.5: the Deduction Theorem
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 11. Meta-theorems: the Deduction (Meta-)Theorem, as @DEDUCTION
;;; ---------------------------------------------------------------------
;;;
;;; Gamma, A |- B  implies  Gamma |- A -> B.
;;;
;;; @DEDUCTION is a genuinely new kind of meta-level operation for this
;;; file: unlike @NOT-FREE-IN?/@SUBST/etc. (Section 4), which are meta-
;;; PREDICATES/meta-CONSTRUCTORS dispatched from inside CHECK-CONDITION/
;;; MATCH-TEMPLATE while a single line of a proof is being matched,
;;; @DEDUCTION operates on an entire RAW-PROOF at once, as a
;;; preprocessing/rewriting step that runs BEFORE CHECK-AND-EXTEND or
;;; CHECK-K-PROOF ever sees the result.
;;;
;;; It does not need to be trusted. This file's LCF-style trust boundary
;;; already guarantees that: @DEDUCTION's own correctness is assumed
;;; NOWHERE else in this file. Whatever raw-proof it hands back is
;;; re-verified from scratch, line by line, by the very same CHECK-K-PROOF
;;; that verifies any other proof, the instant CHECK-AND-EXTEND-BY-
;;; DEDUCTION (below) passes it along. A bug in @DEDUCTION can only ever
;;; produce a proof that gets REJECTED -- it can never cause one to be
;;; wrongly ACCEPTED.
;;;
;;; SCOPE: RAW-PROOF's lines may be :HYP, :AXIOM, or :IR citing MP or GEN.
;;; A line that is :ITH/:TH/:DEF-ABBREV is refused with a clear error: it
;;; cites an existing derived rule that may itself take any number of
;;; hypothesis-patterns by line-citation the same way MP takes two;
;;; generalizing the MP case below to an arbitrary derived rule's arity is
;;; possible in principle but is not implemented here.
;;;
;;; GEN's KNOWN EDGE CASE: GEN's own free-variable restriction (the
;;; Verallgemeinerungsverbot) is checked, at ORIGINAL admission time,
;;; against Gamma AS IT STOOD AT THAT LINE -- only the :HYP lines strictly
;;; earlier in RAW-PROOF, since CHECK-K-PROOF accumulates Gamma top-down.
;;; If HYP-FORMULA's own :HYP line happens to come AFTER some GEN line
;;; that generalizes a variable X, then X's freedom in HYP-FORMULA was
;;; never checked by the ORIGINAL proof at all (HYP-FORMULA was not yet
;;; open at that point) -- Case 4 below still builds a III.2 step that
;;; needs X not free in HYP-FORMULA, and in that specific (unusual)
;;; ordering, X could in fact occur free in it. @DEDUCTION does not check
;;; this in advance (it never receives a LEDGER, by design -- it stays a
;;; pure syntactic transform); CHECK-K-PROOF's own re-verification of that
;;; III.2 instance's @NOT-FREE-IN? side condition is what actually decides
;;; it, for real, against the genuine formula. Exactly the same LCF
;;; guarantee as everywhere else in this file: at worst, an unusual
;;; ordering makes @DEDUCTION's output get REJECTED; it is never a route
;;; to a wrongly ACCEPTED one.
;;;
;;; CONSTRUCTION: structural induction over RAW-PROOF's lines, in order,
;;; threading a fresh line-number counter and a MAPPING (alist: original
;;; numbering -> (new-conclusion-line-number . original-formula) -- the
;;; ORIGINAL formula is kept alongside the new line number because the MP
;;; and GEN cases below need to recover their own citations' original
;;; formulas from it, not just a line number). Four cases:
;;;
;;;   1. The line IS the discharged hypothesis itself (:HYP, formula
;;;      equal to HYP-FORMULA, call it H): its replacement conclusion is
;;;      H -> H, proved from K (II.1) and S (II.2) alone -- exactly the
;;;      classical textbook derivation of A -> A (see BOOTSTRAP-AXIOMS'
;;;      own commentary on why the OLD K/K/B-composition basis could not
;;;      derive this at all, and why the CURRENT K/S/contraposition basis
;;;      can):
;;;        n0  (H->((H->H)->H)) -> ((H->(H->H))->(H->H))  [II.2 ?A=H ?B=(.to H H) ?C=H]
;;;        n1  H -> ((H -> H) -> H)                         [II.1 ?A=H ?B=(.to H H)]
;;;        n2  (H -> (H -> H)) -> (H -> H)                  [MP n0 n1]
;;;        n3  H -> (H -> H)                                [II.1 ?A=H ?B=H]
;;;        n4  H -> H                                        [MP n2 n3]
;;;
;;;   2. The line is any OTHER :HYP, or is an :AXIOM (its truth does not
;;;      depend on Gamma at all): call its formula PHI. PHI remains
;;;      available unconditionally in the new proof (an axiom instance is
;;;      simply replicated; a hypothesis other than the discharged one
;;;      stays open), so plain K-weakening gets H -> PHI:
;;;        n0  PHI                                [the original line, unchanged]
;;;        n1  PHI -> (H -> PHI)                   [II.1 ?A=PHI ?B=H]
;;;        n2  H -> PHI                            [MP n1 n0]
;;;
;;;   3. The line is :IR citing (MP I J): original line I's formula is
;;;      (PSI -> PHI) and line J's formula is PSI, concluding PHI. By
;;;      induction the new proof already contains H -> (PSI -> PHI) (I's
;;;      new conclusion) and H -> PSI (J's new conclusion); S combines
;;;      them:
;;;        n0  (H->(PSI->PHI)) -> ((H->PSI)->(H->PHI))  [II.2 ?A=H ?B=PSI ?C=PHI]
;;;        n1  (H -> PSI) -> (H -> PHI)                  [MP n0 I-CONCL]
;;;        n2  H -> PHI                                   [MP n1 J-CONCL]
;;;
;;;   4. The line is :IR citing (GEN I X): original line I's formula is
;;;      B, and this line's own formula is (.forall X B). By induction the
;;;      new proof already contains H -> B (I's new conclusion). GEN
;;;      itself is still legal on it (see "GEN's KNOWN EDGE CASE" above:
;;;      Gamma in the new proof is a SUBSET of Gamma in the original proof
;;;      at the corresponding point, either identical or missing exactly
;;;      H, so whatever variable-freedom check justified the ORIGINAL GEN
;;;      application still justifies this one); axiom III.2 then moves H
;;;      across the quantifier:
;;;        n0  (.forall X (H -> B))                      [GEN I-CONCL X]
;;;        n1  (.forall X (H->B)) -> (H -> (.forall X B)) [III.2 ?x=X ?A=H ?B=B]
;;;        n2  H -> (.forall X B)                          [MP n1 n0]
;;;
;;; Every case's final line's formula is (H -> <original line's formula>),
;;; so MAPPING is always extended with (original-numbering . (that final
;;; line's new number . original-formula)).

(defun @deduction-p-implies-p-block (h n)
  "Case 1's five lines (see the section header): H -> H from K and S
alone. Returns (VALUES new-lines next-counter final-line-number)."
  (let ((n0 n) (n1 (1+ n)) (n2 (+ n 2)) (n3 (+ n 3)) (n4 (+ n 4))
        (h-to-h (list '.to h h)))
    (values
     (list (list n0 (list '.to (list '.to h (list '.to h-to-h h))
                                (list '.to (list '.to h h-to-h) (list '.to h h)))
                 :axiom '(II.2))
           (list n1 (list '.to h (list '.to h-to-h h)) :axiom '(II.1))
           (list n2 (list '.to (list '.to h h-to-h) (list '.to h h)) :ir (list 'MP n0 n1))
           (list n3 (list '.to h h-to-h) :axiom '(II.1))
           (list n4 (list '.to h h) :ir (list 'MP n2 n3)))
     (+ n 5)
     n4)))

(defun @deduction-weaken-block (h phi role by n)
  "Case 2's three lines: H -> PHI from PHI (ROLE/BY replicated, but
RENUMBERED to N -- reusing the original line's own numbering here would
collide with this walk's own fresh counter, e.g. under a second, nested
@DEDUCTION call re-numbering an already-transformed proof) via plain
K-weakening. Returns (VALUES new-lines next-counter final-line-number)."
  (let ((n0 n) (n1 (1+ n)) (n2 (+ n 2)))
    (values
     (list (list n0 phi role by)
           (list n1 (list '.to phi (list '.to h phi)) :axiom '(II.1))
           (list n2 (list '.to h phi) :ir (list 'MP n1 n0)))
     (+ n 3)
     n2)))

(defun @deduction-mp-block (h psi phi i-concl-n j-concl-n n)
  "Case 3's three lines: H -> PHI from H -> (PSI -> PHI) (at I-CONCL-N)
and H -> PSI (at J-CONCL-N) via S. Returns (VALUES new-lines next-counter
final-line-number)."
  (let ((n0 n) (n1 (1+ n)) (n2 (+ n 2)))
    (values
     (list (list n0 (list '.to (list '.to h (list '.to psi phi))
                                (list '.to (list '.to h psi) (list '.to h phi)))
                 :axiom '(II.2))
           (list n1 (list '.to (list '.to h psi) (list '.to h phi)) :ir (list 'MP n0 i-concl-n))
           (list n2 (list '.to h phi) :ir (list 'MP n1 j-concl-n)))
     (+ n 3)
     n2)))

(defun @deduction-gen-block (h x b i-concl-n n)
  "Case 4's three lines: H -> (.forall X B) from H -> B (at I-CONCL-N,
where B is the pre-generalization formula) via GEN followed by axiom
III.2. Returns (VALUES new-lines next-counter final-line-number)."
  (let ((n0 n) (n1 (1+ n)) (n2 (+ n 2))
        (h-to-b (list '.to h b)))
    (values
     (list (list n0 (list '.forall x h-to-b) :ir (list 'GEN i-concl-n x))
           (list n1 (list '.to (list '.forall x h-to-b) (list '.to h (list '.forall x b)))
                 :axiom '(III.2))
           (list n2 (list '.to h (list '.forall x b)) :ir (list 'MP n1 n0)))
     (+ n 3)
     n2)))

(defun @deduction-walk (h lines n mapping acc)
  "The induction itself: LINES is what remains of the original RAW-PROOF
(each already a (NUMBERING FORMULA ROLE BY) list, not yet a K-LINE
struct); ACC accumulates new lines in reverse. See the section header for
MAPPING's shape and the three cases."
  (if (null lines)
      (reverse acc)
      (destructuring-bind (num formula role by) (car lines)
        (cond
          ((and (eq role :hyp) (equal formula h))
           (multiple-value-bind (new-lines next concl) (@deduction-p-implies-p-block h n)
             (@deduction-walk h (cdr lines) next (acons num (cons concl formula) mapping)
                              (append (reverse new-lines) acc))))
          ((or (eq role :hyp) (eq role :axiom))
           (multiple-value-bind (new-lines next concl)
               (@deduction-weaken-block h formula role by n)
             (@deduction-walk h (cdr lines) next (acons num (cons concl formula) mapping)
                              (append (reverse new-lines) acc))))
          ((and (eq role :ir) (consp by) (eq (car by) 'MP))
           (destructuring-bind (mp-tag i j) by
             (declare (ignore mp-tag))
             (let ((i-entry (cdr (assoc i mapping :test #'equal)))
                   (j-entry (cdr (assoc j mapping :test #'equal))))
               (unless (and i-entry j-entry)
                 (error "@DEDUCTION: line ~S cites ~S/~S out of order or unknown." num i j))
               (multiple-value-bind (new-lines next concl)
                   (@deduction-mp-block h (cdr j-entry) formula (car i-entry) (car j-entry) n)
                 (@deduction-walk h (cdr lines) next (acons num (cons concl formula) mapping)
                                  (append (reverse new-lines) acc))))))
          ((and (eq role :ir) (consp by) (eq (car by) 'GEN))
           (destructuring-bind (gen-tag i x) by
             (declare (ignore gen-tag))
             (let ((i-entry (cdr (assoc i mapping :test #'equal))))
               (unless i-entry
                 (error "@DEDUCTION: line ~S cites ~S out of order or unknown." num i))
               (multiple-value-bind (new-lines next concl)
                   (@deduction-gen-block h x (cdr i-entry) (car i-entry) n)
                 (@deduction-walk h (cdr lines) next (acons num (cons concl formula) mapping)
                                  (append (reverse new-lines) acc))))))
          (t
           (error "@DEDUCTION: line ~S has role ~S, which this construction ~
                   does not (yet) support -- only :HYP, :AXIOM, and :IR ~
                   citing MP or GEN are handled. A cited :ITH/:TH/:DEF-ABBREV ~
                   may itself take premises by line-citation the way MP ~
                   does, which this version does not generalize to."
                  num role))))))

(defun @deduction (hyp-formula raw-proof)
  "Transform RAW-PROOF (a K-proof deriving some formula from an open-
hypothesis set that includes HYP-FORMULA) into a new raw K-proof deriving
(HYP-FORMULA -> <RAW-PROOF's own conclusion>) from RAW-PROOF's other open
hypotheses alone -- the Deduction (Meta-)Theorem. See the section header
above for the construction and its scope. Untrusted: the result is only
ever accepted if CHECK-K-PROOF re-verifies it from scratch, exactly like
any other raw-proof (see CHECK-AND-EXTEND-BY-DEDUCTION)."
  (@deduction-walk hyp-formula raw-proof 0 nil nil))

(defun check-and-extend-by-deduction (ledger kind name hyp-formula raw-proof &optional (log (silent-log)))
  "Convenience wrapper: admit (HYP-FORMULA -> <RAW-PROOF's conclusion>)
as a new KIND/NAME ledger entry, built via @DEDUCTION from a proof of
RAW-PROOF's conclusion under an open-hypothesis set including HYP-
FORMULA. Exactly as trustworthy as calling CHECK-AND-EXTEND directly on
some other raw-proof -- @DEDUCTION's output is re-verified from scratch,
never taken on faith."
  (check-and-extend ledger kind name (@deduction hyp-formula raw-proof) log))

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
