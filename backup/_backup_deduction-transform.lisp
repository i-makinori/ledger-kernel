;;;; _backup_deduction-transform.lisp -- BACKUP (not loaded by any ASDF system)
;;;;
;;;; Removed from the kernel on 2026-09-27 to keep src/ small (every line
;;;; of src/ is something a reader has to trust or understand). Nothing in
;;;; hilbert-library/ or zf-library/ used it. Kept here as material for a
;;;; later version.
;;;;
;;;; WHAT IT WAS
;;;;   @DEDUCTION and CHECK-AND-EXTEND-BY-DEDUCTION: the Deduction Theorem as an
;;;;   untrusted proof TRANSFORMATION. Given a proof of Gamma, H |- B it built an
;;;;   explicit proof of Gamma |- H -> B (the textbook induction over lines:
;;;;   p->p block, weakening via II.1, MP via II.2, Gen via III.2), which the
;;;;   kernel then checked like any other proof -- no trust in the Deduction
;;;;   Theorem needed. Limits: lines had to be :hyp/:axiom/MP/Gen only, proofs
;;;;   grew about 3x per discharge, and a Gen of a variable free in H made
;;;;   before H was introduced was (soundly but needlessly) rejected.
;;;;   The library uses the trusted route instead,
;;;;   CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT (still in src/deduction.lisp).
;;;;   Restoring this is the natural first step toward an independent checker
;;;;   that does not trust the Deduction Theorem (expand every TH-DED entry).
;;;;
;;;; HOW TO RESTORE
;;;;   1. Put section 'src/deduction.lisp (transform part)' back at the top of
;;;;      src/deduction.lisp (it only needs CHECK-K-PROOF and CHECK-AND-EXTEND).
;;;;   2. Re-export @DEDUCTION and CHECK-AND-EXTEND-BY-DEDUCTION.
;;;;   3. Tests: put TEST-DEDUCTION-THEOREM back into tests/deduction-tests.lisp
;;;;      and call it in RUN-SELF-TESTS (tests/core-tests.lisp) just before
;;;;      TEST-DEDUCTION-THEOREM-DIRECT. The direct test also had one check,
;;;;      '@DEDUCTION genuinely fails here', on its GEN edge-case proof:
;;;;        (check-k-proof (@deduction h edge-proof) ledger)  ; expected NIL
;;;;
;;;; The code below is verbatim from commit 3229ca5 (before removal).

;;; =====================================================================
;;; src/deduction.lisp (transform part)
;;; =====================================================================

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

;;; =====================================================================
;;; tests/deduction-tests.lisp (TEST-DEDUCTION-THEOREM)
;;; =====================================================================

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

