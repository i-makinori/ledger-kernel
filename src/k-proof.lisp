;;;; k-proof.lisp -- Section 6: K-proofs and CHECK-AND-EXTEND
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 6. K-proofs and CHECK-AND-EXTEND
;;; ---------------------------------------------------------------------
;;;
;;; A raw k-line is (NUMBERING FORMULA ROLE BY):
;;;   ROLE is one of :HYP, :AXIOM, :IR, :ITH, :TH, :DEF-ABBREV.
;;;   BY carries role-specific justification data, e.g.
;;;     (:AXIOM axiom-name)
;;;     (:IR irule-name cited-numbering...)
;;;     (:ITH ith-name cited-numbering...)
;;;     (:TH th-name)
;;;     (:HYP)
;;;
;;; CHECK-K-PROOF walks the lines in order, maintaining a local
;;; "proven-so-far" list (numbering -> formula), and for each line
;;; dispatches on ROLE. Crucially, when a line cites a DERIVED ledger
;;; entry (an :ITH/:TH-kind rule), it does NOT trust the schema/pattern
;;; match alone -- it fully instantiates that entry's own stored proof
;;; with the concrete bindings and re-verifies it via a recursive
;;; CHECK-K-PROOF call, bottoming out at :PRIMITIVE entries and object-
;;; level side conditions.

(defstruct k-line numbering formula role by)

(defun raw->k-line (raw)
  (destructuring-bind (numbering formula role by) raw
    (make-k-line :numbering numbering :formula formula :role role :by by)))

(defun find-proven (numbering proven-alist)
  (cdr (assoc numbering proven-alist :test #'equal)))

(defun match-templates-seq (pats vals binds)
  "Match each of PATS against the correspondingly-positioned VALS, in
order, threading BINDS left-to-right through MATCH-TEMPLATE. Returns the
final bindings, or +FAIL+ as soon as any pair fails to match or the two
lists have different lengths."
  (cond
    ((match-fail-p binds) +fail+)
    ((and (null pats) (null vals)) binds)
    ((or (null pats) (null vals)) +fail+)
    (t (match-templates-seq (cdr pats) (cdr vals)
                             (match-template (car pats) (car vals) binds)))))

(defun resolve-cited (nums proven-alist)
  "Look up each of NUMS (proof-line citations) in PROVEN-ALIST via
FIND-PROVEN, returning the list of formulas found in the same order, or
+FAIL+ if any citation does not yet resolve to a previously-proven line."
  (cond
    ((null nums) nil)
    (t (let ((actual (find-proven (car nums) proven-alist)))
         (if (null actual)
             +fail+
             (let ((rest (resolve-cited (cdr nums) proven-alist)))
               (if (match-fail-p rest) +fail+ (cons actual rest))))))))

(defun check-k-ir-line (line proven-alist ledger open-hyps)
  "ROLE = :IR. BY = (irule-name . rest), where REST splits into two
groups: leading PROOF-LINE CITATIONS (numbers resolved to formulas via
PROVEN-ALIST) followed by LITERAL EXTRA PARAMETERS -- values supplied
directly rather than cited from earlier lines. This split is needed
because a rule like Gen takes both a premise line AND a bare variable
argument that never appeared as its own proof line: (Gen 0 v0) cites
line 0 as the premise and passes v0 as the variable to generalize on.
An irule's FORM therefore has the shape
  (PREMISE-PATTERNS EXTRA-PARAM-PATTERNS :=> CONCLUSION-PATTERN)
where PREMISE-PATTERNS match the cited formulas (in order), and
EXTRA-PARAM-PATTERNS match the literal extra arguments (in order, after
all citations). Once every pattern variable is bound this way, the
CONCLUSION-PATTERN is matched against LINE's own formula, and finally
the rule's side conditions are checked (which can consult Gamma, passed
in as OPEN-HYPS, via @not-free-in-dependencies?)."
  (destructuring-bind (irule-name . rest) (k-line-by line)
    (labels ((try-entries (entries)
               (and entries
                    (or (try-ir-entry (car entries) irule-name rest line proven-alist ledger open-hyps)
                        (try-entries (cdr entries))))))
      (try-entries (entries-of-kind 'irule ledger)))))

(defun try-ir-entry (entry irule-name rest line proven-alist ledger open-hyps)
  "Try a single :IRULE-kind ledger ENTRY against LINE, as described in
CHECK-K-IR-LINE. Returns T if ENTRY justifies LINE, else NIL."
  (destructuring-bind (name conditions form) (entry-payload entry)
    (and (eq name irule-name)
         (destructuring-bind (premise-pats extra-pats arrow concl-pat) form
           (declare (ignore arrow))
           (let ((n (length premise-pats)) (m (length extra-pats)))
             (and (= (length rest) (+ n m))
                  (let* ((cited (subseq rest 0 n))
                         (extras (subseq rest n))
                         (actuals (resolve-cited cited proven-alist)))
                    (and (not (match-fail-p actuals))
                         (let ((b1 (match-templates-seq premise-pats actuals nil)))
                           (and (not (match-fail-p b1))
                                (let ((b2 (match-templates-seq extra-pats extras b1)))
                                  (and (not (match-fail-p b2))
                                       (let ((b3 (match-template concl-pat (k-line-formula line) b2)))
                                         (and (not (match-fail-p b3))
                                              (nth-value 1 (check-conditions conditions b3 ledger nil open-hyps))))))))))))))))

(defun check-k-axiom-line (line ledger open-hyps)
  "ROLE = :AXIOM. BY = (axiom-name . extra-args), where EXTRA-ARGS are
literal values supplied directly by the citing proof -- e.g. axiom
III.1's substituted term, (III.1 v2) -- analogous to an IRULE's
EXTRA-PARAM-PATTERNS. Axioms never cite earlier proof lines, so unlike
CHECK-K-IR-LINE there is no citation-splitting step: all of BY's cdr is
EXTRA-ARGS.

An axiom's FORM has the shape (EXTRA-PARAM-PATTERNS CONCLUSION-PATTERN).
EXTRA-PARAM-PATTERNS are matched against EXTRA-ARGS FIRST, seeding their
bindings into BINDS before CONCLUSION-PATTERN is matched against the
line's own formula -- this is what lets a meta-constructor embedded in
CONCLUSION-PATTERN (axiom III.1's (@subst ?x ?t ?A)) find ?T already
ground when MATCH-TEMPLATE reaches it, without any unification."
  (destructuring-bind (axiom-name . extra-args) (k-line-by line)
    (labels ((try-entries (entries)
               (and entries
                    (or (try-axiom-entry (car entries) axiom-name extra-args line open-hyps ledger)
                        (try-entries (cdr entries))))))
      (try-entries (entries-of-kind 'axiom ledger)))))

(defun try-axiom-entry (entry axiom-name extra-args line open-hyps ledger)
  "Try a single :AXIOM-kind ledger ENTRY against LINE, as described in
CHECK-K-AXIOM-LINE. Returns T if ENTRY justifies LINE, else NIL."
  (destructuring-bind (name conditions form) (entry-payload entry)
    (and (eq name axiom-name)
         (destructuring-bind (extra-pats concl-pat) form
           (and (= (length extra-pats) (length extra-args))
                (let ((b1 (match-templates-seq extra-pats extra-args nil)))
                  (and (not (match-fail-p b1))
                       (let ((b2 (match-template concl-pat (k-line-formula line) b1)))
                         (and (not (match-fail-p b2))
                              (nth-value 1 (check-conditions conditions b2 ledger nil open-hyps)))))))))))

(defun proof-hypotheses (raw-proof)
  (mapcar #'k-line-formula
          (remove-if-not (lambda (l) (eq (k-line-role l) :hyp))
                          (mapcar #'raw->k-line raw-proof))))

(defun proof-conclusion (raw-proof)
  (k-line-formula (raw->k-line (car (last raw-proof)))))

;;; --- Optional logging -----------------------------------------------
;;;
;;; CHECK-K-PROOF's own soundness logic never consults a LOG-CONFIG: a
;;; missing, silent, or even wrongly-configured logger can never turn a
;;; rejected proof into an accepted one, or vice versa -- LOG-CONFIG only
;;; ever gates a side-effecting PRINT, layered strictly on top of the
;;; existing T/NIL verdicts. Two independent flags, matching what a
;;; reader of a rejected or accepted proof actually wants to ask:
;;;   ERRORS       -- when a line is REJECTED, print which line, its
;;;                   role, and (for :AXIOM/:IR/:ITH/:TH/:DEF-ABBREV
;;;                   lines) which name it tried to cite.
;;;   APPLICATIONS -- the same, when a line is ACCEPTED -- turning a
;;;                   successful run into a readable, step-by-step trace
;;;                   of which rule justified which line.
;;; Both default to NIL (silent), so every existing call site that never
;;; passes a LOG-CONFIG behaves exactly as before this section existed.

(defstruct (log-config (:constructor make-log-config (&key errors applications)))
  (errors nil) (applications nil))

(defun silent-log ()
  "The default LOG-CONFIG: neither flag set, nothing printed."
  (make-log-config))

(defun log-line-result (log line ok)
  "Print one diagnostic line for LINE's outcome, gated on whichever of
LOG's two flags applies. LOG may be NIL (treated the same as
(SILENT-LOG)), so callers written before this section still pass."
  (when (and log (or (and ok (log-config-applications log))
                      (and (not ok) (log-config-errors log))))
    (format t "~&[~:[REJECT~;accept~]] line ~S (~S~@[ ~S~]).~%"
            ok (k-line-numbering line) (k-line-role line)
            (and (consp (k-line-by line)) (car (k-line-by line))))))

(defun log-admission-result (log name ok)
  "As LOG-LINE-RESULT, but for the top-level accept/reject of an entire
CHECK-AND-EXTEND/CHECK-AND-EXTEND-ABBREV admission, identified by NAME
rather than by a line number."
  (when (and log (or (and ok (log-config-applications log))
                      (and (not ok) (log-config-errors log))))
    (format t "~&[~:[REJECT~;accept~]] admission of ~S.~%" ok name)))

(defun check-k-proof (raw-proof ledger &optional (log (silent-log)))
  "Re-verify RAW-PROOF from scratch against LEDGER (entries strictly
earlier than whatever is being admitted; caller is responsible for
passing an appropriately-restricted ledger view, e.g. via
ENTRIES-UPTO). Returns T iff every line checks out; when it does not, the
second value is the NUMBERING of the first line that was rejected (every
line before it was accepted, none after it was checked). Gamma (the open
hypotheses) starts fresh as NIL here, local to this call, and is threaded
explicitly through WALK below as an ordinary accumulator argument: a
:HYP line extends it (by consing) for the REST of this proof only, and a
recursive re-verification of some cited :DERIVED entry's own stored
proof (via TRY-DERIVED-ENTRY, which calls this function again) starts
this same function again from its own fresh NIL, so it gets its own
Gamma rather than inheriting or leaking into the caller's.

LOG, when non-silent, prints a line-by-line trace (see LOG-LINE-RESULT
above); it is threaded into the same recursive re-verification of a
cited :DERIVED entry's own stored proof, so a request to trace
applications or errors sees the FULL expansion this file always performs
anyway -- all the way down to :PRIMITIVE entries -- not just the
top-level proof's own lines."
  (labels ((walk (lines proven open-hyps)
             (if (null lines)
                 t
                 (let* ((line (raw->k-line (car lines)))
                        (ok
                          (case (k-line-role line)
                            ;; A :HYP line must itself be a well-formed
                            ;; formula, so a malformed or undeclared
                            ;; "formula" can never be smuggled in as an
                            ;; assumption. Whether it is added to
                            ;; OPEN-HYPS for the rest of the walk is
                            ;; decided below, once OK is known.
                            (:hyp (judgement? 'wff? (k-line-formula line) ledger))
                            (:axiom (check-k-axiom-line line ledger open-hyps))
                            (:ir (check-k-ir-line line proven ledger open-hyps))
                            ;; :ITH, :TH, and :DEF-ABBREV all fall
                            ;; through to the catch-all: all three are
                            ;; DERIVED entries (proof required at
                            ;; admission, full re-expansion required at
                            ;; every use), and CHECK-K-DERIVED-LINE's own
                            ;; kind filter covers all three uniformly.
                            ;; There is deliberately no weaker,
                            ;; axiom-like ("trust the schema match
                            ;; alone") path for DEF-ABBREV, which would
                            ;; let an abbreviation whose admission proof
                            ;; is unrelated to its claimed definiens
                            ;; assert an arbitrary formula for free --
                            ;; CHECK-AND-EXTEND-ABBREV closes that by
                            ;; requiring the proof's own conclusion to
                            ;; match DEFINIENS at admission time.
                            (t (check-k-derived-line line proven ledger log)))))
                   (log-line-result log line ok)
                   (if ok
                       (walk (cdr lines)
                             (cons (cons (k-line-numbering line) (k-line-formula line)) proven)
                             (if (eq (k-line-role line) :hyp)
                                 (cons (k-line-formula line) open-hyps)
                                 open-hyps))
                       (values nil (k-line-numbering line)))))))
    (walk raw-proof nil nil)))

(defun match-schema-hyps-against-cited (pats nums proven-alist ledger binds)
  "Match each of PATS (a list of schema-hypothesis formulas some entry
requires as premises) against the formula cited by the corresponding
entry of NUMS (proof-line numbers, resolved via FIND-PROVEN against
PROVEN-ALIST), threading BINDS left-to-right through MATCH-SCHEMA-ATOMS.
Shared by TRY-DERIVED-ENTRY (ITH/TH/DEF-ABBREV, whose schema-hyps are
ALL of the stored proof's :HYP lines) and TRY-DEDUCTION-ENTRY (TH-DED,
Section 11.5, whose schema-hyps are the stored proof's :HYP lines MINUS
the one already discharged into the conclusion) -- both need to match
some list of required premises against citations the identical way."
  (cond
    ((match-fail-p binds) +fail+)
    ((and (null pats) (null nums)) binds)
    ((or (null pats) (null nums)) +fail+)
    (t (let ((actual (find-proven (car nums) proven-alist)))
         (if (null actual)
             +fail+
             (match-schema-hyps-against-cited (cdr pats) (cdr nums) proven-alist ledger
                                               (match-schema-atoms (car pats) actual ledger binds)))))))

;;; --- Optional memoization of the recursive re-verification step --------
;;;
;;; TRY-DERIVED-ENTRY and TRY-DEDUCTION-ENTRY both end the same way: once
;;; an entry E's schema is matched against the citing LINE (and, if E has
;;; any required premises, against CITED), the resulting bindings B2
;;; instantiate E's own stored RAW-PROOF, which is then re-verified from
;;; scratch via CHECK-K-PROOF against ENTRIES-UPTO(ENTRY-K E). Nothing
;;; about that re-verification's OUTCOME depends on where the citation
;;; came from: it is a pure function of (E . B2) alone. Two facts make
;;; this precise:
;;;
;;;   1. E, once appended to the ledger, is an immutable structure that
;;;      is never mutated and never reused as a *different* entry
;;;      elsewhere -- ENTRY-K assigns it one fixed position forever.
;;;   2. ENTRIES-UPTO(ENTRY-K E) -- the "entries strictly before E" view
;;;      E's own proof is checked against -- is, by the ledger's
;;;      append-only design, exactly the same frozen prefix no matter
;;;      which later LEDGER value, or which call site, asks for it: it
;;;      can only ever contain what already existed at the moment E was
;;;      admitted.
;;;
;;; So memoizing CHECK-K-PROOF's verdict for a given (E . B2) pair is
;;; sound: it changes nothing about WHAT the checker accepts, only skips
;;; literally repeating an already-completed, deterministic computation.
;;; This matters most for entries with NO required premises (an ordinary
;;; zero-Gamma TH/TH-DED citation, e.g. "(th-identity)" with no cited
;;; line numbers): there, B2 is derived purely from the citing LINE's own
;;; formula, so the SAME entry cited with the SAME instantiation
;;; anywhere in the ledger -- however many times, however deeply nested
;;; -- is verified only once. An entry with required premises (Gamma) can
;;; still be memoized exactly the same way -- B2 is just as deterministic
;;; once CITED has been resolved into concrete bindings -- but in
;;; practice sees fewer cache hits, since B2 there also depends on
;;; whatever happened to be proven earlier in the CITING proof.
;;;
;;; OFF by default: ordinary use of this kernel, including every
;;; RUN-*-SELF-TESTS call, exercises the original always-re-verify path
;;; with no behavioural difference whatsoever. This is a pure performance
;;; layer bolted on top of the trusted core, never a relaxation of it --
;;; see TEST-DERIVED-ENTRY-MEMOIZATION below for a differential check
;;; (same verdicts, cache on vs. off) plus a demonstration of the speedup
;;; on exactly the exponential-blowup pattern that motivated this.

(defvar *derived-verify-cache* nil
  "NIL (the default): no memoization, identical to this kernel's original
behaviour. Otherwise an EQUAL hash table mapping (ENTRY . BINDS) to the
CHECK-K-PROOF verdict already computed for that pair. Set via
ENABLE-DERIVED-ENTRY-MEMOIZATION / DISABLE-DERIVED-ENTRY-MEMOIZATION.")

(defun verify-derived-instantiation (e binds instantiated ledger log)
  "The recursive re-verification step shared by TRY-DERIVED-ENTRY and
TRY-DEDUCTION-ENTRY: re-checks INSTANTIATED (E's own stored proof, with
schema bindings BINDS already substituted throughout) against entries
strictly before E. Memoized on (E . BINDS) whenever *DERIVED-VERIFY-
CACHE* is non-NIL; see the section header for why that's sound."
  (if *derived-verify-cache*
      (let ((key (cons e binds)))
        (multiple-value-bind (cached found) (gethash key *derived-verify-cache*)
          (if found
              cached
              (setf (gethash key *derived-verify-cache*)
                    (check-k-proof instantiated (entries-upto (entry-k e) ledger) log)))))
      (check-k-proof instantiated (entries-upto (entry-k e) ledger) log)))

(defun enable-derived-entry-memoization ()
  "Turns on (E . BINDS) memoization (see above) for the rest of this
image, or until DISABLE-DERIVED-ENTRY-MEMOIZATION is called. Starts from
an empty cache."
  (setf *derived-verify-cache* (make-hash-table :test #'equal)))

(defun disable-derived-entry-memoization ()
  "Reverts to this kernel's original always-re-verify behaviour."
  (setf *derived-verify-cache* nil))

(defun reset-derived-entry-memoization ()
  "Clears accumulated cache entries without disabling memoization (a
no-op if memoization is currently off)."
  (when *derived-verify-cache*
    (setf *derived-verify-cache* (make-hash-table :test #'equal))))

;;; --- Instantiating a cited entry --------------------------------------
;;;
;;; Citing a derived entry E at a line LINE works on E's stored proof:
;;;
;;;   1. RENAME: apply any variable renaming the citation asked for (:INST,
;;;      below) to the whole stored proof -- formulas and rule arguments
;;;      alike, bound occurrences included.
;;;   2. MATCH: find schema bindings -- atomic-wff symbols to formulas,
;;;      predicate schema symbols to lambda bindings -- by matching E's
;;;      hypotheses against the cited lines and its conclusion against
;;;      LINE, starting from any bindings :INST supplies explicitly.
;;;   3. INSTANTIATE: apply the bindings to every line of the stored proof:
;;;      each formula, and each argument of each rule citation (e.g. the
;;;      formula argument of (III.3 x A t)), but not line numbers.
;;;   4. COMPARE: the instantiated proof's hypotheses must be EQUAL to the
;;;      cited formulas and its conclusion EQUAL to LINE's formula.
;;;   5. RE-VERIFY: the instantiated proof is checked from scratch by
;;;      CHECK-K-PROOF against entries strictly before E.
;;;
;;; Steps 4 and 5 alone make the citation sound: LINE is then literally the
;;; conclusion of a fully checked proof whose hypotheses are exactly the
;;; cited formulas. Steps 1-3 only have to PROPOSE that proof; an error in
;;; them can make a correct citation fail, never a wrong one succeed.
;;;
;;; :INST. A citation's BY may end with :INST followed by a list of
;;; explicit bindings, e.g. (th-foo 3 4 :inst ((A (.eq v0 v1))
;;;                                             (P (v2) (.in v2 v1))
;;;                                             (v0 v7))):
;;;   (A formula)            atomic-wff symbol A := formula
;;;   (P (x1 .. xn) body)    predicate schema P := lambda (x1..xn) body;
;;;                          x1..xn distinct variables, n = P's arity
;;;   (v0 t)                 replace variable v0 by the term t throughout the
;;;                          stored proof (bound occurrences included, so
;;;                          if v0 is ever bound -- or generalised by Gen --
;;;                          t must be a variable, or the instance fails)
;;; Explicit bindings are needed when matching cannot find a binding by
;;; itself (a predicate schema applied to non-variables, or a symbol that
;;; does not occur in the matched formulas) and for renaming variables,
;;; which matching never does on its own.

(defun split-citation-inst (cited)
  "Split a citation's argument list into (VALUES LINE-REFS INST-LIST OK).
OK is NIL when :INST is present but not followed by exactly one list."
  (let ((pos (position :inst cited)))
    (if (null pos)
        (values cited nil t)
        (let ((tail (nthcdr (1+ pos) cited)))
          (values (subseq cited 0 pos) (car tail)
                  (and (= (length tail) 1) (listp (car tail))))))))

(defun parse-citation-inst (inst ledger)
  "Turn an :INST list into (VALUES RENAMING SCHEMA-BINDS OK): RENAMING an
alist variable -> term, SCHEMA-BINDS an alist in MATCH-SCHEMA-ATOMS'
format. OK is NIL if any entry is malformed (see the :INST note above)."
  (let ((renaming nil) (binds nil))
    (dolist (item inst (values (nreverse renaming) (nreverse binds) t))
      (unless (and (consp item) (symbolp (car item)) (listp (cdr item)))
        (return (values nil nil nil)))
      (let ((sym (car item)))
        (cond
          ((atomic-wff-symbol-p sym ledger)
           (unless (= (length item) 2) (return (values nil nil nil)))
           (push (cons sym (second item)) binds))
          ((variable-p sym ledger)
           (unless (= (length item) 2)
             (return (values nil nil nil)))
           (push (cons sym (second item)) renaming))
          ((predicate-schema-arity sym ledger)
           (unless (and (= (length item) 3) (listp (second item))
                        (= (length (second item)) (predicate-schema-arity sym ledger))
                        (distinct-variables-p (second item) ledger))
             (return (values nil nil nil)))
           (push (cons sym (list :lambda (second item) (third item))) binds))
          (t (return (values nil nil nil))))))))

(defun instantiate-raw-proof (raw-proof binds)
  "Step 3 above (also used for step 1, with a variable renaming as BINDS):
instantiate every line's formula and every argument of its BY citation,
leaving the rule name and any reference to one of RAW-PROOF's own line
numbers untouched."
  (let ((numbers (mapcar #'first raw-proof)))
    (mapcar (lambda (raw)
              (destructuring-bind (num formula role by) raw
                (list num
                      (instantiate-schema-atoms formula binds)
                      role
                      (if (consp by)
                          (cons (car by)
                                (mapcar (lambda (arg)
                                          (if (member arg numbers :test #'equal)
                                              arg
                                              (instantiate-schema-atoms arg binds)))
                                        (cdr by)))
                          by))))
            raw-proof)))

(defun cited-formulas (nums proven-alist)
  "The formulas proven at line numbers NUMS, or :MISSING if one is absent."
  (let ((fs (mapcar (lambda (n) (find-proven n proven-alist)) nums)))
    (if (some #'null fs) :missing fs)))

(defun try-derived-entry (e cited line proven-alist ledger &optional (log (silent-log)) (inst nil))
  "Try exactly ONE candidate DERIVED entry E as the justification for
LINE, following steps 1-5 of the section note above: E's schema
hypotheses are matched against the CITED formulas and its schema
conclusion against LINE's own formula, the stored proof is instantiated,
its hypotheses and conclusion are compared with the cited formulas and
LINE, and the instantiated proof is re-verified via CHECK-K-PROOF.
Failure here means only \"this particular entry doesn't work\", not \"no
entry works\" -- see CHECK-K-DERIVED-LINE, which tries every candidate in
turn. INST is the citation's explicit :INST list, if any.

LEDGER is threaded through exactly as received. CHECK-K-DERIVED-LINE is
sometimes called with a LEDGER already restricted via ENTRIES-UPTO
(recursively re-verifying a cited entry's own stored proof, so it can
only see entries strictly before that entry's own K); using an
unrestricted ledger here would let a proof reach entries admitted AFTER
the one being re-checked. LOG is passed straight through into the
recursive CHECK-K-PROOF call, so a trace request follows the full
expansion into E's own stored proof too."
  (destructuring-bind (name stored-proof) (entry-payload e)
    (declare (ignore name))
    (multiple-value-bind (renaming seed ok) (parse-citation-inst inst ledger)
      (let* ((raw-proof (if renaming (instantiate-raw-proof stored-proof renaming) stored-proof))
             (schema-hyps (proof-hypotheses raw-proof))
             (schema-concl (proof-conclusion raw-proof))
             (actual-hyps (cited-formulas cited proven-alist)))
        (and ok
             (listp actual-hyps)
             (= (length schema-hyps) (length actual-hyps))
             (let ((b1 (match-schema-hyps-against-cited schema-hyps cited proven-alist ledger seed)))
               (and (not (match-fail-p b1))
                    (let ((b2 (match-schema-atoms schema-concl (k-line-formula line) ledger b1)))
                      (and (not (match-fail-p b2))
                           (let ((instantiated (instantiate-raw-proof raw-proof b2)))
                             (and (equal (proof-hypotheses instantiated) actual-hyps)
                                  (equal (proof-conclusion instantiated) (k-line-formula line))
                                  (verify-derived-instantiation e (cons renaming b2) instantiated
                                                                ledger log))))))))))))

(defun try-deduction-entry (e cited line proven-alist ledger &optional (log (silent-log)) (inst nil))
  "Try a single :TH-DED-kind ledger ENTRY (admitted by
CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT, Section 11.5) as the justification
for LINE. A TH-DED entry's payload is (NAME HYP-FORMULA RAW-PROOF), not
(NAME RAW-PROOF).

CORRECTNESS NOTE (this is the one point where an earlier version of this
function was WRONG, caught before it was ever relied on): HYP-FORMULA is
only the ONE hypothesis the Deduction Theorem discharged into the
conclusion (.to HYP-FORMULA PHI) -- RAW-PROOF may still have OTHER open
hypotheses (Gamma) that were never discharged at all. The Deduction
Theorem gives Gamma |- H -> PHI, NOT |- H -> PHI outright; treating Gamma
as vanished (as an earlier draft of this function did) would let a proof
of, say, A, (.to A B) |- B get cited as the unconditional \"theorem\"
(.to (.to A B) B) -- which is not a tautology (false under A=false,
B=false). So Gamma's formulas remain genuine required premises here,
matched against CITED exactly the way TRY-DERIVED-ENTRY matches an
ordinary entry's schema-hypotheses (via the shared
MATCH-SCHEMA-HYPS-AGAINST-CITED). Only HYP-FORMULA itself -- filtered out
of RAW-PROOF's own hypothesis list below -- is exempt from citation,
because it alone has been folded into the object-level implication.

Otherwise this follows the same steps 1-5 as TRY-DERIVED-ENTRY: the
instantiated Gamma must equal the cited formulas, (.to H' PHI') -- H' and
PHI' the instantiated HYP-FORMULA and conclusion -- must equal LINE's
formula, and the instantiated RAW-PROOF, including H''s own :HYP line,
is re-verified via CHECK-K-PROOF from a fresh empty OPEN-HYPS."
  (destructuring-bind (name stored-hyp stored-proof) (entry-payload e)
    (declare (ignore name))
    (multiple-value-bind (renaming seed ok) (parse-citation-inst inst ledger)
      (let* ((hyp-formula (if renaming (instantiate-schema-atoms stored-hyp renaming) stored-hyp))
             (raw-proof (if renaming (instantiate-raw-proof stored-proof renaming) stored-proof))
             (gamma (remove hyp-formula (proof-hypotheses raw-proof) :test #'equal))
             (actual-hyps (cited-formulas cited proven-alist)))
        (and ok
             (listp actual-hyps)
             (= (length gamma) (length actual-hyps))
             (let ((b1 (match-schema-hyps-against-cited gamma cited proven-alist ledger seed)))
               (and (not (match-fail-p b1))
                    (let* ((schema-concl (list '.to hyp-formula (proof-conclusion raw-proof)))
                           (b2 (match-schema-atoms schema-concl (k-line-formula line) ledger b1)))
                      (and (not (match-fail-p b2))
                           (let ((instantiated (instantiate-raw-proof raw-proof b2))
                                 (inst-hyp (instantiate-schema-atoms hyp-formula b2)))
                             (and (member inst-hyp (proof-hypotheses instantiated) :test #'equal)
                                  (equal (mapcar (lambda (g) (instantiate-schema-atoms g b2)) gamma)
                                         actual-hyps)
                                  (equal (list '.to inst-hyp (proof-conclusion instantiated))
                                         (k-line-formula line))
                                  (verify-derived-instantiation e (cons renaming b2) instantiated
                                                                ledger log))))))))))))

(defun check-k-derived-line (line proven-alist ledger &optional (log (silent-log)))
  "ROLE is :ITH, :TH, :DEF-ABBREV, or :TH-DED: BY = (rule-name .
cited-numbering...), optionally ending in :INST and an explicit binding
list (see the section note above). Look up EVERY DERIVED entry named
RULE-NAME (ITH, TH, DEF-ABBREV, and TH-DED all share one name-citation
syntax) and try each in turn, accepting on the first that fully checks
out. An ITH/TH/DEF-ABBREV candidate goes through TRY-DERIVED-ENTRY; a
TH-DED candidate goes through TRY-DEDUCTION-ENTRY instead, whose required
premises are the stored proof's OTHER open hypotheses (everything except
the one formula already discharged into the conclusion's antecedent) --
see its own docstring for why that distinction matters. Neither ever
trusts the schema/pattern match by itself; both compare the instantiated
proof with LINE and the cited formulas and bottom out in a real
CHECK-K-PROOF re-verification.

Trying every candidate (rather than stopping at the first NAME match)
matters once more than one entry can share a name: CHECK-AND-EXTEND
refuses to admit a genuinely colliding name, but a stale or
adversarially-constructed ledger could still contain duplicates, and
CHECK-K-AXIOM-LINE/CHECK-K-IR-LINE already backtrack across same-named
axiom/irule entries the same way.

Candidates come from LEDGER's BY-DERIVED-NAME index -- an O(log n)
lookup of the one bucket already keyed by RULE-NAME, honoring LEDGER's
BOUND -- rather than a scan of every entry in the ledger regardless of
kind or name."
  (destructuring-bind (rule-name . args) (k-line-by line)
    (multiple-value-bind (cited inst ok) (split-citation-inst args)
      (and ok
           (let ((candidates (treap-values-below (alist-get (ledger-by-derived-name ledger) rule-name)
                                                  (ledger-bound ledger))))
             (some (lambda (e)
                     (if (eq (entry-kind e) 'th-ded)
                         (try-deduction-entry e cited line proven-alist ledger log inst)
                         (try-derived-entry e cited line proven-alist ledger log inst)))
                   candidates))))))

(defun derived-rule-name-taken-p (name ledger)
  "T iff NAME already labels some ITH/TH/DEF-ABBREV/TH-DED entry. These
share one name-citation syntax (a :ITH/:TH/:DEF-ABBREV/:TH-DED line's BY
is just (name . args), with no kind tag of its own to disambiguate), so
letting
a new entry silently reuse an existing name would make
CHECK-K-DERIVED-LINE's candidate search ambiguous and let a later,
possibly weaker or unrelated proof shadow an earlier one under the same
citable name. Checked by CHECK-AND-EXTEND and CHECK-AND-EXTEND-ABBREV
before admitting anything. An O(log n) BY-DERIVED-NAME lookup, like
CHECK-K-DERIVED-LINE above."
  (not (null (treap-values-below (alist-get (ledger-by-derived-name ledger) name) (ledger-bound ledger)))))

(defun check-and-extend (ledger kind name raw-proof &optional (log (silent-log)))
  "The general (non-bootstrap) growth path for ITH/TH entries. RAW-PROOF's
conclusion (last line) becomes the new entry's payload; the whole raw
proof is stored so the entry is fully auditable. The proof is checked
against LEDGER AS IT STANDS RIGHT NOW (all strictly earlier entries) --
nothing in RAW-PROOF may depend on the entry it is trying to create.
Returns the NEW ledger.

KIND must be ITH or TH: CHECK-AND-EXTEND always stores its payload as
(NAME RAW-PROOF), which is the shape CHECK-K-DERIVED-LINE expects for
ITH/TH/DEF-ABBREV entries -- calling it with, say, KIND='AXIOM would
silently create a malformed axiom entry (axioms need a (NAME CONDITIONS
FORM) payload) that would later crash CHECK-K-AXIOM-LINE's
DESTRUCTURING-BIND the first time it was scanned. DEF-ABBREV entries
have their own dedicated admission path, CHECK-AND-EXTEND-ABBREV
(definitions carry an extra DEFINIENS argument to cross-check), so it is
excluded here too -- use that instead for abbreviations.

LOG, when non-silent, traces CHECK-K-PROOF's line-by-line verdicts (see
LOG-LINE-RESULT) as it re-verifies RAW-PROOF, plus one final line for
this admission's own overall accept/reject (LOG-ADMISSION-RESULT)."
  (unless (eq kind 'th)
    (error "CHECK-AND-EXTEND: KIND must be TH, got ~S." kind))
  (when (derived-rule-name-taken-p name ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND: the name ~S is already used by an existing ~
            ITH/TH/DEF-ABBREV entry -- refused to avoid an ambiguous or ~
            shadowing citation." name))
  ;; LEDGER here is already exactly "every entry strictly earlier than
  ;; the one about to be created" -- it doesn't contain that entry yet --
  ;; so passing it straight through is ENTRIES-UPTO's restriction for
  ;; free, without even the O(1) cost of constructing a bounded view.
  (unless (check-k-proof raw-proof ledger log)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND: proof of ~S rejected." name))
  (log-admission-result log name t)
  (ledger-append ledger kind (list name raw-proof) (list :derived raw-proof)))
