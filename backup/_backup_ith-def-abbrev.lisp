;;;; _backup_ith-def-abbrev.lisp -- BACKUP (not loaded by any ASDF system)
;;;;
;;;; Removed from the kernel on 2026-09-27 to keep src/ small (every line
;;;; of src/ is something a reader has to trust or understand). Nothing in
;;;; hilbert-library/ or zf-library/ used it. Kept here as material for a
;;;; later version.
;;;;
;;;; WHAT IT WAS
;;;;   Two extra kinds of derived entry:
;;;;     ITH        -- same checking as TH, only a different kind label
;;;;                  ("inference theorem"); cited with :ith.
;;;;     DEF-ABBREV -- a TH whose proof's conclusion must match a declared
;;;;                  DEFINIENS schema in both directions; admitted with
;;;;                  CHECK-AND-EXTEND-ABBREV, cited with :def-abbrev.
;;;;   Neither added checking power: both were stored and re-verified exactly as
;;;;   TH. Real definitions now go through the .system FOLD/UNFOLD axioms and
;;;;   DEFINE-FUNCTION-BY-DESCRIPTION.
;;;;
;;;; HOW TO RESTORE
;;;;   1. src/k-proof.lisp: add CHECK-AND-EXTEND-ABBREV back (section below);
;;;;      let CHECK-AND-EXTEND accept KIND in (ith th).
;;;;   2. src/ledger.lisp LEDGER-APPEND: the kinds indexed by name were
;;;;      (ith th def-abbrev th-ded).
;;;;   3. src/persistence.lisp: LEDGER-COMMANDS emitted (:ith NAME PROOF) and
;;;;      (:def-abbrev NAME DEFINIENS PROOF); LEDGER-FROM-COMMANDS replayed them
;;;;      (section below).
;;;;   4. src/meta.lisp: nothing (only @PROVEN? looked at ITH).
;;;;   5. web/: api.lisp and deps.lisp listed ith / def-abbrev among derived kinds.
;;;;   6. Tests: TEST-ABBREV-USAGE (tests/core-tests.lisp), the persistence check
;;;;      citing my-ax1, and the name-uniqueness check that used
;;;;      CHECK-AND-EXTEND-ABBREV (section below).
;;;;
;;;; The code below is verbatim from commit 3229ca5 (before removal).

;;; =====================================================================
;;; src/k-proof.lisp: CHECK-AND-EXTEND-ABBREV
;;; =====================================================================

(defun check-and-extend-abbrev (ledger name definiens raw-proof &optional (log (silent-log)))
  "Abbreviation/definition admission: this is ALSO a ledger object
requiring a proof, unlike Goedel's own meta-level definitions. DEFINIENS
is the schema NAME is meant to stand for (written using atomic-wff-symbol
schema atoms, e.g. A, exactly like an ITH/TH schema); RAW-PROOF must be a
genuine K-proof whose OWN CONCLUSION (last line) matches DEFINIENS via
MATCH-SCHEMA-ATOMS, checked in BOTH directions.

Requiring RAW-PROOF's actual conclusion to match DEFINIENS is what makes
this sound: DEF-ABBREV lines are checked via CHECK-K-DERIVED-LINE against
the STORED PROOF's own real conclusion, never against the caller's
DEFINIENS claim directly, so a mismatched DEFINIENS cannot be used to
assert anything false. But a ONE-DIRECTIONAL schema match alone would
still leave a labeling-honesty gap: a bare, unconstrained schema atom
like DEFINIENS = 'A matches ANY conclusion at all, so an entry could be
admitted whose recorded DEFINIENS bears no real relationship to what it
actually proves. Matching in the OTHER direction too (conclusion-as-
pattern against definiens-as-expr) closes this: a bare atom on either
side only matches a compound expression as a STRUCTURED schema, so
matching the actual conclusion's real structure against a too-vague
DEFINIENS fails wherever DEFINIENS omits structure the conclusion
actually has.

LOG is as in CHECK-AND-EXTEND, above."
  (when (derived-rule-name-taken-p name ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-ABBREV: the name ~S is already used by an ~
            existing ITH/TH/DEF-ABBREV entry -- refused to avoid an ~
            ambiguous or shadowing citation." name))
  (unless (judgement? 'wff? definiens ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-ABBREV: definiens ~S is not a well-formed formula." definiens))
  ;; As in CHECK-AND-EXTEND: LEDGER is already the right restriction.
  (unless (check-k-proof raw-proof ledger log)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-ABBREV: proof for ~S rejected." name))
  (let ((concl (proof-conclusion raw-proof)))
    (when (or (match-fail-p (match-schema-atoms definiens concl ledger nil))
              (match-fail-p (match-schema-atoms concl definiens ledger nil)))
      (log-admission-result log name nil)
      (error "CHECK-AND-EXTEND-ABBREV: the supplied proof's conclusion (~S) ~
              does not match the claimed definiens ~S for ~S -- refused ~
              (an abbreviation's proof must actually establish its own ~
              definiens, as the SAME schema in both directions, or it ~
              would let ~S be cited under a misleading description of ~
              what it really proves)."
             concl definiens name name)))
  (log-admission-result log name t)
  (ledger-append ledger 'def-abbrev (list name raw-proof) (list :derived raw-proof)))

;;; =====================================================================
;;; src/persistence.lisp: LEDGER-COMMANDS / LEDGER-FROM-COMMANDS (whole, before removal)
;;; =====================================================================

(defun ledger-commands (ledger)
  "The command stream that reconstructs LEDGER, in original admission
order, from a freshly bootstrapped kernel. Reads straight off LEDGER's
own ALL index (in K order, honoring BOUND), so it is always in sync with
whatever LEDGER actually contains -- never off some separately
maintained log that could drift from it. A DEF-ABBREV entry does not
itself store the DEFINIENS its admitter originally supplied (only its
NAME and RAW-PROOF do), so its command instead uses the proof's own
conclusion (PROOF-CONCLUSION) as DEFINIENS -- CHECK-AND-EXTEND-ABBREV's
own admission check already establishes that this is schema-equivalent
to whatever the original definiens was, so replaying it this way passes
the identical check again."
  (loop for e in (treap-values-below (ledger-all ledger) (ledger-bound ledger))
        for origin = (entry-origin e)
        for cmd = (if (eq (car origin) :primitive)
                      ;; :PRIMITIVE entries are BOOTSTRAP-KERNEL's (or a
                      ;; .system file's) own doing -- the seed symbols plus
                      ;; TERM?/WFF?/IRULE/AXIOM rules -- reconstructed by
                      ;; bootstrapping again in LEDGER-FROM-COMMANDS, never
                      ;; by a DECLARE-* command, which would wrongly treat an
                      ;; already-seeded symbol as a fresh one and be refused.
                      ;; The one exception is a DEFINE-FUNCTION-BY-DESCRIPTION
                      ;; definition, written once, at its defining axiom.
                      (and (eq (second origin) :by-description)
                           (eq (entry-kind e) 'axiom)
                           (third origin))
                      (case (entry-kind e)
                        (atomic-wff-symbol (list :declare-atomic-wff-symbol (entry-payload e)))
                        (variable-symbol (list :declare-variable-symbol (entry-payload e)))
                        (predicate-schema-symbol
                         (list* :declare-predicate-schema-symbol (entry-payload e)))
                        ((th ith)
                         (destructuring-bind (name raw-proof) (entry-payload e)
                           (list (if (eq (entry-kind e) 'th) :th :ith) name raw-proof)))
                        (def-abbrev
                         (destructuring-bind (name raw-proof) (entry-payload e)
                           (list :def-abbrev name (proof-conclusion raw-proof) raw-proof)))
                        (th-ded
                         (destructuring-bind (name hyp-formula raw-proof) (entry-payload e)
                           (list :th-ded name hyp-formula raw-proof)))
                        (t nil)))
        when cmd collect cmd))

(defun ledger-from-commands (commands &key (log (silent-log))
                                            (ledger (error "LEDGER-FROM-COMMANDS: :LEDGER is required (e.g. one built by BOOTSTRAP-KERNEL-FROM-SPEC-FILE).")))
  "The inverse of LEDGER-COMMANDS: starting from LEDGER (a freshly
bootstrapped kernel, with the given seed vocabulary, if LEDGER is not
supplied -- this must match whatever the ORIGINAL ledger was bootstrapped
with, since :PRIMITIVE entries are never themselves part of COMMANDS),
replay COMMANDS against it in order via the ordinary growth API.

Passing an already-grown LEDGER (rather than always starting over from
BOOTSTRAP-KERNEL) is what lets one COMMANDS stream build on top of
another's result -- separate files as separate, linkable \"modules\" of
one growing Hilbert system, the same way an assembler links separately
compiled object files rather than only ever assembling one monolithic
source. Nothing about this is privileged: LEDGER, whatever grew it, is
still just an ordinary ledger, and every command here still goes through
the same CHECK-AND-EXTEND/CHECK-AND-EXTEND-ABBREV/DECLARE-* gates."
  (progn
    (dolist (cmd commands ledger)
      (destructuring-bind (op . args) cmd
        (setf ledger
              (case op
                (:declare-atomic-wff-symbol (declare-atomic-wff-symbol ledger (first args)))
                (:declare-variable-symbol (declare-variable-symbol ledger (first args)))
                (:declare-predicate-schema-symbol
                 (declare-predicate-schema-symbol ledger (first args) (second args)))
                ((:th :ith) (destructuring-bind (name raw-proof) args
                              (check-and-extend ledger (if (eq op :th) 'th 'ith) name raw-proof log)))
                (:def-abbrev (destructuring-bind (name definiens raw-proof) args
                               (check-and-extend-abbrev ledger name definiens raw-proof log)))
                (:th-ded (destructuring-bind (name hyp-formula raw-proof) args
                           (check-and-extend-by-deduction-direct ledger name hyp-formula raw-proof log)))
                (:define-function-by-description
                 (apply #'define-function-by-description ledger args))
                (t (error "LEDGER-FROM-COMMANDS: unknown command ~S" cmd))))))))

;;; =====================================================================
;;; tests/core-tests.lisp: TEST-ABBREV-USAGE, TEST-VACUOUS-GEN-AND-BAD-ITH, TEST-NAME-UNIQUENESS (before removal)
;;; =====================================================================

(defun test-abbrev-usage (ledger)
  "Admits my-ax1 as a genuinely-connected label for the II.1 schema (the
supplied proof's own conclusion IS the claimed definiens), uses it at
several instances, and confirms a mismatched instance, an undefined
name, and an unrelated definiens ('evil') are all rejected -- the last
is the critical regression guarding CHECK-AND-EXTEND-ABBREV itself (see
its docstring). Returns the ledger extended with my-ax1."
  (let* ((ledger (check-and-extend-abbrev ledger 'my-ax1 '(.to A (.to A A))
                                           '((0 (.to A (.to A A)) :axiom (II.1))))))
    (expect "Using my-ax1 at B: (.to B (.to B B)) via :def-abbrev"
            (check-k-proof '((0 (.to B (.to B B)) :def-abbrev (my-ax1))) ledger)
            t)
    (expect "Using my-ax1 at the freshly-declared Q: (.to Q (.to Q Q))"
            (check-k-proof '((0 (.to Q (.to Q Q)) :def-abbrev (my-ax1))) ledger)
            t)
    (expect "Attack: (.to B (.to C B)) is not an instance of my-ax1 (A<>A mismatch) -- must reject"
            (check-k-proof '((0 (.to B (.to C B)) :def-abbrev (my-ax1))) ledger)
            nil)
    (expect "Attack: citing an undefined abbreviation name -- must reject"
            (check-k-proof '((0 (.to B (.to B B)) :def-abbrev (no-such-abbrev))) ledger)
            nil)
    (expect "Attack: 'evil' abbreviation with an unrelated proof -- must be REFUSED at admission"
            (handler-case
                (progn (check-and-extend-abbrev ledger 'evil 'A '((0 (.to A (.to A A)) :axiom (II.1))))
                       nil)
              (error () t))
            t)
    (expect "Attack payload: citing 'evil' must never assert an arbitrary formula for free"
            (check-k-proof '((0 (.forall v0 (.eq v0 v1)) :def-abbrev (evil))) ledger)
            nil)
    ledger))

(defun test-vacuous-gen-and-bad-ith (ledger)
  "Derives th-gen-vacuous via CHECK-AND-EXTEND and uses it in a later
proof, then defines ith-bad-gen (whose schema alone is legitimate) and
confirms a capturing instantiation of it is rejected on full
re-expansion. Returns the ledger extended with both new entries."
  (let* ((ledger (check-and-extend ledger 'th 'th-gen-vacuous
                                    '((0 A :hyp nil)
                                      (1 (.forall v0 A) :ir (Gen 0 v0))))))
    (expect "Using th-gen-vacuous legally: B |- forall v0 B"
            (check-k-proof '((X B :hyp nil)
                              (Y (.forall v0 B) :th (th-gen-vacuous X)))
                            ledger)
            t)
    (let* ((ledger (handler-case
                        (let ((new-ledger (check-and-extend ledger 'ith 'ith-bad-gen
                                                             '((0 A :hyp nil)
                                                               (1 (.forall v0 A) :ir (Gen 0 v0))))))
                          (expect "ith-bad-gen defines cleanly (vacuous case is legitimate on its own)" t t)
                          new-ledger)
                      (error (e)
                        (format t "ith-bad-gen unexpectedly rejected at definition time: ~A~%" e)
                        (expect "ith-bad-gen defines cleanly (vacuous case is legitimate on its own)" nil t)
                        ledger))))
      (expect "Attack: instantiate ith-bad-gen with A := (.eq v0 v1) -- must reject"
              (check-k-proof '((X (.eq v0 v1) :hyp nil)
                                (Y (.forall v0 (.eq v0 v1)) :ith (ith-bad-gen X)))
                              ledger)
              nil)
      ledger)))

(defun test-name-uniqueness (ledger)
  "ITH/TH/DEF-ABBREV names must be unique, and CHECK-AND-EXTEND must
refuse a non-ITH/TH kind."
  (expect "Re-using an existing name (my-ax1) for a new TH -- must be refused"
          (handler-case
              (progn (check-and-extend ledger 'th 'my-ax1 '((0 (.to A (.to A A)) :axiom (II.1)))) nil)
            (error () t))
          t)
  (expect "Re-using an existing name (th-gen-vacuous) for a new DEF-ABBREV -- must be refused"
          (handler-case
              (progn (check-and-extend-abbrev ledger 'th-gen-vacuous 'A
                                               '((0 A :hyp nil) (1 (.forall v0 A) :ir (Gen 0 v0))))
                     nil)
            (error () t))
          t)
  (expect "CHECK-AND-EXTEND refuses a non-ITH/TH kind (e.g. AXIOM)"
          (handler-case
              (progn (check-and-extend ledger 'axiom 'sneaky '((0 A :hyp nil))) nil)
            (error () t))
          t)
  ledger)

