;;;; system-spec.lisp -- Section 18: describing a whole system as a file
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 18. Describing a whole system (not just its theorems) as a file
;;; ---------------------------------------------------------------------
;;;
;;; Everything BOOTSTRAP-KERNEL admits is already, internally, plain data:
;;; a TERM?/WFF? formation rule is (NAME CONDITIONS RESULT-PATTERN), an
;;; AXIOM is (NAME CONDITIONS (EXTRA-PARAM-PATTERNS CONCLUSION-PATTERN)),
;;; an IRULE is (NAME CONDITIONS (PREMISE-PATTERNS EXTRA-PARAM-PATTERNS
;;; :=> CONCLUSION-PATTERN)) -- see BOOTSTRAP-KERNEL's own body, Section 7.
;;; The only reason a DIFFERENT logical system has meant editing this
;;; Lisp file up to now is that those literals are hand-written directly
;;; into BOOTSTRAP-KERNEL's source. This section externalizes exactly
;;; that data into a file format -- a SYSTEM SPEC -- read the same
;;; READ-based way a .ledger module already is (Section 10), and
;;; interpreted by BOOTSTRAP-KERNEL-FROM-SPEC below.
;;;
;;; A system-spec command is one of:
;;;   (:atomic-wff-symbols SYM...)
;;;   (:variable-symbols SYM...)
;;;   (:term-formation NAME CONDITIONS RESULT-PATTERN)
;;;   (:wff-formation   NAME CONDITIONS RESULT-PATTERN)
;;;   (:axiom NAME CONDITIONS (EXTRA-PARAM-PATTERNS CONCLUSION-PATTERN))
;;;   (:irule NAME CONDITIONS (PREMISE-PATTERNS EXTRA-PARAM-PATTERNS
;;;                            :=> CONCLUSION-PATTERN))
;;;
;;; CONDITIONS/patterns may freely use VAR?/WFF?/TERM? and any existing
;;; meta-predicate/meta-constructor (@SUBST, @SUBST-OK?, @NOT-FREE-IN?,
;;; @NOT-FREE-IN-DEPENDENCIES?, ...) by name -- the SAME fixed, closed
;;; catalog CHECK-CONDITION/MATCH-TEMPLATE already dispatch on (Section
;;; 3/4). A spec file can freely ASSEMBLE a new system out of that
;;; vocabulary (a different propositional basis, a different quantifier
;;; theory, brand-new connective/relation syntax such as a modal .BOX),
;;; but it cannot introduce a genuinely NEW meta-predicate -- one backed
;;; by new Lisp code -- from data alone; that remains a kernel-source-
;;; level extension, same as always.
;;;
;;; THE CRITICAL DIFFERENCE FROM A .LEDGER MODULE FILE, stated plainly:
;;; a .ledger file's THEOREMS are independently re-verified by CHECK-K-
;;; PROOF on every load, so a corrupted or dishonest .ledger file can at
;;; worst fail to load -- it can never smuggle in something false (see
;;; Section 10's own header). A system-spec file is not like that. It
;;; mints entries with ORIGIN = :PRIMITIVE -- admitted by fiat, exactly
;;; as BOOTSTRAP-KERNEL's own hardcoded axioms are, with NOTHING to check
;;; them against. Loading a system-spec file is not verification; it is
;;; an act of trust in whoever wrote it, in exactly the same sense that
;;; reading and trusting BOOTSTRAP-KERNEL's own Lisp source already was.
;;; An inconsistent axiom set (e.g. one that lets a WFF and its own
;;; negation both be proved) is not something CHECK-K-PROOF can detect
;;; from inside the system it defines -- that is Goedel's second
;;; incompleteness theorem, not a gap in this checker. What DOES stay
;;; true, and matters just as much here as anywhere else in this file:
;;; BOOTSTRAP-KERNEL-FROM-SPEC is the only function that can turn a spec
;;; command into a :PRIMITIVE entry (its own private LABELS-bound ADMIT,
;;; exactly like BOOTSTRAP-KERNEL's -- see Section 2's ADMIT-PRIMITIVE
;;; commentary), so loading a spec file is at least as auditable an act
;;; as calling BOOTSTRAP-KERNEL was: everything downstream of it (every
;;; :DERIVED theorem built on top) is still fully, independently
;;; re-verified against whatever the spec turned out to admit.

(defun bootstrap-kernel-from-spec (spec &key (atomic-symbols '(A B C D E F G H))
                                              (variables '(v0 v1 v2 v3 v4 v5))
                                              (ledger nil)
                                              (origin-note nil))
  "Builds a ledger by interpreting SPEC (a list of system-spec commands,
see the section header) instead of BOOTSTRAP-KERNEL's own hardcoded
axiom/rule literals. LEDGER, when supplied, is the starting point (an
already-bootstrapped-or-spec-built ledger) SPEC's commands are admitted
onto -- this is how a base system-spec file (say, propositional +
predicate + equality) and an add-on one (say, Peano arithmetic's
vocabulary and axioms) chain into a single growing PRIMITIVE base, the
same way READ-LEDGER-FROM-FILE's :LEDGER argument chains .ledger MODULE
files together (Section 10) -- except everything admitted here is
:PRIMITIVE, not :DERIVED, so nothing is or could be re-verified: see the
section header's trust-model note. When LEDGER is NIL, a fresh EMPTY-
LEDGER is seeded with ATOMIC-SYMBOLS/VARIABLES first, exactly as
BOOTSTRAP-KERNEL's own first two ADMIT-EACH calls do.

ORIGIN-NOTE, when non-NIL, is recorded after :PRIMITIVE in every admitted
entry's ORIGIN, i.e. (:PRIMITIVE . ORIGIN-NOTE). It is metadata only --
nothing in the checker reads past the :PRIMITIVE tag -- and exists so
that LEDGER-COMMANDS can tell which :PRIMITIVE entries came from a
replayable, checked definition (see DEFINE-FUNCTION-BY-DESCRIPTION)."
  (labels ((admit (ledger kind payload)
             "Mirrors BOOTSTRAP-KERNEL's own private ADMIT exactly (see
Section 2/7): the only two places in this whole file able to create a
:PRIMITIVE-origin entry are this LABELS binding and BOOTSTRAP-KERNEL's
own, neither reachable from outside its own lexical scope."
             (ledger-append ledger kind payload (list* :primitive origin-note)))
           (admit-each (ledger kind syms)
             (if (null syms)
                 ledger
                 (admit-each (admit ledger kind (car syms)) kind (cdr syms)))))
    (let ((ledger (or ledger
                       (admit-each (admit-each (empty-ledger) 'atomic-wff-symbol atomic-symbols)
                                   'variable-symbol variables))))
      (dolist (cmd spec ledger)
        (setf ledger
              (case (car cmd)
                (:atomic-wff-symbols (admit-each ledger 'atomic-wff-symbol (cdr cmd)))
                (:variable-symbols (admit-each ledger 'variable-symbol (cdr cmd)))
                (:term-formation (destructuring-bind (name conditions result-pattern) (cdr cmd)
                                    (admit ledger 'term? (list name conditions result-pattern))))
                (:wff-formation (destructuring-bind (name conditions result-pattern) (cdr cmd)
                                   (admit ledger 'wff? (list name conditions result-pattern))))
                (:axiom (destructuring-bind (name conditions form) (cdr cmd)
                          (admit ledger 'axiom (list name conditions form))))
                (:irule (destructuring-bind (name conditions form) (cdr cmd)
                          (admit ledger 'irule (list name conditions form))))
                (t (error "BOOTSTRAP-KERNEL-FROM-SPEC: unknown system-spec command ~S" cmd))))))))

(defun read-system-spec-from-file (path)
  "Reads PATH as a flat list of system-spec commands (plain S-expressions,
one or more per file, read back exactly as WRITE-COMMANDS-TO-FILE-style
tooling would write them) -- the same *PACKAGE*-bound READ loop
READ-LEDGER-FROM-FILE uses for .ledger MODULE files (Section 10), so
symbols like A, v0, .forall print and read back identically."
  (let ((*package* (find-package :ledger-kernel)))
    (with-open-file (in path :direction :input)
      (loop for form = (read in nil :eof)
            until (eq form :eof)
            collect form))))

(defun bootstrap-kernel-from-spec-file (path &key (atomic-symbols '(A B C D E F G H))
                                                   (variables '(v0 v1 v2 v3 v4 v5))
                                                   (ledger nil))
  "READ-SYSTEM-SPEC-FROM-FILE plus BOOTSTRAP-KERNEL-FROM-SPEC in one call
-- the system-spec analogue of READ-LEDGER-FROM-FILE."
  (bootstrap-kernel-from-spec (read-system-spec-from-file path)
                               :atomic-symbols atomic-symbols :variables variables :ledger ledger))
