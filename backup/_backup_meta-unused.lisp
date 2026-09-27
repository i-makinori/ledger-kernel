;;;; _backup_meta-unused.lisp -- BACKUP (not loaded by any ASDF system)
;;;;
;;;; Removed from the kernel on 2026-09-27 to keep src/ small (every line
;;;; of src/ is something a reader has to trust or understand). Nothing in
;;;; hilbert-library/ or zf-library/ used it. Kept here as material for a
;;;; later version.
;;;;
;;;; WHAT IT WAS
;;;;   Meta operations no system file uses:
;;;;     @PROVEN?     side condition: WFF is an open hypothesis or the conclusion
;;;;                  of an admitted TH/ITH. (Unused, and it would make a rule's
;;;;                  applicability depend on the ledger's contents.)
;;;;     @SUBSTN      simultaneous substitution of several variables (two-hop
;;;;                  through gensyms so the substitutions cannot interfere).
;;;;     @SUBSTN-OK?  capture check for @SUBSTN.
;;;;   @SUBSTN / @SUBSTN-OK? were needed only by n-ary inductive predicates
;;;;   (_backup_inductive.lisp). SUBSTITUTE-WFF-MULTI itself stays in
;;;;   src/meta.lisp: predicate-schema beta reduction (SCHEMA-BETA) uses it.
;;;;
;;;; HOW TO RESTORE
;;;;   1. Add META-SUBST-MULTI-OK? and META-PROVEN? back to src/meta.lisp
;;;;      (SUBSTITUTE-WFF-MULTI is still there).
;;;;   2. In META-PREDICATES-TABLE add
;;;;        (cons '@proven? #'meta-proven?) (cons '@substn-ok? #'meta-subst-multi-ok?)
;;;;      and in META-CONSTRUCTORS-TABLE add
;;;;        (cons '@substn (lambda (vars terms wff) (substitute-wff-multi vars terms wff)))
;;;;
;;;; The code below is verbatim from commit 3229ca5 (before removal).

;;; =====================================================================
;;; src/meta.lisp
;;; =====================================================================

(defun meta-subst-multi-ok? (ledger open-hyps vars terms wff)
  "As META-SUBST-OK?, but for the whole VARS/TERMS tuple SUBSTITUTE-WFF-
MULTI would apply at once: capture-safe iff EVERY individual (var . term)
pair in the tuple would itself be capture-safe against the ORIGINAL WFF
-- the two-hop GENSYM trick means the substitutions never interact, so
checking each pair independently against the untouched WFF is exactly
right, not an approximation."
  (declare (ignore open-hyps))
  (every (lambda (v tm) (meta-subst-ok? ledger nil v tm wff)) vars terms))

(defun meta-proven? (ledger open-hyps wff)
  "Is WFF currently an open hypothesis in the proof being checked (Gamma,
OPEN-HYPS), or the conclusion of some already-admitted :TH/:ITH ledger
entry? Used only inside side conditions of DERIVED rules being checked
against entries strictly earlier than themselves (see CHECK-AND-EXTEND).
Consults only the TH/ITH buckets of LEDGER's kind index (ENTRIES-OF-KIND),
never the whole ledger -- there is no index on a conclusion FORMULA
itself, so within those two buckets this still checks each candidate in
turn, but it no longer pays for every unrelated WFF?/AXIOM/IRULE/etc.
entry along the way."
  (or (member wff open-hyps :test #'equal)
      (some (lambda (e) (equal (proof-conclusion (second (entry-payload e))) wff))
            (append (entries-of-kind 'th ledger) (entries-of-kind 'ith ledger)))))

