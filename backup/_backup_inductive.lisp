;;;; _backup_inductive.lisp -- BACKUP (not loaded by any ASDF system)
;;;;
;;;; Removed from the kernel on 2026-09-27 to keep src/ small (every line
;;;; of src/ is something a reader has to trust or understand). Nothing in
;;;; hilbert-library/ or zf-library/ used it. Kept here as material for a
;;;; later version.
;;;;
;;;; WHAT IT WAS
;;;;   DEFINE-INDUCTIVE-PREDICATE(S): declare unary / n-ary / mutually inductive
;;;;   predicates over ZERO and S from introduction clauses. Admits one
;;;;   WFF-formation rule per predicate, one intro AXIOM (base clause) or IRULE
;;;;   (step clause) per clause, and an induction principle -- all :PRIMITIVE,
;;;;   after a well-formedness check (arity, schema variables, every predicate
;;;;   reachable from a base clause). Needed the @SUBSTN / @SUBSTN-OK? meta
;;;;   operations (see _backup_meta-unused.lisp).
;;;;
;;;; HOW TO RESTORE
;;;;   1. Restore _backup_meta-unused.lisp first (@SUBSTN, @SUBSTN-OK?).
;;;;   2. Copy section 'src/inductive.lisp' to src/inductive.lisp and add
;;;;      (:file "inductive") to ledger-kernel.asd after "system-spec".
;;;;   3. Export DEFINE-INDUCTIVE-PREDICATE(S) if wanted.
;;;;   4. Copy section 'tests/inductive-tests.lisp' back, add it to the tests
;;;;      system and call (run-inductive-definition-self-tests) from tests/run.lisp.
;;;;      Its tests used (bootstrap-kernel :arithmetic t); use (fol-kernel :arithmetic t).
;;;;
;;;; The code below is verbatim from commit 3229ca5 (before removal).

;;; =====================================================================
;;; src/inductive.lisp
;;; =====================================================================

;;;; inductive.lisp -- Section 20: general inductive predicate definitions
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 20. General inductive predicate definitions
;;; ---------------------------------------------------------------------
;;;
;;; P3 (Peano induction, Section 7) is hand-written for one specific
;;; shape: a domain built from exactly two constructors (ZERO, S), with
;;; every term automatically "in" the domain (there is no separate "is a
;;; natural number" predicate to check -- the whole term universe already
;;; plays that role). DEFINE-INDUCTIVE-PREDICATE generalizes this to an
;;; arbitrary, user-specified inductively defined UNARY PREDICATE over the
;;; existing term universe: "EVEN(x)", "PRIME(x)", "REACHABLE(x)",
;;; whatever the caller wants, given as a finite list of INTRODUCTION
;;; CLAUSES (base facts and recursive step rules) -- and, from those
;;; clauses alone, mechanically derives:
;;;   (a) a WFF-formation rule for the new predicate,
;;;   (b) one AXIOM (base case) or IRULE (step case, since it needs to
;;;       cite an already-established premise line, exactly like MP/Gen)
;;;       per clause, and
;;;   (c) the INDUCTION AXIOM itself: the generalization of P3 to however
;;;       many clauses were given, complete with the appropriate
;;;       @SUBST-OK? capture-avoidance side condition per clause.
;;;
;;; TRUST MODEL: exactly as Section 18's own .system-file mechanism, this
;;; is built entirely on top of BOOTSTRAP-KERNEL-FROM-SPEC -- the only
;;; two places in this file able to mint a :PRIMITIVE-origin ledger entry
;;; are BOOTSTRAP-KERNEL's own LABELS-bound ADMIT and this one, and
;;; DEFINE-INDUCTIVE-PREDICATE reaches the ledger through the latter, not
;;; some new privileged back door. So: introducing a new inductively
;;; defined predicate is exactly as trusted-by-fiat as introducing a new
;;; Peano axiom by hand would be -- nothing here is or could be
;;; independently re-verified against anything else. Unlike Peano's own
;;; P1-P10, whose SOUNDNESS this file's author checked by hand before
;;; hardcoding them, an arbitrary caller-supplied clause set could in
;;; principle be inconsistent (e.g. two clauses whose conclusions
;;; contradict each other structurally aren't detected as suspicious by
;;; anything below) -- this mechanism makes it *convenient* to state a new
;;; inductive definition, it does not make it *safe by construction*
;;; (there is no automated relative-consistency check here, matching the
;;; same honest limitation Section 18's own header already documents for
;;; hand-written .system files).
;;;
;;; A CLAUSE is a 3-element list (REC-VARS EXTRA-VARS RESULT-TERM), where
;;; REC-VARS and EXTRA-VARS are lists of ordinary ?-PREFIXED SCHEMA
;;; PATTERN VARIABLES (exactly the same kind already used throughout every
;;; other AXIOM/IRULE in this file, e.g. ?x, ?A -- nothing new to learn):
;;;   - REC-VARS: variables standing for a term ALREADY KNOWN to satisfy
;;;     the predicate being defined -- each contributes a premise
;;;     (NAME ?r) that the citing proof must supply as an already-proven
;;;     line, and an inductive hypothesis A[?r/x] inside the induction
;;;     axiom.
;;;   - EXTRA-VARS: any other schema variables RESULT-TERM needs that are
;;;     NOT themselves required to satisfy the predicate (there usually
;;;     are none, for the common "unary constructor" shape).
;;;   - RESULT-TERM: the term such that the clause concludes
;;;     (NAME RESULT-TERM), built from REC-VARS/EXTRA-VARS plus whatever
;;;     ordinary ground vocabulary (S, +, zero, ...) already exists.
;;; A clause with empty REC-VARS is a base case (admitted as an AXIOM); a
;;; clause with nonempty REC-VARS is a step case (admitted as an IRULE, so
;;; a citing proof must supply the recursive premise(s) as earlier proof
;;; lines, the same way MP/Gen do).
;;;
;;; Worked example, EVEN: "zero is even; if x is even, so is S(S(x))":
;;;   (define-inductive-predicate ledger 'even
;;;     '((nil nil zero)            ; EVEN(zero)
;;;       ((?x) nil (S (S ?x)))))   ; EVEN(x) -> EVEN(S(S(x)))
;;; produces EVEN-INTRO-1 (axiom: EVEN(zero)), EVEN-INTRO-2 (irule:
;;; EVEN(?x) |- EVEN(S(S(?x)))), and EVEN-IND, the induction axiom:
;;;   A[zero/x] -> ((forall y (EVEN(y) -> (A[y/x] -> A[S(S(y))/x])))
;;;                 -> forall x (EVEN(x) -> A))
;;; (see TEST-INDUCTIVE-EVEN below for citing EVEN-IND to actually prove
;;; something with it, mirroring TEST-PEANO-INDUCTION-PROOF's own
;;; base/step/GEN/MP-twice usage pattern for P3).

;;; --- General form: n-ary, possibly mutually recursive predicates -------
;;;
;;; The worked example above (EVEN) is the common case: one, unary,
;;; self-recursive predicate. DEFINE-INDUCTIVE-PREDICATES generalizes this
;;; along both axes at once:
;;;   - N-ARY: a predicate need not take a single term -- CLAUSE's own
;;;     RESULT becomes RESULT-TERMS, a list of as many terms as the
;;;     predicate's declared ARITY, e.g. a binary DOUBLE-OF(x,y) relation.
;;;   - MUTUAL RECURSION: several predicates can be defined TOGETHER as a
;;;     GROUP, each one's clauses free to cite ANY predicate in the group
;;;     as a recursive premise -- not only itself -- e.g. EVEN/ODD, each
;;;     defined via the OTHER's own step case.
;;; A CLAUSE is now (REC-SPECS EXTRA-VARS RESULT-TERMS):
;;;   - REC-SPECS: a list of (PRED-NAME VAR1 ... VARk), one per recursive
;;;     premise, PRED-NAME any predicate in the GROUP (itself, for
;;;     ordinary self-recursion, or another member, for genuine mutual
;;;     recursion) and VAR1..VARk that many fresh schema variables naming
;;;     PRED-NAME's own arguments at this call site. Each contributes a
;;;     premise (PRED-NAME VAR1...VARk) the citing proof must supply, and
;;;     -- inside the induction axioms -- an inductive hypothesis
;;;     "PRED-NAME's own motive holds of VAR1...VARk", using PRED-NAME's
;;;     OWN motive (not necessarily the clause's own predicate's motive:
;;;     this is exactly what makes mutual induction mutual).
;;;   - EXTRA-VARS/RESULT-TERMS: as before, just RESULT-TERMS is now a
;;;     TUPLE (one term per argument position) rather than a single term.
;;; GROUP is a list of (PRED-NAME ARITY . CLAUSES) triples. Simultaneous
;;; substitution into an n-ary motive (needed once ARITY > 1, since
;;; @SUBST only ever replaces ONE variable) uses the new @SUBSTN/
;;; @SUBSTN-OK? meta-forms (this section's header, Section 4).
;;;
;;; DEFINE-INDUCTIVE-PREDICATE (singular, below) remains exactly as
;;; before -- a thin wrapper for the common unary/non-mutual case, so
;;; every existing caller (TEST-INDUCTIVE-EVEN/TEST-INDUCTIVE-GENERALITY
;;; included) keeps working unchanged.

(defun rename-inductive-clause-vars (clause tag)
  "As before, generalized to CLAUSE = (REC-SPECS EXTRA-VARS RESULT-TERMS):
alpha-renames every VAR occurring across all of REC-SPECS' own
VAR1...VARk lists, plus EXTRA-VARS, to fresh schema pattern variables
tagged with TAG, leaving each REC-SPEC's own PRED-NAME and RESULT-TERMS'
ground vocabulary otherwise untouched (RESULT-TERMS are walked and
renamed consistently, since they may reuse the same var symbols)."
  (destructuring-bind (rec-specs extra-vars result-terms) clause
    (let* ((all-vars (append (mapcan (lambda (s) (copy-list (rest s))) rec-specs) extra-vars))
           (renaming (mapcar (lambda (v)
                                (cons v (intern (format nil "?C~A-~A" tag (subseq (symbol-name v) 1))
                                                 (symbol-package v))))
                              all-vars)))
      (labels ((ren (form)
                 (cond ((and (pat-var-p form) (assoc form renaming)) (cdr (assoc form renaming)))
                       ((consp form) (cons (ren (car form)) (ren (cdr form))))
                       (t form))))
        (list (mapcar (lambda (s) (cons (first s) (mapcar (lambda (v) (cdr (assoc v renaming))) (rest s))))
                      rec-specs)
              (mapcar (lambda (v) (cdr (assoc v renaming))) extra-vars)
              (mapcar #'ren result-terms))))))

(defun inductive-intro-command (pred-name idx clause)
  "As before, generalized to CLAUSE = (REC-SPECS EXTRA-VARS RESULT-TERMS)
and an N-ARY PRED-NAME: an (:AXIOM ...) command for a base case (empty
REC-SPECS), an (:IRULE ...) command for a step case, whose premise
patterns are now (QNAME VAR1...VARk) per REC-SPEC (QNAME possibly a
DIFFERENT predicate in the group, for mutual recursion) and whose
conclusion is (PRED-NAME . RESULT-TERMS)."
  (destructuring-bind (rec-specs extra-vars result-terms) clause
    (let ((intro-name (intern (format nil "~A-INTRO-~D" (symbol-name pred-name) idx) (symbol-package pred-name))))
      (if (null rec-specs)
          (list :axiom intro-name
                (mapcar (lambda (v) (list 'term? v)) extra-vars)
                (list nil (cons pred-name result-terms)))
          (list :irule intro-name
                (mapcar (lambda (v) (list 'term? v)) extra-vars)
                (list (mapcar (lambda (s) (cons (first s) (rest s))) rec-specs)
                      extra-vars
                      :=>
                      (cons pred-name result-terms)))))))

(defun inductive-hyp-pattern (target-pred motive-table clause)
  "As before, generalized: MOTIVE-TABLE is an alist PRED-NAME -> (SUBJECT-
VARS . MOTIVE-VAR) for every predicate in the GROUP (SUBJECT-VARS a list
of that predicate's own ARITY-many schema variables, one per argument
position). Builds one antecedent from an ALREADY ALPHA-RENAMED CLAUSE,
using @SUBSTN (not @SUBST) throughout so this works uniformly whether
TARGET-PRED (the predicate CLAUSE's own RESULT-TERMS conclude about) or
any REC-SPEC's own PRED-NAME is unary or N-ARY, and using EACH recursive
premise's OWN predicate's OWN motive for its inductive hypothesis -- the
mechanism that makes mutual induction mutual: EVEN's own induction axiom
still needs ODD's motive available wherever an EVEN clause recurses
through an ODD premise."
  (destructuring-bind (rec-specs extra-vars result-terms) clause
    (let* ((tgt (cdr (assoc target-pred motive-table)))
           (body (list '@substn (car tgt) result-terms (cdr tgt))))
      (dolist (spec (reverse rec-specs))
        (destructuring-bind (qname . qvars) spec
          (let ((q (cdr (assoc qname motive-table))))
            (setf body (list '.to (cons qname qvars)
                              (list '.to (list '@substn (car q) qvars (cdr q)) body))))))
      (dolist (v (reverse (append (mapcan (lambda (s) (copy-list (rest s))) rec-specs) extra-vars)))
        (setf body (list '.forall v body)))
      body)))

(defun check-inductive-group-well-formed (ledger group)
  "Validates GROUP (see DEFINE-INDUCTIVE-PREDICATES' own header for its
format) BEFORE any entry is minted, refusing -- via ERROR, atomically,
nothing partially applied -- a GROUP that would otherwise go through
silently and produce either a confusing internal crash deep inside
INDUCTIVE-HYP-PATTERN, a subtly WRONG axiom, or (the concrete bug this
section's own worked examples actually hit during development, when the
mutual EVEN/ODD example first reused the name EVEN already minted by
TEST-INDUCTIVE-EVEN on the same threaded ledger) two DIFFERENT
predicates' rules silently sharing one name and letting
TRY-AXIOM-ENTRY/TRY-IR-ENTRY match against whichever one happens to come
first in the ledger:

  1. NAME COLLISION: none of the fresh entry-names GROUP is about to mint
     (each predicate's own WFF-formation rule name, each clause's own
     INTRO-name, each predicate's own IND-name) may already be in use by
     an existing TERM?/WFF?/AXIOM/IRULE entry in LEDGER.
  2. SHAPE: predicate names are pairwise distinct within GROUP; each
     ARITY is a positive integer; every REC-SPEC's own PRED-NAME actually
     names a member of GROUP (not a typo, and not some other, unrelated
     predicate already in the ledger -- ASSOC silently returning NIL here
     is exactly what would otherwise turn into a wrong axiom, not a
     crash); every REC-SPEC's own variable count matches that target
     predicate's declared ARITY; every clause's own RESULT-TERMS length
     matches ITS OWN predicate's declared ARITY; every REC-SPEC/EXTRA-VAR
     is a genuine schema pattern variable (PAT-VAR-P).
  3. GROUNDEDNESS: every predicate in GROUP must be reachable from SOME
     chain of base clauses -- the least fixed point of \"has at least one
     clause whose REC-SPECS are ALL already-known-inhabited\" (base
     clauses, with empty REC-SPECS, are inhabited immediately -- exactly
     the same fixpoint computation as \"which nonterminals of a grammar
     can produce at least one string\") must eventually cover every
     predicate in GROUP. A predicate that can never actually be
     introduced (no base case anywhere in its own dependency closure --
     a forgotten base clause, or a mutual-recursion cycle that never
     bottoms out) would still get a technically SOUND induction axiom
     (vacuously true, about the empty relation), so this isn't a
     soundness gap -- but it is almost certainly not what was intended,
     so it's refused rather than silently accepted.

Note what this does NOT try to guarantee: it does not (and, given how
this file's clause format works, does not need to) check strict
positivity in the usual inductive-definition sense -- REC-SPECS are
always plain predicate-application PREMISES, never embedded negated or
higher-order inside a RESULT-TERM, so there is no way for this
particular mechanism to build a non-monotone operator whose least fixed
point wouldn't exist in the first place. What CAN still go wrong here is
purely definitional/bookkeeping mistakes, which is exactly what the
three checks above catch."
  (let ((pred-names (mapcar #'first group)))
    (unless (= (length pred-names) (length (remove-duplicates pred-names)))
      (error "DEFINE-INDUCTIVE-PREDICATES: duplicate predicate name(s) within GROUP: ~S" pred-names))
    ;; -- 2: shape --
    (dolist (g group)
      (destructuring-bind (name arity . clauses) g
        (unless (and (integerp arity) (plusp arity))
          (error "DEFINE-INDUCTIVE-PREDICATES: ~S's ARITY must be a positive integer, got ~S" name arity))
        (dolist (clause clauses)
          (destructuring-bind (rec-specs extra-vars result-terms) clause
            (unless (= (length result-terms) arity)
              (error "DEFINE-INDUCTIVE-PREDICATES: a clause of ~S has ~D RESULT-TERM(S) but ~S's own declared ARITY is ~D~%  clause: ~S"
                     name (length result-terms) name arity clause))
            (dolist (v extra-vars)
              (unless (pat-var-p v)
                (error "DEFINE-INDUCTIVE-PREDICATES: EXTRA-VAR ~S in a clause of ~S is not a schema pattern variable (must start with ?)~%  clause: ~S"
                       v name clause)))
            (dolist (spec rec-specs)
              (destructuring-bind (qname . qvars) spec
                (let ((tgt (assoc qname group)))
                  (unless tgt
                    (error "DEFINE-INDUCTIVE-PREDICATES: a REC-SPEC in a clause of ~S cites ~S, which is not a member of this GROUP~%  clause: ~S~%  GROUP predicates: ~S"
                           name qname clause pred-names))
                  (unless (= (length qvars) (second tgt))
                    (error "DEFINE-INDUCTIVE-PREDICATES: a REC-SPEC in a clause of ~S cites ~S with ~D variable(s), but ~S's own declared ARITY is ~D~%  clause: ~S"
                           name qname (length qvars) qname (second tgt) clause)))
                (dolist (v qvars)
                  (unless (pat-var-p v)
                    (error "DEFINE-INDUCTIVE-PREDICATES: REC-SPEC variable ~S in a clause of ~S is not a schema pattern variable (must start with ?)~%  clause: ~S"
                           v name clause)))))))))
    ;; -- 1: name collisions against the LIVE ledger --
    (let ((existing (mapcan (lambda (k) (mapcar (lambda (e) (first (entry-payload e))) (entries-of-kind k ledger)))
                             '(term? wff? axiom irule))))
      (dolist (g group)
        (destructuring-bind (name arity . clauses) g
          (declare (ignore arity))
          (let ((wff-name (intern (format nil "WFF_~A?" (symbol-name name)) (symbol-package name)))
                (ind-name (intern (format nil "~A-IND" (symbol-name name)) (symbol-package name)))
                (intro-names (loop for c in clauses for i from 1
                                    collect (intern (format nil "~A-INTRO-~D" (symbol-name name) i)
                                                     (symbol-package name)))))
            (dolist (nm (list* wff-name ind-name intro-names))
              (when (member nm existing)
                (error "DEFINE-INDUCTIVE-PREDICATES: refusing to define ~S -- the name ~S is already in use by an existing TERM?/WFF?/AXIOM/IRULE entry (defining it again would silently make TRY-AXIOM-ENTRY/TRY-IR-ENTRY try BOTH the old and the new rule under the same shared name)"
                       name nm)))))))
    ;; -- 3: groundedness (least fixed point over the whole GROUP) --
    (let ((inhabited nil) (changed t))
      (loop while changed do
        (setf changed nil)
        (dolist (g group)
          (destructuring-bind (name arity . clauses) g
            (declare (ignore arity))
            (unless (member name inhabited)
              (when (some (lambda (c) (every (lambda (spec) (member (first spec) inhabited)) (first c))) clauses)
                (push name inhabited)
                (setf changed t))))))
      (dolist (g group)
        (let ((name (first g)))
          (unless (member name inhabited)
            (error "DEFINE-INDUCTIVE-PREDICATES: ~S can never actually be derived -- no chain of clauses within this GROUP bottoms out in a base case for it (a forgotten base clause, or a mutual-recursion cycle with no way to get started). Predicates that DO bottom out: ~S"
                   name inhabited))))))
  t)

(defun define-inductive-predicates (ledger group)
  "General public entry point (see this subsection's own header for the
GROUP/CLAUSE format and DEFINE-INDUCTIVE-PREDICATE, below, for the common
unary/non-mutual convenience wrapper). Extends LEDGER, via BOOTSTRAP-
KERNEL-FROM-SPEC exactly as the unary case already did, with: one WFF-
formation rule and one induction axiom PER predicate in GROUP, and one
introduction AXIOM/IRULE per clause across every predicate -- the
induction axioms all share the SAME antecedent list (built from every
clause in the whole GROUP, not just their own predicate's), differing
only in which predicate's own motive their final conclusion is about,
which is exactly what makes proving any ONE of a mutually recursive
group's properties require establishing the induction step for ALL of
them together. CHECK-INDUCTIVE-GROUP-WELL-FORMED (above) is run FIRST
and refuses the whole call before anything is minted if GROUP is
malformed or would collide with LEDGER's existing entries."
  (check-inductive-group-well-formed ledger group)
  (let* ((motive-table
           (mapcar (lambda (g)
                     (destructuring-bind (name arity . clauses) g
                       (declare (ignore clauses))
                       (cons name (cons (loop for i from 1 to arity
                                              collect (intern (format nil "?IND-X-~A-~D" (symbol-name name) i)
                                                               (symbol-package name)))
                                         (intern (format nil "?IND-A-~A" (symbol-name name)) (symbol-package name))))))
                   group))
         (wff-cmds
           (mapcar (lambda (g)
                     (destructuring-bind (name arity . clauses) g
                       (declare (ignore clauses))
                       (let ((args (loop for i from 1 to arity
                                         collect (intern (format nil "?A~D" i) (symbol-package name)))))
                         (list :wff-formation (intern (format nil "WFF_~A?" (symbol-name name)) (symbol-package name))
                               (mapcar (lambda (a) (list 'term? a)) args)
                               (list 'wff? (cons name args))))))
                   group))
         (intro-cmds
           (mapcan (lambda (g)
                     (destructuring-bind (name arity . clauses) g
                       (declare (ignore arity))
                       (loop for c in clauses for i from 1 collect (inductive-intro-command name i c))))
                   group))
         ;; A single running counter across EVERY clause in the whole
         ;; group, so alpha-renamed variables from two different clauses
         ;; -- even ones belonging to two different predicates -- can
         ;; never collide once spliced together into the shared
         ;; antecedent list every induction axiom below is built from.
         (tag 0)
         (renamed (mapcan (lambda (g)
                             (destructuring-bind (name arity . clauses) g
                               (declare (ignore arity))
                               (mapcar (lambda (c) (incf tag) (cons name (rename-inductive-clause-vars c tag)))
                                       clauses)))
                           group))
         (hyps (mapcar (lambda (r) (inductive-hyp-pattern (car r) motive-table (cdr r))) renamed))
         (subst-ok-conditions
           (mapcar (lambda (r) (let ((tgt (cdr (assoc (car r) motive-table))))
                                  (list '@substn-ok? (car tgt) (third (cdr r)) (cdr tgt))))
                   renamed))
         (var-wff-conditions
           (mapcan (lambda (g) (let ((tgt (cdr (assoc (first g) motive-table))))
                                  (append (mapcar (lambda (v) (list 'var? v)) (car tgt))
                                          (list (list 'wff? (cdr tgt))))))
                   group))
         (all-conditions (append var-wff-conditions subst-ok-conditions))
         (all-extra-params (mapcan (lambda (g) (let ((tgt (cdr (assoc (first g) motive-table))))
                                                  (append (car tgt) (list (cdr tgt)))))
                                    group))
         (ind-cmds
           (mapcar (lambda (g)
                     (destructuring-bind (name arity . clauses) g
                       (declare (ignore arity clauses))
                       (let* ((tgt (cdr (assoc name motive-table)))
                              (concl (list '.to (cons name (car tgt)) (cdr tgt))))
                         (dolist (v (reverse (car tgt))) (setf concl (list '.forall v concl)))
                         (let ((body concl))
                           (dolist (h (reverse hyps)) (setf body (list '.to h body)))
                           (list :axiom (intern (format nil "~A-IND" (symbol-name name)) (symbol-package name))
                                 all-conditions
                                 (list all-extra-params body))))))
                   group)))
    (bootstrap-kernel-from-spec (append wff-cmds intro-cmds ind-cmds) :ledger ledger)))

(defun define-inductive-predicate (ledger name clauses)
  "Backward-compatible convenience wrapper over DEFINE-INDUCTIVE-
PREDICATES for the common case: a single, non-mutually-recursive, UNARY
predicate. CLAUSES keep the original 2-part shape (REC-VARS EXTRA-VARS
RESULT) -- REC-VARS are all implicitly recursive premises of NAME ITSELF
(there is no other predicate in a singleton, non-mutual group to
reference), and RESULT is a single term (not a tuple), since the
predicate is unary. See this section's own header for the clause format
and the worked EVEN example."
  (define-inductive-predicates
   ledger
   (list (list* name 1
                (mapcar (lambda (c)
                          (destructuring-bind (rec-vars extra-vars result) c
                            (list (mapcar (lambda (v) (list name v)) rec-vars) extra-vars (list result))))
                        clauses)))))

;;; =====================================================================
;;; tests/inductive-tests.lisp
;;; =====================================================================

;;;; inductive-tests.lisp -- Section 20: inductive definition tests
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun test-inductive-even (ledger)
  "Worked example: EVEN(zero); EVEN(x) -> EVEN(S(S(x))). Exercises
formation, both flavors of introduction rule (AXIOM for the base case,
IRULE for the step case), attack tests, and a genuine induction proof --
mirroring TEST-PEANO-INDUCTION-PROOF's own base/step/GEN/MP-twice usage
pattern for P3, but now for a predicate that P3 knows nothing about,
generated entirely from data by DEFINE-INDUCTIVE-PREDICATE itself."
  (let ((ledger (define-inductive-predicate ledger 'even '((nil nil zero) ((?x) nil (S (S ?x)))))))
    (expect "(EVEN v0) is a wff" (judgement? 'wff? '(even v0) ledger) t)
    (expect "EVEN(zero) via the base-case AXIOM"
            (check-k-proof '((0 (even zero) :axiom (even-intro-1))) ledger) t)
    (let* ((proof2 '((0 (even zero) :axiom (even-intro-1))
                      (1 (even (S (S zero))) :ir (even-intro-2 0))))
           (ledger2 (check-and-extend ledger 'th 'th-even-2 proof2)))
      (expect "EVEN(S(S(zero))) via the step-case IRULE, citing EVEN(zero)"
              (check-k-proof proof2 ledger2) t)
      (expect "EVEN(S(S(S(S(zero))))) chaining the step-case IRULE twice"
              (check-k-proof '((0 (even zero) :axiom (even-intro-1))
                                (1 (even (S (S zero))) :ir (even-intro-2 0))
                                (2 (even (S (S (S (S zero))))) :ir (even-intro-2 1)))
                              ledger2)
              t)
      (expect "Attack: the step-case IRULE citing a line that ISN'T (EVEN ...) at all -- must reject"
              (check-k-proof '((0 (.eq zero zero) :axiom (IV.1))
                                (1 (even (S (S zero))) :ir (even-intro-2 0)))
                              ledger2)
              nil))
    ;; The induction proof itself: forall v0 (EVEN(v0) -> v0=v0). Trivial
    ;; (reflexivity), chosen so the STEP case's own inductive hypothesis
    ;; and recursive premise are legitimately available but simply unused
    ;; (weakened away via II.1/K) -- exactly the case that most exercises
    ;; whether the generated EVEN-IND axiom threads a genuinely UNUSED
    ;; hypothesis through correctly, matching this project's own "prove
    ;; the wiring, not just the arithmetic" testing style.
    (let* ((step-lemma-proof
             '((0 (.eq (S (S v1)) (S (S v1))) :axiom (IV.1))
               (1 (.to (.eq (S (S v1)) (S (S v1))) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))) :axiom (II.1))
               (2 (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1)))) :ir (MP 1 0))
               (3 (.to (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))
                       (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))))
                  :axiom (II.1))
               (4 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))) :ir (MP 3 2))))
           (ledger (check-and-extend ledger 'th 'th-even-step-lemma step-lemma-proof)))
      (expect "step lemma (no open hyps -- a closed tautological derivation) checks"
              (check-k-proof step-lemma-proof ledger) t)
      (progn
        (expect "GEN v1 on the step lemma checks (v1 free in no open hyp: the lemma is closed)"
                (check-k-proof `((0 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))) :th (th-even-step-lemma))
                                  (1 (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1)))))) :ir (Gen 0 v1)))
                                ledger)
                t)
        (expect "full induction proof of forall v0 (EVEN(v0) -> v0=v0), via the GENERATED EVEN-IND axiom"
                (check-k-proof `((0 (.eq zero zero) :axiom (IV.1))
                                  (1 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))) :th (th-even-step-lemma))
                                  (2 (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1)))))) :ir (Gen 1 v1))
                                  (3 (.to (.eq zero zero)
                                          (.to (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))))
                                               (.forall v0 (.to (even v0) (.eq v0 v0)))))
                                     :axiom (even-ind v0 (.eq v0 v0)))
                                  (4 (.to (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))))
                                          (.forall v0 (.to (even v0) (.eq v0 v0))))
                                     :ir (MP 3 0))
                                  (5 (.forall v0 (.to (even v0) (.eq v0 v0))) :ir (MP 4 2)))
                                ledger)
                t)
        (expect "Attack: EVEN-IND cited with a WRONG base term (S(zero) instead of zero) -- must reject"
                (check-k-proof `((0 (.to (.eq (S zero) (S zero))
                                        (.to (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))))
                                             (.forall v0 (.to (even v0) (.eq v0 v0)))))
                                     :axiom (even-ind v0 (.eq v0 v0))))
                                ledger)
                nil)
        (expect "Attack: EVEN-IND's step antecedent MISSING the recursive (EVEN v1) premise -- must reject"
                (check-k-proof `((0 (.to (.eq zero zero)
                                        (.to (.forall v1 (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1)))))
                                             (.forall v0 (.to (even v0) (.eq v0 v0)))))
                                     :axiom (even-ind v0 (.eq v0 v0))))
                                ledger)
                nil)
        ledger))))

(defun test-inductive-generality (ledger)
  "A SECOND, differently-shaped inductive predicate (POS: S(zero) is
positive; if x is positive so is S(x) -- successor closure starting from
1, not 0), defined via the exact same DEFINE-INDUCTIVE-PREDICATE, to
confirm nothing about EVEN's own S-of-S shape was accidentally baked into
the generator. Formation and introduction only, kept short."
  (let ((ledger (define-inductive-predicate ledger 'pos '((nil nil (S zero)) ((?x) nil (S ?x))))))
    (expect "(POS v0) is a wff" (judgement? 'wff? '(pos v0) ledger) t)
    (expect "POS(S(zero)) via the base-case AXIOM"
            (check-k-proof '((0 (pos (S zero)) :axiom (pos-intro-1))) ledger) t)
    (expect "POS(S(S(zero))) via the step-case IRULE, citing POS(S(zero))"
            (check-k-proof '((0 (pos (S zero)) :axiom (pos-intro-1))
                              (1 (pos (S (S zero))) :ir (pos-intro-2 0)))
                            ledger)
            t)
    (expect "Attack: POS-INTRO-1 does not admit POS(zero) (that's EVEN's base case, not POS's)"
            (check-k-proof '((0 (pos zero) :axiom (pos-intro-1))) ledger)
            nil)
    ledger))

(defun test-inductive-mutual-even-odd (ledger)
  "Worked example for MUTUAL RECURSION: EVEN and ODD defined TOGETHER as a
2-member GROUP, each citing the OTHER in its own step case:
  EVEN(zero);  ODD(x) -> EVEN(S(x));  EVEN(x) -> ODD(S(x))
via
  (define-inductive-predicates ledger
    '((even 1 (nil nil (zero)) (((odd ?x)) nil ((S ?x))))
      (odd 1 (((even ?x)) nil ((S ?x))))))
Exercises formation of both predicates, introduction (AXIOM for EVEN's
base case, IRULE for both step cases, each threading through the OTHER
predicate's own premise), an attack test, and -- the real point of this
example -- a genuine MUTUAL induction proof: EVEN-IND's own antecedent
chain mentions ODD's motive (in its EVEN-step hyp) and EVEN's motive (in
its ODD-step hyp) alongside EVEN's own base hyp, so citing it correctly
requires supplying trivial motives for BOTH EVEN and ODD at once, and
BOTH (previously proven, mutually shaped) step-lemmas as premises --
proving forall v0 (EVEN(v0) -> v0=v0) is impossible without ODD's own
half of the machinery, even though ODD never appears in the final
conclusion. Mirrors TEST-INDUCTIVE-EVEN's own reflexivity trick (A(x) :=
x=x) so the recursive premises/hypotheses are legitimately available yet
simply unused, isolating the WIRING rather than any arithmetic content."
  (let ((ledger (define-inductive-predicates
                 ledger
                 '((even 1 (nil nil (zero)) (((odd ?x)) nil ((S ?x))))
                   (odd 1 (((even ?x)) nil ((S ?x))))))))
    (expect "(EVEN v0) is a wff" (judgement? 'wff? '(even v0) ledger) t)
    (expect "(ODD v0) is a wff" (judgement? 'wff? '(odd v0) ledger) t)
    (expect "EVEN(zero) via the base-case AXIOM"
            (check-k-proof '((0 (even zero) :axiom (even-intro-1))) ledger) t)
    (let* ((proof2 '((0 (even zero) :axiom (even-intro-1))
                      (1 (odd (S zero)) :ir (odd-intro-1 0))))
           (ledger2 (check-and-extend ledger 'th 'th-odd-1 proof2)))
      (expect "ODD(S(zero)) via ODD's step IRULE, citing EVEN(zero)"
              (check-k-proof proof2 ledger2) t)
      (expect "EVEN(S(S(zero))) via EVEN's step IRULE, citing ODD(S(zero))"
              (check-k-proof '((0 (even zero) :axiom (even-intro-1))
                                (1 (odd (S zero)) :ir (odd-intro-1 0))
                                (2 (even (S (S zero))) :ir (even-intro-2 1)))
                              ledger2)
              t)
      (expect "Attack: EVEN's step IRULE citing EVEN itself instead of ODD -- must reject"
              (check-k-proof '((0 (even zero) :axiom (even-intro-1))
                                (1 (even (S (S zero))) :ir (even-intro-2 0)))
                              ledger2)
              nil))
    ;; The mutual induction proof itself: forall v0 (EVEN(v0) -> v0=v0),
    ;; citing EVEN-IND with BOTH motives A_even(x):=x=x and A_odd(x):=x=x
    ;; supplied at once (extra params, in group order: x_even, A_even,
    ;; x_odd, A_odd), and needing BOTH mutual step-lemmas as premises.
    (let* ((step-lemma-even
             '((0 (.eq (S v1) (S v1)) :axiom (IV.1))
               (1 (.to (.eq (S v1) (S v1)) (.to (.eq v1 v1) (.eq (S v1) (S v1)))) :axiom (II.1))
               (2 (.to (.eq v1 v1) (.eq (S v1) (S v1))) :ir (MP 1 0))
               (3 (.to (.to (.eq v1 v1) (.eq (S v1) (S v1)))
                       (.to (odd v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                  :axiom (II.1))
               (4 (.to (odd v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))) :ir (MP 3 2))))
           (ledger (check-and-extend ledger 'th 'th-mutual-even-step-lemma step-lemma-even))
           (step-lemma-odd
             '((0 (.eq (S v1) (S v1)) :axiom (IV.1))
               (1 (.to (.eq (S v1) (S v1)) (.to (.eq v1 v1) (.eq (S v1) (S v1)))) :axiom (II.1))
               (2 (.to (.eq v1 v1) (.eq (S v1) (S v1))) :ir (MP 1 0))
               (3 (.to (.to (.eq v1 v1) (.eq (S v1) (S v1)))
                       (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                  :axiom (II.1))
               (4 (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))) :ir (MP 3 2))))
           (ledger (check-and-extend ledger 'th 'th-mutual-odd-step-lemma step-lemma-odd)))
      (expect "step-lemma-even (closed tautological derivation) checks"
              (check-k-proof step-lemma-even ledger) t)
      (expect "step-lemma-odd (closed tautological derivation) checks"
              (check-k-proof step-lemma-odd ledger) t)
      (expect "full MUTUAL induction proof of forall v0 (EVEN(v0) -> v0=v0), via the GENERATED EVEN-IND axiom, needing BOTH mutual step-lemmas"
              (check-k-proof
               `((0 (.eq zero zero) :axiom (IV.1))
                 (1 (.to (odd v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))) :th (th-mutual-even-step-lemma))
                 (2 (.forall v1 (.to (odd v1) (.to (.eq v1 v1) (.eq (S v1) (S v1))))) :ir (Gen 1 v1))
                 (3 (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))) :th (th-mutual-odd-step-lemma))
                 (4 (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1))))) :ir (Gen 3 v1))
                 (5 (.to (.eq zero zero)
                         (.to (.forall v1 (.to (odd v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                              (.to (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                                   (.forall v0 (.to (even v0) (.eq v0 v0))))))
                    :axiom (even-ind v0 (.eq v0 v0) v0 (.eq v0 v0)))
                 (6 (.to (.forall v1 (.to (odd v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                         (.to (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                              (.forall v0 (.to (even v0) (.eq v0 v0)))))
                    :ir (MP 5 0))
                 (7 (.to (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                         (.forall v0 (.to (even v0) (.eq v0 v0))))
                    :ir (MP 6 2))
                 (8 (.forall v0 (.to (even v0) (.eq v0 v0))) :ir (MP 7 4)))
               ledger)
              t)
      ledger)))

(defun test-inductive-nary-sumr (ledger)
  "Worked example for N-ARY relations: SUMR(x,y,z), the graph of addition
(\"x+y=z\"), defined as a ternary predicate WITHOUT reference to the +
function symbol at all:
  SUMR(x,zero,x);   SUMR(x,y,z) -> SUMR(x,S(y),S(z))
via
  (define-inductive-predicates ledger
    '((sumr 3 (nil (?x) (?x zero ?x))
             (((sumr ?x ?y ?z)) nil (?x (S ?y) (S ?z))))))
Exercises: an ARITY-3 predicate (RESULT-TERMS a genuine 3-tuple), a base
clause using EXTRA-VARS (?x, which the predicate depends on but which is
not itself required to satisfy anything recursively), a self-recursive
step clause whose single REC-SPEC premise and conclusion both mention
all 3 argument positions at once (exercising @SUBSTN's SIMULTANEOUS,
not one-at-a-time, substitution), and an attack test."
  (let ((ledger (define-inductive-predicates
                 ledger
                 '((sumr 3 (nil (?x) (?x zero ?x))
                          (((sumr ?x ?y ?z)) nil (?x (S ?y) (S ?z))))))))
    (expect "(SUMR v0 v1 v2) is a wff" (judgement? 'wff? '(sumr v0 v1 v2) ledger) t)
    (expect "SUMR(v0,zero,v0) via the base-case AXIOM (x+0=x)"
            (check-k-proof '((0 (sumr v0 zero v0) :axiom (sumr-intro-1))) ledger) t)
    (let* ((proof2 '((0 (sumr v0 zero v0) :axiom (sumr-intro-1))
                      (1 (sumr v0 (S zero) (S v0)) :ir (sumr-intro-2 0))))
           (ledger2 (check-and-extend ledger 'th 'th-sumr-1 proof2)))
      (expect "SUMR(v0,S(zero),S(v0)) via the step-case IRULE (x+1=S(x))"
              (check-k-proof proof2 ledger2) t)
      (expect "SUMR(v0,S(S(zero)),S(S(v0))) chaining the step-case IRULE twice (x+2=S(S(x)))"
              (check-k-proof '((0 (sumr v0 zero v0) :axiom (sumr-intro-1))
                                (1 (sumr v0 (S zero) (S v0)) :ir (sumr-intro-2 0))
                                (2 (sumr v0 (S (S zero)) (S (S v0))) :ir (sumr-intro-2 1)))
                              ledger2)
              t)
      (expect "Attack: SUMR's step IRULE with a wrong (non-successor) output slot -- must reject"
              (check-k-proof '((0 (sumr v0 zero v0) :axiom (sumr-intro-1))
                                (1 (sumr v0 (S zero) v0) :ir (sumr-intro-2 0)))
                              ledger2)
              nil))
    ledger))

(defun test-inductive-consistency-checks (ledger)
  "CHECK-INDUCTIVE-GROUP-WELL-FORMED's own self-tests: every one of its
three refusal categories (name collision, shape, groundedness), each
provoked deliberately and confirmed to signal an ERROR rather than
silently minting something wrong or crashing somewhere deeper, plus a
sanity check that legitimate GROUPs (fresh mutual and n-ary examples,
using names distinct from any already on LEDGER) still succeed."
  (flet ((must-signal-error (thunk)
           (handler-case (progn (funcall thunk) :no-error)
             (error () :caught-error))))
    ;; -- 1: name collision. LEDGER already has EVEN (from TEST-INDUCTIVE-
    ;; EVEN, threaded in by RUN-INDUCTIVE-DEFINITION-SELF-TESTS below) --
    ;; this is the EXACT bug this whole check exists to catch.
    (expect "Attack: redefining EVEN on a ledger that already has it -- must error, not silently double-mint EVEN-INTRO-1/2"
            (must-signal-error
             (lambda () (define-inductive-predicates
                         ledger '((even 1 (nil nil (zero)) (((even ?x)) nil ((S ?x))))))))
            :caught-error)
    ;; -- 2: shape --
    (expect "Attack: a clause's RESULT-TERMS length doesn't match its own predicate's declared ARITY -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates ledger '((cf1 2 (nil nil (zero)) nil)))))
            :caught-error)
    (expect "Attack: a REC-SPEC citing a predicate name that isn't in this GROUP at all -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates
                         ledger '((cf2 1 (nil nil (zero)) (((not-in-group ?x)) nil ((S ?x))))))))
            :caught-error)
    (expect "Attack: a REC-SPEC's variable count not matching its target predicate's own declared ARITY -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates
                         ledger '((cf3 2 (nil nil (zero zero)) (((cf3 ?x)) nil ((S ?x) (S ?x))))))))
            :caught-error)
    (expect "Attack: an EXTRA-VAR that isn't a genuine schema pattern variable -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates ledger '((cf4 1 (nil (not-a-var) (zero)))))))
            :caught-error)
    (expect "Attack: two predicates in the same GROUP sharing one name -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates
                         ledger '((cf5 1 (nil nil (zero))) (cf5 1 (nil nil (zero)))))))
            :caught-error)
    (expect "Attack: a non-positive-integer ARITY -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates ledger '((cf6 0 (nil nil nil))))))
            :caught-error)
    ;; -- 3: groundedness --
    (expect "Attack: pure self-recursion with NO base clause at all -- can never be derived, must error"
            (must-signal-error
             (lambda () (define-inductive-predicates
                         ledger '((cf7 1 (((cf7 ?x)) nil ((S ?x))))))))
            :caught-error)
    (expect "Attack: a 2-predicate mutual cycle with no base case anywhere in it -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates
                         ledger '((cf8 1 (((cf9 ?x)) nil ((S ?x))))
                                  (cf9 1 (((cf8 ?x)) nil ((S ?x))))))))
            :caught-error)
    ;; -- sanity: legitimate groups (fresh names) still go through --
    (expect "Sanity: a legitimate mutual-recursion GROUP with fresh names still succeeds"
            (let ((l (define-inductive-predicates
                      ledger '((cok-even 1 (nil nil (zero)) (((cok-odd ?x)) nil ((S ?x))))
                               (cok-odd 1 (((cok-even ?x)) nil ((S ?x))))))))
              (judgement? 'wff? '(cok-even v0) l))
            t)
    (expect "Sanity: a legitimate n-ary GROUP with a fresh name still succeeds"
            (let ((l (define-inductive-predicates
                      ledger '((cok-sumr 3 (nil (?x) (?x zero ?x))
                                         (((cok-sumr ?x ?y ?z)) nil (?x (S ?y) (S ?z))))))))
              (judgement? 'wff? '(cok-sumr v0 v1 v2) l))
            t)
    ledger))

(defun run-inductive-definition-self-tests ()
  "Section 20: DEFINE-INDUCTIVE-PREDICATE(S) -- formation, introduction
(both AXIOM and IRULE clause shapes), a full induction proof via a
mechanically generated induction axiom, attack tests, and a second,
differently-shaped predicate confirming the generator isn't secretly
EVEN-specific; CHECK-INDUCTIVE-GROUP-WELL-FORMED's own consistency-check
attack tests (name collision, shape, groundedness); plus the two
general-case worked examples: mutual recursion (EVEN/ODD) and an n-ary
relation (SUMR, the graph of addition)."
  (let* ((ledger (fol-kernel :arithmetic t))
         (ledger (test-inductive-even ledger))
         (ledger (test-inductive-generality ledger))
         (ledger (test-inductive-consistency-checks ledger)))
    (declare (ignorable ledger))
    ;; The two general-case (DEFINE-INDUCTIVE-PREDICATES, plural) worked
    ;; examples each get their OWN fresh ledger rather than threading the
    ;; one above: they reuse the predicate name EVEN (the mutual example)
    ;; and would otherwise now be REFUSED outright by
    ;; CHECK-INDUCTIVE-GROUP-WELL-FORMED's own name-collision check,
    ;; since the DIFFERENTLY-SHAPED, purely self-recursive EVEN already
    ;; minted by TEST-INDUCTIVE-EVEN is still on this same ledger (this
    ;; is precisely the bug TEST-INDUCTIVE-CONSISTENCY-CHECKS' first
    ;; attack test above provokes deliberately and confirms is now
    ;; caught, rather than silently accepted the way it was when this
    ;; mutual EVEN/ODD example was first written).
    (test-inductive-mutual-even-odd (fol-kernel :arithmetic t))
    (test-inductive-nary-sumr (fol-kernel :arithmetic t))
    (format t "~%Inductive-definition self-tests complete.~%")))

