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
