;;;; _backup_alpha-conversion.lisp -- BACKUP (not loaded by any ASDF system)
;;;;
;;;; Removed from the kernel on 2026-09-27 to keep src/ small (every line
;;;; of src/ is something a reader has to trust or understand). Nothing in
;;;; hilbert-library/ or zf-library/ used it. Kept here as material for a
;;;; later version.
;;;;
;;;; WHAT IT WAS
;;;;   ALPHA-RENAME-ENTRY / ALPHA-RENAME-FORALL: re-admit a theorem with a
;;;;   bound variable or atomic symbol renamed, by transitively renaming the
;;;;   stored proof (and the proofs it cites) and re-verifying everything. An
;;;;   untrusted tool: every output went through CHECK-AND-EXTEND. Also held
;;;;   RENAME-SYMBOL-EVERYWHERE, which function-definition.lisp now does with
;;;;   CL:SUBST, and FIND-NAMED-ENTRY.
;;;;
;;;; HOW TO RESTORE
;;;;   1. Copy section 'src/alpha-conversion.lisp' to src/ and add
;;;;      (:file "alpha-conversion") to ledger-kernel.asd after "tautology".
;;;;   2. Re-add to the exports in src/package.lisp: FIND-NAMED-ENTRY
;;;;      RENAME-SYMBOL-EVERYWHERE ALPHA-RENAME-ENTRY ALPHA-RENAME-FORALL.
;;;;   3. It matched entry kinds (th ith) and def-abbrev; drop those that no
;;;;      longer exist (see _backup_ith-def-abbrev.lisp).
;;;;   4. Tests: section 'tests/alpha-conversion-tests.lisp', called by
;;;;      (run-alpha-conversion-self-tests); replace BOOTSTRAP-KERNEL with FOL-KERNEL.
;;;;
;;;; The code below is verbatim from commit 3229ca5 (before removal).

;;; =====================================================================
;;; src/alpha-conversion.lisp
;;; =====================================================================

;;;; alpha-conversion.lisp -- Section 16: alpha-conversion
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 16. Alpha-conversion: renaming bound variables, free variables, and
;;;     atomic-wff-symbols throughout an existing ledger entry
;;; ---------------------------------------------------------------------
;;;
;;; Motivation: the kernel deliberately has NO automatic alpha-equivalence.
;;; Formulas are matched purely structurally (EQUAL / MATCH-SCHEMA-ATOMS),
;;; so (.forall v0 A) and (.forall v1 A) are entirely different, unrelated
;;; formulas to CHECK-K-PROOF -- citing THEOREM under a differently-named
;;; bound variable than it was originally proved with simply fails to
;;; match. That is correct, principled behaviour for a structural checker,
;;; not a bug, but it means a person working with the library needs an
;;; explicit, honest way to get "the same theorem, renamed" when they
;;; actually want that.
;;;
;;; Design: never trust the rename itself. Build a candidate raw-proof by
;;; renaming OLD-SYM -> NEW-SYM through every formula, then re-admit it via
;;; the ordinary checked growth functions (CHECK-AND-EXTEND /
;;; CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT / CHECK-AND-EXTEND-ABBREV) exactly
;;; as if it were freshly hand-written. A bad rename -- one that causes
;;; variable capture, or breaks GEN's freshness side-condition partway
;;; through a longer proof -- is simply rejected by the ordinary checker;
;;; nothing new has to be trusted, and the LCF discipline ("always
;;; re-verify") is preserved exactly.
;;;
;;; Two complementary constructs:
;;;
;;;   ALPHA-RENAME-ENTRY   -- general purpose. Renames a symbol (bound
;;;     variable, free variable, OR atomic-wff-symbol -- these are treated
;;;     uniformly, since propositional letters never occupy binder
;;;     position) throughout an EXISTING named entry's stored proof and
;;;     re-admits it under a new name. TRANSITIVE: if the proof cites
;;;     another TH/ITH/TH-DED/DEF-ABBREV entry BY NAME WITH NO ARGUMENTS
;;;     (a "zero-premise" citation, which only checks by exact structural
;;;     match against that entry's own fixed conclusion), and OLD-SYM
;;;     occurs in that dependency's own conclusion too, the dependency is
;;;     recursively alpha-renamed first (memoized, so a dependency shared
;;;     by several lines is only renamed once) and the citation is
;;;     rewritten to point at the renamed copy. A dependency that doesn't
;;;     mention OLD-SYM at all is left cited exactly as before.
;;;
;;;   ALPHA-RENAME-FORALL  -- narrower, axiom-based. Directly constructs
;;;     the general schema-level implication (forall x. A) -> (forall y.
;;;     A[x:=y]) from scratch via III.1 + Gen + MP, discharged through
;;;     CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT, with no pre-existing proof to
;;;     rename. Useful as a standalone renaming LEMMA one can MP against
;;;     any existing (forall x. A) theorem, rather than rebuilding that
;;;     theorem's whole proof under a new name.
;;;
;;; Known limitation: .EXISTS currently has only a formation rule in this
;;; kernel (no existential instantiation/generalization axioms), so there
;;; is no ALPHA-RENAME-EXISTS counterpart to ALPHA-RENAME-FORALL --
;;; ALPHA-RENAME-ENTRY still works on a proof that happens to mention
;;; .EXISTS, since it never needs to prove anything ABOUT .EXISTS itself,
;;; only re-verify the (unchanged) proof that produced it.

(defun rename-symbol-everywhere (old new tree)
  "Literal, unconditional symbol rename through an arbitrary S-expression:
every occurrence of OLD becomes NEW, INCLUDING when OLD sits in binder
head position (e.g. the V0 in (.forall v0 ...)) and including occurrences
below that binder. Deliberately NOT the same operation as SUBSTITUTE-WFF:
substitution must skip under a binder that re-binds the same name (that
name there refers to a different, locally-bound variable, and capture
must be avoided), whereas alpha-conversion renames one specific
bound/free variable or atomic-wff-symbol EVERYWHERE it occurs, including
the binder itself, uniformly and unconditionally through the whole
formula."
  (cond ((eq tree old) new)
        ((consp tree) (cons (rename-symbol-everywhere old new (car tree))
                             (rename-symbol-everywhere old new (cdr tree))))
        (t tree)))

(defun find-named-entry (ledger name)
  "Most recent (highest-K) ITH/TH/DEF-ABBREV/TH-DED entry citable under
NAME, or NIL. Uses the same by-name index (LEDGER-BY-DERIVED-NAME) and
backtracking-friendly TREAP-VALUES-BELOW lookup that citation checking and
DERIVED-RULE-NAME-TAKEN-P already rely on internally."
  (let ((candidates (treap-values-below (alist-get (ledger-by-derived-name ledger) name) (ledger-bound ledger))))
    (car (sort (copy-list candidates) #'> :key #'entry-k))))

(defun entry-public-formula (e)
  "The single formula an entry is 'known by' when cited with no extra
arguments: a TH/ITH's stored conclusion, a TH-DED's (hyp -> conclusion),
or a DEF-ABBREV's definiens. NIL for entries with no such notion (e.g.
AXIOM, IRULE)."
  (case (entry-kind e)
    ((th ith)
     (destructuring-bind (name raw-proof) (entry-payload e)
       (declare (ignore name))
       (proof-conclusion raw-proof)))
    (th-ded
     (destructuring-bind (name hyp-formula raw-proof) (entry-payload e)
       (declare (ignore name))
       (list '.to hyp-formula (proof-conclusion raw-proof))))
    (def-abbrev
     (destructuring-bind (name raw-proof) (entry-payload e)
       (declare (ignore name))
       (proof-conclusion raw-proof)))
    (t nil)))

(defun alpha-dep-name (old-name old-sym new-sym)
  "Deterministic derived name for an auto-renamed transitive dependency,
so re-running the same rename twice reuses the same auxiliary entry
rather than growing the ledger unboundedly."
  (intern (format nil "~A|~A->~A" old-name old-sym new-sym) (symbol-package old-name)))

(defun rename-raw-proof-transitively (ledger raw-proof old-sym new-sym memo log)
  "Renames OLD-SYM -> NEW-SYM through every formula of RAW-PROOF. For any
:TH/:ITH/:TH-DED/:DEF-ABBREV citation whose cited entry's PUBLIC formula
contains OLD-SYM, recursively alpha-renames that dependency first (via
ALPHA-RENAME-ENTRY-1, memoized in MEMO) and rewrites the citation to the
renamed name; a dependency not mentioning OLD-SYM is cited unchanged.
:AXIOM/:IR citation arguments (schema instantiation formulas / MP-or-Gen
line numbers and variables) are renamed directly since they are never
entry names. Returns (values possibly-extended-ledger renamed-raw-proof)."
  (let ((ledger ledger))
    (let ((new-lines
            (mapcar
             (lambda (line)
               (destructuring-bind (num formula role by) line
                 (list num
                       (rename-symbol-everywhere old-sym new-sym formula)
                       role
                       (case role
                         ((:axiom :ir)
                          (cons (car by) (mapcar (lambda (x) (rename-symbol-everywhere old-sym new-sym x)) (cdr by))))
                         ((:th :ith :th-ded :def-abbrev)
                          (if (null by)
                              by
                              (multiple-value-bind (ledger2 final-name)
                                  (alpha-rename-entry-1 ledger (car by) old-sym new-sym memo log)
                                (setf ledger ledger2)
                                (cons final-name (cdr by)))))
                         (t by)))))
             raw-proof)))
      (values ledger new-lines))))

(defun alpha-rename-entry-1 (ledger old-name old-sym new-sym memo log)
  "Internal worker for transitive dependency renaming, called by
RENAME-RAW-PROOF-TRANSITIVELY. Returns (values new-ledger name-to-cite).
If OLD-NAME's entry doesn't mention OLD-SYM (or isn't a
TH/ITH/TH-DED/DEF-ABBREV at all -- e.g. names an :AXIOM or :IRULE, which
are cited differently), it's returned unchanged. Memoized on OLD-NAME so a
dependency shared by several lines or entries is renamed only once."
  (multiple-value-bind (cached found) (gethash old-name memo)
    (when found (return-from alpha-rename-entry-1 (values ledger cached))))
  (let ((e (find-named-entry ledger old-name)))
    (unless e
      (error "ALPHA-RENAME-ENTRY: no ITH/TH/DEF-ABBREV/TH-DED entry named ~S." old-name))
    (unless (and (member (entry-kind e) '(th ith th-ded def-abbrev))
                 (symbol-occurs-p old-sym (entry-public-formula e)))
      (setf (gethash old-name memo) old-name)
      (return-from alpha-rename-entry-1 (values ledger old-name)))
    (let ((new-name (alpha-dep-name old-name old-sym new-sym)))
      (when (find-named-entry ledger new-name)
        (setf (gethash old-name memo) new-name)
        (return-from alpha-rename-entry-1 (values ledger new-name)))
      ;; Bind before recursing: harmless even in the (currently impossible,
      ;; ledger is append-only/acyclic) case of a citation cycle.
      (setf (gethash old-name memo) new-name)
      (case (entry-kind e)
        ((th ith)
         (destructuring-bind (name raw-proof) (entry-payload e)
           (declare (ignore name))
           (multiple-value-bind (ledger2 renamed-proof)
               (rename-raw-proof-transitively ledger raw-proof old-sym new-sym memo log)
             (values (check-and-extend ledger2 (entry-kind e) new-name renamed-proof log) new-name))))
        (th-ded
         (destructuring-bind (name hyp-formula raw-proof) (entry-payload e)
           (declare (ignore name))
           (multiple-value-bind (ledger2 renamed-proof)
               (rename-raw-proof-transitively ledger raw-proof old-sym new-sym memo log)
             (values (check-and-extend-by-deduction-direct
                      ledger2 new-name (rename-symbol-everywhere old-sym new-sym hyp-formula)
                      renamed-proof log)
                     new-name))))
        (def-abbrev
         (destructuring-bind (name raw-proof) (entry-payload e)
           (declare (ignore name))
           (multiple-value-bind (ledger2 renamed-proof)
               (rename-raw-proof-transitively ledger raw-proof old-sym new-sym memo log)
             (values (check-and-extend-abbrev ledger2 new-name (proof-conclusion renamed-proof) renamed-proof log)
                     new-name))))))))

(defun symbol-occurs-p (sym tree)
  "T if SYM occurs anywhere in TREE (an arbitrary S-expression)."
  (cond ((eq tree sym) t)
        ((consp tree) (or (symbol-occurs-p sym (car tree)) (symbol-occurs-p sym (cdr tree))))
        (t nil)))

(defun alpha-rename-entry (ledger old-name new-name old-sym new-sym &optional (log (silent-log)))
  "Public entry point. Renames OLD-SYM -> NEW-SYM (a bound variable, a
free variable, or an atomic-wff-symbol -- all handled uniformly by
RENAME-SYMBOL-EVERYWHERE) throughout OLD-NAME's stored proof and
re-admits the result under NEW-NAME, transitively renaming any dependency
that needs it (see section header). Fully re-verified via the ordinary
checked growth functions; a rename that causes capture or an invalid
proof step is simply rejected by the checker, exactly like any other
malformed submission."
  (let ((e (find-named-entry ledger old-name)))
    (unless e
      (error "ALPHA-RENAME-ENTRY: no ITH/TH/DEF-ABBREV/TH-DED entry named ~S." old-name))
    (unless (member (entry-kind e) '(th ith th-ded def-abbrev))
      (error "ALPHA-RENAME-ENTRY: ~S names a ~S entry, not ITH/TH/DEF-ABBREV/TH-DED." old-name (entry-kind e)))
    (let ((memo (make-hash-table :test #'eq)))
      (case (entry-kind e)
        ((th ith)
         (destructuring-bind (name raw-proof) (entry-payload e)
           (declare (ignore name))
           (multiple-value-bind (ledger2 renamed-proof)
               (rename-raw-proof-transitively ledger raw-proof old-sym new-sym memo log)
             (check-and-extend ledger2 (entry-kind e) new-name renamed-proof log))))
        (th-ded
         (destructuring-bind (name hyp-formula raw-proof) (entry-payload e)
           (declare (ignore name))
           (multiple-value-bind (ledger2 renamed-proof)
               (rename-raw-proof-transitively ledger raw-proof old-sym new-sym memo log)
             (check-and-extend-by-deduction-direct
              ledger2 new-name (rename-symbol-everywhere old-sym new-sym hyp-formula)
              renamed-proof log))))
        (def-abbrev
         (destructuring-bind (name raw-proof) (entry-payload e)
           (declare (ignore name))
           (multiple-value-bind (ledger2 renamed-proof)
               (rename-raw-proof-transitively ledger raw-proof old-sym new-sym memo log)
             (check-and-extend-abbrev ledger2 new-name (proof-conclusion renamed-proof) renamed-proof log))))))))

(defun alpha-rename-forall (ledger x y a name &optional (log (silent-log)))
  "Standalone, axiom-based construction of the general schema-level
theorem (forall x. A) -> (forall y. A[x:=y]), built directly from III.1 +
Gen + MP via the deduction-direct discharge mechanism, with no
pre-existing proof to rename. (Y must be fresh for A per III.1's own side
condition and Gen's freshness condition against the open hypothesis
(forall x. A); the checker rejects the construction outright if not --
e.g. if Y already occurs free in A, renaming X to Y would capture it.)"
  (check-and-extend-by-deduction-direct
   ledger name (list '.forall x a)
   `((0 (.forall ,x ,a) :hyp nil)
     (1 (.to (.forall ,x ,a) ,(substitute-wff x y a)) :axiom (III.1 ,y))
     (2 ,(substitute-wff x y a) :ir (MP 1 0))
     (3 (.forall ,y ,(substitute-wff x y a)) :ir (Gen 2 ,y)))
   log))

;;; =====================================================================
;;; tests/alpha-conversion-tests.lisp
;;; =====================================================================

;;;; alpha-conversion-tests.lisp -- Section 16: alpha-conversion tests
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun test-alpha-conversion (ledger)
  "Exercises ALPHA-RENAME-ENTRY (on TH, TH-DED-derived TH, and DEF-ABBREV
entries, including the transitive-dependency case) and ALPHA-RENAME-FORALL,
plus both intended failure modes (name collision, capture attempt). LEDGER
must already carry Peano arithmetic and TH-ZERO-PLUS-IDENTITY (Section 13)."
  ;; The concrete motivating example: TH-ZERO-PLUS-IDENTITY was proved with
  ;; bound variable V0; citing it under V1 must fail (no auto-alpha), but
  ;; ALPHA-RENAME-ENTRY can mechanically produce the V1 version, re-verified
  ;; from scratch -- including transitively renaming TH-ZERO-PLUS-STEP,
  ;; which TH-ZERO-PLUS-IDENTITY cites by name with no arguments and whose
  ;; own induction hypothesis also mentions V0.
  (expect "citing TH-ZERO-PLUS-IDENTITY under the wrong bound-variable name (V1) fails, as expected (no auto-alpha)"
          (check-k-proof '((0 (.forall v1 (.eq (+ zero v1) v1)) :th (th-zero-plus-identity))) ledger)
          nil)
  (let ((ledger (alpha-rename-entry ledger 'th-zero-plus-identity 'th-zero-plus-identity-v1 'v0 'v1)))
    (expect "ALPHA-RENAME-ENTRY: renamed TH-ZERO-PLUS-IDENTITY-V1 is citable, and now matches under V1"
            (check-k-proof '((0 (.forall v1 (.eq (+ zero v1) v1)) :th (th-zero-plus-identity-v1))) ledger)
            t)
    (expect "...while the original TH-ZERO-PLUS-IDENTITY (bound V0) is untouched and still citable"
            (check-k-proof '((0 (.forall v0 (.eq (+ zero v0) v0)) :th (th-zero-plus-identity))) ledger)
            t)
    ;; def-abbrev path, with the same transitive V0 dependency.
    (let* ((ledger (check-and-extend-abbrev
                    ledger 'my-zero-identity-abbrev '(.forall v0 (.eq (+ zero v0) v0))
                    '((0 (.forall v0 (.eq (+ zero v0) v0)) :th (th-zero-plus-identity)))))
           (ledger (alpha-rename-entry ledger 'my-zero-identity-abbrev 'my-zero-identity-abbrev-v1 'v0 'v1)))
      (expect "ALPHA-RENAME-ENTRY on a DEF-ABBREV entry: renamed abbrev is citable under V1"
              (check-k-proof '((0 (.forall v1 (.eq (+ zero v1) v1)) :def-abbrev (my-zero-identity-abbrev-v1))) ledger)
              t)
      ;; atomic-wff-symbol renaming (propositional letter, not a variable).
      (let* ((ledger (check-and-extend ledger 'th 'th-tiny-k '((0 (.to A (.to B A)) :axiom (II.1)))))
             (ledger (alpha-rename-entry ledger 'th-tiny-k 'th-tiny-k-g 'a 'g)))
        (expect "ALPHA-RENAME-ENTRY on an atomic-wff-symbol (A -> G, a propositional letter, not a variable)"
                (check-k-proof '((0 (.to G (.to B G)) :th (th-tiny-k-g))) ledger)
                t)
        ;; ALPHA-RENAME-FORALL: a standalone renaming lemma, usable via MP
        ;; against any (forall v0 ...) theorem, without rebuilding its proof.
        (let ((ledger (alpha-rename-forall ledger 'v0 'v1 '(.eq (+ zero v0) v0) 'th-forall-rename-v0-v1)))
          (expect "ALPHA-RENAME-FORALL builds (forall v0 A)->(forall v1 A[v0:=v1]) as a real, re-citable theorem"
                  (check-k-proof
                   '((0 (.to (.forall v0 (.eq (+ zero v0) v0)) (.forall v1 (.eq (+ zero v1) v1)))
                        :th (th-forall-rename-v0-v1)))
                   ledger)
                  t)
          (expect "...and it actually composes via MP against TH-ZERO-PLUS-IDENTITY to reprove the V1 form"
                  (check-k-proof
                   '((0 (.forall v0 (.eq (+ zero v0) v0)) :th (th-zero-plus-identity))
                     (1 (.to (.forall v0 (.eq (+ zero v0) v0)) (.forall v1 (.eq (+ zero v1) v1)))
                        :th (th-forall-rename-v0-v1))
                     (2 (.forall v1 (.eq (+ zero v1) v1)) :ir (MP 1 0)))
                   ledger)
                  t)
          ;; Attack 1: NEW-NAME collides with an already-used name -- must
          ;; be refused by the ordinary CHECK-AND-EXTEND name-collision
          ;; guard, not silently overwrite or shadow the existing entry.
          (expect "attack: ALPHA-RENAME-ENTRY refuses a NEW-NAME that collides with an existing entry"
                  (handler-case (progn (alpha-rename-entry ledger 'th-zero-plus-identity 'th-identity 'v0 'v1) :admitted)
                    (error () :refused))
                  :refused)
          ;; Attack 2: ALPHA-RENAME-FORALL where Y is not actually fresh
          ;; for A (Y already occurs free in A) -- renaming X to Y would
          ;; capture it, so III.1's own side condition must reject this.
          (expect "attack: ALPHA-RENAME-FORALL refuses a capturing rename (Y already free in A)"
                  (handler-case
                      (progn (alpha-rename-forall ledger 'v0 'v1 '(.exists v1 (.eq v0 v1)) 'th-bad-capture) :admitted)
                    (error () :refused))
                  :refused)
          ledger)))))

(defun run-alpha-conversion-self-tests ()
  "As RUN-SELF-TESTS, but against a BOOTSTRAP-KERNEL :ARITHMETIC T ledger
carrying Peano arithmetic and TH-ZERO-PLUS-IDENTITY -- Section 16."
  (let* ((ledger (fol-kernel :arithmetic t))
         (ledger (test-equality-axioms ledger))
         (ledger (test-peano-axioms ledger))
         (ledger (test-peano-induction-proof ledger))
         (ledger (test-alpha-conversion ledger)))
    (declare (ignorable ledger))
    (format t "~%Alpha-conversion self-tests complete.~%")))

