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
