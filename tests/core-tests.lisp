;;;; core-tests.lisp -- Section 9: core self tests
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 9. Self tests
;;; ---------------------------------------------------------------------

(defun test-basic-formation (ledger)
  "Basic formation checks; does not grow the ledger."
  (expect "A is a wff" (judgement? 'wff? 'A ledger) t)
  (expect "v0 is a var" (judgement? 'var? 'v0 ledger) t)
  (expect "(.to A B) is a wff" (judgement? 'wff? '(.to A B) ledger) t)
  (expect "(.forall v0 A) is a wff" (judgement? 'wff? '(.forall v0 A) ledger) t)
  (expect "Z is NOT a wff (undeclared)" (judgement? 'wff? 'Z ledger) nil)
  ledger)

(defun test-axiom-and-inference (ledger)
  "Axiom II.1, MP, and Gen (legal and illegal); does not grow the ledger."
  (expect "II.1 instance: (.to A (.to A A))"
          (check-k-proof '((0 (.to A (.to A A)) :axiom (II.1))) ledger) t)
  (expect "MP: A, (.to A B) |- B"
          (check-k-proof '((0 A :hyp nil)
                            (1 (.to A B) :hyp nil)
                            (2 B :ir (MP 1 0)))
                          ledger)
          t)
  (expect "Gen legal: A |- forall v0 A (v0 not free in any open hyp)"
          (check-k-proof '((0 A :hyp nil)
                            (1 (.forall v0 A) :ir (Gen 0 v0)))
                          ledger)
          t)
  (expect "Gen illegal (attack): open hyp (.eq v0 v1) has v0 free -- must reject"
          (check-k-proof '((0 (.eq v0 v1) :hyp nil)
                            (1 (.forall v0 (.eq v0 v1)) :ir (Gen 0 v0)))
                          ledger)
          nil)
  ledger)

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

(defun test-admit-primitive-closed (ledger)
  "ADMIT-PRIMITIVE must be unreachable post-bootstrap."
  (expect "ADMIT-PRIMITIVE is closed post-bootstrap"
          (handler-case (progn (admit-primitive 'atomic-wff-symbol 'SHOULD-FAIL) nil)
            (error () t))
          t)
  ledger)

(defun test-sigma-growth (ledger)
  "Post-bootstrap growth of Sigma: a brand-new symbol is unusable as a
wff until declared, then becomes usable immediately after
DECLARE-ATOMIC-WFF-SYMBOL/DECLARE-VARIABLE-SYMBOL (no bootstrap
reopening, no proof obligation); freshness is enforced both ways,
rejecting a re-declared or reserved-shape name. Returns the ledger
extended with the freshly-declared Q and w0."
  (expect "Q is NOT yet a wff (not declared)" (judgement? 'wff? 'Q ledger) nil)
  (let* ((ledger (declare-atomic-wff-symbol ledger 'Q)))
    (expect "Q IS a wff after DECLARE-ATOMIC-WFF-SYMBOL (post-bootstrap growth)"
            (judgement? 'wff? 'Q ledger) t)
    (expect "(.to Q A) is a wff, combining the freshly-declared Q with A"
            (judgement? 'wff? '(.to Q A) ledger) t)
    (let* ((ledger (declare-variable-symbol ledger 'w0)))
      (expect "w0 is a var after DECLARE-VARIABLE-SYMBOL" (judgement? 'var? 'w0 ledger) t)
      (expect "Gen over the freshly-declared w0: Q |- forall w0 Q"
              (check-k-proof '((0 Q :hyp nil) (1 (.forall w0 Q) :ir (Gen 0 w0))) ledger)
              t)
      (expect "Re-declaring A (already in Sigma) is rejected"
              (handler-case (progn (declare-atomic-wff-symbol ledger 'A) nil) (error () t))
              t)
      (expect "Declaring .forall (reserved binder head) is rejected"
              (handler-case (progn (declare-atomic-wff-symbol ledger '.forall) nil) (error () t))
              t)
      (expect "Declaring ?X (pattern-variable shape) is rejected"
              (handler-case (progn (declare-variable-symbol ledger '?x) nil) (error () t))
              t)
      (expect "Declaring @foo (meta-tag shape) is rejected"
              (handler-case (progn (declare-atomic-wff-symbol ledger '@foo) nil) (error () t))
              t)
      ledger)))

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

(defun test-axiom-iii1 (ledger)
  "Axiom III.1 (universal instantiation): the genuine case (instantiating
x:=v0 with the genuinely different term t:=v2), the degenerate case
(t=x), and a capturing-substitution attack (t:=v1 captured by an inner
(.forall v1 ...) binder), which @subst-ok? exists to block. Does not
grow the ledger."
  (expect "III.1 genuine instantiation: forall v0 (.eq v0 v1) -> (.eq v2 v1) via (III.1 v2)"
          (check-k-proof '((0 (.to (.forall v0 (.eq v0 v1)) (.eq v2 v1)) :axiom (III.1 v2))) ledger)
          t)
  (expect "III.1 degenerate case t=x still works: forall v0 (.eq v0 v1) -> (.eq v0 v1)"
          (check-k-proof '((0 (.to (.forall v0 (.eq v0 v1)) (.eq v0 v1)) :axiom (III.1 v0))) ledger)
          t)
  (expect "Attack: III.1 with a capturing substitution (t:=v1 captured by inner forall v1) -- must reject"
          (check-k-proof '((0 (.to (.forall v0 (.forall v1 (.eq v0 v1)))
                                   (.forall v1 (.eq v1 v1)))
                              :axiom (III.1 v1)))
                          ledger)
          nil)
  ledger)

(defun test-hyp-wellformedness (ledger)
  ":HYP lines must be genuine, declared, well-formed formulas."
  (expect "Attack: an undeclared symbol as a :HYP formula -- must reject"
          (check-k-proof '((0 totally-undeclared-garbage :hyp nil)) ledger)
          nil)
  (expect "Attack: a malformed (non-wff-shaped) :HYP formula -- must reject"
          (check-k-proof '((0 (.bogus-head v0 v1) :hyp nil)) ledger)
          nil)
  (expect "Sanity: a genuine wff as :HYP still works"
          (check-k-proof '((0 (.eq v0 v1) :hyp nil)) ledger)
          t)
  ledger)

(defun test-exists-formation (ledger)
  ".EXISTS formation, free/bound-variable tracking, and Gen's restriction
seeing straight through .exists the same as .forall."
  (expect "(.exists v0 (.eq v0 v1)) is a wff" (judgement? 'wff? '(.exists v0 (.eq v0 v1)) ledger) t)
  (expect "v0 is bound (not free) under .exists v0"
          (not (member 'v0 (free-vars-wff '(.exists v0 (.eq v0 v1)) ledger) :test #'eq))
          t)
  (expect "v1 IS free under .exists v0 (.eq v0 v1)"
          (member 'v1 (free-vars-wff '(.exists v0 (.eq v0 v1)) ledger) :test #'eq)
          t)
  (expect "Gen restriction still applies with .exists in the open hyp -- must reject"
          (check-k-proof '((0 (.exists v1 (.eq v0 v1)) :hyp nil)
                            (1 (.forall v0 (.exists v1 (.eq v0 v1))) :ir (Gen 0 v0)))
                          ledger)
          nil)
  ledger)

(defun test-negation-and-new-axioms (ledger)
  "(.neg A) formation, plus the K/S/contraposition basis (II.1/II.2/II.3):
a II.3 instance genuinely needs .NEG, and -- the whole point of the
switch away from the old K/K/B-composition basis -- A -> A is now
actually derivable via K (II.1) and S (II.2) alone. Does not grow the
ledger."
  (expect "(.neg A) is a wff" (judgement? 'wff? '(.neg A) ledger) t)
  (expect "(.neg (.to A B)) is a wff (.neg nests over any wff)"
          (judgement? 'wff? '(.neg (.to A B)) ledger) t)
  (expect "II.1 (K) instance with A<>B: (.to A (.to B A))"
          (check-k-proof '((0 (.to A (.to B A)) :axiom (II.1))) ledger) t)
  (expect "II.2 (S) instance: (.to A (.to B C)) -> ((.to A B) -> (.to A C))"
          (check-k-proof '((0 (.to (.to A (.to B C)) (.to (.to A B) (.to A C))) :axiom (II.2))) ledger)
          t)
  (expect "II.3 (contraposition) instance, needs .neg: (.to (.neg B) (.neg A)) -> (.to A B)"
          (check-k-proof '((0 (.to (.to (.neg B) (.neg A)) (.to A B)) :axiom (II.3))) ledger)
          t)
  (expect "A -> A is now derivable from K and S alone (impossible under the old K/K/B basis)"
          (check-k-proof
           '((0 (.to (.to A (.to (.to A A) A)) (.to (.to A (.to A A)) (.to A A))) :axiom (II.2))
             (1 (.to A (.to (.to A A) A)) :axiom (II.1))
             (2 (.to (.to A (.to A A)) (.to A A)) :ir (MP 0 1))
             (3 (.to A (.to A A)) :axiom (II.1))
             (4 (.to A A) :ir (MP 2 3)))
           ledger)
          t)
  ledger)

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

(defun test-backtracking-and-self-ref (ledger)
  "Simulates a stale/adversarial ledger, bypassing CHECK-AND-EXTEND's own
uniqueness guard via LEDGER-APPEND directly, with TWO entries named
'dup: an unusable first one and a working second one, confirming
backtracking finds the working one; then confirms a proof trying to
cite ITSELF by name, before that name exists in the ledger at all,
fails by construction (the ENTRIES-UPTO boundary)."
  (let* ((ledger (ledger-append ledger 'th
                                 (list 'dup '((0 A :hyp nil) (1 A :ir (Gen 0 v0))))
                                 (list :derived '((0 A :hyp nil) (1 A :ir (Gen 0 v0))))))
         (ledger (ledger-append ledger 'th
                                 (list 'dup '((0 A :hyp nil) (1 (.forall v0 A) :ir (Gen 0 v0))))
                                 (list :derived '((0 A :hyp nil) (1 (.forall v0 A) :ir (Gen 0 v0)))))))
    (expect "Backtracking: citing 'dup' finds the SECOND, working entry after the first fails"
            (check-k-proof '((X B :hyp nil) (Y (.forall v0 B) :th (dup X))) ledger)
            t)
    (expect "Attack: a theorem's own proof citing itself by name -- must be refused"
            (handler-case
                (progn (check-and-extend ledger 'th 'self-ref
                                          '((0 A :hyp nil) (1 A :th (self-ref 0))))
                       nil)
              (error () t))
            t)
    ledger))

(defun test-failed-line-report (ledger)
  "CHECK-K-PROOF's second value names the first rejected line."
  (multiple-value-bind (ok failed-at)
      (check-k-proof '((0 A :hyp nil)
                       (1 (.to A (.to B A)) :axiom (II.1))
                       (2 (.to B A) :ir (MP 1 0))
                       (3 B :ir (MP 2 0))
                       (4 A :hyp nil))
                     ledger)
    (expect "check-k-proof rejects a proof whose line 3 does not follow" ok nil)
    (expect "... and reports line 3 as the first rejected line" (eql failed-at 3) t))
  (multiple-value-bind (ok failed-at)
      (check-k-proof '((0 A :hyp nil) (1 (.to A (.to B A)) :axiom (II.1))) ledger)
    (expect "a correct proof has no failed line" (and ok (null failed-at)) t))
  ledger)

(defun run-self-tests ()
  "Threads the ledger explicitly through each growth step via a single
flat LET*, calling one named test-phase function per step: each phase
takes the ledger as it stood after the previous phase and returns the
ledger as it should stand afterward (unchanged, for a phase that only
checks; extended, for one that also grows Sigma or the ledger itself)."
  (let* ((ledger (fol-kernel))
         (ledger (test-basic-formation ledger))
         (ledger (test-axiom-and-inference ledger))
         (ledger (test-vacuous-gen-and-bad-ith ledger))
         (ledger (test-admit-primitive-closed ledger))
         (ledger (test-sigma-growth ledger))
         (ledger (test-abbrev-usage ledger))
         (ledger (test-axiom-iii1 ledger))
         (ledger (test-hyp-wellformedness ledger))
         (ledger (test-exists-formation ledger))
         (ledger (test-negation-and-new-axioms ledger))
         (ledger (test-name-uniqueness ledger))
         (ledger (test-deduction-theorem ledger))
         (ledger (test-deduction-theorem-direct ledger))
         ;; TEST-PERSISTENCE-ROUND-TRIP must run on a ledger built
         ;; entirely through the ordinary growth API (CHECK-AND-EXTEND/
         ;; CHECK-AND-EXTEND-ABBREV/DECLARE-*) -- exactly what it is
         ;; checking WRITE-LEDGER-TO-FILE/READ-LEDGER-FROM-FILE can
         ;; faithfully round-trip. It therefore runs BEFORE
         ;; TEST-BACKTRACKING-AND-SELF-REF, which deliberately injects an
         ;; adversarial, never-verified entry via LEDGER-APPEND directly
         ;; (bypassing CHECK-AND-EXTEND's own checks) to exercise
         ;; backtracking -- exactly the kind of stale/unsound entry
         ;; persistence's replay-through-the-real-gates design is
         ;; SUPPOSED to refuse to resurrect, so it must never be asked to
         ;; round-trip that ledger.
         (ledger (test-persistence-round-trip ledger))
         (ledger (test-chained-module-loading ledger))
         (ledger (test-file-reader-safety ledger))
         (ledger (test-backtracking-and-self-ref ledger))
         (ledger (test-failed-line-report ledger)))
    (declare (ignorable ledger))
    (format t "~%Self-tests complete.~%"))
  ;; Section 13's equality/Peano self-tests run against their OWN
  ;; separately-bootstrapped (:ARITHMETIC T) ledger -- see
  ;; RUN-ARITHMETIC-SELF-TESTS' own docstring -- so they are simply
  ;; appended here rather than threaded through the LET* above.
  (run-arithmetic-self-tests))
