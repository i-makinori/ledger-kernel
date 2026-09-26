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
  (let* ((ledger (bootstrap-kernel :arithmetic t))
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
    (test-inductive-mutual-even-odd (bootstrap-kernel :arithmetic t))
    (test-inductive-nary-sumr (bootstrap-kernel :arithmetic t))
    (format t "~%Inductive-definition self-tests complete.~%")))
