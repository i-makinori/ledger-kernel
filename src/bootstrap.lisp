;;;; bootstrap.lisp -- Sections 7-8: bootstrap of the primitive Hilbert system
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 7. Bootstrap: populate the primitive Hilbert system
;;; ---------------------------------------------------------------------
;;;
;;; wff?/var?/term? formation, MP, Gen (with its generalization
;;; restriction), and axioms II.1-III.2. Declared atomic symbols/variables
;;; are also admitted as primitive ledger entries, so Sigma is a real
;;; projection from day one rather than a hardcoded list.
;;;
;;; :ATOMIC-SYMBOLS/:VARIABLES below are only the SEED vocabulary -- how
;;; much of Sigma exists the moment the kernel is born. They are NOT the
;;; only way Sigma can ever grow: DECLARE-ATOMIC-WFF-SYMBOL and
;;; DECLARE-VARIABLE-SYMBOL (section 2) remain usable for the whole life
;;; of the kernel, letting new symbols be added one at a time, on demand,
;;; long after bootstrap has closed.

(defun bootstrap-kernel (&key (atomic-symbols '(A B C D E F G H)) (variables '(v0 v1 v2 v3 v4 v5))
                               (arithmetic nil))
  "Returns the freshly-built ledger: a pure function whose result IS the
kernel -- the caller (RUN-SELF-TESTS, or anyone else) captures it and
threads it onward into every later check or growth call.

ARITHMETIC, when true, additionally admits the Peano vocabulary (ZERO, S,
+, *) and axioms (P1-P7, Section 7.5) on top of the always-present
equality axioms (IV.1-IV.2). Default NIL, so every existing caller (every
self-test, and both HILBERT-LIBRARY modules) gets EXACTLY the same
kernel as before this parameter existed."
  (labels ((admit (ledger kind payload)
             "The ONLY place in the whole file that can create a
:PRIMITIVE-origin entry -- a LABELS binding local to BOOTSTRAP-KERNEL's
own call, so nothing outside this function's own body can ever reach it.
Returns the new ledger, like LEDGER-APPEND."
             (ledger-append ledger kind payload (list :primitive)))
           (admit-each (ledger kind syms)
             (if (null syms)
                 ledger
                 (admit-each (admit ledger kind (car syms)) kind (cdr syms))))
           (bootstrap-formation-rules (ledger)
             "TERM?/WFF? formation rules: variables are terms, and the
connectives/binders/relation that build WFFs out of smaller WFFs, terms
and variables.

NOTE: there is deliberately no generic \"(wff? ?A)\"/\"(var? ?x)\"
primitive rule with no side condition here -- such a rule would match
ANY single argument, so it would accept even an undeclared symbol as a
wff/var. Bare declared symbols are instead recognized directly against
Sigma via ATOMIC-WFF-SYMBOL-P/VARIABLE-P in the JUDGEMENT-BIND override
in section 8, below."
             (let* ((ledger (admit ledger 'term? (list 'var-term '((var? ?x)) '(term? ?x))))
                    ;; (.iota x A): "the x such that A" -- a TERM-producing
                    ;; binder (see Section 19). Its formation rule is
                    ;; exactly as inert on its own as .EXISTS's own
                    ;; formation rule below was before III.3/IOTA existed:
                    ;; a bare (var? ?x)(wff? ?A) => term? (.iota ?x ?A)
                    ;; rule, with all of the actual meaning supplied by
                    ;; IOTA (Section 7's BOOTSTRAP-INFERENCE-RULES) and by
                    ;; BINDER-HEADS already listing .IOTA so free-variable/
                    ;; substitution/capture-avoidance machinery treats it
                    ;; correctly wherever it occurs, including nested
                    ;; inside an ordinary WFF as an argument term.
                    (ledger (admit ledger 'term? (list 'iota-term '((var? ?x) (wff? ?A)) '(term? (.iota ?x ?A)))))
                    (ledger (admit ledger 'wff? (list 'wff_to? '((wff? ?A) (wff? ?B)) '(wff? (.to ?A ?B)))))
                    (ledger (admit ledger 'wff? (list 'wff_neg? '((wff? ?A)) '(wff? (.neg ?A)))))
                    (ledger (admit ledger 'wff? (list 'wff_forall? '((var? ?x) (wff? ?A)) '(wff? (.forall ?x ?A)))))
                    ;; .EXISTS's SYNTAX: (var? x)(wff? A) => wff? (.exists x A).
                    ;; *BINDER-HEADS* already lists .EXISTS, so FREE-VARS-WFF/
                    ;; SUBSTITUTE-WFF/COUNT-BOUND-OCCURRENCES already treat it as a
                    ;; genuine binder. Unlike when this comment was first written,
                    ;; .EXISTS now DOES have a piece of real proof theory on top of
                    ;; this formation rule -- III.3, existential generalization
                    ;; (Section 7's BOOTSTRAP-AXIOMS) -- though still no full
                    ;; existential ELIMINATION/instantiation rule; see Section 19's
                    ;; own header for exactly what that still leaves out.
                    (ledger (admit ledger 'wff? (list 'wff_exists? '((var? ?x) (wff? ?A)) '(wff? (.exists ?x ?A)))))
                    ;; A minimal atomic relation on terms, so that a bare variable can
                    ;; legitimately occur FREE inside a genuine well-formed formula
                    ;; (without some relation symbol, a variable standing alone is a
                    ;; TERM, not a WFF).
                    (ledger (admit ledger 'wff? (list 'wff_eq? '((term? ?s) (term? ?t)) '(wff? (.eq ?s ?t))))))
               ledger))
           (bootstrap-inference-rules (ledger)
             "MP and Gen (WITH the generalization restriction), plus IOTA
(definite-description elimination -- Section 19) and EXISTS-ELIM
(genuine existential elimination -- Section 21).
FORM shape: (PREMISE-PATTERNS EXTRA-PARAM-PATTERNS :=> CONCLUSION-PATTERN)."
             (let* ((ledger (admit ledger 'irule (list 'MP '((wff? ?A) (wff? ?B))
                                                        '(((.to ?A ?B) ?A) nil :=> ?B))))
                    (ledger (admit ledger 'irule (list 'Gen '((var? ?x) (wff? ?A) (@not-free-in-dependencies? ?x))
                                                        '((?A) (?x) :=> (.forall ?x ?A)))))
                    ;; IOTA: from (a) EXISTENCE, (.exists ?x ?A), and (b)
                    ;; UNIQUENESS, (.forall ?y (.forall ?z (.to (@subst ?x
                    ;; ?y ?A) (.to (@subst ?x ?z ?A) (.eq ?y ?z))))) --
                    ;; "any two things satisfying A are equal" -- BOTH
                    ;; cited as already-proven premise lines (however they
                    ;; were established; IOTA does not care), conclude
                    ;; A[(.iota ?x ?A)/?x]: the iota-term itself satisfies
                    ;; A. Note this is an IRULE, not an AXIOM, precisely
                    ;; BECAUSE it needs premises cited from the current
                    ;; proof (the way MP/Gen do) rather than holding as a
                    ;; bare schema on its own -- existence and uniqueness
                    ;; are facts about a PARTICULAR A, not universal
                    ;; truths. ?Y and ?Z are bound purely from matching the
                    ;; UNIQUENESS premise's own outer .FORALL structure
                    ;; (MATCH-TEMPLATE processes a pattern's CAR before its
                    ;; CDR, left to right, exactly as III.1's (@subst ?x ?t
                    ;; ?A) conclusion pattern already relies on ?x/?A being
                    ;; bound before it is reached) -- ?X and ?A are already
                    ;; ground by the time the UNIQUENESS premise is
                    ;; matched, since EXISTENCE is listed first and
                    ;; MATCH-SCHEMA-HYPS-AGAINST-CITED threads bindings
                    ;; across premises strictly in the order given.
                    (ledger (admit ledger 'irule
                                   (list 'IOTA
                                         '((var? ?x) (wff? ?A) (@subst-ok? ?x (.iota ?x ?A) ?A))
                                         '(((.exists ?x ?A)
                                            (.forall ?y (.forall ?z (.to (@subst ?x ?y ?A)
                                                                         (.to (@subst ?x ?z ?A) (.eq ?y ?z))))))
                                           nil :=>
                                           (@subst ?x (.iota ?x ?A) ?A)))))
                    ;; EXISTS-ELIM (Section 21): the genuine existential
                    ;; ELIMINATION rule III.3 always lacked. From (a)
                    ;; EXISTENCE, (.exists ?x ?A), and (b) a proof that
                    ;; some already-established formula ?Ac (which the
                    ;; side conditions verify really is A with x
                    ;; instantiated to a FRESH witness variable ?w)
                    ;; implies C -- (.to ?Ac ?C) -- conclude C outright,
                    ;; discharging the witness. This is the standard
                    ;; Hilbert-style "existential instantiation" rule
                    ;; (Mendelson's Rule C, or natural deduction's
                    ;; exists-elim flattened into one step since the
                    ;; DEDUCTION THEOREM already lets a caller build
                    ;; "A[w/x] -> C" from a genuine sub-proof assuming
                    ;; A[w/x] -- see CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT).
                    ;; (Named ?w, not ?c: a pattern variable ?c and ?C are
                    ;; THE SAME SYMBOL once read -- Common Lisp's default
                    ;; reader case-normalizes to upper case -- so ?w keeps
                    ;; the witness variable and the conclusion schema
                    ;; variable properly distinct.)
                    ;;
                    ;; UNLIKE IOTA/III.1's own embedded (@subst ...)
                    ;; conclusion patterns, this rule cannot write
                    ;; (@subst ?x ?w ?A) directly inside its SECOND PREMISE
                    ;; pattern: PREMISE-PATTERNS are all matched BEFORE
                    ;; EXTRA-PARAM-PATTERNS (see TRY-IR-ENTRY), so ?w --
                    ;; supplied only as an extra citation argument, the
                    ;; way GEN's own ?x is -- is not yet bound at the
                    ;; point the second premise would need to evaluate
                    ;; @subst. The fix: match ?Ac PURELY STRUCTURALLY
                    ;; (no embedded meta-constructor at all) against
                    ;; whatever concrete antecedent the citing proof
                    ;; supplies, then verify AS A SIDE CONDITION -- once
                    ;; ?x/?A/?w are all ground -- that ?Ac genuinely does
                    ;; equal A[w/x], via the new @substitutes? meta-
                    ;; predicate (a boolean CHECK, unlike @subst itself,
                    ;; which is a meta-CONSTRUCTOR evaluated during
                    ;; matching).
                    ;;
                    ;; Freshness (?w must be a genuinely NEW name, standing
                    ;; for "whichever thing A holds of", never confused
                    ;; with anything already in play) is exactly Gen's own
                    ;; @not-free-in-dependencies? restriction, PLUS two
                    ;; more: ?w must not leak into the CONCLUSION ?C (or
                    ;; the "witness" would illegitimately survive past the
                    ;; elimination step) and must not already occur free
                    ;; in ?A itself (or "instantiating x to w" could
                    ;; collide with an unrelated, already-meaningful
                    ;; occurrence of w inside A). @subst-ok? additionally
                    ;; guards the substitution itself against capture by
                    ;; some OTHER binder inside A, exactly as everywhere
                    ;; else @subst is used.
                    (ledger (admit ledger 'irule
                                   (list 'EXISTS-ELIM
                                         '((var? ?x) (var? ?w) (wff? ?A) (wff? ?Ac) (wff? ?C)
                                           (@substitutes? ?x ?w ?A ?Ac)
                                           (@subst-ok? ?x ?w ?A)
                                           (@not-free-in? ?w ?A)
                                           (@not-free-in? ?w ?C)
                                           (@not-free-in-dependencies? ?w))
                                         '(((.exists ?x ?A) (.to ?Ac ?C))
                                           (?w) :=>
                                           ?C)))))
               ledger))
           (bootstrap-axioms (ledger)
             "Axioms II.1-II.3 (propositional) and III.1-III.2 (predicate).
FORM shape: (EXTRA-PARAM-PATTERNS CONCLUSION-PATTERN) -- see
CHECK-K-AXIOM-LINE. Only III.1 actually takes an extra parameter (the
substituted term); the rest take none.

II.1-II.3 are the standard K/S/contraposition basis for classical
implicational logic (this replaces an earlier K/K/B-composition basis
that, as a combinator system, could not even derive the identity schema
A -> A: {B, K} alone are not combinatorially complete -- neither is
{B, C, K} (BCK logic is contraction-free and still lacks the sharing
S provides), so the discharge/MP cases of any Deduction-Theorem-style
meta-rule were unimplementable underneath it. II.2 (S) restores that:
     II.1  A -> (B -> A)                                     [K]
     II.2  (A -> (B -> C)) -> ((A -> B) -> (A -> C))          [S]
     II.3  (.neg B -> .neg A) -> (A -> B)                     [contraposition]
II.3 is the first axiom to mention .NEG; see BOOTSTRAP-FORMATION-RULES
above for its (otherwise inert) formation rule.

{II.1, II.2, II.3} is exactly Lukasiewicz's classical 3-axiom basis
(rename A:=q, B:=p in II.3 and it reads (.neg p -> .neg q) -> (q -> p),
his A3 verbatim), which he proved POST-COMPLETE for classical
propositional logic: every classical tautology -- including case-split,
double-negation elimination, and Peirce's law -- IS already a theorem
of {II.1,II.2,II.3,MP} alone, with no further axiom needed in
principle. In that sense II.4 below is REDUNDANT, unlike IV.3/IV.4 or
P8-P10 above/below, which were proven IMPOSSIBLE to derive from what
preceded them. The distinction matters and is recorded here rather than
glossed over: II.4 could be derived, but its shortest known derivations
from {II.1,II.2,II.3} alone run to dozens of raw MP/axiom steps (this
is a well-documented curiosity of Lukasiewicz-style bases -- automated
provers have spent real effort just finding short proofs of facts like
not-not-p -> p from them), and a bounded forward-chaining search tried
here during development did not converge on one in practical time. Ad-
mitting it directly, clearly labelled as classically-redundant-but-not-
reconstructed, is the honest and practical choice: it keeps kernel
proofs usable for actual work (Kalmar's completeness construction,
below) without either pretending the shortcut doesn't exist or forcing
a many-dozen-line combinator proof into every citing theorem's history.
     II.4  (A -> C) -> ((.neg A -> C) -> C)                   [case-split]"
             (let* ((ledger (admit ledger 'axiom (list 'II.1 '((wff? ?A) (wff? ?B))
                                                        '(nil (.to ?A (.to ?B ?A))))))
                    (ledger (admit ledger 'axiom (list 'II.2 '((wff? ?A) (wff? ?B) (wff? ?C))
                                                        '(nil (.to (.to ?A (.to ?B ?C)) (.to (.to ?A ?B) (.to ?A ?C)))))))
                    (ledger (admit ledger 'axiom (list 'II.3 '((wff? ?A) (wff? ?B))
                                                        '(nil (.to (.to (.neg ?B) (.neg ?A)) (.to ?A ?B))))))
                    (ledger (admit ledger 'axiom (list 'II.4 '((wff? ?A) (wff? ?C))
                                                        '(nil (.to (.to ?A ?C) (.to (.to (.neg ?A) ?C) ?C))))))
                    ;; III.1: universal instantiation, forall x A -> A[t/x], for an
                    ;; ARBITRARY term t supplied as the citing proof's extra argument
                    ;; (e.g. (III.1 v2)). (@subst ?x ?t ?A) is evaluated by
                    ;; MATCH-TEMPLATE once ?x and ?A are bound (from matching
                    ;; (.forall ?x ?A) against the antecedent, which happens first,
                    ;; left-to-right) and ?t is bound (seeded from EXTRA-ARGS before
                    ;; CONCLUSION-PATTERN is even matched) -- never by unification.
                    ;; @subst-ok? still guards against capturing t's free variables
                    ;; under a binder inside A.
                    (ledger (admit ledger 'axiom (list 'III.1 '((var? ?x) (wff? ?A) (term? ?t) (@subst-ok? ?x ?t ?A))
                                                        '((?t) (.to (.forall ?x ?A) (@subst ?x ?t ?A))))))
                    (ledger (admit ledger 'axiom (list 'III.2 '((var? ?x) (wff? ?A) (wff? ?B) (@not-free-in? ?x ?A))
                                                        '(nil (.to (.forall ?x (.to ?A ?B)) (.to ?A (.forall ?x ?B)))))))
                    ;; III.3: existential generalization, A[t/x] -> exists x. A --
                    ;; the direct dual of III.1 (universal INSTANTIATION), but for
                    ;; introducing .EXISTS rather than eliminating .FORALL, and
                    ;; UNCONDITIONAL (no Gen-style freshness restriction: unlike
                    ;; universally generalizing an arbitrary A into forall x. A,
                    ;; concluding "something satisfies A" from "THIS PARTICULAR
                    ;; witness t satisfies A" is always safe). Before this axiom,
                    ;; .EXISTS had a formation rule but no way to ever actually PROVE
                    ;; a .EXISTS-headed formula at all -- see BOOTSTRAP-FORMATION-
                    ;; RULES' updated commentary. Still not a full existential
                    ;; ELIMINATION/instantiation rule (Section 19's own header notes
                    ;; exactly what that gap still leaves out) -- but it, together
                    ;; with IOTA below, is exactly what makes IOTA practically usable:
                    ;; IOTA's EXISTENCE premise needs to come from SOMEWHERE, and this
                    ;; is that somewhere.
                    ;;
                    ;; UNLIKE III.1, ?X and ?A cannot be left to be bound
                    ;; structurally from the CONCLUSION-PATTERN match: here the
                    ;; binder (.exists ?x ?A) sits in the CONSEQUENT, while the
                    ;; META-CONSTRUCTOR (@subst ?x ?t ?A) sits in the ANTECEDENT --
                    ;; and MATCH-TEMPLATE processes a (.to ANTECEDENT CONSEQUENT)
                    ;; pattern's antecedent strictly before its consequent, left to
                    ;; right. So by the time @subst is reached, ?x/?A would still be
                    ;; unbound and matching would fail outright (never back-solved).
                    ;; The fix: like GEN's own variable argument, ?X and ?A are
                    ;; supplied directly as extra citation arguments -- e.g.
                    ;; (III.3 v0 (.eq v0 v1) v1) -- seeding BINDS before
                    ;; CONCLUSION-PATTERN is matched at all, exactly as EXTRA-ARGS
                    ;; already do for ?T in both this axiom and III.1.
                    (ledger (admit ledger 'axiom (list 'III.3 '((var? ?x) (wff? ?A) (term? ?t) (@subst-ok? ?x ?t ?A))
                                                        '((?x ?A ?t) (.to (@subst ?x ?t ?A) (.exists ?x ?A))))))
                    ;; IV.1-IV.4: first-order equality. .EQ has existed as a
                    ;; WFF-formation rule since BOOTSTRAP-FORMATION-RULES
                    ;; (wff_eq?), but until now it was semantically INERT --
                    ;; no axiom ever said what (.eq ?s ?t) actually MEANS.
                    ;;   IV.1  t = t                          [reflexivity]
                    ;;   IV.2  x = t -> (A -> A[t/x])          [Leibniz substitution]
                    ;;   IV.3  s = t -> t = s                  [symmetry]
                    ;;   IV.4  s = t -> (t = u -> s = u)        [transitivity]
                    ;; IV.2 reuses EXACTLY the same @subst/@subst-ok?
                    ;; machinery III.1 already established (capture-avoidance
                    ;; included, for free) -- the only difference from III.1's
                    ;; own conclusion pattern is that here the antecedent is
                    ;; (.eq ?x ?t) rather than (.forall ?x ?A), and ?t is an
                    ;; ordinary schema TERM here (not an axiom extra-param),
                    ;; since (unlike III.1) there is a WFF, not a binder, to
                    ;; bind ?x and ?A structurally before @subst is evaluated.
                    ;;
                    ;; IV.3/IV.4 are ADMITTED DIRECTLY rather than derived
                    ;; from IV.1+IV.2 -- and this is a deliberate, checked
                    ;; decision, not laziness. SUBSTITUTE-WFF replaces EVERY
                    ;; free occurrence of ?x throughout ?A uniformly, so
                    ;; FV(@subst ?x ?t ?A) subset-of (FV(?A) \ {?x}) union
                    ;; FV(?t): ?x can NEVER survive into the result of an
                    ;; IV.2 application. Symmetry's conclusion (t = s)
                    ;; necessarily still mentions s -- so if ?x is bound to
                    ;; s (forced, to match a hypothesis s=t via MP), s can
                    ;; never appear in the output of THAT step, for ANY
                    ;; choice of ?A: proving t=s from s=t via IV.2 is not
                    ;; merely hard here, it is FORMALLY UNREACHABLE this way
                    ;; (confirmed by hand and by attempted construction
                    ;; before writing this comment). The usual textbook
                    ;; trick instead substitutes into ONE of several
                    ;; DESIGNATED occurrences of a multi-argument predicate
                    ;; (Mendelson's congruence-per-symbol axioms), which is
                    ;; a genuinely different, finer-grained schema than
                    ;; SUBSTITUTE-WFF's "replace every free occurrence"
                    ;; semantics -- implementing that generally was judged
                    ;; not worth the complexity here, so symmetry and
                    ;; transitivity are simply their own primitive axioms.
                    ;; IV.2 remains useful in its own right wherever ?A has
                    ;; only ONE free occurrence of ?x to begin with (no
                    ;; occurrence-selection issue arises), which is exactly
                    ;; how axiom P3 (induction, Section 7.5) uses @subst.
                    (ledger (admit ledger 'axiom (list 'IV.1 '((term? ?t))
                                                        '(nil (.eq ?t ?t)))))
                    (ledger (admit ledger 'axiom (list 'IV.2 '((var? ?x) (wff? ?A) (term? ?t) (@subst-ok? ?x ?t ?A))
                                                        '(nil (.to (.eq ?x ?t) (.to ?A (@subst ?x ?t ?A)))))))
                    (ledger (admit ledger 'axiom (list 'IV.3 '((term? ?s) (term? ?t))
                                                        '(nil (.to (.eq ?s ?t) (.eq ?t ?s))))))
                    (ledger (admit ledger 'axiom (list 'IV.4 '((term? ?s) (term? ?t) (term? ?u))
                                                        '(nil (.to (.eq ?s ?t) (.to (.eq ?t ?u) (.eq ?s ?u))))))))
               ledger))
           (bootstrap-peano-vocabulary (ledger)
             "Term-formation rules for elementary arithmetic's four fixed
function symbols: ZERO (arity 0), S (successor, arity 1), + and * (arity
2). Only admitted when BOOTSTRAP-KERNEL is called with :ARITHMETIC T --
these are one specific theory's vocabulary, not part of the generic
kernel, so every existing self-test/library file that never asks for
:ARITHMETIC sees an unchanged TERM? rule set (just VAR-TERM, as before)."
             (let* ((ledger (admit ledger 'term? (list 'zero-term nil '(term? zero))))
                    (ledger (admit ledger 'term? (list 'succ-term '((term? ?x)) '(term? (S ?x)))))
                    (ledger (admit ledger 'term? (list 'plus-term '((term? ?x) (term? ?y)) '(term? (+ ?x ?y)))))
                    (ledger (admit ledger 'term? (list 'times-term '((term? ?x) (term? ?y)) '(term? (* ?x ?y))))))
               ledger))
           (bootstrap-peano-axioms (ledger)
             "The Peano axioms proper (P1-P2: successor's basic properties;
P3: induction; P4-P7: the recursive defining equations for + and *, which
in this system -- unlike a system with recursive DEFINITIONS -- must be
stated as axioms, since there is no primitive recursion mechanism other
than proof; P8-P10: congruence of S/+/* under equality).

P8-P10 exist for the SAME reason IV.3/IV.4 (symmetry/transitivity) are
their own primitive axioms rather than IV.2 (Leibniz) instances: IV.2
cannot hold one occurrence of a variable fixed while changing another
occurrence of the SAME variable elsewhere (SUBSTITUTE-WFF replaces every
free occurrence uniformly), and congruence -- \"x=y implies S(x)=S(y)\" --
is exactly that shape (x appears on both the hypothesis and, unchanged in
ROLE but needing its OWN copy, the conclusion). Stated directly as axioms
instead, matching Mendelson's own per-function-symbol congruence scheme.

P3 (induction) is stated CURRIED -- (A[0/x] -> ((forall x (A -> A[Sx/x]))
-> (forall x A))) -- rather than with a conjunction of the base case and
step case, because this kernel has never had a .AND connective (see
BOOTSTRAP-FORMATION-RULES' own commentary on .EXISTS: adding connective
syntax without wiring in more axioms is safe, but here it is simply
unnecessary -- currying an implication is logically equivalent to
conjoining its antecedents and is already expressible with .TO alone).

Unlike III.1 (where ?t is an axiom extra-param because there is no WFF
structure available to bind ?x/?A from first), P3 needs BOTH ?x and ?A
supplied as extra-params: its conclusion pattern's very first component
is (@subst ?x zero ?A), and MATCH-TEMPLATE evaluates a meta-constructor
node only once ALL of its arguments are already ground -- so ?x and ?A
must already be bound before matching even starts, exactly the same
reason III.1 seeds ?t from EXTRA-ARGS rather than leaving it to
structural matching. A citation therefore looks like (P3 v0 (.eq v0 v0)),
supplying the induction variable and the full schema formula explicitly."
             (let* ((ledger (admit ledger 'axiom (list 'P1 '((term? ?x))
                                                        '(nil (.neg (.eq (S ?x) zero))))))
                    (ledger (admit ledger 'axiom (list 'P2 '((term? ?x) (term? ?y))
                                                        '(nil (.to (.eq (S ?x) (S ?y)) (.eq ?x ?y))))))
                    (ledger (admit ledger 'axiom (list 'P3 '((var? ?x) (wff? ?A) (term? zero) (term? (S ?x))
                                                              (@subst-ok? ?x zero ?A) (@subst-ok? ?x (S ?x) ?A))
                                                        '((?x ?A)
                                                          (.to (@subst ?x zero ?A)
                                                               (.to (.forall ?x (.to ?A (@subst ?x (S ?x) ?A)))
                                                                    (.forall ?x ?A)))))))
                    (ledger (admit ledger 'axiom (list 'P4 '((term? ?x))
                                                        '(nil (.eq (+ ?x zero) ?x)))))
                    (ledger (admit ledger 'axiom (list 'P5 '((term? ?x) (term? ?y))
                                                        '(nil (.eq (+ ?x (S ?y)) (S (+ ?x ?y)))))))
                    (ledger (admit ledger 'axiom (list 'P6 '((term? ?x))
                                                        '(nil (.eq (* ?x zero) zero)))))
                    (ledger (admit ledger 'axiom (list 'P7 '((term? ?x) (term? ?y))
                                                        '(nil (.eq (* ?x (S ?y)) (+ (* ?x ?y) ?x))))))
                    (ledger (admit ledger 'axiom (list 'P8 '((term? ?x) (term? ?y))
                                                        '(nil (.to (.eq ?x ?y) (.eq (S ?x) (S ?y)))))))
                    (ledger (admit ledger 'axiom (list 'P9 '((term? ?x1) (term? ?y1) (term? ?x2) (term? ?y2))
                                                        '(nil (.to (.eq ?x1 ?y1)
                                                                   (.to (.eq ?x2 ?y2) (.eq (+ ?x1 ?x2) (+ ?y1 ?y2))))))))
                    (ledger (admit ledger 'axiom (list 'P10 '((term? ?x1) (term? ?y1) (term? ?x2) (term? ?y2))
                                                        '(nil (.to (.eq ?x1 ?y1)
                                                                   (.to (.eq ?x2 ?y2) (.eq (* ?x1 ?x2) (* ?y1 ?y2)))))))))
               ledger)))
    (let* ((ledger (admit-each (empty-ledger) 'atomic-wff-symbol atomic-symbols))
           (ledger (admit-each ledger 'variable-symbol variables))
           (ledger (bootstrap-formation-rules ledger))
           (ledger (bootstrap-inference-rules ledger))
           (ledger (bootstrap-axioms ledger))
           (ledger (if arithmetic (bootstrap-peano-vocabulary ledger) ledger))
           (ledger (if arithmetic (bootstrap-peano-axioms ledger) ledger)))
      ledger)))

;;; ---------------------------------------------------------------------
;;; 8. WFF?/VAR? special-casing for bare declared symbols
;;; ---------------------------------------------------------------------
;;;
;;; A bare atomic-wff or variable symbol (e.g. A, v0) has no internal
;;; structure to pattern-match against a rule's FORM, so JUDGEMENT-BIND's
;;; generic dispatch is extended here to consult Sigma directly for the
;;; base cases of the WFF?/VAR? judgements, as a projection instead of a
;;; hardcoded list.

;;;
;;; The same goes for an application (P t1 ... tn) of a declared predicate
;;; schema symbol of arity n: it is a wff exactly when every ti is a term.

(defun predicate-schema-application-wff-p (expr ledger seen open-hyps)
  (and (consp expr)
       (let ((arity (predicate-schema-arity (car expr) ledger)))
         (and arity
              (listp (cdr expr))
              (= (length (cdr expr)) arity)
              (every (lambda (arg) (judgement? 'term? arg ledger seen open-hyps)) (cdr expr))))))

(let ((orig #'judgement-bind))
  (setf (symbol-function 'judgement-bind)
        (lambda (kind args binds ledger &optional (seen nil) (open-hyps nil))
          (if (or (and (= (length args) 1) (symbolp (car args))
                       (or (and (eq kind 'wff?) (atomic-wff-symbol-p (car args) ledger))
                           (and (eq kind 'var?) (variable-p (car args) ledger))
                           (and (eq kind 'term?) (variable-p (car args) ledger))))
                  (and (= (length args) 1) (eq kind 'wff?)
                       (predicate-schema-application-wff-p (car args) ledger seen open-hyps)))
              (values binds t)
              (funcall orig kind args binds ledger seen open-hyps)))))
