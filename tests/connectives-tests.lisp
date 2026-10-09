;;;; connectives-tests.lisp -- hilbert-library/00-connectives.system
;;;; Part of the ledger-kernel/tests system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun connectives-ledger ()
  "00-classical-fol-equality.system + 00-connectives.system."
  (bootstrap-kernel-from-spec-file
   (library-path "00-connectives.system")
   :ledger (bootstrap-kernel-from-spec-file (library-path "00-classical-fol-equality.system"))))

(defun same-formula-p (ledger f g)
  "T iff F and G are the same formula to the kernel (after expanding
abbreviations and naming bound variables away)."
  (equal (named->db f ledger) (named->db g ledger)))

(defun test-connectives-formation-and-axioms (ledger)
  "The connectives are abbreviations: wffs by expansion, the same formula
as their expansion, with no formation rule or axiom of their own."
  (expect "(.and A B) is a wff" (judgement? 'wff? '(.and A B) ledger) t)
  (expect "(.or A (.neg B)) is a wff" (judgement? 'wff? '(.or A (.neg B)) ledger) t)
  (expect "(.iff A (.and B C)) is a wff" (judgement? 'wff? '(.iff A (.and B C)) ledger) t)
  (expect "(.exists1 v0 (.eq v0 v1)) is a wff" (judgement? 'wff? '(.exists1 v0 (.eq v0 v1)) ledger) t)
  (expect "(.exists1 v0 (.exists1 v1 (.eq v0 v1))) is a wff (nested, fresh u each time)"
          (judgement? 'wff? '(.exists1 v0 (.exists1 v1 (.eq v0 v1))) ledger) t)
  (expect "Attack: (.exists1 A B) with a non-variable binder is not a wff"
          (judgement? 'wff? '(.exists1 A B) ledger) nil)
  (expect "00-connectives.system adds no axiom and no formation rule"
          (and (notany (lambda (e) (search "FOLD" (symbol-name (first (entry-payload e)))))
                       (entries-of-kind 'axiom ledger))
               (subsetp '(.and .or .iff .exists1)
                        (mapcar (lambda (e) (car (first (entry-payload e))))
                                (entries-of-kind 'abbreviation ledger))))
          t)
  (expect "A and B is the formula not(A -> not B)"
          (same-formula-p ledger '(.and A B) '(.neg (.to A (.neg B)))) t)
  (expect "A or B is the formula not A -> B"
          (same-formula-p ledger '(.or A B) '(.to (.neg A) B)) t)
  (expect "A iff B is (A -> B) and (B -> A), expanded through .and"
          (same-formula-p ledger '(.iff A B) '(.neg (.to (.to A B) (.neg (.to B A))))) t)
  (expect "Attack: A and B is not the expansion of A or B"
          (same-formula-p ledger '(.and A B) '(.to (.neg A) B)) nil)
  (expect "E!v0 (v0 = v1) is its expansion with u = v2"
          (same-formula-p ledger '(.exists1 v0 (.eq v0 v1))
                          '(.exists v0 (.and (.eq v0 v1) (.forall v2 (.to (.eq v2 v1) (.eq v2 v0))))))
          t)
  (expect "... and with u = v3 (the same formula: u is bound)"
          (same-formula-p ledger '(.exists1 v0 (.eq v0 v1))
                          '(.exists v0 (.and (.eq v0 v1) (.forall v3 (.to (.eq v3 v1) (.eq v3 v0))))))
          t)
  (expect "Attack: an expansion with u free in A is a different formula"
          (same-formula-p ledger '(.exists1 v0 (.eq v0 v2))
                          '(.exists v0 (.and (.eq v0 v2) (.forall v2 (.to (.eq v2 v2) (.eq v2 v0))))))
          nil)
  (expect "Attack: an expansion with u = x is a different formula"
          (same-formula-p ledger '(.exists1 v0 (.eq v0 v1))
                          '(.exists v0 (.and (.eq v0 v1) (.forall v0 (.to (.eq v0 v1) (.eq v0 v0))))))
          nil)
  (expect "Attack: an expansion whose uniqueness clause is not A[u/x] is a different formula"
          (same-formula-p ledger '(.exists1 v0 (.eq v0 v1))
                          '(.exists v0 (.and (.eq v0 v1) (.forall v2 (.to (.eq v0 v1) (.eq v2 v0))))))
          nil)
  (expect "the expansion's fresh u avoids a %n already written in A"
          (same-formula-p ledger '(.exists1 v0 (.eq v0 %0))
                          '(.exists v0 (.and (.eq v0 %0) (.forall v2 (.to (.eq v2 %0) (.eq v2 v0))))))
          t)
  (let ((l (bootstrap-kernel-from-spec
            '((:abbreviation (.ex2 ?A) (.exists ?y (.exists ?z ?A)))
              (:abbreviation (.ex3 ?A) (.ex2 (.exists ?w ?A)))
              (:axiom EX3-TEST ((wff? ?B)) (nil (.to (.ex3 ?B) (.ex3 ?B)))))
            :ledger ledger)))
    (expect "an abbreviation built on another, inside a rule pattern: binders stay apart"
            (and (equal (named->db '(.ex3 (.eq v0 v1)) l)
                        (named->db '(.exists v2 (.exists v3 (.exists v4 (.eq v0 v1)))) l))
                 (check-k-proof '((0 (.to (.ex3 (.eq v0 v1)) (.ex3 (.eq v0 v1))) :axiom (ex3-test))) l))
            t)
    (expect "Attack: ... and the pattern does not match a formula with fewer quantifiers"
            (check-k-proof '((0 (.to (.ex2 (.eq v0 v1)) (.ex2 (.eq v0 v1))) :axiom (ex3-test))) l)
            nil))
  (expect "Attack: declaring an abbreviation over the primitive .to -- must error"
          (handler-case (progn (bootstrap-kernel-from-spec '((:abbreviation (.to ?A ?B) (.or ?A ?B)))
                                                           :ledger ledger)
                               :admitted)
            (error () :refused))
          :refused)
  (expect "Attack: an abbreviation using itself -- must error"
          (handler-case (progn (bootstrap-kernel-from-spec '((:abbreviation (.loop ?A) (.neg (.loop ?A))))
                                                           :ledger ledger)
                               :admitted)
            (error () :refused))
          :refused)
  (expect "Attack: an abbreviation with a parameter not in its head -- must error"
          (handler-case (progn (bootstrap-kernel-from-spec '((:abbreviation (.half ?A) (.to ?A ?B)))
                                                           :ledger ledger)
                               :admitted)
            (error () :refused))
          :refused)
  ledger)

(defun test-exists1-is-a-binder (ledger)
  ".EXISTS1 is an abbreviation whose expansion binds its variable, so
the variable is bound for free-variable checks and for substitution,
without .EXISTS1 being a kernel binder."
  (expect "v0 is NOT free in (.exists1 v0 (.eq v0 v1))"
          (meta-not-free-in? ledger nil 'v0 '(.exists1 v0 (.eq v0 v1))) t)
  (expect "v1 IS free in (.exists1 v0 (.eq v0 v1))"
          (meta-not-free-in? ledger nil 'v1 '(.exists1 v0 (.eq v0 v1))) nil)
  (expect "III.1 substitutes a free variable under .exists1: forall v1 E!v0 (v0=v1) -> E!v0 (v0=v2)"
          (check-k-proof '((0 (.to (.forall v1 (.exists1 v0 (.eq v0 v1))) (.exists1 v0 (.eq v0 v2)))
                              :axiom (III.1 v2)))
                         ledger) t)
  (expect "III.1 leaves the bound variable of .exists1 alone: forall v0 E!v0 (v0=v1) -> E!v0 (v0=v1)"
          (check-k-proof '((0 (.to (.forall v0 (.exists1 v0 (.eq v0 v1))) (.exists1 v0 (.eq v0 v1)))
                              :axiom (III.1 v2)))
                         ledger) t)
  (expect "Attack: III.1 substituting INTO the bound variable of .exists1 -- must reject"
          (check-k-proof '((0 (.to (.forall v0 (.exists1 v0 (.eq v0 v1))) (.exists1 v0 (.eq v2 v1)))
                              :axiom (III.1 v2)))
                         ledger) nil)
  (expect "Attack: III.1 with a term captured by .exists1 (v1 := v0 under E!v0) -- must reject"
          (check-k-proof '((0 (.to (.forall v1 (.exists1 v0 (.eq v0 v1))) (.exists1 v0 (.eq v0 v0)))
                              :axiom (III.1 v0)))
                         ledger) nil)
  (expect ".exists1, an abbreviation head, is not declarable as a fresh symbol"
          (fresh-symbol-name-p '.exists1 ledger) nil)
  (expect ".exists1 is not a kernel binder"
          (binder-head-p '.exists1) nil)
  ledger)

(defun test-connectives-derivation (ledger)
  "And-elimination, A & B |- A: A & B is not(A -> not-B), so MP applies
directly to the propositional
lemma not(A -> not-B) -> A, proved by hand from the classical library
(ex falso, modus tollens, double negation)."
  (let* ((ledger (reduce (lambda (l f) (read-ledger-from-file (library-path f) :ledger l))
                         '("01-propositional-core.ledger" "02-predicate-core.ledger"
                           "03-equality-core.ledger" "05-classical-logic.ledger")
                         :initial-value ledger))
         (core '(.to (.neg (.to A (.neg B))) A))
         (ledger (check-and-extend
                  ledger 'th 'th-and-elim-left-core
                  `((0 (.to (.neg A) (.to A (.neg B))) :th-ded (th-ex-falso))
                    (1 (.to (.to (.neg A) (.to A (.neg B)))
                            (.to (.neg (.to A (.neg B))) (.neg (.neg A))))
                       :th-ded (th-modus-tollens))
                    (2 (.to (.neg (.to A (.neg B))) (.neg (.neg A))) :ir (MP 1 0))
                    (3 (.to (.to (.neg (.neg A)) A)
                            (.to (.to (.neg (.to A (.neg B))) (.neg (.neg A)))
                                 (.to (.neg (.to A (.neg B))) A)))
                       :th-ded (th-hypothetical-syllogism))
                    (4 (.to (.neg (.neg A)) A) :th-ded (th-dneg-elim))
                    (5 (.to (.to (.neg (.to A (.neg B))) (.neg (.neg A)))
                            (.to (.neg (.to A (.neg B))) A))
                       :ir (MP 3 4))
                    (6 ,core :ir (MP 5 2))))))
    (expect "and-elimination: (.and A B) |- A"
            (check-k-proof `((0 (.and A B) :hyp nil)
                             (1 ,core :th (th-and-elim-left-core))
                             (2 A :ir (MP 1 0)))
                           ledger) t)
    ledger))

(defun connectives-library-ledger ()
  "CONNECTIVES-LEDGER + the 01/02/03/05 modules 06-connectives.ledger needs."
  (reduce (lambda (l f) (read-ledger-from-file (library-path f) :ledger l))
          '("01-propositional-core.ledger" "02-predicate-core.ledger"
            "03-equality-core.ledger" "05-classical-logic.ledger")
          :initial-value (connectives-ledger)))

(defun test-connectives-library (ledger)
  "hilbert-library/06-connectives.ledger loads and its lemmas are usable."
  (let ((ledger (read-ledger-from-file (library-path "06-connectives.ledger") :ledger ledger)))
    (expect "06: th-and-intro at compound formulas"
            (check-k-proof '((0 (.to (.eq v0 v1) (.to (.neg a) (.and (.eq v0 v1) (.neg a))))
                                :th (th-and-intro)))
                           ledger) t)
    (expect "06: th-or-elim"
            (check-k-proof '((0 (.to (.to a c) (.to (.to b c) (.to (.or a b) c))) :th (th-or-elim))) ledger) t)
    (expect "06: th-iff-sym"
            (check-k-proof '((0 (.to (.iff a b) (.iff b a)) :th (th-iff-sym))) ledger) t)
    (expect "06: th-excluded-middle"
            (check-k-proof '((0 (.or (.eq v0 v0) (.neg (.eq v0 v0))) :th (th-excluded-middle))) ledger) t)
    (expect "Attack: th-and-elim-l does not give the right conjunct -- must reject"
            (check-k-proof '((0 (.to (.and a b) b) :th (th-and-elim-l))) ledger) nil)
    ledger))

(defun run-connectives-self-tests ()
  "hilbert-library/00-connectives.system, the .EXISTS1 binder, and
06-connectives.ledger."
  (let* ((ledger (connectives-ledger))
         (ledger (test-connectives-formation-and-axioms ledger))
         (ledger (test-exists1-is-a-binder ledger)))
    (test-connectives-derivation ledger))
  (test-connectives-library (connectives-library-ledger))
  (format t "~%Connectives self-tests complete.~%"))
