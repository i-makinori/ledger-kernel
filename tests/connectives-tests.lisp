;;;; connectives-tests.lisp -- hilbert-library/00-connectives.system
;;;; Part of the ledger-kernel/tests system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun connectives-ledger ()
  "00-classical-fol-equality.system + 00-connectives.system."
  (bootstrap-kernel-from-spec-file
   (library-path "00-connectives.system")
   :ledger (bootstrap-kernel-from-spec-file (library-path "00-classical-fol-equality.system"))))

(defun connectives-axiom-ok-p (ledger formula axiom-name)
  (check-k-proof (list (list 0 formula :axiom (list axiom-name))) ledger))

(defun test-connectives-formation-and-axioms (ledger)
  "Formation of .AND/.OR/.IFF/.EXISTS1 and one instance of each
FOLD/UNFOLD axiom, plus EXISTS1 side-condition attacks."
  (expect "(.and A B) is a wff" (judgement? 'wff? '(.and A B) ledger) t)
  (expect "(.or A (.neg B)) is a wff" (judgement? 'wff? '(.or A (.neg B)) ledger) t)
  (expect "(.iff A (.and B C)) is a wff" (judgement? 'wff? '(.iff A (.and B C)) ledger) t)
  (expect "(.exists1 v0 (.eq v0 v1)) is a wff" (judgement? 'wff? '(.exists1 v0 (.eq v0 v1)) ledger) t)
  (expect "Attack: (.exists1 A B) with a non-variable binder is not a wff"
          (judgement? 'wff? '(.exists1 A B) ledger) nil)
  (expect "AND-UNFOLD" (connectives-axiom-ok-p ledger '(.to (.and A B) (.neg (.to A (.neg B)))) 'and-unfold) t)
  (expect "AND-FOLD" (connectives-axiom-ok-p ledger '(.to (.neg (.to A (.neg B))) (.and A B)) 'and-fold) t)
  (expect "OR-UNFOLD" (connectives-axiom-ok-p ledger '(.to (.or A B) (.to (.neg A) B)) 'or-unfold) t)
  (expect "OR-FOLD" (connectives-axiom-ok-p ledger '(.to (.to (.neg A) B) (.or A B)) 'or-fold) t)
  (expect "IFF-UNFOLD" (connectives-axiom-ok-p ledger '(.to (.iff A B) (.and (.to A B) (.to B A))) 'iff-unfold) t)
  (expect "IFF-FOLD" (connectives-axiom-ok-p ledger '(.to (.and (.to A B) (.to B A)) (.iff A B)) 'iff-fold) t)
  (expect "Attack: AND-UNFOLD to the expansion of OR -- must reject"
          (connectives-axiom-ok-p ledger '(.to (.and A B) (.to (.neg A) B)) 'and-unfold) nil)
  (expect "EXISTS1-UNFOLD with u = v2"
          (connectives-axiom-ok-p
           ledger '(.to (.exists1 v0 (.eq v0 v1))
                        (.exists v0 (.and (.eq v0 v1) (.forall v2 (.to (.eq v2 v1) (.eq v2 v0))))))
           'exists1-unfold) t)
  (expect "EXISTS1-FOLD with u = v3"
          (connectives-axiom-ok-p
           ledger '(.to (.exists v0 (.and (.eq v0 v1) (.forall v3 (.to (.eq v3 v1) (.eq v3 v0)))))
                        (.exists1 v0 (.eq v0 v1)))
           'exists1-fold) t)
  (expect "Attack: EXISTS1-UNFOLD with u free in A -- must reject"
          (connectives-axiom-ok-p
           ledger '(.to (.exists1 v0 (.eq v0 v2))
                        (.exists v0 (.and (.eq v0 v2) (.forall v2 (.to (.eq v2 v2) (.eq v2 v0))))))
           'exists1-unfold) nil)
  (expect "Attack: EXISTS1-UNFOLD with u = x -- must reject"
          (connectives-axiom-ok-p
           ledger '(.to (.exists1 v0 (.eq v0 v1))
                        (.exists v0 (.and (.eq v0 v1) (.forall v0 (.to (.eq v0 v1) (.eq v0 v0))))))
           'exists1-unfold) nil)
  (expect "Attack: EXISTS1-UNFOLD whose uniqueness clause is not A[u/x] -- must reject"
          (connectives-axiom-ok-p
           ledger '(.to (.exists1 v0 (.eq v0 v1))
                        (.exists v0 (.and (.eq v0 v1) (.forall v2 (.to (.eq v0 v1) (.eq v2 v0))))))
           'exists1-unfold) nil)
  ledger)

(defun test-exists1-is-a-binder (ledger)
  "The one-line kernel change: .EXISTS1 is in BINDER-HEADS, so its
variable is bound for free-variable checks and for substitution."
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
  (expect ".exists1 is a reserved head, not declarable as a fresh symbol"
          (fresh-symbol-name-p '.exists1 ledger) nil)
  ledger)

(defun test-connectives-derivation (ledger)
  "And-elimination, A & B |- A, through AND-UNFOLD and the propositional
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
                             (1 (.to (.and A B) (.neg (.to A (.neg B)))) :axiom (and-unfold))
                             (2 (.neg (.to A (.neg B))) :ir (MP 1 0))
                             (3 ,core :th (th-and-elim-left-core))
                             (4 A :ir (MP 3 2)))
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
