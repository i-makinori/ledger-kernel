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
  "And-elimination, A & B |- A, through AND-UNFOLD and a propositional
tautology proved by PROVE-TAUTOLOGY on top of the classical library."
  (let* ((ledger (reduce (lambda (l f) (read-ledger-from-file (library-path f) :ledger l))
                         '("01-propositional-core.ledger" "02-predicate-core.ledger"
                           "03-equality-core.ledger" "05-classical-logic.ledger")
                         :initial-value ledger))
         (core '(.to (.neg (.to A (.neg B))) A))
         (ledger (prove-tautology ledger core 'th-and-elim-left-core)))
    (expect "and-elimination: (.and A B) |- A"
            (check-k-proof `((0 (.and A B) :hyp nil)
                             (1 (.to (.and A B) (.neg (.to A (.neg B)))) :axiom (and-unfold))
                             (2 (.neg (.to A (.neg B))) :ir (MP 1 0))
                             (3 ,core :th (th-and-elim-left-core))
                             (4 A :ir (MP 3 2)))
                           ledger) t)
    ledger))

(defun run-connectives-self-tests ()
  "hilbert-library/00-connectives.system and the .EXISTS1 binder."
  (let* ((ledger (connectives-ledger))
         (ledger (test-connectives-formation-and-axioms ledger))
         (ledger (test-exists1-is-a-binder ledger))
         (ledger (test-connectives-derivation ledger)))
    (declare (ignorable ledger))
    (format t "~%Connectives self-tests complete.~%")))
