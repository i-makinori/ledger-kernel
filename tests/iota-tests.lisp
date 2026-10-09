;;;; iota-tests.lisp -- Section 19: descriptions and existential introduction
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 19. Descriptions (.iota x A), "the x such that A", as a contextual
;;;     abbreviation (00-connectives.system, Principia *14.01): not a
;;;     term, but a way of writing the formula it stands in. At the
;;;     narrowest atomic formula psi holding it,
;;;       psi[(.iota x A)]  :=  exists b (forall x (A <-> x = b) and psi[b]).
;;;     There is no IOTA rule: what a description satisfies is proved from
;;;     that expansion (07-quantifier-schemas.ledger's th-desc-proper and
;;;     th-desc-atomic), and an improper description satisfies nothing.
;;; ---------------------------------------------------------------------

(defun description-ledger ()
  "Base logic + 00-connectives.system + 01/02/03/05/06/07."
  (reduce (lambda (l f) (read-ledger-from-file (library-path f) :ledger l))
          '("06-connectives.ledger" "07-quantifier-schemas.ledger")
          :initial-value (connectives-library-ledger)))

(defun test-description-expansion (ledger)
  (expect "(.iota v0 (.eq v0 v1)) alone is not a term"
          (judgement? 'term? '(.iota v0 (.eq v0 v1)) ledger) nil)
  (expect "(.iota v0 (.eq v0 v1)) alone is not a wff"
          (judgement? 'wff? '(.iota v0 (.eq v0 v1)) ledger) nil)
  (expect "(.eq (.iota v0 (.eq v0 v1)) v1) is a wff"
          (judgement? 'wff? '(.eq (.iota v0 (.eq v0 v1)) v1) ledger) t)
  (expect "... and it is the formula exists b (forall v0 (v0=v1 <-> v0=b) and b=v1)"
          (equal (named->db '(.eq (.iota v0 (.eq v0 v1)) v1) ledger)
                 (named->db '(.exists v2 (.and (.forall v0 (.iff (.eq v0 v1) (.eq v0 v2))) (.eq v2 v1))) ledger))
          t)
  (expect "narrowest scope: not (iota = v1) is not-exists, not exists-not"
          (equal (named->db '(.neg (.eq (.iota v0 (.eq v0 v1)) v1)) ledger)
                 (named->db '(.neg (.exists v2 (.and (.forall v0 (.iff (.eq v0 v1) (.eq v0 v2))) (.eq v2 v1))))
                            ledger))
          t)
  (expect "two descriptions in one atomic formula: the left one outermost"
          (equal (named->db '(.eq (.iota v0 (.eq v0 v1)) (.iota v0 (.eq v0 v3))) ledger)
                 (named->db '(.exists v4 (.and (.forall v0 (.iff (.eq v0 v1) (.eq v0 v4)))
                                               (.exists v5 (.and (.forall v0 (.iff (.eq v0 v3) (.eq v0 v5)))
                                                                 (.eq v4 v5)))))
                            ledger))
          t)
  (expect "a description under a binder of its own free variable keeps it bound there"
          (equal (named->db '(.forall v1 (.eq (.iota v0 (.eq v0 v1)) v1)) ledger)
                 (named->db '(.forall v1 (.exists v2 (.and (.forall v0 (.iff (.eq v0 v1) (.eq v0 v2)))
                                                           (.eq v2 v1))))
                            ledger))
          t)
  (expect "an abbreviation's body may bind its variable by a description"
          (handler-case
              (progn (bootstrap-kernel-from-spec '((:abbreviation (the-eq ?x) (.iota ?y (.eq ?y ?x))))
                                                 :ledger ledger)
                     t)
            (error () nil))
          t)
  (expect "Attack: a body variable neither a parameter nor bound by the description -- must error"
          (handler-case
              (progn (bootstrap-kernel-from-spec '((:abbreviation (the-eq ?x) (.iota ?y (.eq ?z ?x))))
                                                 :ledger ledger)
                     :admitted)
            (error () :refused))
          :refused)
  ledger)

(defun test-axiom-iii3 (ledger)
  "III.3: A[t/x] -> exists x. A, unconditional (no Gen-style freshness
side condition -- see its own commentary in BOOTSTRAP-AXIOMS for why
that's sound). EXTRA-PARAM-PATTERNS are (?x ?A ?t), NOT just (?t) like
III.1 -- ?x/?A must be supplied directly since the binder here sits in
the CONSEQUENT while @subst sits in the ANTECEDENT (MATCH-TEMPLATE
processes antecedent before consequent, so ?x/?A can't be left to bind
structurally the way III.1's own (.forall ?x ?A) antecedent does)."
  (expect "III.3: v1=v1 -> exists v0(v0=v1)"
          (check-k-proof '((0 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1))) :th (th-exists-intro :inst ((p (v0) (.eq v0 v1)) (v1 v1))))) ledger)
          t)
  (let ((ledger (check-and-extend ledger 'th 'th-exists-v0-eq-v1
                                   '((0 (.eq v1 v1) :axiom (IV.1))
                                     (1 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1))) :th (th-exists-intro :inst ((p (v0) (.eq v0 v1)) (v1 v1))))
                                     (2 (.exists v0 (.eq v0 v1)) :ir (MP 1 0)))
                                   (silent-log))))
    (expect "TH-EXISTS-V0-EQ-V1 is a real, re-citable ledger theorem"
            (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :th (th-exists-v0-eq-v1))) ledger) t)
    (expect "Attack: III.3 with a MISMATCHED extra-arg t (v2 instead of v1) -- must reject"
            (check-k-proof '((0 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1))) :th (th-exists-intro :inst ((p (v0) (.eq v0 v1)) (v1 v2))))) ledger)
            nil)
    ledger))

(defun test-description-proofs (ledger)
  "What a description satisfies is proved, not postulated."
  (let ((x '(.eq (.iota v0 (.eq v0 v1)) v1)))
    (expect "|- (the v0 such that v0 = v1) = v1, by th-desc-atomic"
            (check-k-proof `((0 (.iff (.eq v0 v1) (.eq v0 v1)) :th (th-iff-refl))
                             (1 (.forall v0 (.iff (.eq v0 v1) (.eq v0 v1))) :ir (gen 0 v0))
                             (2 (.iff ,x (.eq v1 v1))
                                :th (th-desc-atomic 1 :inst ((p (v0) (.eq v0 v1)) (q (v0) (.eq v0 v1)))))
                             (3 (.to (.iff ,x (.eq v1 v1)) (.to (.eq v1 v1) ,x)) :th (th-iff-mpr))
                             (4 (.to (.eq v1 v1) ,x) :ir (mp 3 2))
                             (5 (.eq v1 v1) :axiom (iv.1))
                             (6 ,x :ir (mp 4 5)))
                           ledger)
            t))
  (expect "Attack: x = x at an improper description -- IV.1 does not apply, must reject"
          (check-k-proof '((0 (.eq (.iota v0 (.neg (.eq v0 v0))) (.iota v0 (.neg (.eq v0 v0)))) :axiom (iv.1)))
                         ledger)
          nil)
  (expect "Attack: :inst renaming a variable to a description -- not a term, must reject"
          (check-k-proof '((0 (.to (.forall v0 (.eq v0 v0)) (.eq (.iota v1 (.eq v1 v2)) (.iota v1 (.eq v1 v2))))
                              :th (th-forall-elim :inst ((v1 (.iota v1 (.eq v1 v2)))))))
                         ledger)
          nil)
  ;; Citing an entry renames its own internal variables apart from what
  ;; the citation brings in, and hands a renaming down to the citations
  ;; inside it (k-proof.lisp, PREPARE-CITED-PROOF).
  (expect "a binding mentioning v3, which th-desc-atomic generalizes inside, is renamed apart"
          (check-k-proof '((0 (.forall v0 (.iff (.eq v0 v3) (.eq v0 v1))) :hyp nil)
                           (1 (.iff (.exists v2 (.and (.forall v0 (.iff (.eq v0 v3) (.eq v0 v2))) (q v2))) (q v1))
                              :th (th-desc-atomic 0 :inst ((p (v0) (.eq v0 v3))))))
                         ledger)
          t)
  (expect ":inst ((v1 v4)) reaches the lemmas th-desc-atomic cites"
          (check-k-proof '((0 (.forall v0 (.iff (p v0) (.eq v0 v4))) :hyp nil)
                           (1 (.iff (.exists v2 (.and (.forall v0 (.iff (p v0) (.eq v0 v2))) (q v2))) (q v4))
                              :th (th-desc-atomic 0 :inst ((v1 v4)))))
                         ledger)
          t)
  (expect "Attack: the same renaming with the conclusion left at v1 -- must reject"
          (check-k-proof '((0 (.forall v0 (.iff (p v0) (.eq v0 v4))) :hyp nil)
                           (1 (.iff (.exists v2 (.and (.forall v0 (.iff (p v0) (.eq v0 v2))) (q v2))) (q v1))
                              :th (th-desc-atomic 0 :inst ((v1 v4)))))
                         ledger)
          nil)
  ledger)

(defun run-iota-self-tests ()
  "Section 19: descriptions as contextual abbreviations, existential
introduction, and attack tests."
  (let* ((ledger (description-ledger))
         (ledger (test-description-expansion ledger))
         (ledger (test-axiom-iii3 ledger))
         (ledger (test-description-proofs ledger)))
    (declare (ignorable ledger))
    (format t "~%Description self-tests complete.~%")))
