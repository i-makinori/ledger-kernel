;;;; side-condition-tests.lisp -- (:meta-predicate ...) / (:meta-constructor ...)
;;;; Part of the ledger-kernel/tests system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; A .system file declares the meta-forms its side conditions are written
;;; with, chosen from the kernel's catalog (KERNEL-META-CATALOG). A rule
;;; may use only what its system has declared, before it; a system that
;;; declares none simply has no such side conditions.

(defparameter *bare-quantifier-spec*
  '((:term-formation var-term ((var? ?x)) (term? ?x))
    (:wff-formation wff_to? ((wff? ?A) (wff? ?B)) (wff? (.to ?A ?B)))
    (:wff-formation wff_forall? ((var? ?x) (wff? ?A)) (wff? (.forall ?x ?A)))
    (:wff-formation wff_eq? ((term? ?s) (term? ?t)) (wff? (.eq ?s ?t))))
  "Formation rules only: no side condition is used, so none is declared.")

(defparameter *q2-axiom*
  '(:axiom Q2 ((var? ?x) (wff? ?A) (wff? ?B) (@not-free-in? ?x ?A))
    (nil (.to (.forall ?x (.to ?A ?B)) (.to ?A (.forall ?x ?B))))))

(defun spec-refused-p (spec &optional ledger)
  "T iff BOOTSTRAP-KERNEL-FROM-SPEC refuses SPEC (on LEDGER)."
  (handler-case (progn (bootstrap-kernel-from-spec spec :ledger ledger) nil)
    (error () t)))

(defun test-side-condition-declarations ()
  (let ((base (fol-kernel)))
    (expect "the base system declares the three meta-predicates and @subst it uses"
            (and (equal (mapcar (lambda (e) (car (entry-payload e))) (entries-of-kind 'meta-predicate base))
                        '(@not-free-in? @not-free-in-dependencies? @subst-ok?))
                 (equal (mapcar (lambda (e) (car (entry-payload e))) (entries-of-kind 'meta-constructor base))
                        '(@subst)))
            t)
    (expect "... and not @substitutes?, which none of its rules needs"
            (declared-meta-form '@substitutes? :predicate base) nil))
  (expect "a system with no side condition needs no declaration"
          (spec-refused-p *bare-quantifier-spec*) nil)
  (expect "Attack: an axiom using @not-free-in? in a system that does not declare it -- must error"
          (spec-refused-p (append *bare-quantifier-spec* (list *q2-axiom*))) t)
  (expect "Attack: declared only AFTER the axiom that uses it -- must error"
          (spec-refused-p (append *bare-quantifier-spec*
                                  (list *q2-axiom* '(:meta-predicate @not-free-in? ?x ?A))))
          t)
  (let ((ledger (bootstrap-kernel-from-spec
                 (append *bare-quantifier-spec*
                         (list '(:meta-predicate @not-free-in? ?x ?A) *q2-axiom*)))))
    (expect "declared first, the axiom is admitted"
            (and (find 'q2 (entries-of-kind 'axiom ledger) :key (lambda (e) (first (entry-payload e)))) t)
            t)
    (expect "... and its side condition is checked: x not free in A"
            (check-k-proof '((0 (.to (.forall v0 (.to A (.eq v0 v0))) (.to A (.forall v0 (.eq v0 v0))))
                                :axiom (Q2)))
                           ledger)
            t)
    (expect "Attack: ... with x free in A -- must reject"
            (check-k-proof '((0 (.to (.forall v0 (.to (.eq v0 v1) (.eq v0 v0)))
                                     (.to (.eq v0 v1) (.forall v0 (.eq v0 v0))))
                                :axiom (Q2)))
                           ledger)
            nil)
    (expect "Attack: declaring @not-free-in? twice -- must error"
            (spec-refused-p '((:meta-predicate @not-free-in? ?x ?A)) ledger) t)
    (expect "Attack: an axiom applying @not-free-in? to three arguments -- must error"
            (spec-refused-p '((:axiom Q2B ((var? ?x) (wff? ?A) (@not-free-in? ?x ?A ?A))
                               (nil (.to ?A ?A))))
                            ledger)
            t)
    (expect "Attack: @subst in a pattern without (:meta-constructor @subst ...) -- must error"
            (spec-refused-p '((:axiom Q1 ((var? ?x) (wff? ?A) (term? ?t))
                               ((?t) (.to (.forall ?x ?A) (@subst ?x ?t ?A)))))
                            ledger)
            t)
    (expect "Attack: an abbreviation whose body uses an undeclared @subst -- must error"
            (spec-refused-p '((:abbreviation (.ex1 ?x ?A)
                               (.forall ?u (.to (@subst ?x ?u ?A) (.eq ?u ?x)))))
                            ledger)
            t)
    (expect "with @subst declared, the same axiom is admitted"
            (spec-refused-p '((:meta-constructor @subst ?x ?t ?A)
                              (:axiom Q1 ((var? ?x) (wff? ?A) (term? ?t))
                               ((?t) (.to (.forall ?x ?A) (@subst ?x ?t ?A)))))
                            ledger)
            nil))
  (expect "Attack: declaring a meta-predicate the kernel cannot compute -- must error"
          (spec-refused-p '((:meta-predicate @provable? ?A))) t)
  (expect "Attack: declaring @not-free-in? with the wrong number of arguments -- must error"
          (spec-refused-p '((:meta-predicate @not-free-in? ?x))) t)
  (expect "Attack: declaring the constructor @subst as a meta-predicate -- must error"
          (spec-refused-p '((:meta-predicate @subst ?x ?t ?A))) t)
  (expect "Attack: declaration arguments that are not distinct pattern variables -- must error"
          (spec-refused-p '((:meta-predicate @not-free-in? ?x ?x))) t)
  (expect "Attack: a Deduction Theorem case using an undeclared side condition -- must error"
          (spec-refused-p (append *bare-quantifier-spec*
                                  '((:irule MP ((wff? ?A) (wff? ?B)) (((.to ?A ?B) ?A) nil :=> ?B))
                                    (:meta-theorem deduction
                                     (:discharge (@vdash ?H ?A) (.to ?H ?A))
                                     (:case MP ((wff? ?H) (@not-free-in? ?H ?H))
                                      (((@vdash ?H (.to ?A ?B)) (@vdash ?H ?A)) nil :=> (@vdash ?H ?B)))))))
          t))

(defun run-side-condition-self-tests ()
  "Declared side conditions: (:meta-predicate ...) and (:meta-constructor ...)."
  (test-side-condition-declarations)
  (format t "~%Side-condition self-tests complete.~%"))
