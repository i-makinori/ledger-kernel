;;;; debruijn-tests.lisp -- bound variables as de Bruijn indices (machine B)
;;;; Part of the ledger-kernel/tests system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun test-debruijn-conversion (ledger)
  "NAMED->DB, its inverse DB->NAMED, and the shapes they produce."
  (let ((named '(.forall v0 (.forall v1 (.eq v0 v1))))
        (db '(.forall (.forall (.eq (:bv 1) (:bv 0))))))
    (expect "forall v0 forall v1 (v0 = v1) becomes forall forall (1 = 0)"
            (equal (named->db named ledger) db) t)
    (expect "NAMED->DB is idempotent"
            (equal (named->db db ledger) db) t)
    (expect "alpha-equivalent formulas get the same kernel form"
            (equal (named->db '(.forall v3 (.forall v2 (.eq v3 v2))) ledger) db) t)
    (expect "different binding structure stays different"
            (equal (named->db '(.forall v0 (.forall v1 (.eq v1 v0))) ledger) db) nil)
    (expect "an inner binder shadows an outer one of the same name"
            (equal (named->db '(.forall v0 (.forall v0 (.eq v0 v0))) ledger)
                   '(.forall (.forall (.eq (:bv 0) (:bv 0)))))
            t)
    (expect "free variables keep their names"
            (equal (named->db '(.exists v0 (.eq v0 v1)) ledger) '(.exists (.eq (:bv 0) v1))) t)
    (expect "a binder over a non-variable (A) is left alone, and is not a wff"
            (and (equal (named->db '(.forall a (.eq a a)) ledger) '(.forall a (.eq a a)))
                 (not (judgement? 'wff? '(.forall a (.eq a a)) ledger)))
            t)
    (expect "DB->NAMED then NAMED->DB gives back the kernel form"
            (equal (named->db (db->named db ledger) ledger) db) t)
    (expect "DB->NAMED never lets a chosen name capture a free variable"
            (equal (named->db (db->named '(.forall (.eq (:bv 0) v0)) ledger) ledger)
                   '(.forall (.eq (:bv 0) v0)))
            t)
    (expect "DB-OPEN then DB-CLOSE with a variable not in the body is the identity"
            (equal (db-close (db-open '(.forall (.eq (:bv 1) (:bv 0))) 'v4) 'v4)
                   '(.forall (.eq (:bv 1) (:bv 0))))
            t)
    (expect "a dangling index is not locally closed" (locally-closed-p '(.eq (:bv 0) v1)) nil)
    (expect "a dangling index is not a wff" (judgement? 'wff? '(.eq (:bv 0) v1) ledger) nil)
    ledger))

(defun test-debruijn-alpha-equivalence (ledger)
  "Proof steps compare formulas up to renaming of bound variables."
  (expect "MP with the premise written as forall v0 and the rule's antecedent as forall v3"
          (check-k-proof '((0 (.forall v0 (.eq v0 v0)) :hyp nil)
                           (1 (.to (.forall v3 (.eq v3 v3)) B) :hyp nil)
                           (2 B :ir (mp 1 0)))
                         ledger)
          t)
  (expect "Attack: MP where the antecedent differs in binding structure -- must reject"
          (check-k-proof '((0 (.forall v0 (.forall v1 (.eq v0 v1))) :hyp nil)
                           (1 (.to (.forall v0 (.forall v1 (.eq v1 v0))) B) :hyp nil)
                           (2 B :ir (mp 1 0)))
                         ledger)
          nil)
  (let* ((l1 (check-and-extend ledger 'th 'th-db-a '((0 (.forall v0 (.eq v0 v0)) :hyp nil))))
         (l2 (check-and-extend l1 'th 'th-db-b '((0 (.forall v5 (.eq v5 v5)) :hyp nil)))))
    (expect "two theorems differing only in bound names have EQUAL payloads (up to the name)"
            (equal (second (entry-payload (car (last (treap-values-below (ledger-all l1) nil)))))
                   (second (entry-payload (car (last (treap-values-below (ledger-all l2) nil))))))
            t)
    (expect "... while each keeps its own text for display and saving"
            (equal (second (entry-source-payload (car (last (treap-values-below (ledger-all l2) nil)))))
                   '((0 (.forall v5 (.eq v5 v5)) :hyp nil)))
            t)
    (expect "a theorem stated with v0 is cited at an alpha-variant written with v2"
            (check-k-proof '((0 (.forall v2 (.eq v2 v2)) :hyp nil)
                             (1 (.forall v2 (.eq v2 v2)) :th (th-db-a 0)))
                           l2)
            t))
  ledger)

(defun test-debruijn-substitution (ledger)
  "Substitution cannot capture, and the instances that need a renamed
bound variable are now accepted as they are."
  (expect "III.1 with the renamed instance: forall v1 exists v0 (v0 /= v1) -> exists v2 (v2 /= v0)"
          (check-k-proof '((0 (.to (.forall v1 (.exists v0 (.neg (.eq v0 v1))))
                                   (.exists v2 (.neg (.eq v2 v0))))
                              :axiom (III.1 v0)))
                         ledger)
          t)
  (expect "Attack: III.1 with the captured instance: ... -> exists v0 (v0 /= v0) -- must reject"
          (check-k-proof '((0 (.to (.forall v1 (.exists v0 (.neg (.eq v0 v1))))
                                   (.exists v0 (.neg (.eq v0 v0))))
                              :axiom (III.1 v0)))
                         ledger)
          nil)
  (expect "IV.2 substitutes under a binder without capture: v0 = v1 -> (forall v1 (v0 = v1) -> forall v2 (v1 = v2))"
          (check-k-proof '((0 (.to (.eq v0 v1)
                                   (.to (.forall v1 (.eq v0 v1)) (.forall v2 (.eq v1 v2))))
                              :axiom (IV.2)))
                         ledger)
          t)
  (expect "Attack: a raw index as III.1's term -- must reject"
          (check-k-proof '((0 (.to (.forall (.eq (:bv 0) v1)) (.eq (:bv 0) v1)) :axiom (III.1 (:bv 0))))
                         ledger)
          nil)
  (expect "@subst-ok? still detects a term that is not locally closed"
          (meta-subst-ok? ledger nil 'v0 '(:bv 0) '(.eq v0 v1)) nil)
  (expect "@subst-ok? holds for kernel-form arguments"
          (meta-subst-ok? ledger nil 'v0 'v2 '(.forall (.eq (:bv 0) v0))) t)
  (expect "Gen by v0 on A may be written forall v3 A (alpha-equivalent)"
          (check-k-proof '((0 A :hyp nil) (1 (.forall v3 A) :ir (gen 0 v0))) ledger)
          t)
  (expect "Attack: Gen by v0 while v0 is free in an open hypothesis -- must reject"
          (check-k-proof '((0 (.eq v0 v0) :hyp nil) (1 (.forall v0 (.eq v0 v0)) :ir (gen 0 v0))) ledger)
          nil)
  (expect "Gen by v1 on v1 = v1 gives forall v2 (v2 = v2)"
          (check-k-proof '((0 (.eq v1 v1) :axiom (IV.1)) (1 (.forall v2 (.eq v2 v2)) :ir (gen 0 v1)))
                         ledger)
          t)
  (expect "Attack: Gen by v1 cited for forall v2 (v1 = v1), which leaves v1 free -- must reject"
          (check-k-proof '((0 (.eq v1 v1) :axiom (IV.1)) (1 (.forall v2 (.eq v1 v1)) :ir (gen 0 v1)))
                         ledger)
          nil)
  ledger)

(defun test-debruijn-fresh-variables (ledger)
  "The fresh variables %0, %1, ... used to open binders."
  (expect "%3 is a variable of every ledger" (variable-p '%3 ledger) t)
  (expect "Attack: declaring %3 as an atomic-wff symbol -- must error"
          (handler-case (progn (declare-atomic-wff-symbol ledger '%3) :declared)
            (error () :refused))
          :refused)
  (expect "fresh choice depends only on the input: 3 for (.eq %2 v0), 0 for (.eq v0 v1)"
          (equal (list (next-fresh-index '(.eq %2 v0)) (next-fresh-index '(.eq v0 v1))) '(3 0))
          t)
  (expect "a proof that already uses %0 as a variable still checks (III.1 picks another)"
          (check-k-proof '((0 (.to (.forall v1 (.eq %0 v1)) (.eq %0 v2)) :axiom (III.1 v2))) ledger)
          t)
  (expect "Attack: III.2 with the bound variable free in A, disguised as %0 -- must reject"
          (check-k-proof '((0 (.to (.forall v1 (.to (.eq v1 v1) B))
                                   (.to (.eq %0 %0) (.forall v1 B)))
                              :axiom (III.2)))
                         ledger)
          nil)
  ledger)

(defun test-debruijn-schema-capture (ledger)
  "An atomic symbol stands for a formula that does not depend on the
variables bound around it; dependence is written P(x)."
  (let* ((ledger (check-and-extend-by-deduction-direct
                  ledger 'th-db-gen-a 'a '((0 A :hyp nil) (1 (.forall v0 A) :ir (gen 0 v0))))))
    (expect "A -> forall v0 A, cited with A := (v1 = v1)"
            (check-k-proof '((0 (.to (.eq v1 v1) (.forall v3 (.eq v1 v1))) :th-ded (th-db-gen-a))) ledger)
            t)
    (expect "Attack: A -> forall v1 A with A := (v1 = v1) (A would capture v1) -- must reject"
            (check-k-proof '((0 (.to (.eq v1 v1) (.forall v1 (.eq v1 v1))) :th-ded (th-db-gen-a))) ledger)
            nil))
  ledger)

(defun test-rule-binder-names (ledger)
  "A rule's bound pattern variables are registered as ?BV1, ?BV2, ... in
order of first appearance; other pattern variables keep their names."
  (flet ((rule (kind name)
           (find name (entries-of-kind kind ledger) :key (lambda (e) (first (entry-payload e))))))
    (let ((ledger (bootstrap-kernel-from-spec-file (library-path "00-connectives.system") :ledger ledger)))
      (flet ((rule (kind name)
               (find name (entries-of-kind kind ledger) :key (lambda (e) (first (entry-payload e))))))
        (let ((e (rule 'axiom 'exists1-unfold)))
          (expect "EXISTS1-UNFOLD: ?x, ?u become ?BV1, ?BV2 in the form"
                  (equal (third (entry-payload e))
                         '(nil (.to (.exists1 ?bv1 ?a)
                                (.exists ?bv1 (.and ?a (.forall ?bv2 (.to (@subst ?bv1 ?bv2 ?a)
                                                                         (.eq ?bv2 ?bv1))))))))
                  t)
          (expect "... and in the side conditions, renamed together"
                  (equal (second (entry-payload e))
                         '((var? ?bv1) (var? ?bv2) (wff? ?a)
                           (@not-free-in? ?bv2 ?bv1) (@not-free-in? ?bv2 ?a)
                           (@subst-ok? ?bv1 ?bv2 ?a)))
                  t)
          (expect "... and the names as written are kept in the origin"
                  (equal (getf (cdr (entry-origin e)) :source-names) '((?x . ?bv1) (?u . ?bv2)))
                  t))))
    (expect "Gen: ?x, used free in the extra argument and bound in the result, is ?BV1 throughout"
            (equal (third (entry-payload (rule 'irule 'gen))) '((?a) (?bv1) :=> (.forall ?bv1 ?a)))
            t)
    (expect "III.1: the bound ?x is ?BV1; ?A and ?t keep their names"
            (equal (third (entry-payload (rule 'axiom 'iii.1)))
                   '((?t) (.to (.forall ?bv1 ?a) (@subst ?bv1 ?t ?a))))
            t)
    (expect "MP has no binder, nothing is renamed"
            (equal (third (entry-payload (rule 'irule 'mp))) '(((.to ?a ?b) ?a) nil :=> ?b))
            t))
  (expect "Attack: a rule that already uses ?BV1 for another variable -- must error"
          (handler-case
              (progn (bootstrap-kernel-from-spec
                      '((:axiom bad ((var? ?x) (term? ?bv1)) (nil (.forall ?x (.eq ?x ?bv1)))))
                      :ledger ledger)
                     :admitted)
            (error () :refused))
          :refused)
  (expect "a rule written with ?BVn names already is admitted unchanged"
          (let* ((l (bootstrap-kernel-from-spec
                     '((:axiom refl-all ((var? ?bv1)) (nil (.forall ?bv1 (.eq ?bv1 ?bv1)))))
                     :ledger ledger))
                 (e (find 'refl-all (entries-of-kind 'axiom l) :key (lambda (e) (first (entry-payload e))))))
            (equal (third (entry-payload e)) '(nil (.forall ?bv1 (.eq ?bv1 ?bv1)))))
          t)
  ledger)

(defun run-debruijn-self-tests ()
  (format t "~&--- de Bruijn (machine B) ---~%")
  (let ((ledger (fol-kernel)))
    (test-debruijn-conversion ledger)
    (test-debruijn-alpha-equivalence ledger)
    (test-debruijn-substitution ledger)
    (test-debruijn-fresh-variables ledger)
    (test-debruijn-schema-capture ledger)
    (test-rule-binder-names ledger)
    t))
