;;;; function-definition-tests.lisp -- Section 22: DEFINE-FUNCTION-BY-DESCRIPTION tests
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun test-define-function-by-description (ledger)
  "Worked example: DOUBLE(x) := the y such that y = x+x. Proves EXISTENCE
(trivially, y:=x+x itself witnesses it, via III.3) and UNIQUENESS
(symmetry/transitivity, the exact same multi-step deduction-theorem-direct
chaining pattern as Section 19's own uniq-full) as ordinary, independent
theorems first -- DEFINE-FUNCTION-BY-DESCRIPTION never sees a single
IOTA/EXISTS-ELIM step, only their FINAL closed conclusions -- then defines
DOUBLE and confirms the defining axiom makes it behave exactly as
specified, plus attack tests for both prerequisite-mismatch failure
modes."
  (let* ((exists-proof '((0 (.eq (+ v0 v0) (+ v0 v0)) :axiom (IV.1))
                          (1 (.to (.eq (+ v0 v0) (+ v0 v0)) (.exists v1 (.eq v1 (+ v0 v0)))) :axiom (III.3 v1 (.eq v1 (+ v0 v0)) (+ v0 v0)))
                          (2 (.exists v1 (.eq v1 (+ v0 v0))) :ir (MP 1 0))
                          (3 (.forall v0 (.exists v1 (.eq v1 (+ v0 v0)))) :ir (Gen 2 v0))))
         (ledger (check-and-extend ledger 'th 'th-double-exists exists-proof)))
    (expect "existence: forall v0 (exists v1 (v1=v0+v0)) is a real ledger theorem"
            (check-k-proof '((0 (.forall v0 (.exists v1 (.eq v1 (+ v0 v0)))) :th (th-double-exists))) ledger)
            t)
    (let* ((inner '((0 (.eq v1 (+ v0 v0)) :hyp nil)
                     (1 (.eq v2 (+ v0 v0)) :hyp nil)
                     (2 (.to (.eq v2 (+ v0 v0)) (.eq (+ v0 v0) v2)) :axiom (IV.3))
                     (3 (.eq (+ v0 v0) v2) :ir (MP 2 1))
                     (4 (.to (.eq v1 (+ v0 v0)) (.to (.eq (+ v0 v0) v2) (.eq v1 v2))) :axiom (IV.4))
                     (5 (.to (.eq (+ v0 v0) v2) (.eq v1 v2)) :ir (MP 4 0))
                     (6 (.eq v1 v2) :ir (MP 5 3))))
           (ledger (check-and-extend-by-deduction-direct ledger 'dbl-uniq-step1 '(.eq v2 (+ v0 v0)) inner))
           (step2 '((0 (.eq v1 (+ v0 v0)) :hyp nil)
                    (1 (.to (.eq v2 (+ v0 v0)) (.eq v1 v2)) :th-ded (dbl-uniq-step1 0))))
           (ledger (check-and-extend-by-deduction-direct ledger 'dbl-uniq-step2 '(.eq v1 (+ v0 v0)) step2))
           (ledger (check-and-extend ledger 'th 'dbl-uniq-gen-v2
                                      '((0 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2))) :th-ded (dbl-uniq-step2))
                                        (1 (.forall v2 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2)))) :ir (Gen 0 v2)))))
           (ledger (check-and-extend ledger 'th 'dbl-uniq-gen-v1
                                      '((0 (.forall v2 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2)))) :th (dbl-uniq-gen-v2))
                                        (1 (.forall v1 (.forall v2 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2))))) :ir (Gen 0 v1)))))
           (ledger (check-and-extend ledger 'th 'th-double-uniqueness
                                      '((0 (.forall v1 (.forall v2 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2))))) :th (dbl-uniq-gen-v1))
                                        (1 (.forall v0 (.forall v1 (.forall v2 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2)))))) :ir (Gen 0 v0))))))
      (expect "uniqueness: forall v0,v1,v2 (v1=v0+v0 -> (v2=v0+v0 -> v1=v2)) is a real ledger theorem"
              (check-k-proof '((0 (.forall v0 (.forall v1 (.forall v2 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2))))))
                                  :th (th-double-uniqueness)))
                              ledger)
              t)
      (let ((defined-ledger (define-function-by-description
                              ledger 'double '(v0) 'v1 'v2 '(.eq v1 (+ v0 v0))
                              'th-double-exists 'th-double-uniqueness)))
        (expect "(double v0) is a term after DEFINE-FUNCTION-BY-DESCRIPTION"
                (judgement? 'term? '(double v0) defined-ledger) t)
        (expect "the defining axiom makes DOUBLE(v0) = v0+v0 usable directly, no IOTA in sight"
                (check-k-proof '((0 (.eq (double v0) (+ v0 v0)) :axiom (double-def))) defined-ledger)
                t)
        (expect "Attack: EXISTENCE-NAME argument swapped for UNIQUENESS-NAME -- must error, not silently define"
                (handler-case (progn (define-function-by-description
                                       ledger 'double2 '(v0) 'v1 'v2 '(.eq v1 (+ v0 v0))
                                       'th-double-uniqueness 'th-double-exists)
                                      :no-error)
                              (error () :caught-error))
                :caught-error)
        (expect "Attack: a WRONG defining formula (mismatched with the actual proven theorems) -- must error"
                (handler-case (progn (define-function-by-description
                                       ledger 'double3 '(v0) 'v1 'v2 '(.eq v1 (+ v0 zero))
                                       'th-double-exists 'th-double-uniqueness)
                                      :no-error)
                              (error () :caught-error))
                :caught-error)
        defined-ledger))))

(defun run-function-definition-self-tests ()
  "Section 22: DEFINE-FUNCTION-BY-DESCRIPTION -- the DOUBLE worked
example (existence, uniqueness, definition, and using the defined
function directly) plus two prerequisite-mismatch attack tests."
  (let* ((ledger (bootstrap-kernel :arithmetic t))
         (ledger (test-define-function-by-description ledger)))
    (declare (ignorable ledger))
    (format t "~%Function-definition self-tests complete.~%")))
