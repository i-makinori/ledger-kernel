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
        (expect "DOUBLE-DEF, proved by IOTA, gives DOUBLE(v0) = v0+v0"
                (check-k-proof '((0 (.eq (double v0) (+ v0 v0)) :th (double-def))) defined-ledger)
                t)
        (expect "... and at other arguments through :inst"
                (check-k-proof '((0 (.eq (double (s v3)) (+ (s v3) (s v3)))
                                    :th (double-def :inst ((v0 (s v3))))))
                               defined-ledger)
                t)
        (expect "a definition adds no axiom: (double v0) is the iota term"
                (and (= (length (entries-of-kind 'axiom defined-ledger))
                        (length (entries-of-kind 'axiom ledger)))
                     (equal (named->db '(double v0) defined-ledger)
                            (named->db '(.iota v1 (.eq v1 (+ v0 v0))) defined-ledger)))
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

(defun test-define-function-shape-attacks (ledger)
  "Attacks on DEFINE-FUNCTION-BY-DESCRIPTION whose cited theorems are
genuine, so only CHECK-DEFINITION-SHAPE stands between them and a
contradiction. A(y) := y = v1: with v1 an argument this defines the
identity; with v1 a free parameter, or with the name S, it would give
(S zero) = zero."
  (let* ((l (check-and-extend ledger 'th 'fd-ex
              '((0 (.eq v1 v1) :axiom (IV.1))
                (1 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1))) :axiom (III.3 v0 (.eq v0 v1) v1))
                (2 (.exists v0 (.eq v0 v1)) :ir (MP 1 0)))))
         (l (check-and-extend-by-deduction-direct l 'fd-u1 '(.eq v2 v1)
              '((0 (.eq v0 v1) :hyp nil)
                (1 (.eq v2 v1) :hyp nil)
                (2 (.to (.eq v2 v1) (.eq v1 v2)) :axiom (IV.3))
                (3 (.eq v1 v2) :ir (MP 2 1))
                (4 (.to (.eq v0 v1) (.to (.eq v1 v2) (.eq v0 v2))) :axiom (IV.4))
                (5 (.to (.eq v1 v2) (.eq v0 v2)) :ir (MP 4 0))
                (6 (.eq v0 v2) :ir (MP 5 3)))))
         (l (check-and-extend-by-deduction-direct l 'fd-u2 '(.eq v0 v1)
              '((0 (.eq v0 v1) :hyp nil)
                (1 (.to (.eq v2 v1) (.eq v0 v2)) :th-ded (fd-u1 0)))))
         (uniq '(.forall v0 (.forall v2 (.to (.eq v0 v1) (.to (.eq v2 v1) (.eq v0 v2))))))
         (l (check-and-extend l 'th 'fd-un
              `((0 (.to (.eq v0 v1) (.to (.eq v2 v1) (.eq v0 v2))) :th-ded (fd-u2))
                (1 (.forall v2 (.to (.eq v0 v1) (.to (.eq v2 v1) (.eq v0 v2)))) :ir (Gen 0 v2))
                (2 ,uniq :ir (Gen 1 v0)))))
         (l (check-and-extend l 'th 'fd-ex-all
              '((0 (.exists v0 (.eq v0 v1)) :th (fd-ex))
                (1 (.forall v1 (.exists v0 (.eq v0 v1))) :ir (Gen 0 v1)))))
         (l (check-and-extend l 'th 'fd-un-all
              `((0 ,uniq :th (fd-un))
                (1 (.forall v1 ,uniq) :ir (Gen 0 v1))))))
    (flet ((refused-p (thunk)
             (handler-case (progn (funcall thunk) nil) (error () t))))
      (expect "the identity, A(v1, y) := y = v1 with v1 an argument, is still admitted"
              (not (refused-p (lambda ()
                                (define-function-by-description
                                  l 'fd-ident '(v1) 'v0 'v2 '(.eq v0 v1) 'fd-ex-all 'fd-un-all))))
              t)
      (expect "Attack: a free parameter v1 in A (c = v1 for every v1, so 0 = S 0) -- must error"
              (refused-p (lambda ()
                           (define-function-by-description
                             l 'fd-c '() 'v0 'v2 '(.eq v0 v1) 'fd-ex 'fd-un)))
              t)
      (expect "Attack: redefining the existing function symbol S as the identity -- must error"
              (refused-p (lambda ()
                           (define-function-by-description
                             l 's '(v1) 'v0 'v2 '(.eq v0 v1) 'fd-ex-all 'fd-un-all)))
              t)
      (expect "Attack: defining the same new symbol twice -- must error"
              (refused-p (lambda ()
                           (let ((l2 (define-function-by-description
                                       l 'fd-twice '(v1) 'v0 'v2 '(.eq v0 v1) 'fd-ex-all 'fd-un-all)))
                             (define-function-by-description
                               l2 'fd-twice '(v1) 'v0 'v2 '(.eq v0 v1) 'fd-ex-all 'fd-un-all))))
              t)
      (expect "Attack: Y-VAR equal to an argument -- must error"
              (refused-p (lambda () (check-definition-shape l 'fd-x '(v1) 'v1 'v2 '(.eq v1 v1))))
              t)
      (expect "Attack: Y2-VAR occurring in A -- must error"
              (refused-p (lambda () (check-definition-shape l 'fd-x '(v1) 'v0 'v2
                                                            '(.forall v3 (.to (.eq v3 v2) (.eq v0 v1))))))
              t)
      (expect "Attack: A binding an argument variable inside it -- must error"
              (refused-p (lambda () (check-definition-shape l 'fd-x '(v1) 'v0 'v2
                                                            '(.to (.forall v1 (.eq v1 v1)) (.eq v0 v1)))))
              t)
      (expect "Attack: declaring NIL as an atomic wff -- must error"
              (refused-p (lambda () (declare-atomic-wff-symbol l nil)))
              t)
      (expect "Attack: declaring the keyword :BV as a variable -- must error"
              (refused-p (lambda () (declare-variable-symbol l :bv)))
              t))))

(defun run-function-definition-self-tests ()
  "Section 22: DEFINE-FUNCTION-BY-DESCRIPTION -- the DOUBLE worked
example (existence, uniqueness, definition, and using the defined
function directly) plus two prerequisite-mismatch attack tests."
  (let* ((ledger (fol-kernel :arithmetic t))
         (ledger (test-define-function-by-description ledger)))
    (declare (ignorable ledger))
    (test-define-function-shape-attacks (fol-kernel :arithmetic t))
    (format t "~%Function-definition self-tests complete.~%")))
