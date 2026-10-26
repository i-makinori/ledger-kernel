;;;; contradiction-tests.lisp -- (:contradiction ...) and its detection
;;;; Part of the ledger-kernel/tests system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; A system says what a contradiction is; the kernel reports a ledger
;;; that reaches one. These tests make a system inconsistent on purpose,
;;; with an axiom "every formula", and watch for the report.

(defun admit-quietly (thunk)
  "(VALUES ledger warnings): call THUNK, collecting CONTRADICTION-DETECTED
warnings instead of printing them."
  (let ((warnings nil))
    (values (handler-bind ((contradiction-detected
                             (lambda (w) (push w warnings) (muffle-warning w))))
              (funcall thunk))
            (nreverse warnings))))

(defun test-contradiction-detection ()
  (let ((base (fol-kernel)))
    (expect "the base system declares A and not-A as its contradiction"
            (mapcar (lambda (e) (first (entry-payload e))) (entries-of-kind 'contradiction-form base))
            '(a-and-not-a))
    (expect "the classical lemmas of 01 and 05 reach no contradiction"
            (ledger-contradictions (classical-logic-ledger base))
            nil)
    (let* ((bad (bootstrap-kernel-from-spec '((:axiom EVERYTHING ((wff? ?A)) (nil ?A))) :ledger base))
           (l1 (check-and-extend bad 'th 'th-eq '((0 (.eq v0 v0) :axiom (EVERYTHING))))))
      (expect "one theorem alone is no contradiction"
              (ledger-contradictions l1) nil)
      (multiple-value-bind (l2 warnings)
          (admit-quietly (lambda ()
                           (check-and-extend l1 'th 'th-neq '((0 (.neg (.eq v0 v0)) :axiom (EVERYTHING))))))
        (expect "proving its negation too is reported: (A-AND-NOT-A (TH-EQ TH-NEQ))"
                (equal (ledger-contradictions l2) '((a-and-not-a (th-eq th-neq))))
                t)
        (expect "... with a CONTRADICTION-DETECTED warning"
                (and (= (length warnings) 1)
                     (equal (contradiction-theorems (first warnings)) '(th-eq th-neq)))
                t)
        (expect "... and the theorem is still admitted"
                (check-k-proof '((0 (.neg (.eq v0 v0)) :th (th-neq))) l2) t)
        (expect "the report is not saved: replaying the ledger finds it again"
                (equal (ledger-contradictions
                        (admit-quietly (lambda () (ledger-from-commands (ledger-commands l2) :ledger bad))))
                       '((a-and-not-a (th-eq th-neq))))
                t))
      (expect "found in either order, and up to the names of bound variables"
              (equal (ledger-contradictions
                      (admit-quietly
                       (lambda ()
                         (let ((l (check-and-extend bad 'th 'th-n
                                                    '((0 (.neg (.forall v1 (.eq v1 v1))) :axiom (EVERYTHING))))))
                           (check-and-extend l 'th 'th-p '((0 (.forall v2 (.eq v2 v2)) :axiom (EVERYTHING))))))))
                     '((a-and-not-a (th-p th-n))))
              t)
      (expect "a closed TH-DED counts: H -> H and not (H -> H)"
              (equal (ledger-contradictions
                      (admit-quietly
                       (lambda ()
                         (let ((l (check-and-extend-by-deduction-direct bad 'th-id '(.eq v0 v1)
                                                                       '((0 (.eq v0 v1) :hyp nil)))))
                           (check-and-extend l 'th 'th-not-id
                                             '((0 (.neg (.to (.eq v0 v1) (.eq v0 v1))) :axiom (EVERYTHING))))))))
                     '((a-and-not-a (th-id th-not-id))))
              t)
      (expect "a theorem still resting on a hypothesis does not count"
              (ledger-contradictions
               (admit-quietly
                (lambda ()
                  (check-and-extend l1 'th 'th-neq-hyp
                                    '((0 (.neg (.eq v0 v0)) :hyp nil))))))
              nil)))
  (let* ((bare (bootstrap-kernel-from-spec
                '((:wff-formation wff_to? ((wff? ?A) (wff? ?B)) (wff? (.to ?A ?B)))
                  (:axiom EVERYTHING ((wff? ?A)) (nil ?A)))))
         (l (check-and-extend bare 'th 'th-a '((0 A :axiom (EVERYTHING)))))
         (l (check-and-extend l 'th 'th-h '((0 H :axiom (EVERYTHING))))))
    (expect "a system that declares no contradiction has nothing to report"
            (ledger-contradictions l) nil)
    (let* ((bot (bootstrap-kernel-from-spec '((:contradiction falsum () (H))) :ledger bare)))
      (expect "a one-formula contradiction (a falsum H): proving H is reported"
              (equal (ledger-contradictions
                      (admit-quietly (lambda () (check-and-extend bot 'th 'th-h '((0 H :axiom (EVERYTHING)))))))
                     '((falsum (th-h))))
              t)
      (expect "... and proving A is not"
              (ledger-contradictions (check-and-extend bot 'th 'th-a '((0 A :axiom (EVERYTHING)))))
              nil)
      (expect "Attack: declaring the same contradiction twice -- must error"
              (handler-case (progn (bootstrap-kernel-from-spec '((:contradiction falsum () (A))) :ledger bot)
                                   :admitted)
                (error () :refused))
              :refused))))

(defun run-contradiction-self-tests ()
  "Declared contradictions and their detection."
  (test-contradiction-detection)
  (format t "~%Contradiction self-tests complete.~%"))
