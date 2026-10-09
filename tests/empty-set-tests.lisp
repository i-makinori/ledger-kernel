;;;; empty-set-tests.lisp -- zf-library/01-empty-set.ledger and persistence
;;;; of DEFINE-FUNCTION-BY-DESCRIPTION
;;;; Part of the ledger-kernel/tests system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun zf-library-path (name)
  (asdf:system-relative-pathname :ledger-kernel (concatenate 'string "zf-library/" name)))

(defun zf-logic-ledger ()
  "ZF-LEDGER (the three .system files) + hilbert-library 01/02/03/05/06:
everything 01-empty-set.ledger is loaded on top of."
  (reduce (lambda (l f) (read-ledger-from-file (library-path f) :ledger l))
          '("01-propositional-core.ledger" "02-predicate-core.ledger"
            "03-equality-core.ledger" "05-classical-logic.ledger"
            "06-connectives.ledger")
          :initial-value (zf-ledger)))

(defun test-empty-set-library (ledger)
  "Loads 01-empty-set.ledger and checks its theorems and the definition
of (empty). Returns the extended ledger."
  (let ((ledger (read-ledger-from-file (zf-library-path "01-empty-set.ledger") :ledger ledger)))
    (expect "th-zf-empty-exists: exists y forall z not(z in y)"
            (check-k-proof '((0 (.exists v1 (.forall v2 (.neg (.in v2 v1)))) :th (th-zf-empty-exists)))
                           ledger) t)
    (expect "th-zf-empty-unique: two empty sets are equal"
            (check-k-proof '((0 (.forall v1 (.forall v3 (.to (.forall v2 (.neg (.in v2 v1)))
                                                              (.to (.forall v2 (.neg (.in v2 v3)))
                                                                   (.eq v1 v3)))))
                                :th (th-zf-empty-unique)))
                           ledger) t)
    (expect "(empty) is a term" (judgement? 'term? '(empty) ledger) t)
    (expect "(.in v0 (empty)) is a wff" (judgement? 'wff? '(.in v0 (empty)) ledger) t)
    (expect "EMPTY-DEF: forall z not(z in (empty))"
            (check-k-proof '((0 (.forall v2 (.neg (.in v2 (empty)))) :axiom (empty-def))) ledger) t)
    (expect "th-zf-not-in-empty: not(v0 in (empty))"
            (check-k-proof '((0 (.neg (.in v0 (empty))) :th (th-zf-not-in-empty))) ledger) t)
    (expect "Attack: 'v0 in (empty)' is not a theorem under th-zf-not-in-empty -- must reject"
            (check-k-proof '((0 (.in v0 (empty)) :th (th-zf-not-in-empty))) ledger) nil)
    (expect "Attack: EMPTY-DEF does not say (empty) has a member -- must reject"
            (check-k-proof '((0 (.exists v2 (.in v2 (empty))) :axiom (empty-def))) ledger) nil)
    (expect "Attack: redefining EMPTY -- must error"
            (handler-case
                (progn (define-function-by-description
                         ledger 'empty '() 'v1 'v3 '(.forall v2 (.neg (.in v2 v1)))
                         'th-zf-empty-exists 'th-zf-empty-unique)
                       :defined)
              (error () :refused))
            :refused)
    ledger))

(defun test-definition-persistence (ledger)
  "A ledger holding a DEFINE-FUNCTION-BY-DESCRIPTION definition survives
WRITE-LEDGER-TO-FILE / READ-LEDGER-FROM-FILE, and a tampered definition
command is refused on load."
  (let ((path "/tmp/ledger-kernel-self-test-definition.tmp")
        (bad-path "/tmp/ledger-kernel-self-test-definition-tampered.tmp"))
    (unwind-protect
         (let* ((commands (ledger-commands ledger))
                (def-cmd (find :define-function-by-description commands :key #'car)))
           (expect "LEDGER-COMMANDS emits the (empty) definition as a command"
                   (and def-cmd (eq (second def-cmd) 'empty)) t)
           (expect "... exactly once"
                   (count :define-function-by-description commands :key #'car)
                   1)
           (write-commands-to-file commands path)
           (expect "the reloaded ledger (from the .system base only) still proves not(v0 in (empty))"
                   (check-k-proof '((0 (.neg (.in v0 (empty))) :th (th-zf-not-in-empty)))
                                  (read-ledger-from-file path :ledger (zf-ledger)))
                   t)
           (write-commands-to-file
            (substitute (list :define-function-by-description 'empty '() 'v1 'v3
                              '(.forall v2 (.in v2 v1))   ; "the universal set" instead
                              'th-zf-empty-exists 'th-zf-empty-unique)
                        def-cmd commands)
            bad-path)
           (expect "Attack: a tampered definition command (wrong formula) is refused on load"
                   (handler-case (progn (read-ledger-from-file bad-path :ledger (zf-ledger)) :loaded)
                     (error () :refused))
                   :refused))
      (ignore-errors (delete-file path))
      (ignore-errors (delete-file bad-path)))
    ledger))

(defun run-empty-set-self-tests ()
  "zf-library/01-empty-set.ledger and persistence of function definitions."
  (let* ((ledger (zf-logic-ledger))
         (ledger (test-empty-set-library ledger))
         (ledger (test-definition-persistence ledger)))
    (declare (ignorable ledger))
    (format t "~%Empty-set self-tests complete.~%")))
