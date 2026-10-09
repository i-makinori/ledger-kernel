;;;; run.lisp -- entry point that runs every self-test suite
;;;; Part of the ledger-kernel/tests system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun run-all-self-tests ()
  "Run every self-test suite in order. Prints one [pass]/[FAIL] line per
check and a final summary. Returns T if every check passed, NIL otherwise
(as a second value, the list (PASSED FAILED))."
  (let ((*expect-results* (cons 0 0)))
    (run-self-tests)
    (run-classical-logic-self-tests)
    (run-derived-entry-memoization-self-tests)
    (run-iota-self-tests)
    (run-exists-elim-self-tests)
    (run-function-definition-self-tests)
    (run-connectives-self-tests)
    (run-zf-self-tests)
    (run-empty-set-self-tests)
    (run-predicate-schema-self-tests)
    (run-peano-library-self-tests)
    (run-debruijn-self-tests)
    (destructuring-bind (passed . failed) *expect-results*
      (format t "~%~D/~D self-tests passed~:[, ~D FAILED~;~*~].~%"
              passed (+ passed failed) (zerop failed) failed)
      (values (zerop failed) (list passed failed)))))
