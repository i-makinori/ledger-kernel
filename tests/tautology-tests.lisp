;;;; tautology-tests.lisp -- Section 15: PROVE-TAUTOLOGY tests
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun test-prove-tautology (ledger)
  (let ((hs (list '.to (list '.to 'b 'c) (list '.to (list '.to 'a 'b) (list '.to 'a 'c))))
        (peirce (list '.to (list '.to (list '.to 'a 'b) 'a) 'a))
        (contra (list '.to (list '.to 'a 'b) (list '.to (list '.neg 'b) (list '.neg 'a)))))
    (let ((ledger (prove-tautology ledger hs 'th-hyp-syll-auto)))
      (expect "PROVE-TAUTOLOGY re-derives hypothetical syllogism's tautology automatically"
              (check-k-proof `((0 ,hs :th (th-hyp-syll-auto))) ledger) t)
      (let ((ledger (prove-tautology ledger peirce 'th-peirce-auto)))
        (expect "PROVE-TAUTOLOGY proves Peirce's law, ((A->B)->A)->A, automatically"
                (check-k-proof `((0 ,peirce :th (th-peirce-auto))) ledger) t)
        (let ((ledger (prove-tautology ledger contra 'th-contra-auto)))
          (expect "PROVE-TAUTOLOGY proves contraposition, (A->B)->(not-B->not-A), automatically"
                  (check-k-proof `((0 ,contra :th (th-contra-auto))) ledger) t)
          (expect "PROVE-TAUTOLOGY refuses a genuine non-tautology (A->B alone)"
                  (handler-case (progn (prove-tautology ledger '(.to a b) 'th-bad-auto) :admitted)
                    (error () :refused))
                  :refused)
          ledger)))))

(defun run-tactics-self-tests ()
  "As RUN-SELF-TESTS, but exercising PROVE-TAUTOLOGY on top of a ledger
that already carries the classical lemmas -- Section 15."
  (let* ((ledger (bootstrap-kernel))
         (ledger (test-classical-logic ledger))
         (ledger (test-prove-tautology ledger)))
    (declare (ignorable ledger))
    (format t "~%Tactics self-tests complete.~%")))
