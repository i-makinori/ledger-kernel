;;;; _backup_tautology-tests.lisp -- BACKUP (not loaded by any ASDF system)
;;;;
;;;; The PROVE-TAUTOLOGY tests, removed with _backup_tautology.lisp on
;;;; 2026-10-09 (see that file for why and how to restore). Below: the
;;;; original tests/tautology-tests.lisp, then the PROVE-TAUTOLOGY tests
;;;; taken out of tests/connectives-tests.lisp and tests/empty-set-tests.lisp.
;;;;
;;;; ---------------------------------------------------------------------

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
  (let* ((ledger (fol-kernel))
         (ledger (test-classical-logic ledger))
         (ledger (test-prove-tautology ledger)))
    (declare (ignorable ledger))
    (format t "~%Tactics self-tests complete.~%")))

;;; --- Moved from tests/connectives-tests.lisp ---------------------------

(defun test-prove-tautology-with-connectives (ledger)
  "PROVE-TAUTOLOGY sees through .AND/.OR/.IFF, refuses non-tautologies,
and names its intermediate entries so the ledger survives a file round
trip."
  (let* ((trans '(.to (.iff a b) (.to (.iff b c) (.iff a c))))
         (demorgan '(.iff (.neg (.and a b)) (.or (.neg a) (.neg b))))
         (ledger (prove-tautology ledger trans 'th-test-iff-trans))
         (ledger (prove-tautology ledger demorgan 'th-test-demorgan)))
    (expect "PROVE-TAUTOLOGY: iff is transitive"
            (check-k-proof `((0 ,trans :th (th-test-iff-trans))) ledger) t)
    (expect "PROVE-TAUTOLOGY: De Morgan, not(A and B) iff (not A or not B)"
            (check-k-proof `((0 ,demorgan :th (th-test-demorgan))) ledger) t)
    (expect "PROVE-TAUTOLOGY result is schematic: iff-transitivity at compound formulas"
            (check-k-proof '((0 (.to (.iff (.eq v0 v1) (.eq v1 v0))
                                     (.to (.iff (.eq v1 v0) (.and a b))
                                          (.iff (.eq v0 v1) (.and a b))))
                                :th (th-test-iff-trans)))
                           ledger) t)
    (expect "PROVE-TAUTOLOGY refuses (A or B) -> A"
            (handler-case (progn (prove-tautology ledger '(.to (.or a b) a) 'th-test-bad) :admitted)
              (error () :refused))
            :refused)
    (expect "PROVE-TAUTOLOGY refuses (A iff B) -> (A and B)"
            (handler-case (progn (prove-tautology ledger '(.to (.iff a b) (.and a b)) 'th-test-bad2) :admitted)
              (error () :refused))
            :refused)
    (expect "intermediate entries get interned names (TH-TEST-IFF-TRANS.T1, .CONTRA)"
            (and (derived-rule-name-taken-p (find-symbol "TH-TEST-IFF-TRANS.T1" :ledger-kernel) ledger)
                 (derived-rule-name-taken-p (find-symbol "TH-TEST-IFF-TRANS.CONTRA" :ledger-kernel) ledger))
            t)
    (let ((path "/tmp/ledger-kernel-self-test-tautology.tmp"))
      (unwind-protect
           (expect "a ledger built by PROVE-TAUTOLOGY round-trips through a file"
                   (let ((reloaded (progn (write-ledger-to-file ledger path)
                                          (read-ledger-from-file path :ledger (connectives-ledger)))))
                     (check-k-proof `((0 ,demorgan :th (th-test-demorgan))) reloaded))
                   t)
        (ignore-errors (delete-file path))))
    ledger))


;;; --- Moved from tests/empty-set-tests.lisp -----------------------------

(defun test-tautology-over-set-atoms (ledger)
  "PROVE-TAUTOLOGY with compound atoms such as (.in v0 v1)."
  (let* ((target '(.to (.in v0 v1) (.or (.in v0 v1) (.forall v2 (.in v2 v0)))))
         (ledger (prove-tautology ledger target 'th-test-in-or)))
    (expect "PROVE-TAUTOLOGY over set-theoretic atoms: x in y -> (x in y or forall z. z in x)"
            (check-k-proof `((0 ,target :th (th-test-in-or))) ledger) t)
    ledger))

