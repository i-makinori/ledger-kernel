;;;; memoization-tests.lisp -- Section 17: differential check for DERIVED-entry memoization
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 17. Differential check for the optional DERIVED-entry memoization
;;;     layer (see the "Optional memoization" subsection right before
;;;     TRY-DERIVED-ENTRY, Section 6)
;;; ---------------------------------------------------------------------
;;;
;;; Confirms VERIFY-DERIVED-INSTANTIATION's cache changes no verdict --
;;; only how fast it's reached -- on exactly the pathological citation
;;; pattern that motivated it: a "doubling chain" of TH entries, each of
;;; whose 2-line proof cites the previous THEOREM twice (redundantly),
;;; which costs 2^depth work to verify without memoization even though
;;; every formula involved is purely propositional (.to A (.to B A)) via
;;; a single axiom, with no quantifiers and no side conditions anywhere
;;; -- demonstrating that the re-verification cost this section addresses
;;; comes from DERIVED-entry citation, not from side-condition checking
;;; (see the README's discussion of this distinction).

(defun build-doubling-chain (n &optional (prefix "THDBL"))
  "N TH entries T_0..T_(n-1), all proving (.to A (.to B A)) via axiom
II.1; T_0 cites the axiom directly, and every T_i (i>0) cites T_(i-1)
TWICE (two separate, redundant lines) -- the worst case for a checker
with no memoization."
  (let ((ledger (fol-kernel))
        (concl '(.to A (.to B A))))
    (setf ledger (check-and-extend ledger 'th (intern (format nil "~A0" prefix))
                                    (list (list 0 concl :axiom (list 'II.1)))))
    (loop for i from 1 below n
          for prev = (intern (format nil "~A~D" prefix (1- i)))
          do (setf ledger
                   (check-and-extend ledger 'th (intern (format nil "~A~D" prefix i))
                                      (list (list 0 concl :th (list prev))
                                            (list 1 concl :th (list prev))))))
    ledger))

(defun test-derived-entry-memoization ()
  "Builds the doubling chain at a depth deep enough to matter but
shallow enough that a memoization-OFF run still finishes in a self-
test's time budget, checks it both ways, and confirms IDENTICAL verdicts
-- the cache changes nothing about what is accepted. Then pushes
memoization ON alone to a depth (2^60 worth of naive work) that would be
entirely infeasible without it, to demonstrate the actual point."
  (disable-derived-entry-memoization)
  (let* ((depth 16)
         (ledger (build-doubling-chain depth))
         (goal (list (list 0 '(.to A (.to B A)) :th (list (intern (format nil "THDBL~D" (1- depth)))))))
         (t0 (get-internal-real-time))
         (verdict-off (check-k-proof goal ledger))
         (t1 (get-internal-real-time)))
    (format t "  [memo off] doubling-chain depth ~D: ~A in ~,3Fs~%"
            depth verdict-off (/ (- t1 t0) (float internal-time-units-per-second)))
    (enable-derived-entry-memoization)
    (let* ((ledger2 (build-doubling-chain depth "THDBL2"))
           (goal2 (list (list 0 '(.to A (.to B A)) :th (list (intern (format nil "THDBL2~D" (1- depth)))))))
           (t2 (get-internal-real-time))
           (verdict-on (check-k-proof goal2 ledger2))
           (t3 (get-internal-real-time)))
      (format t "  [memo on ] doubling-chain depth ~D: ~A in ~,3Fs~%"
              depth verdict-on (/ (- t3 t2) (float internal-time-units-per-second)))
      (expect "memoization changes no verdict: same doubling-chain, on vs off"
              (eq verdict-off verdict-on) t)
      (expect "memoization ON: the doubling-chain checks out (T)" verdict-on t))
    (reset-derived-entry-memoization)
    (let* ((deep 60)
           (ledger3 (build-doubling-chain deep "THDBL3"))
           (goal3 (list (list 0 '(.to A (.to B A)) :th (list (intern (format nil "THDBL3~D" (1- deep)))))))
           (t4 (get-internal-real-time))
           (verdict-deep (check-k-proof goal3 ledger3))
           (t5 (get-internal-real-time)))
      (format t "  [memo on ] doubling-chain depth ~D (2^~D work if unmemoized): ~A in ~,3Fs~%"
              deep deep verdict-deep (/ (- t5 t4) (float internal-time-units-per-second)))
      (expect "memoization ON: a depth utterly infeasible without it still checks out (T)" verdict-deep t))
    (disable-derived-entry-memoization)))

(defun test-memoization-across-vocabulary-branches ()
  "Two ledgers share TH-IDENTITY but declare KK differently afterwards:
as a variable, (.eq kk kk) is a wff; as an atomic wff, it is not. A
verdict cached in one branch must not be reused in the other."
  (let* ((base (check-and-extend-by-deduction-direct (fol-kernel) 'th-identity 'a '((0 a :hyp nil))))
         (as-var (declare-variable-symbol base 'kk))
         (as-atom (declare-atomic-wff-symbol base 'kk))
         (line '((0 (.to (.eq kk kk) (.eq kk kk)) :th-ded (th-identity)))))
    (enable-derived-entry-memoization)
    (unwind-protect
         (progn
           (expect "memoized: the citation holds where kk is a variable"
                   (check-k-proof line as-var) t)
           (expect "Attack: ... and that cached verdict is not reused where kk is an atomic wff"
                   (check-k-proof line as-atom) nil))
      (disable-derived-entry-memoization))))

(defun run-derived-entry-memoization-self-tests ()
  "As RUN-SELF-TESTS, but exercising the optional memoization layer --
Section 17. Leaves memoization OFF when done, so it never silently
changes behaviour for anything that runs after it (including every other
RUN-*-SELF-TESTS call in this same trailing auto-run form)."
  (test-derived-entry-memoization)
  (test-memoization-across-vocabulary-branches)
  (format t "~%Derived-entry memoization self-tests complete.~%"))
