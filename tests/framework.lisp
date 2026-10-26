;;;; framework.lisp -- minimal self-test framework
;;;; Part of the ledger-kernel/tests system (see ledger-kernel.asd).
;;;;
;;;; The self tests live in the LEDGER-KERNEL package itself (they
;;;; exercise internal, unexported functions), but only in the separate
;;;; LEDGER-KERNEL/TESTS system, so loading the kernel alone never defines
;;;; or runs any of them.
;;;;
;;;; The kernel proper keeps all of its state in explicit arguments; the
;;;; one special variable below belongs to the test harness only and just
;;;; tallies results so that ASDF:TEST-SYSTEM can report failure.

(in-package :ledger-kernel)

(defvar *expect-results* nil
  "While RUN-ALL-SELF-TESTS is running, a cons (PASSED . FAILED) that
EXPECT increments. NIL outside of it, in which case EXPECT only prints.")

(defun expect (label got expected)
  "Print a [pass]/[FAIL] line for LABEL, comparing GOT and EXPECTED as
generalized booleans. Returns T on pass, NIL on failure."
  (let ((ok (eql (not (null got)) (not (null expected)))))
    (when *expect-results*
      (if ok
          (incf (car *expect-results*))
          (incf (cdr *expect-results*))))
    (format t "[~:[FAIL~;pass~]] ~A~%" ok label)
    ok))

(defun library-path (name)
  "Absolute pathname of NAME inside this system's hilbert-library/
directory, so the tests do not depend on the current working directory."
  (asdf:system-relative-pathname :ledger-kernel
                                 (concatenate 'string "hilbert-library/" name)))

(defparameter *base-system-files*
  '("00-fol-language.system" "00-classical-logic.system"
    "00-equality.system" "00-description.system")
  "The standard base system, layer by layer: language, logic, equality,
descriptions (hilbert-library/).")

(defun base-system-spec ()
  "The directives of *BASE-SYSTEM-FILES*, in loading order."
  (loop for f in *base-system-files*
        append (read-system-spec-from-file (library-path f))))

(defun base-system-ledger ()
  "A fresh ledger with *BASE-SYSTEM-FILES* loaded."
  (reduce (lambda (l f) (bootstrap-kernel-from-spec-file (library-path f) :ledger l))
          *base-system-files* :initial-value nil))

(defun fol-kernel (&key arithmetic)
  "A fresh ledger holding classical first-order logic with equality, loaded
from *BASE-SYSTEM-FILES* (and, with ARITHMETIC, 00-peano-arithmetic.system
on top). Seed vocabulary: atomic symbols A-H, variables v0-v5."
  (let ((ledger (base-system-ledger)))
    (if arithmetic
        (bootstrap-kernel-from-spec-file (library-path "00-peano-arithmetic.system") :ledger ledger)
        ledger)))
