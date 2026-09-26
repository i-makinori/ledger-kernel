;;;; system-spec-tests.lisp -- Section 18: system-spec tests
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun test-bootstrap-from-spec ()
  "Loads hilbert-library/00-classical-fol-equality.system (the exact same
formation rules / MP / Gen / II.1-4 / III.1-2 / IV.1-4 BOOTSTRAP-KERNEL's
own Lisp source hardcodes, now expressed purely as data) chained with
hilbert-library/00-peano-arithmetic.system (likewise mirroring
BOOTSTRAP-PEANO-VOCABULARY/BOOTSTRAP-PEANO-AXIOMS), and confirms the
result is the SAME ledger BOOTSTRAP-KERNEL's hardcoded :ARITHMETIC T path
produces: not just \"behaves the same on a few checks\", but entry for
entry, the same (KIND PAYLOAD ORIGIN) content in the same K order (a
straight EQUALP of the two LEDGER structs would NOT be meaningful here,
and deliberately isn't what's checked -- TREAP-INSERT assigns each node a
RANDOM balancing priority, so two ledgers built by separate sequences of
inserts, however identical their logical content, almost certainly end
up as different tree SHAPES internally; comparing entries in K-order
instead checks exactly the thing that actually matters here and nothing
about incidental internal representation). Then, for good measure,
re-runs a representative slice of Section 9's own hardcoded-bootstrap
self-test battery against the spec-loaded ledger unchanged -- the very
same TEST-* functions, looking for the very same things, now aimed at a
ledger this file's author never hand-wrote a single AXIOM/IRULE form
for."
  (let ((hardcoded (bootstrap-kernel :arithmetic t))
        (from-spec (bootstrap-kernel-from-spec-file
                    (library-path "00-peano-arithmetic.system")
                    :ledger (bootstrap-kernel-from-spec-file
                             (library-path "00-classical-fol-equality.system")))))
    (flet ((entry-content-list (ledger)
             (mapcar (lambda (e) (list (entry-kind e) (entry-payload e) (entry-origin e)))
                     (treap-values-below (ledger-all ledger) (ledger-bound ledger)))))
      (expect "a system-spec-loaded ledger has IDENTICAL entries, in the identical order, to BOOTSTRAP-KERNEL's own hardcoded one"
              (equal (entry-content-list hardcoded) (entry-content-list from-spec)) t))
    (let* ((ledger from-spec)
           (ledger (test-basic-formation ledger))
           (ledger (test-axiom-and-inference ledger))
           (ledger (test-vacuous-gen-and-bad-ith ledger))
           (ledger (test-admit-primitive-closed ledger))
           (ledger (test-sigma-growth ledger))
           (ledger (test-abbrev-usage ledger))
           (ledger (test-axiom-iii1 ledger))
           (ledger (test-hyp-wellformedness ledger))
           (ledger (test-exists-formation ledger))
           (ledger (test-negation-and-new-axioms ledger))
           (ledger (test-name-uniqueness ledger))
           (ledger (test-deduction-theorem ledger))
           (ledger (test-deduction-theorem-direct ledger))
           (ledger (test-equality-axioms ledger))
           (ledger (test-peano-axioms ledger))
           (ledger (test-peano-induction-proof ledger)))
      (declare (ignorable ledger))
      ledger)))

(defun run-bootstrap-from-spec-self-tests ()
  "As RUN-SELF-TESTS, but against a ledger built entirely from the
system-spec files -- Section 18."
  (test-bootstrap-from-spec)
  (format t "~%Bootstrap-from-spec self-tests complete.~%"))
