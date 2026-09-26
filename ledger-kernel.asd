;;;; ledger-kernel.asd

(defsystem "ledger-kernel"
  :description "A minimal Hilbert-style proof checker built on an append-only ledger."
  :author "i-makinori"
  :version "0.1.0"
  :pathname "src/"
  :serial t
  :components ((:file "package")
               (:file "pattern")
               (:file "treap")
               (:file "ledger")
               (:file "side-conditions")
               (:file "meta")
               (:file "judgement")
               (:file "k-proof")
               (:file "bootstrap")
               (:file "persistence")
               (:file "deduction")
               (:file "tautology")
               (:file "alpha-conversion")
               (:file "system-spec")
               (:file "inductive")
               (:file "function-definition"))
  :in-order-to ((test-op (test-op "ledger-kernel/tests"))))

(defsystem "ledger-kernel/tests"
  :description "Self tests for ledger-kernel."
  :depends-on ("ledger-kernel")
  :pathname "tests/"
  :serial t
  :components ((:file "framework")
               (:file "core-tests")
               (:file "deduction-tests")
               (:file "persistence-tests")
               (:file "arithmetic-tests")
               (:file "classical-logic-tests")
               (:file "tautology-tests")
               (:file "alpha-conversion-tests")
               (:file "memoization-tests")
               (:file "system-spec-tests")
               (:file "iota-tests")
               (:file "inductive-tests")
               (:file "exists-elim-tests")
               (:file "function-definition-tests")
               (:file "zf-tests")
               (:file "run"))
  :perform (test-op (o c)
             (unless (uiop:symbol-call :ledger-kernel :run-all-self-tests)
               (error "ledger-kernel self-tests failed."))))
