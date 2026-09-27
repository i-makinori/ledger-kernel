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
               (:file "iota-tests")
               (:file "inductive-tests")
               (:file "exists-elim-tests")
               (:file "function-definition-tests")
               (:file "connectives-tests")
               (:file "zf-tests")
               (:file "empty-set-tests")
               (:file "predicate-schema-tests")
               (:file "run"))
  :perform (test-op (o c)
             (unless (uiop:symbol-call :ledger-kernel :run-all-self-tests)
               (error "ledger-kernel self-tests failed."))))

(defsystem "ledger-kernel/web"
  :description "Web UI for browsing ledgers and checking proofs (outside the trusted kernel)."
  :depends-on ("ledger-kernel" "hunchentoot" "yason")
  :pathname "web/"
  :serial t
  :components ((:file "package")
               (:file "render")
               (:file "worlds")
               (:file "deps")
               (:file "api")
               (:file "server")
               (:file "static-export"))
  :in-order-to ((test-op (test-op "ledger-kernel/web/tests"))))

(defsystem "ledger-kernel/web/tests"
  :description "Tests for the web UI's renderer and JSON API."
  :depends-on ("ledger-kernel/web" "ledger-kernel/tests")
  :pathname "web/"
  :components ((:file "tests"))
  :perform (test-op (o c)
             (unless (uiop:symbol-call :ledger-kernel :run-web-self-tests)
               (error "ledger-kernel web self-tests failed."))))
