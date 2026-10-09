;;;; package.lisp -- ledger-kernel
;;;;
;;;; A Hilbert-style proof checker whose state is one append-only,
;;;; immutable LEDGER of numbered entries. Entry K is the K-th admitted
;;;; entry; its ORIGIN is :PRIMITIVE (trusted, admitted only while loading
;;;; a .system spec), :DECLARED (a fresh vocabulary symbol) or :DERIVED
;;;; (carries a K-proof re-checked against entries strictly before K).
;;;; Sigma (vocabulary) and Gamma (open hypotheses) are projections of,
;;;; or arguments alongside, the ledger -- never global state. The one
;;;; special variable is the optional verdict cache *DERIVED-VERIFY-CACHE*
;;;; (k-proof.lisp, off by default), which changes only speed, never a
;;;; verdict; apart from it the code uses no mutable global state.
;;;;
;;;; Layers:
;;;;   kernel -- pattern, treap, ledger, debruijn, side-conditions, meta, judgement,
;;;;             k-proof: the trusted checker.
;;;;   tools  -- persistence, deduction, system-spec,
;;;;             function-definition: build or load ledgers and proofs;
;;;;             every :DERIVED result still passes the kernel.

(defpackage :ledger-kernel
  (:use :cl)
  (:export #:entry-k #:entry-kind #:entry-payload
           #:entry-origin #:ledger-append #:check-and-extend
           #:declare-atomic-wff-symbol
           #:declare-variable-symbol #:declare-predicate-schema-symbol #:judgement? #:run-self-tests
           #:make-log-config #:silent-log
           #:ledger-commands #:ledger-from-commands
           #:write-ledger-to-file #:read-ledger-from-file
           #:write-commands-to-file
           #:check-and-extend-by-deduction-direct
           #:enable-derived-entry-memoization
           #:disable-derived-entry-memoization
           #:reset-derived-entry-memoization
           #:bootstrap-kernel-from-spec
           #:read-system-spec-from-file
           #:bootstrap-kernel-from-spec-file))

(in-package :ledger-kernel)
