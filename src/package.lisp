;;;; package.lisp -- ledger-kernel
;;;;
;;;; Bw(x,y) made literal: a single append-only "ledger" of k-indexed
;;;; entries, where an entry's ORIGIN is either :PRIMITIVE (admitted by
;;;; fiat, bootstrap only) or :DERIVED (admitted only after a full K-proof
;;;; re-verified from scratch against strictly earlier ledger entries).
;;;;
;;;; Design decisions this system honors:
;;;;  - Sigma (vocabulary) and Gamma (open hypotheses) are NOT separately
;;;;    threaded state; they are two independent read-only projections
;;;;    over the same ledger (filter-by-kind).
;;;;  - A "side condition" is just a rule of a specially-tagged kind.
;;;;    A side condition whose verification genuinely needs meta-level
;;;;    computation (e.g. not-free-in, substitution) is instead defined
;;;;    as a plain Lisp DEFUN and invoked via an @-tagged meta-predicate;
;;;;    it is never itself a ledger entry.
;;;;  - Proofs are always fully expanded: a :DERIVED entry's use in a
;;;;    later proof is checked by instantiating its schema variables with
;;;;    the concrete bindings in play and re-running the full K-proof
;;;;    checker on the instantiated proof -- never trusted at the
;;;;    schema/pattern level alone.
;;;;  - All state (the ledger, Gamma, pattern bindings, the cycle guard)
;;;;    is threaded explicitly as ordinary function arguments and return
;;;;    values -- no DEFVAR/DEFPARAMETER, no SETF/SETQ, no dynamic
;;;;    rebinding anywhere in the file.
;;;;  - Meta predicates/constructors are plain Lisp DEFUNs, dispatched by
;;;;    the @ prefix; they are fixed and never part of the extensible
;;;;    rule database.
;;;;  - ORIGIN is modeled as a two-constructor type, Curry-Howard style:
;;;;      :PRIMITIVE  -- axiom-like, carries no proof
;;;;      :DERIVED    -- carries a full K-proof that was checked
;;;;  - Abbreviation/definition entries are ALSO ledger objects requiring
;;;;    a (conservativity) proof, unlike Goedel's own meta-level
;;;;    definitions.
;;;;  - Every time a proof or definition is admitted, k increases by
;;;;    exactly one. K IS the ledger position; ENTRY-K IS Goedel's y.

;;; ---------------------------------------------------------------------
;;; 0. Utilities
;;; ---------------------------------------------------------------------

(defpackage :ledger-kernel
  (:use :cl)
  (:export #:bootstrap-kernel #:entry-k #:entry-kind #:entry-payload
           #:entry-origin #:ledger-append #:admit-primitive #:check-and-extend
           #:check-and-extend-abbrev #:declare-atomic-wff-symbol
           #:declare-variable-symbol #:declare-predicate-schema-symbol #:judgement? #:run-self-tests
           #:make-log-config #:silent-log
           #:ledger-commands #:ledger-from-commands
           #:write-ledger-to-file #:read-ledger-from-file
           #:write-commands-to-file
           #:@deduction #:check-and-extend-by-deduction
           #:check-and-extend-by-deduction-direct
           #:prove-tautology
           #:find-named-entry #:rename-symbol-everywhere
           #:alpha-rename-entry #:alpha-rename-forall
           #:enable-derived-entry-memoization
           #:disable-derived-entry-memoization
           #:reset-derived-entry-memoization
           #:bootstrap-kernel-from-spec
           #:read-system-spec-from-file
           #:bootstrap-kernel-from-spec-file))

(in-package :ledger-kernel)
