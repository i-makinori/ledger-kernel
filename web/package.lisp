;;;; package.lisp -- ledger-kernel/web
;;;;
;;;; A small web front end for browsing ledgers (definitions, axioms,
;;;; theorems and their proofs) and checking proofs interactively.
;;;;
;;;; It sits entirely OUTSIDE the trusted kernel: it only reads ledgers
;;;; and calls CHECK-K-PROOF, so nothing here can admit anything the
;;;; kernel would not. The code lives in the LEDGER-KERNEL package (so it
;;;; can name the object-language symbols .TO, .FORALL, TH, ... directly)
;;;; but in its own ASDF system, which the kernel never depends on.

(in-package :ledger-kernel)

(export '(start-web-server stop-web-server render-formula export-static-site))
