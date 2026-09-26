;;;; serve.lisp -- start the web UI from the command line
;;;;
;;;; From the repository root:
;;;;   sbcl --load tools/serve.lisp            (http://127.0.0.1:8080/)
;;;;   PORT=9000 sbcl --load tools/serve.lisp
;;;; Needs Hunchentoot and yason (Quicklisp: (ql:quickload '(:hunchentoot :yason))).

(require :asdf)
#+quicklisp (ql:quickload '(:hunchentoot :yason) :silent t)
(asdf:load-asd (merge-pathnames "ledger-kernel.asd"))
(asdf:load-system :ledger-kernel/web)

(ledger-kernel:start-web-server
 :port (let ((p (uiop:getenv "PORT"))) (if (and p (plusp (length p))) (parse-integer p) 8080)))

;; Keep the process alive when run non-interactively.
(unless (find-package :swank)
  (loop (sleep 3600)))
