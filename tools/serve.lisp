;;;; serve.lisp -- start the web UI from the command line
;;;;
;;;; From the repository root:
;;;;   sbcl --load tools/serve.lisp            (http://127.0.0.1:8080/)
;;;;   PORT=9000 sbcl --load tools/serve.lisp
;;;; Needs Hunchentoot and yason (Quicklisp: (ql:quickload '(:hunchentoot :yason))).
;;;;
;;;; Environment variables (all optional):
;;;;   ADDRESS                 interface to listen on        (127.0.0.1)
;;;;   PORT                    port                           (8080)
;;;;   LEDGER_CHECK_TIMEOUT    seconds allowed per check      (20)
;;;;   LEDGER_MAX_CHECKS       checks running at once         (2)
;;;;   LEDGER_MAX_THREADS      connections served at once     (16)
;;;; For a public server keep ADDRESS=127.0.0.1 behind a reverse proxy and
;;;; lower LEDGER_CHECK_TIMEOUT (see deploy/README.md).

(require :asdf)
#+quicklisp (ql:quickload '(:hunchentoot :yason) :silent t)
(asdf:load-asd (merge-pathnames "ledger-kernel.asd"))
(asdf:load-system :ledger-kernel/web)

(flet ((env (name default)
         (let ((v (uiop:getenv name)))
           (if (and v (plusp (length v))) v default)))
       (env-int (name default)
         (let ((v (uiop:getenv name)))
           (if (and v (plusp (length v))) (parse-integer v) default))))
  (ledger-kernel:start-web-server
   :address (env "ADDRESS" "127.0.0.1")
   :port (env-int "PORT" 8080)
   :check-timeout (env-int "LEDGER_CHECK_TIMEOUT" 20)
   :max-concurrent-checks (env-int "LEDGER_MAX_CHECKS" 2)
   :max-threads (env-int "LEDGER_MAX_THREADS" 16)))

;; Keep the process alive when run non-interactively.
(unless (find-package :swank)
  (loop (sleep 3600)))
