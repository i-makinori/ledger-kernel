;;;; server.lisp -- Hunchentoot routes
;;;;
;;;;   GET  /                          the single-page UI (static/index.html)
;;;;   GET  /static/...                JS / CSS
;;;;   GET  /api/worlds                available worlds
;;;;   GET  /api/entries?world=zf      every entry of a world (summary)
;;;;   GET  /api/entry?world=zf&k=12   one entry, with its proof
;;;;   POST /api/check                 {"world": "zf", "proof": "((0 ...) ...)"}
;;;;
;;;; The server binds to 127.0.0.1 by default; put a reverse proxy (TLS,
;;;; rate limits) in front of it to serve it publicly (deploy/). /api/check
;;;; reads untrusted text with SAFE-READ-FORMS (no evaluation, no new
;;;; symbols, bounded nesting), within a size limit, a time limit and a
;;;; limit on concurrent checks. Nothing is ever added to a ledger.

(in-package :ledger-kernel)

(defvar *web-acceptor* nil)

(defun web-static-directory ()
  (asdf:system-relative-pathname :ledger-kernel "web/static/"))

(defun json-response (data &optional (status 200))
  (setf (hunchentoot:content-type*) "application/json; charset=utf-8"
        (hunchentoot:return-code*) status)
  (with-output-to-string (out)
    (yason:encode data out)))

(defun call-with-json-errors (thunk)
  "Encode (FUNCALL THUNK) as JSON; any error becomes a 400 {\"error\": ...}.
A SERIOUS-CONDITION that is not an ERROR (running out of stack on absurdly
nested input) is answered too, instead of taking the thread down."
  (handler-case (json-response (funcall thunk))
    (error (c) (json-response (json-obj "error" (princ-to-string c)) 400))
    (serious-condition (c)
      (json-response (json-obj "error" (format nil "Request too complex (~A)." (type-of c))) 400))))

;;; --- Limits for a server reachable from outside ----------------------------
;;;
;;; Checking is CPU-bound, so only *MAX-CONCURRENT-CHECKS* run at once; a
;;; request arriving when all are busy is answered 503 at once rather than
;;; queued. The request body is capped before it is parsed.

(defvar *max-concurrent-checks* 2)
(defvar *check-semaphore* nil)
(defparameter *max-request-body-length* 262144)

(defun call-with-check-slot (thunk)
  (let ((sem (or *check-semaphore*
                 (setf *check-semaphore* (sb-thread:make-semaphore :count *max-concurrent-checks*)))))
    (if (sb-thread:try-semaphore sem)
        (unwind-protect (funcall thunk)
          (sb-thread:signal-semaphore sem))
        (json-response (json-obj "error" "The checker is busy; please try again in a moment.") 503))))

(defun handle-index ()
  (hunchentoot:handle-static-file (merge-pathnames "index.html" (web-static-directory))
                                  "text/html; charset=utf-8"))

(defun handle-worlds () (call-with-json-errors #'api-worlds))

(defun handle-entries ()
  (call-with-json-errors
   (lambda () (api-entries (or (hunchentoot:get-parameter "world") "zf")))))

(defun handle-entry ()
  (call-with-json-errors
   (lambda ()
     (let ((k (parse-integer (or (hunchentoot:get-parameter "k") "") :junk-allowed t)))
       (unless k (error "Missing or invalid parameter k."))
       (api-entry (or (hunchentoot:get-parameter "world") "zf") k)))))

(defun handle-check ()
  (let ((len (hunchentoot:header-in* :content-length)))
    (if (and len (> (or (parse-integer len :junk-allowed t) 0) *max-request-body-length*))
        (json-response (json-obj "error" "The request is too large.") 413)
        (call-with-check-slot
         (lambda ()
           (call-with-json-errors
            (lambda ()
              (let* ((body (hunchentoot:raw-post-data :force-text t))
                     (request (if (> (length (or body "")) *max-request-body-length*)
                                  (error "The request is too large.")
                                  (yason:parse (or body "{}")))))
                (unless (hash-table-p request) (error "The request must be a JSON object."))
                (api-check (or (gethash "world" request) "zf")
                           (or (gethash "proof" request) ""))))))))))

(defun web-dispatch-table ()
  (list (hunchentoot:create-regex-dispatcher "^/$" 'handle-index)
        (hunchentoot:create-folder-dispatcher-and-handler "/static/" (web-static-directory))
        (hunchentoot:create-regex-dispatcher "^/api/worlds$" 'handle-worlds)
        (hunchentoot:create-regex-dispatcher "^/api/entries$" 'handle-entries)
        (hunchentoot:create-regex-dispatcher "^/api/entry$" 'handle-entry)
        (hunchentoot:create-regex-dispatcher "^/api/check$" 'handle-check)))

(defun start-web-server (&key (port 8080) (address "127.0.0.1")
                              (check-timeout *check-timeout-seconds*)
                              (max-concurrent-checks *max-concurrent-checks*)
                              (max-threads 16))
  "Load the worlds (if not loaded yet) and serve the UI at
http://ADDRESS:PORT/. CHECK-TIMEOUT (seconds per check),
MAX-CONCURRENT-CHECKS and MAX-THREADS (connections served at once) bound
what one client can make the server do. Returns the acceptor."
  (setf *check-timeout-seconds* check-timeout
        *max-concurrent-checks* max-concurrent-checks
        *check-semaphore* (sb-thread:make-semaphore :count max-concurrent-checks))
  (unless *worlds*
    (format t "~&Loading worlds (every proof is re-verified)...~%")
    (load-worlds))
  (when *web-acceptor* (stop-web-server))
  (setf hunchentoot:*hunchentoot-default-external-format* (flexi-streams:make-external-format :utf-8)
        hunchentoot:*default-content-type* "text/html; charset=utf-8"
        hunchentoot:*dispatch-table* (web-dispatch-table))
  (setf *web-acceptor*
        (hunchentoot:start (make-instance 'hunchentoot:easy-acceptor
                                          :port port :address address
                                          :access-log-destination nil
                                          :taskmaster (make-instance
                                                       'hunchentoot:one-thread-per-connection-taskmaster
                                                       :max-thread-count max-threads
                                                       :max-accept-count (* 2 max-threads)))))
  (format t "~&Serving on http://~A:~D/~%" address port)
  *web-acceptor*)

(defun stop-web-server ()
  (when *web-acceptor*
    (hunchentoot:stop *web-acceptor*)
    (setf *web-acceptor* nil)))
