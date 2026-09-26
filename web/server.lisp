;;;; server.lisp -- Hunchentoot routes
;;;;
;;;;   GET  /                          the single-page UI (static/index.html)
;;;;   GET  /static/...                JS / CSS
;;;;   GET  /api/worlds                available worlds
;;;;   GET  /api/entries?world=zf      every entry of a world (summary)
;;;;   GET  /api/entry?world=zf&k=12   one entry, with its proof
;;;;   POST /api/check                 {"world": "zf", "proof": "((0 ...) ...)"}
;;;;
;;;; The server binds to 127.0.0.1 by default. /api/check reads untrusted
;;;; text (with *READ-EVAL* off, a size limit and a time limit), but reading
;;;; still interns symbols; do not expose it publicly without more limits.

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
  "Encode (FUNCALL THUNK) as JSON; any error becomes a 400 {\"error\": ...}."
  (handler-case (json-response (funcall thunk))
    (error (c) (json-response (json-obj "error" (princ-to-string c)) 400))))

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
  (call-with-json-errors
   (lambda ()
     (let* ((body (hunchentoot:raw-post-data :force-text t))
            (request (yason:parse (or body "{}"))))
       (api-check (or (gethash "world" request) "zf")
                  (or (gethash "proof" request) ""))))))

(defun web-dispatch-table ()
  (list (hunchentoot:create-regex-dispatcher "^/$" 'handle-index)
        (hunchentoot:create-folder-dispatcher-and-handler "/static/" (web-static-directory))
        (hunchentoot:create-regex-dispatcher "^/api/worlds$" 'handle-worlds)
        (hunchentoot:create-regex-dispatcher "^/api/entries$" 'handle-entries)
        (hunchentoot:create-regex-dispatcher "^/api/entry$" 'handle-entry)
        (hunchentoot:create-regex-dispatcher "^/api/check$" 'handle-check)))

(defun start-web-server (&key (port 8080) (address "127.0.0.1"))
  "Load the worlds (if not loaded yet) and serve the UI at
http://ADDRESS:PORT/. Returns the acceptor."
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
                                          :access-log-destination nil)))
  (format t "~&Serving on http://~A:~D/~%" address port)
  *web-acceptor*)

(defun stop-web-server ()
  (when *web-acceptor*
    (hunchentoot:stop *web-acceptor*)
    (setf *web-acceptor* nil)))
