;;;; static-export.lisp -- write the web UI as a static site
;;;;
;;;; EXPORT-STATIC-SITE writes the same pages the server shows, with every
;;;; answer the server would give precomputed, so the site can be hosted
;;;; anywhere (GitHub Pages, any file server) or opened from disk:
;;;;
;;;;   DIR/index.html        the UI (web/static/index.html, relative paths)
;;;;   DIR/app.js, style.css  copied from web/static/
;;;;   DIR/data/worlds.js    window.LEDGER_STATIC: the worlds, when and from what
;;;;   DIR/data/ID.js        one world's entry list and every entry's detail
;;;;
;;;; The data is written as JavaScript, not JSON, so it loads with <script>
;;;; tags and works from file:// too. The static site is read-only: checking
;;;; a proof typed in the editor needs the kernel, i.e. the server.
;;;;
;;;; Every proof is re-verified when the worlds are loaded, so an export
;;;; only ever contains what the kernel accepted at that moment.

(in-package :ledger-kernel)

(defun write-text-file (path text)
  (ensure-directories-exist path)
  (with-open-file (out path :direction :output :if-exists :supersede
                            :external-format :utf-8)
    (write-string text out))
  path)

(defun encode-json-string (data)
  (with-output-to-string (out) (yason:encode data out)))

(defun static-world-data (world)
  "Everything the UI asks about WORLD: the entry list and each entry."
  (let ((details (make-hash-table :test #'equal)))
    (dolist (e (world-entries world))
      (setf (gethash (princ-to-string (entry-k e)) details)
            (api-entry (world-id world) (entry-k e))))
    (json-obj "entries" (api-entries (world-id world))
              "entry" details)))

(defun static-index-html ()
  "web/static/index.html, rewritten for a site served from its own folder:
relative asset paths, and the data loaded before the app."
  (let ((html (uiop:read-file-string (merge-pathnames "index.html" (web-static-directory))
                                     :external-format :utf-8)))
    (flet ((replace-once (old new)
             (let ((pos (search old html)))
               (unless pos (error "static-index-html: ~S not found in index.html." old))
               (setf html (concatenate 'string (subseq html 0 pos) new
                                       (subseq html (+ pos (length old))))))))
      (replace-once "href=\"/static/style.css\"" "href=\"style.css\"")
      (replace-once "<script src=\"/static/app.js\"></script>"
                    (format nil "<script src=\"data/worlds.js\"></script>~%<script src=\"app.js\"></script>")))
    html))

(defun iso-timestamp ()
  (multiple-value-bind (s mi h d mo y) (decode-universal-time (get-universal-time) 0)
    (format nil "~4,'0D-~2,'0D-~2,'0DT~2,'0D:~2,'0D:~2,'0DZ" y mo d h mi s)))

(defun git-revision ()
  "Short commit hash of the checkout, or NIL (not a git checkout, no git)."
  (ignore-errors
   (let ((out (uiop:run-program '("git" "rev-parse" "--short" "HEAD")
                                :directory (asdf:system-source-directory :ledger-kernel)
                                :output '(:string :stripped t) :ignore-error-status t)))
     (and (plusp (length out)) (every #'alphanumericp out) out))))

(defun export-static-site (directory)
  "Write the static site into DIRECTORY (created if needed; existing files
of the same names are replaced). Returns DIRECTORY."
  (let ((dir (uiop:ensure-directory-pathname directory)))
    (unless *worlds*
      (format t "~&Loading worlds (every proof is re-verified)...~%")
      (load-worlds))
    (write-text-file (merge-pathnames "index.html" dir) (static-index-html))
    (dolist (file '("app.js" "style.css"))
      (write-text-file (merge-pathnames file dir)
                       (uiop:read-file-string (merge-pathnames file (web-static-directory))
                                              :external-format :utf-8)))
    (write-text-file (merge-pathnames "data/worlds.js" dir)
                     (format nil "window.LEDGER_STATIC = ~A;~%"
                             (encode-json-string
                              (json-obj "worlds" (api-worlds)
                                        "generated" (iso-timestamp)
                                        "revision" (or (git-revision) nil)
                                        "data" (json-obj)))))
    (dolist (w *worlds*)
      (write-text-file (merge-pathnames (format nil "data/~A.js" (world-id w)) dir)
                       (format nil "window.LEDGER_STATIC.data[~A] = ~A;~%"
                               (encode-json-string (world-id w))
                               (encode-json-string (static-world-data w)))))
    (format t "~&Static site written to ~A~%" (namestring dir))
    dir))
