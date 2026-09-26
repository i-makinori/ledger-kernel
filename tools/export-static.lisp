;;;; export-static.lisp -- write the web UI as a static, read-only site
;;;;
;;;; From the repository root:
;;;;   sbcl --non-interactive --load tools/export-static.lisp          (-> site/)
;;;;   OUT=/path/to/dir sbcl --non-interactive --load tools/export-static.lisp
;;;;
;;;; Open site/index.html in a browser, or upload the folder to any static
;;;; host (GitHub Pages, Netlify, ...). Every proof is re-verified while the
;;;; worlds are loaded, so the export contains only what the kernel accepted.
;;;; Needs yason and Hunchentoot, as the web UI does.

(require :asdf)
#+quicklisp (ql:quickload '(:hunchentoot :yason) :silent t)
(asdf:load-asd (merge-pathnames "ledger-kernel.asd"))
(asdf:load-system :ledger-kernel/web)

(ledger-kernel:export-static-site
 (let ((out (uiop:getenv "OUT")))
   (if (and out (plusp (length out)))
       (uiop:ensure-directory-pathname out)
       (merge-pathnames "site/" (uiop:getcwd)))))
