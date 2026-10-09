;;;; api.lisp -- JSON-ready views of worlds, entries, proofs, and proof checks
;;;;
;;;; Every function here returns plain data (hash tables, vectors, strings,
;;;; numbers, :TRUE/:FALSE) that SERVER.LISP encodes as JSON. Nothing here
;;;; talks HTTP, so it can be exercised directly from the REPL or tests.

(in-package :ledger-kernel)

(defun json-obj (&rest kv)
  (let ((h (make-hash-table :test #'equal)))
    (loop for (k v) on kv by #'cddr do (setf (gethash k h) v))
    h))

(defun json-arr (list) (coerce list 'vector))

(defun json-bool (x) (if x 'yason:true 'yason:false))

(defun formula-json (formula ledger)
  "TEXT and SEXP of FORMULA, plus SEGMENTS -- the text split into pieces,
each symbol/operator linked to the entry that introduced it -- when
*RENDER-LINK* is bound (see WITH-WORLD-LINKS)."
  (let ((h (json-obj "text" (let ((*render-link* nil)) (render-formula formula ledger))
                     "sexp" (render-sexp formula))))
    (when *render-link*
      (setf (gethash "segments" h)
            (json-arr (mapcar (lambda (piece)
                                (if (cdr piece)
                                    (json-obj "t" (car piece) "k" (cdr piece))
                                    (json-obj "t" (car piece))))
                              (render-formula-segments formula ledger)))))
    h))

(defun call-with-world-links (world thunk)
  (let ((*render-link* (world-link-function world)))
    (funcall thunk)))

(defun kind-string (kind) (string-downcase (symbol-name kind)))

;;; --- Worlds and entry lists --------------------------------------------------

(defun api-worlds ()
  (json-arr (mapcar (lambda (w)
                      (json-obj "id" (world-id w) "title" (world-title w)
                                "entries" (ledger-count (world-ledger w))
                                "modules" (json-arr (mapcar #'first (world-modules w)))))
                    *worlds*)))

(defun entry-summary-json (world e)
  (let ((ledger (world-ledger world))
        (*render-link* nil))            ; summaries are plain text
    (multiple-value-bind (premises conclusion) (entry-statement e ledger)
      (json-obj "k" (entry-k e)
                "kind" (kind-string (entry-kind e))
                "name" (render-sexp (entry-name e))
                "module" (entry-module world (entry-k e))
                "origin" (kind-string (car (entry-origin e)))
                "aux" (json-bool (entry-aux-p e))
                "hasProof" (json-bool (entry-proof e ledger))
                "premises" (json-arr (mapcar (lambda (f) (render-formula f ledger)) premises))
                "text" (render-formula conclusion ledger)))))

(defun api-entries (world-id)
  (let ((w (find-world world-id)))
    (json-arr (mapcar (lambda (e) (entry-summary-json w e)) (world-entries w)))))

;;; --- One entry, with its proof -------------------------------------------------

(defun proof-line-refs (role args numbers)
  "Which of a line's BY arguments refer to earlier lines of the same proof."
  (let ((line-args (if (member role '(:th :th-ded))
                       (values (split-citation-inst args))
                       args)))
    (remove-if-not (lambda (a) (member a numbers :test #'equal)) line-args)))

(defun proof-lines-json (world raw-proof ledger)
  (let ((numbers (mapcar #'first raw-proof)))
    (json-arr
     (mapcar (lambda (raw)
               (destructuring-bind (num formula role by) raw
                 (let* ((args (and (consp by) (cdr by)))
                        (cited (find-cited-entry world role by)))
                   (json-obj "n" (render-sexp num)
                             "formula" (formula-json formula ledger)
                             "role" (kind-string role)
                             "rule" (if (consp by) (render-sexp (car by)) nil)
                             "args" (json-arr (mapcar #'render-sexp args))
                             "refs" (json-arr (mapcar #'render-sexp (proof-line-refs role args numbers)))
                             "cite" (if cited
                                        (json-obj "k" (entry-k cited)
                                                  "kind" (kind-string (entry-kind cited)))
                                        nil)))))
             raw-proof))))

(defun api-entry (world-id k)
  (let* ((w (find-world world-id)))
    (call-with-world-links w (lambda () (api-entry-1 w world-id k)))))

(defun api-entry-1 (w world-id k)
  (let* ((ledger (world-ledger w))
         (e (or (find-entry-by-k w k) (error "No entry ~D in world ~S." k world-id))))
    (multiple-value-bind (premises conclusion) (entry-statement e ledger)
      (let ((h (entry-summary-json w e))
            (proof (entry-proof e ledger)))
        (setf (gethash "conclusion" h) (formula-json conclusion ledger)
              (gethash "premiseFormulas" h) (json-arr (mapcar (lambda (f) (formula-json f ledger)) premises))
              (gethash "conditions" h) (json-arr (mapcar #'render-sexp (entry-conditions e)))
              (gethash "discharged" h) (if (eq (entry-kind e) 'th-ded)
                                           (formula-json (entry-discharged e ledger) ledger)
                                           nil)
              (gethash "expanded" h) (json-bool (and (eq (entry-kind e) 'th-ded)
                                                     (deduction-entry-expanded-p e)))
              (gethash "proof" h) (if proof (proof-lines-json w proof ledger) nil)
              (gethash "usedBy" h) (json-arr (mapcar (lambda (c) (entry-ref-json w c))
                                                     (entry-used-by (world-deps w) k)))
              (gethash "dependents" h) (entry-dependents-count (world-deps w) k)
              (gethash "foundations" h) (foundations-json w k)
              (gethash "proofSexp" h) (if proof (render-proof-sexp proof) nil))
        h))))

(defun entry-ref-json (world k)
  "A short reference to entry K, for lists of links."
  (let* ((e (find-entry-by-k world k))
         (*render-link* nil))
    (multiple-value-bind (premises conclusion) (entry-statement e (world-ledger world))
      (json-obj "k" k
                "name" (render-sexp (entry-name e))
                "kind" (kind-string (entry-kind e))
                "module" (entry-module world k)
                "text" (concatenate 'string
                                    (if premises
                                        (format nil "~{~A~^, ~} ⊢ "
                                                (mapcar (lambda (f) (render-formula f (world-ledger world)))
                                                        premises))
                                        "")
                                    (render-formula conclusion (world-ledger world)))))))

(defun foundations-json (world k)
  "What entry K ultimately rests on, grouped: axioms, definitional axioms
(functions defined by description), inference rules; plus whether the
Deduction Theorem was trusted as a meta-theorem on the way. NIL for
entries that are not axioms, rules or derived entries."
  (let* ((d (world-deps world))
         (e (find-entry-by-k world k)))
    (when (member (entry-kind e) '(axiom irule th th-ded))
      (multiple-value-bind (ks meta) (entry-foundations d k)
        (let ((axioms nil) (definitions nil) (rules nil))
          (dolist (f (sort (copy-list ks) #'<))
            (let ((fe (find-entry-by-k world f)))
              (cond ((eq (entry-kind fe) 'irule) (push f rules))
                    ((definition-entry-p fe) (push f definitions))
                    (t (push f axioms)))))
          (flet ((refs (list) (json-arr (mapcar (lambda (c) (entry-ref-json world c)) (nreverse list)))))
            (json-obj "axioms" (refs axioms)
                      "definitions" (refs definitions)
                      "rules" (refs rules)
                      "deductionMeta" (json-bool meta))))))))

(defun render-proof-sexp (raw-proof)
  "RAW-PROOF as editable text, one line per proof line."
  (with-output-to-string (out)
    (write-string "(" out)
    (loop for (line . rest) on raw-proof
          do (write-string (render-sexp line) out)
             (when rest (format out "~% ")))
    (write-string ")" out)))

;;; --- Checking a proof typed in the editor --------------------------------------

(defparameter *check-timeout-seconds* 20
  "Re-verification can be expensive; a check taking longer is abandoned.")

(defparameter *max-proof-text-length* 200000)

(defun read-proof-text (text)
  "Parse TEXT into a raw proof with SAFE-READ-FORMS: nothing is evaluated
and no symbol is created. Accepts either one list of lines, ((0 ...) (1 ...)), or the lines
themselves one after another. Returns (VALUES RAW-PROOF ERROR-STRING)."
  (when (> (length text) *max-proof-text-length*)
    (return-from read-proof-text (values nil "The proof text is too long.")))
  (handler-case
      (let* ((forms (safe-read-forms text))
             (proof (if (and (= (length forms) 1) (consp (first forms)) (consp (first (first forms))))
                        (first forms)
                        forms)))
        (loop for line in proof for i from 1
              unless (and (proper-list-p line) (= (length line) 4) (keywordp (third line))
                          (listp (fourth line)))
                do (return-from read-proof-text
                     (values nil (format nil "Line ~D is not of the form (NUMBER FORMULA :ROLE (RULE ARG...)): ~A"
                                         i (render-sexp line)))))
        (if proof (values proof nil) (values nil "The proof is empty.")))
    (error (c) (values nil (format nil "Could not read the proof: ~A" c)))))

(defun check-with-timeout (proof ledger)
  "(VALUES OK FAILED-AT ERROR-STRING)."
  (handler-case
      #+sbcl (sb-ext:with-timeout *check-timeout-seconds*
               (multiple-value-bind (ok failed-at) (check-k-proof proof ledger)
                 (values ok failed-at nil)))
      #-sbcl (multiple-value-bind (ok failed-at) (check-k-proof proof ledger)
               (values ok failed-at nil))
    #+sbcl (sb-ext:timeout ()
             (values nil nil (format nil "Checking took longer than ~D seconds and was stopped."
                                     *check-timeout-seconds*)))
    (error (c) (values nil nil (format nil "The checker signalled an error: ~A" c)))
    ;; e.g. SB-KERNEL::CONTROL-STACK-EXHAUSTED, a STORAGE-CONDITION, not an ERROR
    (serious-condition (c)
      (values nil nil (format nil "The checker ran out of resources: ~A" (type-of c))))))

(defun api-check (world-id text)
  "Check the proof in TEXT against the world's ledger. Reports, per line,
whether it was accepted, rejected (the first failing line), or not
reached. Nothing is added to the ledger."
  (let ((w (find-world world-id)))
    (call-with-world-links w (lambda () (api-check-1 w text)))))

(defun api-check-1 (w text)
  (let ((ledger (world-ledger w)))
    (multiple-value-bind (proof read-error) (read-proof-text text)
      (if read-error
          (json-obj "ok" 'yason:false "error" read-error "lines" (json-arr nil))
          (multiple-value-bind (ok failed-at check-error) (check-with-timeout proof ledger)
            (let ((seen-failure nil))
              (json-obj
               "ok" (json-bool ok)
               "error" (or check-error nil)
               "failedAt" (if failed-at (render-sexp failed-at) nil)
               "conclusion" (formula-json (proof-conclusion proof) ledger)
               "hypotheses" (json-arr (mapcar (lambda (f) (formula-json f ledger)) (proof-hypotheses proof)))
               "lines"
               (json-arr
                (mapcar (lambda (raw)
                          (destructuring-bind (num formula role by) raw
                            (let ((status (cond (ok "accepted")
                                                (check-error "unchecked")
                                                (seen-failure "unchecked")
                                                ((equal num failed-at) (setf seen-failure t) "rejected")
                                                (t "accepted"))))
                              (json-obj "n" (render-sexp num)
                                        "formula" (formula-json formula ledger)
                                        "role" (kind-string role)
                                        "rule" (if (consp by) (render-sexp (car by)) nil)
                                        "args" (json-arr (mapcar #'render-sexp (and (consp by) (cdr by))))
                                        "refs" (json-arr (mapcar #'render-sexp
                                                                 (proof-line-refs role (and (consp by) (cdr by))
                                                                                  (mapcar #'first proof))))
                                        "cite" (let ((cited (find-cited-entry w role by)))
                                                 (if cited
                                                     (json-obj "k" (entry-k cited)
                                                               "kind" (kind-string (entry-kind cited)))
                                                     nil))
                                        "status" status))))
                        proof)))))))))
