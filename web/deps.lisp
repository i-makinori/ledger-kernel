;;;; deps.lisp -- who uses what: citation graph, foundations, dependents
;;;;
;;;; Built once per world from the stored proofs (read-only, outside the
;;;; trusted kernel):
;;;;
;;;;   CITES      k -> entries k's stored proof cites directly (axioms,
;;;;              inference rules, derived entries). A function defined by
;;;;              description counts as citing its existence and uniqueness
;;;;              theorems: that is what justifies its defining axiom.
;;;;   CITED-BY   the reverse.
;;;;
;;;; From these:
;;;;   FOUNDATIONS   the axioms, inference rules and definitions an entry
;;;;                 ultimately rests on (transitively through derived
;;;;                 entries), and whether any step on the way was admitted
;;;;                 by trusting the Deduction Theorem as a meta-theorem
;;;;                 (a TH-DED entry).
;;;;   USED-BY       the entries that cite it -- an auxiliary entry (an
;;;;                 intermediate lemma such as NAME.T5 or NAME-S1) is
;;;;                 replaced by whatever uses IT, so counts are not inflated
;;;;                 by the internal steps of one proof.
;;;;   DEPENDENTS    every non-auxiliary derived entry that depends on it,
;;;;                 directly or not.

(in-package :ledger-kernel)

(defstruct deps
  (cites (make-hash-table))        ; k -> list of k
  (cited-by (make-hash-table))     ; k -> list of k
  (foundations (make-hash-table))  ; k -> (ks . deduction-meta-p), memoised
  (entries (make-hash-table)))     ; k -> entry

(defun find-entry-by-k (world k)
  (if (world-deps world)
      (gethash k (deps-entries (world-deps world)))
      (find k (world-entries world) :key #'entry-k)))

(defun derived-kind-p (kind) (member kind '(th th-ded)))

(defun entry-aux-p (e)
  "An intermediate lemma of some other proof (see AUXILIARY-NAME-P)."
  (and (derived-kind-p (entry-kind e)) (auxiliary-name-p (entry-name e))))

(defun by-description-command (e)
  "The (:DEFINE-FUNCTION-BY-DESCRIPTION ...) command recorded in a
definition's defining axiom, or NIL."
  (let ((origin (entry-origin e)))
    (and (eq (car origin) :primitive) (eq (second origin) :by-description) (third origin))))

(defun direct-citations (world e)
  (let ((ledger (world-ledger world)))
    (remove-duplicates
     (append
      (loop for (nil nil role by) in (entry-proof e)
            for cited = (find-cited-entry world role by)
            when cited collect (entry-k cited))
      ;; (:define-function-by-description name args y y2 a existence uniqueness)
      (let ((cmd (by-description-command e)))
        (when (and cmd (eq (entry-kind e) 'axiom))
          (loop for name in (last cmd 2)
                for cited = (first (treap-values-below (alist-get (ledger-by-derived-name ledger) name) nil))
                when cited collect (entry-k cited)))))
     :from-end t)))

(defun build-deps (world)
  (let ((d (make-deps)))
    (dolist (e (world-entries world))
      (setf (gethash (entry-k e) (deps-entries d)) e))
    (dolist (e (world-entries world))
      (let ((cites (direct-citations world e)))
        (setf (gethash (entry-k e) (deps-cites d)) cites)
        (dolist (c cites) (push (entry-k e) (gethash c (deps-cited-by d))))))
    (maphash (lambda (k v) (setf (gethash k (deps-cited-by d)) (nreverse v))) (deps-cited-by d))
    d))

(defun deps-entry (d k) (gethash k (deps-entries d)))

(defun entry-foundations (d k)
  "(VALUES KS DEDUCTION-META-P): the axioms / inference rules / definitional
axioms entry K rests on, and whether a TH-DED entry was used on the way.
An axiom or rule rests on itself; a definitional axiom on itself plus
whatever its existence and uniqueness theorems rest on."
  (let ((memo (gethash k (deps-foundations d))))
    (when memo (return-from entry-foundations (values (car memo) (cdr memo)))))
  (let* ((e (deps-entry d k))
         (kind (entry-kind e))
         (result
           (cond
             ((member kind '(axiom irule))
              (let ((ks (list k)) (meta nil))
                (when (by-description-command e)
                  (dolist (c (gethash k (deps-cites d)))
                    (multiple-value-bind (cks cmeta) (entry-foundations d c)
                      (setf ks (union ks cks) meta (or meta cmeta)))))
                (cons ks meta)))
             ((derived-kind-p kind)
              (let ((ks nil) (meta (eq kind 'th-ded)))
                (dolist (c (gethash k (deps-cites d)))
                  (multiple-value-bind (cks cmeta) (entry-foundations d c)
                    (setf ks (union ks cks) meta (or meta cmeta))))
                (cons ks meta)))
             (t (cons nil nil)))))
    (setf (gethash k (deps-foundations d)) result)
    (values (car result) (cdr result))))

(defun entry-used-by (d k)
  "Entries that cite K directly, with auxiliary citers replaced by the
entries that use them in turn."
  (let ((seen (make-hash-table)) (out nil))
    (labels ((visit (citer)
               (unless (gethash citer seen)
                 (setf (gethash citer seen) t)
                 (if (entry-aux-p (deps-entry d citer))
                     (mapc #'visit (gethash citer (deps-cited-by d)))
                     (unless (= citer k) (push citer out))))))
      (mapc #'visit (gethash k (deps-cited-by d))))
    (sort out #'<)))

(defun entry-dependents-count (d k)
  "How many non-auxiliary derived entries depend on K, directly or not."
  (let ((seen (make-hash-table)) (count 0))
    (labels ((visit (citer)
               (unless (gethash citer seen)
                 (setf (gethash citer seen) t)
                 (let ((e (deps-entry d citer)))
                   (when (and (derived-kind-p (entry-kind e)) (not (entry-aux-p e)))
                     (incf count)))
                 (mapc #'visit (gethash citer (deps-cited-by d))))))
      (mapc #'visit (gethash k (deps-cited-by d))))
    count))
