;;;; worlds.lisp -- the ledgers the server shows
;;;;
;;;; A WORLD is one ledger built from an ordered list of library files
;;;; (.system then .ledger), exactly as a user would chain them at the
;;;; REPL. Different worlds are different theories -- ZF set theory and
;;;; Peano arithmetic are kept apart rather than mixed into one ledger.
;;;; Each entry remembers which file (MODULE) admitted it.

(in-package :ledger-kernel)

(defparameter *world-specs*
  '(("zf" "ZF set theory"
     ("hilbert-library/00-classical-fol-equality.system"
      "hilbert-library/00-connectives.system"
      "zf-library/00-zf.system"
      "hilbert-library/01-propositional-core.ledger"
      "hilbert-library/02-predicate-core.ledger"
      "hilbert-library/03-equality-core.ledger"
      "hilbert-library/05-classical-logic.ledger"
      "hilbert-library/06-connectives.ledger"
      "hilbert-library/07-quantifier-schemas.ledger"
      "zf-library/01-empty-set.ledger"))
    ("peano" "Peano arithmetic"
     ("hilbert-library/00-classical-fol-equality.system"
      "hilbert-library/00-peano-arithmetic.system"
      "hilbert-library/01-propositional-core.ledger"
      "hilbert-library/02-predicate-core.ledger"
      "hilbert-library/03-equality-core.ledger"
      "hilbert-library/04-peano-arithmetic.ledger"
      "hilbert-library/05-classical-logic.ledger")))
  "(ID TITLE FILES) for every world, FILES relative to the repository.")

(defstruct world id title ledger modules symbols)
;; MODULES: list of (FILE FIRST-K LAST-K), in load order.
;; SYMBOLS: hash table, symbol -> K of the entry that introduced it.

(defvar *worlds* nil "Loaded WORLD structs, built by LOAD-WORLDS.")

(defun web-library-file (relative)
  (asdf:system-relative-pathname :ledger-kernel relative))

(defun load-world (spec)
  (destructuring-bind (id title files) spec
    (let ((ledger nil) (modules nil))
      (dolist (file files)
        (let ((before (if ledger (ledger-count ledger) 0)))
          (setf ledger
                (if (string= (pathname-type file) "system")
                    (bootstrap-kernel-from-spec-file (web-library-file file) :ledger ledger)
                    (read-ledger-from-file (web-library-file file) :ledger ledger)))
          (push (list file (1+ before) (ledger-count ledger)) modules)))
      (make-world :id id :title title :ledger ledger :modules (nreverse modules)
                  :symbols (symbol-index ledger)))))

(defun symbol-index (ledger)
  "Map each symbol of the language to the entry that introduced it:
variables and atomic-wff / predicate schema symbols to their declaration,
connectives, quantifiers, predicates and function symbols to their first
formation rule -- or, for a function defined by description, to its
defining axiom NAME-DEF, which says what it means."
  (let ((index (make-hash-table :test #'eq))
        (entries (treap-values-below (ledger-all ledger) (ledger-bound ledger))))
    (flet ((note (sym k) (when (and sym (symbolp sym) (not (pat-var-p sym)))
                           (unless (gethash sym index) (setf (gethash sym index) k)))))
      (dolist (e entries)
        (let ((p (entry-payload e)))
          (case (entry-kind e)
            ((atomic-wff-symbol variable-symbol) (note p (entry-k e)))
            (predicate-schema-symbol (note (first p) (entry-k e)))
            (axiom
             ;; NAME-DEF axioms of DEFINE-FUNCTION-BY-DESCRIPTION
             (let* ((name (symbol-name (first p)))
                    (len (length name)))
               (when (and (> len 4) (string= (subseq name (- len 4)) "-DEF"))
                 (let ((fn (find-symbol (subseq name 0 (- len 4)) :ledger-kernel)))
                   (when fn (setf (gethash fn index) (entry-k e)))))))
            ((wff? term? var?)
             (let ((result (third p)))   ; e.g. (wff? (.to ?A ?B)) or (term? zero)
               (when (consp result)
                 (let ((form (second result)))
                   (note (if (consp form) (car form) form) (entry-k e))))))))))
    index))

(defun world-link-function (world)
  (let ((index (world-symbols world)))
    (lambda (sym) (gethash sym index))))

(defun load-worlds ()
  (setf *worlds* (mapcar #'load-world *world-specs*)))

(defun find-world (id)
  (or (find id *worlds* :key #'world-id :test #'string=)
      (error "Unknown world ~S." id)))

(defun entry-module (world k)
  (first (find-if (lambda (m) (<= (second m) k (third m))) (world-modules world))))

(defun world-entries (world)
  (let ((l (world-ledger world)))
    (treap-values-below (ledger-all l) (ledger-bound l))))

(defun find-entry-by-k (world k)
  (find k (world-entries world) :key #'entry-k))

;;; --- What an entry says ------------------------------------------------------

(defun entry-name (e)
  (let ((p (entry-payload e)))
    (case (entry-kind e)
      ((atomic-wff-symbol variable-symbol) p)
      (t (if (consp p) (car p) p)))))

(defun entry-proof (e)
  "The stored raw proof of a derived entry, or NIL."
  (case (entry-kind e)
    ((th ith def-abbrev) (second (entry-payload e)))
    (th-ded (third (entry-payload e)))))

(defun entry-statement (e)
  "(VALUES PREMISES CONCLUSION) -- what the entry asserts. PREMISES are
the formulas it needs cited (hypotheses of a derived entry, premises of
an inference rule); CONCLUSION is what it yields. Axiom and rule schemas
contain ?-pattern variables."
  (let ((p (entry-payload e)))
    (case (entry-kind e)
      ((th ith def-abbrev)
       (values (proof-hypotheses (second p)) (proof-conclusion (second p))))
      (th-ded
       (destructuring-bind (name hyp raw) p
         (declare (ignore name))
         (values (remove hyp (proof-hypotheses raw) :test #'equal)
                 (list '.to hyp (proof-conclusion raw)))))
      (axiom (values nil (second (third p))))
      (irule (let ((form (third p)))
               (values (first form) (car (last form)))))
      ((wff? term? var?) (values nil (third p)))
      (predicate-schema-symbol
       (values nil (cons (first p) (loop for i from 1 to (second p)
                                         collect (intern (format nil "?X~D" i) :ledger-kernel)))))
      (t (values nil p)))))

(defun entry-conditions (e)
  "Side conditions of an axiom / rule / formation schema."
  (and (member (entry-kind e) '(axiom irule wff? term? var?))
       (second (entry-payload e))))

(defun auxiliary-name-p (name)
  "Entries generated as intermediate steps (PROVE-TAUTOLOGY's NAME.T1,
NAME.CONTRA, ...; hand-written NAME-S1, NAME-STEP2, ...)."
  (and (symbolp name)
       (let ((s (symbol-name name)))
         (or (find #\. s :start 1)
             (search "-STEP" s)
             (let ((pos (search "-S" s :from-end t)))
               (and pos (< (+ pos 2) (length s))
                    (every #'digit-char-p (subseq s (+ pos 2)))))))))

(defun find-cited-entry (world role by)
  "The ledger entry a proof line's justification refers to, or NIL."
  (when (consp by)
    (let* ((name (car by))
           (l (world-ledger world)))
      (case role
        (:axiom (find name (entries-of-kind 'axiom l) :key (lambda (e) (car (entry-payload e)))))
        (:ir (find name (entries-of-kind 'irule l) :key (lambda (e) (car (entry-payload e)))))
        ((:th :ith :th-ded :def-abbrev)
         (first (treap-values-below (alist-get (ledger-by-derived-name l) name) nil)))))))
