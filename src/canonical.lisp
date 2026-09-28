;;;; canonical.lisp -- the canonical form of an entry
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; A theorem is stored in CANONICAL FORM: the names it was written with
;;; are replaced by names determined by its structure alone.
;;;
;;;   bound variables       BV1, BV2, ...  per formula, in order of the
;;;                                        binders' appearance
;;;   free variables        FV1, FV2, ...  per entry, in order of first
;;;   atomic wff symbols    LF1, LF2, ...  appearance (formula of line 0,
;;;   predicate schemas     PS1/n, ...     its justification, line 1, ...)
;;;
;;; PSk/n is a predicate schema of arity n. Function and predicate
;;; symbols (S, +, .in, empty, ...), theorem names and definition names
;;; keep their names: they are accessors, pointing at the entry that
;;; introduced them.
;;;
;;;   written    (0 (.forall v3 (.eq v3 v1)) :hyp nil)
;;;              (1 (.eq v0 v1) :ir (...))
;;;   canonical  (0 (.forall bv1 (.eq bv1 fv1)) :hyp nil)
;;;              (1 (.eq fv2 fv1) :ir (...))
;;;
;;; Two entries that differ only in how their symbols were named get the
;;; same canonical form. The canonical proof is what is checked and
;;; stored (ENTRY-PAYLOAD); the text as written stays in ENTRY-ORIGIN
;;; with the renaming map, for :INST keys and for saving the source.
;;;
;;; Every canonical name is a symbol of its kind in every ledger (see
;;; VARIABLE-P, ATOMIC-WFF-SYMBOL-P, PREDICATE-SCHEMA-ARITY) and can never
;;; be declared as anything else. Canonicalizing is not trusted: its
;;; output is checked like any proof, and a mistake here can only reject.

;;; --- The canonical symbol families ------------------------------------

(defun canonical-name-parts (sym)
  "(VALUES kind index arity) for a canonical name: kind :FV, :BV, :LF or
:PS (arity only for :PS). NIL for any other symbol."
  (when (and sym (symbolp sym) (not (keywordp sym)))
    (let* ((s (symbol-name sym)) (len (length s)))
      (flet ((digits-p (start end)
               (and (< start end)
                    (loop for i from start below end always (digit-char-p (char s i)))
                    (not (and (char= (char s start) #\0) (> (- end start) 1))))))
        (when (> len 2)
          (let ((prefix (subseq s 0 2)))
            (cond
              ((member prefix '("FV" "BV" "LF") :test #'string=)
               (when (digits-p 2 len)
                 (let ((n (parse-integer s :start 2)))
                   (when (plusp n)
                     (values (cond ((string= prefix "FV") :fv)
                                   ((string= prefix "BV") :bv)
                                   (t :lf))
                             n nil)))))
              ((string= prefix "PS")
               (let ((slash (position #\/ s)))
                 (when (and slash (digits-p 2 slash) (digits-p (1+ slash) len))
                   (let ((n (parse-integer s :start 2 :end slash))
                         (a (parse-integer s :start (1+ slash))))
                     (when (and (plusp n) (plusp a))
                       (values :ps n a)))))))))))))

(defun canonical-symbol (kind n &optional arity)
  "The canonical name of KIND (:FV :BV :LF :PS) and index N."
  (intern (ecase kind
            (:fv (format nil "FV~D" n))
            (:bv (format nil "BV~D" n))
            (:lf (format nil "LF~D" n))
            (:ps (format nil "PS~D/~D" n arity)))
          :ledger-kernel))

(defun canonical-name-p (sym)
  (and (canonical-name-parts sym) t))

(defun canonical-variable-name-p (sym)
  (member (canonical-name-parts sym) '(:fv :bv)))

(defun canonical-atom-name-p (sym)
  (eq (canonical-name-parts sym) :lf))

(defun canonical-schema-arity (sym)
  (multiple-value-bind (kind n arity) (canonical-name-parts sym)
    (declare (ignore n))
    (and (eq kind :ps) arity)))

;;; --- Walking the expressions of a proof ---------------------------------

(defun map-inst-list (fn inst)
  "FN applied to the values of an :INST list, keys left alone:
(key value) -> (key (FN value)); (P params body) -> (P (FN params) (FN body))."
  (if (listp inst)
      (mapcar (lambda (item)
                (cond ((and (consp item) (consp (cdr item)) (null (cddr item)))
                       (list (car item) (funcall fn (second item))))
                      ((and (consp item) (consp (cdr item)) (consp (cddr item)) (null (cdddr item)))
                       (list (car item) (funcall fn (second item)) (funcall fn (third item))))
                      (t item)))
              inst)
      inst))

(defun map-by-args (fn args numbers)
  (cond ((atom args) args)
        ((eq (car args) :inst)
         (list* :inst (map-inst-list fn (cadr args)) (cddr args)))
        ((member (car args) numbers :test #'equal)
         (cons (car args) (map-by-args fn (cdr args) numbers)))
        (t (cons (funcall fn (car args)) (map-by-args fn (cdr args) numbers)))))

(defun map-proof-expressions (fn raw-proof)
  "RAW-PROOF with FN applied to every expression in it: each line's
formula, each extra argument of its justification, and each value of a
citation's :INST list. Line numbers, roles, rule names, references to
lines and :INST keys (which name symbols of the CITED entry) are left
alone."
  (let ((numbers (mapcar (lambda (l) (and (consp l) (first l))) raw-proof)))
    (mapcar (lambda (line)
              (if (and (consp line) (= (length line) 4))
                  (destructuring-bind (num formula role by) line
                    (list num (funcall fn formula) role
                          (if (consp by) (cons (car by) (map-by-args fn (cdr by) numbers)) by)))
                  line))
            raw-proof)))

;;; --- Canonicalizing an entry ----------------------------------------------

(defun db->canonical (x)
  "Kernel form X with its binders named BV1, BV2, ... in order of
appearance (a preorder walk). Distinct binders get distinct names, so
nothing is shadowed and NAMED->DB gives back X."
  (let ((counter 0))
    (labels ((conv (x env)
               (cond
                 ((bvar-p x) (or (nth (second x) env) x))
                 ((db-binder-p x)
                  (let ((v (canonical-symbol :bv (incf counter))))
                    (list (first x) v (conv (second x) (cons v env)))))
                 ((consp x) (cons (conv (car x) env) (conv (cdr x) env)))
                 (t x))))
      (conv x nil))))

(defun free-symbol-renaming (db-proof ledger)
  "Alist old -> canonical name for the free variables, atomic wff symbols
and predicate schemas of kernel-form DB-PROOF, numbered per kind in order
of first appearance."
  (let ((map nil) (nfv 0) (nlf 0) (nps 0))
    (labels ((note (sym kind &optional arity)
               (unless (assoc sym map :test #'eq)
                 (push (cons sym (ecase kind
                                   (:fv (canonical-symbol :fv (incf nfv)))
                                   (:lf (canonical-symbol :lf (incf nlf)))
                                   (:ps (canonical-symbol :ps (incf nps) arity))))
                       map)))
             (walk (x)
               (cond
                 ((and x (symbolp x) (not (keywordp x)))
                  (cond ((variable-p x ledger) (note x :fv))
                        ((atomic-wff-symbol-p x ledger) (note x :lf))))
                 ((bvar-p x) nil)
                 ((consp x)
                  (let ((arity (and (symbolp (car x)) (predicate-schema-arity (car x) ledger))))
                    (if arity
                        (progn (note (car x) :ps arity) (walk (cdr x)))
                        (progn (walk (car x)) (walk (cdr x)))))))))
      (map-proof-expressions (lambda (e) (walk e) e) db-proof))
    (nreverse map)))

(defun rename-symbols (map x)
  "X with each symbol that is a key of MAP replaced by its value."
  (cond ((and (symbolp x) x) (let ((p (assoc x map :test #'eq))) (if p (cdr p) x)))
        ((consp x) (cons (rename-symbols map (car x)) (rename-symbols map (cdr x))))
        (t x)))

(defun entry-canonical-map (e)
  "The renaming map (written name -> canonical name) recorded when E was
admitted, or NIL."
  (let ((origin (entry-origin e)))
    (case (car origin)
      (:derived (third origin))
      (:derived-by-deduction (fourth origin))
      (t nil))))

(defun find-derived-entry (name ledger)
  "The TH/TH-DED entry named NAME in LEDGER, or NIL."
  (first (treap-values-below (alist-get (ledger-by-derived-name ledger) name)
                             (ledger-bound ledger))))

(defun translate-inst-keys (raw-proof ledger)
  "RAW-PROOF with the keys of each citation's :INST list, written with the
cited entry's own names, replaced by that entry's canonical names."
  (mapcar (lambda (line)
            (if (and (consp line) (= (length line) 4)
                     (not (member (third line) '(:hyp :axiom :ir)))
                     (consp (fourth line)))
                (let* ((by (fourth line))
                       (pos (position :inst by))
                       (cited (and pos (find-derived-entry (car by) ledger)))
                       (map (and cited (entry-canonical-map cited))))
                  (if (and pos map (listp (nth (1+ pos) by)))
                      (list (first line) (second line) (third line)
                            (append (subseq by 0 (1+ pos))
                                    (list (mapcar (lambda (item)
                                                    (if (consp item)
                                                        (cons (rename-symbols map (car item)) (cdr item))
                                                        item))
                                                  (nth (1+ pos) by)))
                                    (nthcdr (+ 2 pos) by)))
                      line))
                line))
          raw-proof))

(defun canonicalize-proof (raw-proof ledger)
  "(VALUES canonical-proof map): RAW-PROOF (surface or kernel form) in
canonical form, and the renaming of its free symbols. Idempotent."
  (let* ((db (named->db-proof raw-proof ledger))
         (map (free-symbol-renaming db ledger))
         (renamed (map-proof-expressions (lambda (e) (rename-symbols map e)) db))
         (named (map-proof-expressions #'db->canonical renamed)))
    (values (translate-inst-keys named ledger) map)))

(defun canonicalize-formula (formula map ledger)
  "FORMULA in canonical form under the entry's renaming MAP."
  (db->canonical (rename-symbols map (named->db formula ledger))))

;;; --- Standardizing a cited entry apart ------------------------------------

(defun max-canonical-index (&rest trees)
  "The largest index of an FV / LF / PS name occurring in TREES (0 if none)."
  (let ((best 0))
    (labels ((walk (x)
               (cond ((consp x) (walk (car x)) (walk (cdr x)))
                     (t (multiple-value-bind (kind n) (canonical-name-parts x)
                          (when (and (member kind '(:fv :lf :ps)) (> n best))
                            (setf best n)))))))
      (walk trees))
    best))

(defun shift-canonical-names (x offset)
  "X with every FVk / LFk / PSk/n renamed to index k + OFFSET. Applied to a
cited entry's stored proof so that its free symbols cannot coincide with
the citing proof's (\"standardizing apart\")."
  (cond
    ((consp x) (cons (shift-canonical-names (car x) offset) (shift-canonical-names (cdr x) offset)))
    (t (multiple-value-bind (kind n arity) (canonical-name-parts x)
         (if (member kind '(:fv :lf :ps))
             (canonical-symbol kind (+ n offset) arity)
             x)))))

(defun schematic-variable-p (sym binds)
  "T iff SYM is a free variable of a standardized-apart cited entry: an FV
name at or above the :SCHEMATIC-FROM index recorded in BINDS."
  (let ((from (cdr (assoc :schematic-from binds))))
    (and from
         (multiple-value-bind (kind n) (canonical-name-parts sym)
           (and (eq kind :fv) (>= n from))))))

(defun standardize-proof-apart (raw-proof offset)
  "SHIFT-CANONICAL-NAMES applied to RAW-PROOF's expressions (not to the
:INST keys of its citations, which name symbols of other entries)."
  (map-proof-expressions (lambda (x) (shift-canonical-names x offset)) raw-proof))

(defun standardize-inst (inst map offset)
  "A citation's :INST list with each key -- a name of the cited entry,
as written (translated by its MAP) or already canonical -- shifted by
OFFSET like the entry itself."
  (if (listp inst)
      (mapcar (lambda (item)
                (if (consp item)
                    (cons (shift-canonical-names (rename-symbols map (car item)) offset) (cdr item))
                    item))
              inst)
      inst))
