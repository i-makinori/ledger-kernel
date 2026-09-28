;;;; side-conditions.lisp -- checking a rule's side conditions

(in-package :ledger-kernel)

;;; A side condition is either an object-level judgement such as (wff? ?A),
;;; checked via JUDGEMENT? against ledger entries, or an @-tagged meta-form
;;; such as (@not-free-in? ?x ?A), dispatched to a fixed Lisp function
;;; (META-PREDICATES-TABLE) because it needs computation, not lookup.

(defun at-tagged-p (form)
  "T iff FORM is a list headed by a symbol named @...."
  (and (consp form) (symbolp (car form))
       (> (length (symbol-name (car form))) 1)
       (char= (char (symbol-name (car form)) 0) #\@)))

(defun meta-predicate-p (sym)
  "Entry (@name . function) for meta-predicate SYM, or NIL."
  (assoc sym (meta-predicates-table) :test #'eq))

(defun expand-meta-constructors (form binds)
  "Replace each meta-constructor call in FORM, e.g. (@subst ?x ?t ?A),
by its value with arguments instantiated under BINDS."
  (cond
    ((and (consp form) (meta-constructor-p (car form)))
     (let* ((args (mapcar (lambda (a) (instantiate-with-binds a binds)) (cdr form)))
            (fn (cdr (meta-constructor-p (car form)))))
       (apply fn args)))
    ((consp form)
     (cons (expand-meta-constructors (car form) binds)
           (expand-meta-constructors (cdr form) binds)))
    (t form)))

(defun check-condition (cond-form binds ledger &optional (seen nil) (open-hyps nil))
  "Check COND-FORM under BINDS. Returns (values binds ok-p); BINDS is
never extended. SEEN continues the caller's JUDGEMENT-BIND cycle guard.
OPEN-HYPS (the open hypotheses) is passed to every meta-predicate."
  (cond
    ((at-tagged-p cond-form)
     (let ((fn (cdr (meta-predicate-p (car cond-form)))))
       (unless fn (error "Unknown meta-predicate: ~S" (car cond-form)))
       (let ((args (mapcar (lambda (a) (instantiate-with-binds a binds)) (cdr cond-form))))
         (values binds (apply fn ledger open-hyps args)))))
    (t
     ;; Object-level (kind arg): ARG is already bound by matching the
     ;; rule's FORM, so check the instantiated judgement.
     (let ((inst-arg (instantiate-with-binds (second cond-form) binds)))
       (values binds (%judgement? (car cond-form) inst-arg ledger seen open-hyps))))))

(defun check-conditions (conditions binds ledger &optional (seen nil) (open-hyps nil))
  "Check CONDITIONS in order, stopping at the first failure. Returns
(values binds ok-p)."
  (if (null conditions)
      (values binds t)
      (multiple-value-bind (b1 ok1) (check-condition (car conditions) binds ledger seen open-hyps)
        (if (not ok1)
            (values binds nil)
            (check-conditions (cdr conditions) b1 ledger seen open-hyps)))))
