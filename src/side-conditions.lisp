;;;; side-conditions.lisp -- Section 3: side conditions
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 3. Side conditions: object-level rules vs. meta-level predicates
;;; ---------------------------------------------------------------------
;;;
;;; A rule's payload is (NAME SIDE-CONDITIONS FORM). Each element of
;;; SIDE-CONDITIONS is either:
;;;   - an ordinary object-level judgement to recurse into, e.g. (wff? ?A)
;;;     -- checked via JUDGEMENT?, extensible by adding more ledger
;;;     entries of the relevant kind;
;;;   - an @-tagged meta-form, e.g. (@not-free-in? ?x ?A) or
;;;     (@subst-ok? ?x ?t ?A) -- dispatched immediately to a fixed Lisp
;;;     DEFUN in *META-PREDICATES*, because verifying it needs
;;;     computation (free-variable traversal, substitution) that doesn't
;;;     reduce to "does some entry in the ledger match".

(defun at-tagged-p (form)
  (and (consp form) (symbolp (car form))
       (> (length (symbol-name (car form))) 1)
       (char= (char (symbol-name (car form)) 0) #\@)))

;; META-CONSTRUCTOR-P is declared up in section 1 (MATCH-TEMPLATE needs it
;; already defined); META-CONSTRUCTORS-TABLE, its table-building
;; counterpart, lives at the end of this section, alongside
;; META-PREDICATES-TABLE below.

(defun meta-predicate-p (sym)
  "Alist entry (@name . function) for an @-tagged side condition, or NIL
if SYM names none."
  (assoc sym (meta-predicates-table) :test #'eq))

(defun expand-meta-constructors (form binds)
  "Recursively replace any fully-bound @-tagged meta-constructor call
inside FORM with its computed value. Used to resolve things like
(@subst ?x ?t ?A) appearing inside a rule's FORM before matching it
against a target expression."
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
  "Check one side condition under BINDS against LEDGER. Returns (values
new-binds ok-p). Object-level conditions may extend BINDS (e.g. matching
(wff? ?A) can bind ?A if it wasn't already bound); meta conditions never
extend bindings -- they only test.

SEEN is JUDGEMENT-BIND's cycle guard, threaded through here so that an
object-level condition -- which recurses back into JUDGEMENT? -- continues
the SAME cycle-detection chain as whatever outer JUDGEMENT-BIND call is
currently checking conditions, rather than starting a fresh one.

OPEN-HYPS is Gamma (see the comment above ATOMIC-WFF-SYMBOL-P), passed
along unconditionally as a meta-predicate's second argument so that
META-NOT-FREE-IN-DEPENDENCIES?/META-PROVEN? can consult it without any
special variable."
  (cond
    ((at-tagged-p cond-form)
     (let ((fn (cdr (meta-predicate-p (car cond-form)))))
       (unless fn (error "Unknown meta-predicate: ~S" (car cond-form)))
       (let ((args (mapcar (lambda (a) (instantiate-with-binds a binds)) (cdr cond-form))))
         (values binds (apply fn ledger open-hyps args)))))
    (t
     ;; Object-level: (kind arg). ARG's pattern variables were already
     ;; bound by matching the rule's own FORM against the target
     ;; expression, so instantiate ARG under BINDS first, then verify the
     ;; resulting concrete judgement.
     (let ((inst-arg (instantiate-with-binds (second cond-form) binds)))
       (values binds (judgement? (car cond-form) inst-arg ledger seen open-hyps))))))

(defun check-conditions (conditions binds ledger &optional (seen nil) (open-hyps nil))
  "Thread BINDS through all of CONDITIONS in order, short-circuiting on
first failure. Returns (values final-binds ok-p)."
  (if (null conditions)
      (values binds t)
      (multiple-value-bind (b1 ok1) (check-condition (car conditions) binds ledger seen open-hyps)
        (if (not ok1)
            (values binds nil)
            (check-conditions (cdr conditions) b1 ledger seen open-hyps)))))
