;;;; function-definition.lisp -- Section 22: DEFINE-FUNCTION-BY-DESCRIPTION
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 22. Conservative definitional extension: DEFINE-FUNCTION-BY-DESCRIPTION
;;; ---------------------------------------------------------------------
;;;
;;; IOTA (Section 19) lets a proof USE "the y such that A" as a term, but
;;; only by re-citing existence and uniqueness EVERY SINGLE TIME, and only
;;; ever as a raw (.iota ...) term -- there is no way to give it an
;;; ordinary NAME and have it read like any other function symbol.
;;; DEFINE-FUNCTION-BY-DESCRIPTION packages the standard Hilbert-style
;;; "definition by description" move: given that
;;;   EXISTENCE:   forall x1..xn. exists y. A(x1,...,xn,y)
;;;   UNIQUENESS:  forall x1..xn. forall y. forall y2.
;;;                  (A(...,y) -> (A(...,y2) -> y=y2))
;;; have ALREADY been independently proven (as ordinary closed ledger
;;; theorems, however that was done -- possibly using IOTA/EXISTS-ELIM
;;; themselves, possibly plain induction, this function does not care),
;;; introduces a genuinely new N-ARY FUNCTION SYMBOL together with the
;;; single defining axiom A(x1,...,xn, NAME(x1,...,xn)) -- so the new
;;; symbol can from then on be used exactly like +, S, or any other
;;; function symbol, with no need to re-derive or re-cite anything.
;;;
;;; TRUST MODEL: like every other mechanism in this file that mints new
;;; :PRIMITIVE vocabulary (Section 18's .system files, Section 20's
;;; DEFINE-INDUCTIVE-PREDICATE), this is built on BOOTSTRAP-KERNEL-FROM-
;;; SPEC, not some new privileged back door. What makes it MORE than "just
;;; another way to write an axiom by hand", though, is that it doesn't
;;; simply trust the caller's claim that EXISTENCE-NAME/UNIQUENESS-NAME
;;; say what they need to say -- it RE-CHECKS both, via ordinary
;;; CHECK-K-PROOF citations, against the EXACT expected formula built from
;;; A-FORMULA itself, and refuses (a Lisp ERROR, not a silently-wrong
;;; ledger) if either mismatches. So the honesty of the resulting
;;; definition reduces to two much smaller, independently-verified facts
;;; (a real existence theorem, a real uniqueness theorem, both already
;;; checked by the ordinary re-verifying kernel) plus exactly ONE
;;; unverified meta-theoretic step: that definition-by-description, given
;;; existence and uniqueness, is a conservative extension. That last step
;;; is a standard, well-known theorem of first-order logic -- but this
;;; kernel does not itself formally prove it, so this mechanism makes
;;; each individual definition mechanically CHECKED against its stated
;;; prerequisites without making the underlying conservativity CLAIM
;;; itself machine-verified. Exactly the same honest boundary Section 18
;;; and Section 20 already draw, just pushed one step further out.

(defun rename-many (pairs form)
  "Applies RENAME-SYMBOL-EVERYWHERE (Section 16) once per (OLD . NEW) pair
in PAIRS, in order, to FORM. Safe here because every NEW name used by this
section's own callers is a freshly chosen ?-prefixed schema variable that
cannot already occur in FORM, so the renames can never interfere with
each other regardless of order."
  (dolist (p pairs form) (setf form (rename-symbol-everywhere (car p) (cdr p) form))))

(defun define-function-by-description (ledger name arg-vars y-var y2-var a-formula
                                        existence-name uniqueness-name)
  "See this section's own header for the full contract. ARG-VARS is a list
of already-declared object variables naming A-FORMULA's own x1..xn
argument positions; Y-VAR is the variable naming its output position;
Y2-VAR is a second, distinct object variable used only internally to
state uniqueness (\"any two things satisfying A are equal\")."
  (let* ((expected-existence
           (let ((body (list '.exists y-var a-formula)))
             (dolist (v (reverse arg-vars) body) (setf body (list '.forall v body)))))
         (a-at-y2 (rename-many (list (cons y-var y2-var)) a-formula))
         (expected-uniqueness
           (let ((body (list '.forall y-var
                              (list '.forall y2-var
                                    (list '.to a-formula (list '.to a-at-y2 (list '.eq y-var y2-var)))))))
             (dolist (v (reverse arg-vars) body) (setf body (list '.forall v body))))))
    (unless (eq t (check-k-proof (list (list 0 expected-existence :th (list existence-name))) ledger))
      (error "DEFINE-FUNCTION-BY-DESCRIPTION: ~S does not establish the ~
              required existence schema~%  ~S" existence-name expected-existence))
    (unless (eq t (check-k-proof (list (list 0 expected-uniqueness :th (list uniqueness-name))) ledger))
      (error "DEFINE-FUNCTION-BY-DESCRIPTION: ~S does not establish the ~
              required uniqueness schema~%  ~S" uniqueness-name expected-uniqueness))
    (let* ((schema-xs (loop for i from 1 to (length arg-vars)
                             collect (intern (format nil "?X~D" i) (symbol-package name))))
           (schema-y (intern "?Y" (symbol-package name)))
           (schema-a (rename-many (append (mapcar #'cons arg-vars schema-xs) (list (cons y-var schema-y)))
                                   a-formula))
           (schema-a-at-name (substitute-wff schema-y (cons name schema-xs) schema-a))
           (term-cmd (list :term-formation
                            (intern (format nil "~A-TERM" (symbol-name name)) (symbol-package name))
                            (mapcar (lambda (x) (list 'term? x)) schema-xs)
                            (list 'term? (cons name schema-xs))))
           (def-cmd (list :axiom
                           (intern (format nil "~A-DEF" (symbol-name name)) (symbol-package name))
                           (mapcar (lambda (x) (list 'term? x)) schema-xs)
                           (list nil schema-a-at-name))))
      (bootstrap-kernel-from-spec (list term-cmd def-cmd) :ledger ledger))))
