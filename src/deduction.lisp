;;;; deduction.lisp -- admitting H -> PHI by the Deduction Theorem (TH-DED)

(in-package :ledger-kernel)

;;; The Deduction Theorem is a meta-theorem of a system, not of the
;;; kernel: whether "Gamma, H |- PHI yields Gamma |- H -> PHI" holds
;;; depends on the system's rules (an unrestricted Gen breaks it). So a
;;; .system file must declare it, with one matching rule per way a line
;;; can arise (meta-theorem.lisp), and a system that does not declare it
;;; cannot admit TH-DED entries.
;;;
;;; Checked, for a proof RAW-PROOF of Gamma, H |- PHI:
;;;   1. RAW-PROOF itself, by CHECK-K-PROOF.
;;;   2. DISCHARGEABLE-P: every line is covered by a declared case. A line
;;;      depends on H if it is a :HYP line equal to H, or cites a line that
;;;      does. Then (@vdash H A) must follow by the case for its rule (or
;;;      :ASSUMPTION for H itself) from (@vdash H P) for each cited P. A
;;;      line that does not depend on H must match :INDEPENDENT. A
;;;      derived citation that depends on H needs its cited entry's
;;;      checked instance to be dischargeable, recursively, for each
;;;      premise that depends on H; then Gamma |- H -> PSI follows from the
;;;      Gamma |- H -> Si by propositional steps alone.
;;;
;;; Trusted: the declared cases (each claims the textbook induction step
;;; for its rule goes through in this system), and the final step from
;;; a fully covered proof to Gamma |- H -> PHI. Citations always
;;; re-verify the stored, unexpanded RAW-PROOF (TRY-DEDUCTION-ENTRY). (A
;;; proof-transforming version is kept in
;;; backup/_backup_deduction-transform.lisp.)

(defun irule-premise-count (rule-name ledger)
  "The number of premises of the irule RULE-NAME in LEDGER, or NIL."
  (let ((e (find rule-name (entries-of-kind 'irule ledger)
                 :key (lambda (e) (first (entry-payload e))))))
    (and e (length (first (third (entry-payload e)))))))

(defun dischargeable-p (raw-proof hyp ledger)
  "T iff every line of RAW-PROOF (kernel form, already accepted by
CHECK-K-PROOF against LEDGER) is covered by a declared Deduction Theorem
case with respect to HYP (see above). Otherwise (VALUES NIL n), n the
first line not covered."
  (let ((proven nil)                  ; alist number -> formula
        (dependent nil)               ; line numbers that depend on HYP
        (open-hyps nil))              ; Gamma so far, without HYP
    (flet ((formula-of (n) (cdr (assoc n proven :test #'equal)))
           (depends-p (n) (member n dependent :test #'equal)))
      (dolist (raw raw-proof t)
        (let* ((line (raw->k-line raw))
               (n (k-line-numbering line))
               (f (k-line-formula line))
               (role (k-line-role line))
               (by (k-line-by line))
               (dep nil)
               (ok
                 (case role
                   (:hyp
                    (if (equal f hyp)
                        (progn (setf dep t)
                               (deduction-case-holds-p :assumption hyp nil nil f ledger open-hyps))
                        (deduction-case-holds-p :independent hyp nil nil f ledger open-hyps)))
                   (:axiom
                    (deduction-case-holds-p :independent hyp nil nil f ledger open-hyps))
                   (:ir
                    (let* ((count (or (irule-premise-count (car by) ledger) 0))
                           (cited (subseq (cdr by) 0 (min count (length (cdr by)))))
                           (extras (nthcdr count (cdr by))))
                      (if (some #'depends-p cited)
                          (progn (setf dep t)
                                 (deduction-case-holds-p (car by) hyp (mapcar #'formula-of cited)
                                                         extras f ledger open-hyps))
                          (deduction-case-holds-p :independent hyp nil nil f ledger open-hyps))))
                   (t
                    (let ((cited (values (split-citation-inst (cdr by)))))
                      (if (some #'depends-p cited)
                          (progn (setf dep t)
                                 (citation-dischargeable-p line proven cited #'depends-p ledger))
                          (deduction-case-holds-p :independent hyp nil nil f ledger open-hyps)))))))
          (unless ok (return (values nil n)))
          (push (cons n f) proven)
          (when dep (push n dependent))
          (when (and (eq role :hyp) (not (equal f hyp)))
            (push f open-hyps)))))))

(defun citation-dischargeable-p (line proven cited depends-p ledger)
  "A derived citation LINE whose CITED lines include ones that depend on
HYP: T iff the checked instance of the cited entry is dischargeable with
respect to each of its premises that comes from such a line."
  (multiple-value-bind (instantiated e) (derived-line-instance line proven ledger)
    (and instantiated
         (let ((view (entries-upto (entry-k e) ledger)))
           (every (lambda (n)
                    (or (not (funcall depends-p n))
                        (dischargeable-p instantiated (cdr (assoc n proven :test #'equal)) view)))
                  cited)))))

(defun check-and-extend-by-deduction-direct (ledger name hyp-formula raw-proof &optional (log (silent-log)))
  "Admit HYP-FORMULA -> PHI (as the system's :DISCHARGE declaration writes
it), PHI being RAW-PROOF's conclusion, as TH-DED entry NAME. Requires the
system to declare the Deduction Theorem and RAW-PROOF to be covered by
its cases (DISCHARGEABLE-P). Other hypotheses of RAW-PROOF stay
undischarged and must be supplied when the entry is cited. Returns the
new ledger."
  (flet ((refuse (fmt &rest args)
           (log-admission-result log name nil)
           (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: ~?" fmt args)))
    (when (derived-rule-name-taken-p name ledger)
      (refuse "the name ~S is already used by an existing TH/TH-DED entry -- ~
               refused to avoid an ambiguous or shadowing citation." name))
    (unless (deduction-discharge-entry ledger)
      (refuse "this system does not declare the Deduction Theorem ~
               (:meta-theorem deduction ...), so ~S cannot be admitted by it." name))
    (when (contains-raw-index-p (list hyp-formula raw-proof))
      (refuse "~S contains a raw (:bv n); write bound variables by name." name))
    (unless (judgement? 'wff? hyp-formula ledger)
      (refuse "HYP-FORMULA ~S is not a well-formed formula." hyp-formula))
    (let ((db-hyp (named->db hyp-formula ledger))
          (db-proof (named->db-proof raw-proof ledger)))
      (unless (member db-hyp (proof-hypotheses db-proof) :test #'equal)
        (refuse "HYP-FORMULA ~S does not occur as one of RAW-PROOF's own :HYP ~
                 lines -- nothing would be discharged." hyp-formula))
      (unless (%check-k-proof db-proof ledger log)
        (refuse "proof of ~S rejected." name))
      (multiple-value-bind (ok bad-line) (dischargeable-p db-proof db-hyp ledger)
        (unless ok
          (refuse "line ~S of ~S is not covered by any Deduction Theorem case of ~
                   this system, so ~S cannot be discharged." bad-line name hyp-formula)))
      (log-admission-result log name t)
      ;; Kernel form in the payload, the text as written in the ORIGIN.
      (ledger-append ledger 'th-ded (list name db-hyp db-proof)
                     (list :derived-by-deduction hyp-formula raw-proof)))))
