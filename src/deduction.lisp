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

;;; --- Expansion: the Deduction Theorem as a real proof ---------------------
;;;
;;; With a proof template for every case it needs (meta-theorem.lisp), a
;;; proof of Gamma, H |- PHI is turned into an ordinary proof of
;;; Gamma |- H -> PHI, line by line, the textbook way:
;;;   - a line that does not depend on H is kept as it is (its references
;;;     pointing to the kept lines), and, when a later step needs H -> A,
;;;     the :INDEPENDENT template derives it;
;;;   - H itself becomes the :ASSUMPTION template's H -> H;
;;;   - a line made by an irule from lines that depend on H becomes that
;;;     irule's template, from the H -> P of its premises;
;;;   - a theorem cited from lines that depend on H is first unfolded --
;;;     a theorem abbreviates a proof figure -- by splicing in its checked
;;;     instance (a cited TH-DED expanded first, recursively), whose lines
;;;     are then treated like the others.
;;; The result is checked by %CHECK-K-PROOF like any proof.

(defun expand-deduction (raw-proof hyp ledger)
  "An ordinary kernel-form proof of Gamma |- H -> PHI from kernel-form
RAW-PROOF of Gamma, HYP |- PHI (already accepted by CHECK-K-PROOF against
LEDGER), or (VALUES NIL reason) when some step has no template or cannot
be unfolded. Not checked here; see EXPANDED-DEDUCTION-CHECKS-P."
  (let ((out nil) (counter 0)
        (formula (make-hash-table :test #'equal))   ; label -> formula
        (orig (make-hash-table :test #'equal))      ; label -> emitted label of the line itself
        (trans (make-hash-table :test #'equal))     ; label -> emitted label of H -> formula
        (dep (make-hash-table :test #'equal))       ; label -> T if it depends on HYP
        (alias (make-hash-table :test #'equal))     ; label -> label it stands for
        (open-hyps nil) (inline-id 0))
    (labels ((fail (reason) (throw 'expand-deduction (values nil reason)))
             (res (l) (let ((a (gethash l alias))) (if a (res a) l)))
             (emit (f role by)
               (let ((label (incf counter)))
                 (push (list label f role by) out)
                 label))
             (template-lines (case-name premises premise-labels extras concl &optional line-label)
               (multiple-value-bind (ok binds template)
                   (deduction-case-holds-p case-name hyp premises extras concl ledger open-hyps)
                 (unless ok (fail (list :no-case case-name)))
                 (unless template (fail (list :no-template case-name)))
                 (let ((local (make-hash-table :test #'equal)) (last-label nil))
                   (dolist (tl template last-label)
                     (destructuring-bind (tlabel tformula trole tby) tl
                       (flet ((arg (a)
                                (cond ((and (keywordp a) (string= (symbol-name a) "LINE")) line-label)
                                      ((and (keywordp a)
                                            (> (length (symbol-name a)) 8)
                                            (string= (subseq (symbol-name a) 0 8) "PREMISE-"))
                                       (nth (parse-integer (symbol-name a) :start 8) premise-labels))
                                      ((nth-value 1 (gethash a local)) (gethash a local))
                                      (t (instantiate-template-term a binds)))))
                         (setf last-label
                               (emit (instantiate-template-term tformula binds) trole
                                     (if (consp tby) (cons (car tby) (mapcar #'arg (cdr tby))) tby)))
                         (setf (gethash tlabel local) last-label)))))))
             (ensure-trans (l)
               (let ((l (res l)))
                 (or (gethash l trans)
                     (setf (gethash l trans)
                           (template-lines :independent nil nil nil (gethash l formula) (gethash l orig))))))
             (unfold (line)
               ;; The lines of the checked instance behind derived citation LINE.
               (multiple-value-bind (instantiated e cited inst-hyp)
                   (derived-line-instance line (let ((alist nil))
                                                 (maphash (lambda (k v) (push (cons k v) alist)) formula)
                                                 alist)
                                          ledger)
                 (unless instantiated (fail (list :no-instance (k-line-numbering line))))
                 (let* ((view (entries-upto (entry-k e) ledger))
                        (proof (if (eq (entry-kind e) 'th-ded)
                                   (multiple-value-bind (p why) (expand-deduction instantiated inst-hyp view)
                                     (or p (fail (list :cited (first (entry-payload e)) why))))
                                   instantiated))
                        (hyp-lines (remove-if-not (lambda (l) (eq (third l) :hyp)) proof))
                        (id (incf inline-id))
                        (map (make-hash-table :test #'equal)))
                   (unless (= (length hyp-lines) (length cited))
                     (fail (list :premise-count (k-line-numbering line))))
                   (loop for hl in hyp-lines for c in cited
                         do (setf (gethash (first hl) map) c))
                   (let ((last (car (last proof))))
                     (loop for l in proof
                           unless (eq (third l) :hyp)
                             do (setf (gethash (first l) map)
                                      (if (eq l last) (k-line-numbering line) (list :inline id (first l)))))
                     (when (eq (third last) :hyp)
                       ;; The theorem is one of its own premises.
                       (setf (gethash (k-line-numbering line) alias) (gethash (first last) map))))
                   (flet ((rl (x) (multiple-value-bind (v found) (gethash x map) (if found v x))))
                     (loop for (num f role by) in proof
                           unless (eq role :hyp)
                             collect (list (rl num) f role
                                           (if (and (consp by) (not (eq role :hyp)))
                                               (cons (car by)
                                                     (if (member role '(:ir :axiom))
                                                         (mapcar #'rl (cdr by))
                                                         (let ((after-inst nil))
                                                           (mapcar (lambda (a)
                                                                     (prog1 (if after-inst a (rl a))
                                                                       (setf after-inst (eq a :inst))))
                                                                   (cdr by)))))
                                               by)))))))
             (cited-of (role by)
               (if (eq role :ir)
                   (let ((count (or (irule-premise-count (car by) ledger) 0)))
                     (values (subseq (cdr by) 0 (min count (length (cdr by)))) (nthcdr count (cdr by))))
                   (values (split-citation-inst (cdr by)) nil))))
      (catch 'expand-deduction
        (let ((work (copy-list raw-proof)))
          (loop while work
                do (destructuring-bind (n f role by) (pop work)
                     (setf (gethash n formula) f)
                     (case role
                       (:hyp
                        (if (equal f hyp)
                            (setf (gethash n dep) t
                                  (gethash n trans) (template-lines :assumption nil nil nil f))
                            (progn (setf (gethash n orig) (emit f :hyp nil))
                                   (push f open-hyps))))
                       (:axiom (setf (gethash n orig) (emit f :axiom by)))
                       (t
                        (multiple-value-bind (cited extras) (cited-of role by)
                          (let ((cited (mapcar #'res cited)))
                            (cond
                              ((notany (lambda (c) (gethash c dep)) cited)
                               (setf (gethash n orig)
                                     (emit f role
                                           (cons (car by)
                                                 (if (eq role :ir)
                                                     (append (mapcar (lambda (c) (gethash c orig)) cited) extras)
                                                     (let ((after-inst nil))
                                                       (mapcar (lambda (a)
                                                                 (prog1 (if (and (not after-inst)
                                                                                 (member (res a) cited :test #'equal))
                                                                            (gethash (res a) orig)
                                                                            a)
                                                                   (setf after-inst (eq a :inst))))
                                                               (cdr by))))))))
                              ((eq role :ir)
                               (setf (gethash n dep) t
                                     (gethash n trans)
                                     (template-lines (car by) (mapcar (lambda (c) (gethash c formula)) cited)
                                                     (mapcar #'ensure-trans cited) extras f)))
                              (t
                               ;; Unfold the citation and process its lines in its place.
                               (setf work (append (unfold (make-k-line :numbering n :formula f
                                                                       :role role :by by))
                                                  work))))))))))
          ;; The last line's H -> PHI must be the last line of the result.
          (let* ((last-n (res (first (car (last raw-proof)))))
                 (t-label (ensure-trans last-n)))
            (unless (eql t-label (first (first out)))
              (fail :conclusion-not-last))
            (nreverse out)))))))

(defun expanded-deduction-checks-p (raw-proof hyp ledger)
  "T iff RAW-PROOF (kernel form, Gamma, HYP |- PHI) expands
(EXPAND-DEDUCTION) into a proof that CHECK-K-PROOF accepts against LEDGER,
whose hypotheses are Gamma and whose conclusion is HYP -> PHI as the
system writes it. Otherwise (VALUES NIL reason)."
  (multiple-value-bind (expanded why) (expand-deduction raw-proof hyp ledger)
    (cond
      ((null expanded) (values nil why))
      ((not (equal (proof-conclusion expanded)
                   (discharge-formula hyp (proof-conclusion raw-proof) ledger)))
       (values nil :wrong-conclusion))
      ((not (equal (proof-hypotheses expanded)
                   (remove hyp (proof-hypotheses raw-proof) :test #'equal)))
       (values nil :wrong-hypotheses))
      (t (multiple-value-bind (ok bad) (%check-k-proof expanded ledger)
           (if ok t (values nil (list :rejected-line bad))))))))

(defun check-and-extend-by-deduction-direct (ledger name hyp-formula raw-proof &optional (log (silent-log)))
  "Admit HYP-FORMULA -> PHI as TH-DED entry NAME; see ADMIT-DEDUCTION."
  (admit-deduction ledger name hyp-formula raw-proof log nil))

(defun admit-deduction (ledger name hyp-formula raw-proof log origin-tail)
  "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT's work. ORIGIN-TAIL is a plist
appended to the entry's ORIGIN; (:BY-DESCRIPTION T) marks a lemma
generated by DEFINE-FUNCTION-BY-DESCRIPTION, saved as that command
rather than on its own.

Admit HYP-FORMULA -> PHI (as the system's :DISCHARGE declaration writes
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
      ;; With proof templates for every case it uses, the discharge is
      ;; also built as a real proof and checked; the ORIGIN records whether
      ;; it was (:EXPANDED T), or why not, in which case the declared cases
      ;; are trusted for this entry.
      (multiple-value-bind (expanded why) (expanded-deduction-checks-p db-proof db-hyp ledger)
        (log-admission-result log name t)
        ;; Kernel form in the payload, the text as written in the ORIGIN.
        (ledger-append ledger 'th-ded (list name db-hyp db-proof)
                       (list* :derived-by-deduction hyp-formula raw-proof
                             :expanded (and expanded t)
                             :not-expanded-because (and (not expanded) why)
                             origin-tail))))))

(defun deduction-entry-expanded-p (e)
  "T iff TH-DED entry E was admitted with its discharge built as a real,
checked proof (EXPANDED-DEDUCTION-CHECKS-P)."
  (getf (cdddr (entry-origin e)) :expanded))

(defun expand-deduction-entry (e ledger)
  "The real proof of Gamma |- H -> PHI behind TH-DED entry E of LEDGER, in
kernel form, or (VALUES NIL reason)."
  (destructuring-bind (name hyp proof) (entry-payload e)
    (declare (ignore name))
    (expand-deduction proof hyp (entries-upto (entry-k e) ledger))))
