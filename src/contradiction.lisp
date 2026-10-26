;;;; contradiction.lisp -- what a system counts as a contradiction, and noticing it
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; What a contradiction is depends on the system: A together with not-A
;;; in classical logic, a constant falsum in another, perhaps nothing
;;; expressible at all in a system without negation. So the kernel fixes
;;; no notion of it. A .system file may declare one or more
;;;   (:contradiction NAME CONDITIONS (PATTERN...))
;;; meaning: the ledger is in contradiction when closed theorems (TH, or
;;; TH-DED with no hypothesis left) instantiate every PATTERN under one
;;; binding that satisfies CONDITIONS. The classical one is
;;;   (:contradiction a-and-not-a ((wff? ?A)) (?A (.neg ?A)))
;;; A system that declares none has no notion of contradiction, and
;;; nothing is ever reported for it.
;;;
;;; Whenever a closed theorem is admitted, the kernel looks for a
;;; declared contradiction that it completes together with earlier closed
;;; theorems. If it finds one, the theorem is still admitted -- it is a
;;; theorem of the system as given -- but an entry CONTRADICTION
;;; (FORM-NAME THEOREM-NAME...) is appended right after it and a
;;; CONTRADICTION-DETECTED warning is signalled.
;;;
;;; This is a report, not part of soundness. The patterns are matched
;;; against the theorems' kernel forms, so alpha-equivalent formulas meet
;;; but schematic theorems are not unified with one another: theorems
;;; (.to A A) and (.neg (.to A A)) are found, (.to A A) and
;;; (.neg (.to B B)) are not. Finding nothing proves nothing (Goedel's
;;; second incompleteness theorem).

(define-condition contradiction-detected (warning)
  ((form-name :initarg :form-name :reader contradiction-form-name)
   (theorems :initarg :theorems :reader contradiction-theorems))
  (:report (lambda (c stream)
             (format stream "The ledger is in contradiction (~S): ~{~S~^, ~}."
                     (contradiction-form-name c) (contradiction-theorems c)))))

(defun closed-theorem-conclusion (e ledger)
  "The formula TH / TH-DED entry E proves outright, or NIL if E still
depends on hypotheses."
  (case (entry-kind e)
    (th (let ((proof (second (entry-payload e))))
          (and (null (proof-hypotheses proof)) (proof-conclusion proof))))
    (th-ded (destructuring-bind (name hyp proof) (entry-payload e)
              (declare (ignore name))
              (and (null (remove hyp (proof-hypotheses proof) :test #'equal))
                   (discharge-formula hyp (proof-conclusion proof) ledger))))))

(defun closed-theorems (ledger)
  "(ENTRY . CONCLUSION) for every closed theorem of LEDGER."
  (loop for e in (append (entries-of-kind 'th ledger) (entries-of-kind 'th-ded ledger))
        for c = (closed-theorem-conclusion e ledger)
        when c collect (cons e c)))

(defun contradiction-witness (form-entry new-entry new-conclusion ledger)
  "The entries, one per pattern of contradiction FORM-ENTRY, of closed
theorems that instantiate its patterns under one binding meeting its
conditions, NEW-ENTRY (concluding NEW-CONCLUSION) among them; or NIL."
  (destructuring-bind (name conditions patterns) (entry-payload form-entry)
    (declare (ignore name))
    (let ((theorems nil))
      (labels ((rest-of (pats binds acc)
                 (if (null pats)
                     ;; (:FOUND entry...), so that a one-pattern form,
                     ;; with no other entry to find, still answers non-NIL.
                     (and (nth-value 1 (check-conditions conditions binds ledger))
                          (cons :found (reverse acc)))
                     (dolist (th (or theorems (setf theorems (closed-theorems ledger))) nil)
                       (let ((b (match-template (car pats) (cdr th) binds)))
                         (unless (match-fail-p b)
                           (let ((found (rest-of (cdr pats) b (cons (car th) acc))))
                             (when found (return found)))))))))
        ;; NEW-ENTRY takes each pattern's place in turn; the others are
        ;; looked for among all closed theorems.
        (loop for i from 0 below (length patterns)
              for b = (match-template (nth i patterns) new-conclusion
                                      (seed-fresh nil new-conclusion))
              unless (match-fail-p b)
                do (let ((found (rest-of (append (subseq patterns 0 i) (nthcdr (1+ i) patterns))
                                         b nil)))
                     (when found
                       (let ((others (cdr found)))
                         (return (append (subseq others 0 i) (list new-entry) (nthcdr i others)))))))))))

(defun note-contradictions (ledger name)
  "LEDGER, in which the TH / TH-DED entry NAME has just been admitted,
with a CONTRADICTION entry appended for each declared contradiction it
completes (see above), signalling CONTRADICTION-DETECTED for each."
  (let ((forms (entries-of-kind 'contradiction-form ledger)))
    (if (null forms)
        ledger
        (let* ((e (car (last (treap-values-below (alist-get (ledger-by-derived-name ledger) name) nil))))
               (conclusion (and e (closed-theorem-conclusion e ledger))))
          (if (null conclusion)
              ledger
              (dolist (form forms ledger)
                (let ((witness (contradiction-witness form e conclusion ledger)))
                  (when witness
                    (let ((form-name (first (entry-payload form)))
                          (names (mapcar (lambda (w) (first (entry-payload w))) witness)))
                      (setf ledger (ledger-append ledger 'contradiction (list form-name names)
                                                  (list :detected)))
                      (warn 'contradiction-detected :form-name form-name :theorems names))))))))))

(defun ledger-contradictions (ledger)
  "The contradictions found in LEDGER so far, as (FORM-NAME THEOREM-NAMES)."
  (mapcar #'entry-payload (entries-of-kind 'contradiction ledger)))
