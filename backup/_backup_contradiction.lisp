;;;; _backup_contradiction.lisp -- BACKUP (not loaded by any ASDF system)
;;;;
;;;; Removed from the kernel on 2026-10-26 (it came in with PR #25). The
;;;; kernel's one job is deciding x B_kappa y; noticing that a ledger has
;;;; reached a contradiction is a report about the ledger, not part of that
;;;; decision, so it belongs in a separate tool that reads .system and
;;;; .ledger files as data. Kept here as material for that tool.
;;;;
;;;; WHAT IT WAS
;;;;   A .system file could declare what it counts as a contradiction,
;;;;     (:contradiction NAME CONDITIONS (PATTERN...))
;;;;   e.g. (:contradiction a-and-not-a ((wff? ?A)) (?A (.neg ?A))) in the
;;;;   base system: closed theorems (TH, or TH-DED with no hypothesis left)
;;;;   instantiating every PATTERN under one binding meeting CONDITIONS.
;;;;   Whenever a closed theorem was admitted, the kernel looked for a
;;;;   declared contradiction it completed with earlier ones; it still
;;;;   admitted the theorem, appended a CONTRADICTION entry (form name,
;;;;   theorem names) and signalled a CONTRADICTION-DETECTED warning.
;;;;   LEDGER-CONTRADICTIONS listed them. Matching was on kernel forms
;;;;   (alpha-equivalence), without unifying schematic theorems.
;;;;
;;;; HOW TO RESTORE (into the kernel; a separate tool needs only
;;;; CLOSED-THEOREM-CONCLUSION, CLOSED-THEOREMS, CONTRADICTION-WITNESS)
;;;;   1. Put the code of src/contradiction.lisp below back as
;;;;      src/contradiction.lisp, after "deduction" in ledger-kernel.asd.
;;;;   2. In ADMIT-THEOREM (src/k-proof.lisp) and ADMIT-DEDUCTION /
;;;;      CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT (src/deduction.lisp), wrap
;;;;      the final (ledger-append ...) as (note-contradictions (ledger-append ...) name).
;;;;   3. Add the :CONTRADICTION clause below to the CASE in
;;;;      BOOTSTRAP-KERNEL-FROM-SPEC (src/system-spec.lisp), and the line
;;;;        ;;;   (:contradiction NAME CONDITIONS (PATTERN...))  -- see contradiction.lisp
;;;;      to its list of directives.
;;;;   4. Put the declaration below back into
;;;;      hilbert-library/00-classical-fol-equality.system, after the side
;;;;      conditions.
;;;;   5. Tests: tests/contradiction-tests.lisp below, after "deduction-tests"
;;;;      in the test system, and (run-contradiction-self-tests) in run.lisp.
;;;;   6. Web: the display and test snippets below (web/worlds.lisp: add
;;;;      CONTRADICTION-FORM to the rule-like kinds in ENTRY-STATEMENT and
;;;;      ENTRY-CONDITIONS).
;;;;
;;;; The code below is verbatim from commit 2451726 (before removal).

;;; =====================================================================
;;; src/contradiction.lisp
;;; =====================================================================

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

;;; =====================================================================
;;; src/system-spec.lisp: the clause in BOOTSTRAP-KERNEL-FROM-SPEC's CASE
;;; =====================================================================
#|
                (:contradiction
                 (destructuring-bind (name conditions patterns) (cdr cmd)
                   (unless (and (consp patterns) (proper-list-p patterns))
                     (error "BOOTSTRAP-KERNEL-FROM-SPEC: (:contradiction ~S ...) needs a ~
                             non-empty list of formula patterns, got ~S." name patterns))
                   (when (find name (entries-of-kind 'contradiction-form ledger)
                               :key (lambda (e) (first (entry-payload e))))
                     (error "BOOTSTRAP-KERNEL-FROM-SPEC: contradiction ~S is already declared." name))
                   (admit-rule ledger 'contradiction-form name conditions patterns)))
|#

;;; =====================================================================
;;; hilbert-library/00-classical-fol-equality.system
;;; =====================================================================
#|
;;; --- contradiction ------------------------------------------------------
;;;
;;; What this system counts as a contradiction: some formula and its
;;; negation both proved (contradiction.lisp). The kernel reports it if a
;;; ledger ever gets there; it cannot show that one never will.

(:contradiction a-and-not-a ((wff? ?A)) (?A (.neg ?A)))

|#

;;; =====================================================================
;;; web/worlds.lisp (ENTRY-STATEMENT) and web/tests.lisp (TEST-WEB-API)
;;; =====================================================================
#|
      ;; A declared contradiction: the formulas that, proved together, make one.
      (contradiction-form (values (mapcar (lambda (f) (display-pattern f p)) (third w)) (first p)))

    (let ((c (find "contradiction-form" entries :key (lambda (h) (gethash "kind" h)) :test #'string=)))
      (expect "api-entry: the declared contradiction A, not-A is listed and shown"
              (and c (hash-table-p (api-entry "zf" (gethash "k" c)))) t))
|#

;;; =====================================================================
;;; tests/contradiction-tests.lisp
;;; =====================================================================

;;; A system says what a contradiction is; the kernel reports a ledger
;;; that reaches one. These tests make a system inconsistent on purpose,
;;; with an axiom "every formula", and watch for the report.

(defun admit-quietly (thunk)
  "(VALUES ledger warnings): call THUNK, collecting CONTRADICTION-DETECTED
warnings instead of printing them."
  (let ((warnings nil))
    (values (handler-bind ((contradiction-detected
                             (lambda (w) (push w warnings) (muffle-warning w))))
              (funcall thunk))
            (nreverse warnings))))

(defun test-contradiction-detection ()
  (let ((base (fol-kernel)))
    (expect "the base system declares A and not-A as its contradiction"
            (mapcar (lambda (e) (first (entry-payload e))) (entries-of-kind 'contradiction-form base))
            '(a-and-not-a))
    (expect "the classical lemmas of 01 and 05 reach no contradiction"
            (ledger-contradictions (classical-logic-ledger base))
            nil)
    (let* ((bad (bootstrap-kernel-from-spec '((:axiom EVERYTHING ((wff? ?A)) (nil ?A))) :ledger base))
           (l1 (check-and-extend bad 'th 'th-eq '((0 (.eq v0 v0) :axiom (EVERYTHING))))))
      (expect "one theorem alone is no contradiction"
              (ledger-contradictions l1) nil)
      (multiple-value-bind (l2 warnings)
          (admit-quietly (lambda ()
                           (check-and-extend l1 'th 'th-neq '((0 (.neg (.eq v0 v0)) :axiom (EVERYTHING))))))
        (expect "proving its negation too is reported: (A-AND-NOT-A (TH-EQ TH-NEQ))"
                (equal (ledger-contradictions l2) '((a-and-not-a (th-eq th-neq))))
                t)
        (expect "... with a CONTRADICTION-DETECTED warning"
                (and (= (length warnings) 1)
                     (equal (contradiction-theorems (first warnings)) '(th-eq th-neq)))
                t)
        (expect "... and the theorem is still admitted"
                (check-k-proof '((0 (.neg (.eq v0 v0)) :th (th-neq))) l2) t)
        (expect "the report is not saved: replaying the ledger finds it again"
                (equal (ledger-contradictions
                        (admit-quietly (lambda () (ledger-from-commands (ledger-commands l2) :ledger bad))))
                       '((a-and-not-a (th-eq th-neq))))
                t))
      (expect "found in either order, and up to the names of bound variables"
              (equal (ledger-contradictions
                      (admit-quietly
                       (lambda ()
                         (let ((l (check-and-extend bad 'th 'th-n
                                                    '((0 (.neg (.forall v1 (.eq v1 v1))) :axiom (EVERYTHING))))))
                           (check-and-extend l 'th 'th-p '((0 (.forall v2 (.eq v2 v2)) :axiom (EVERYTHING))))))))
                     '((a-and-not-a (th-p th-n))))
              t)
      (expect "a closed TH-DED counts: H -> H and not (H -> H)"
              (equal (ledger-contradictions
                      (admit-quietly
                       (lambda ()
                         (let ((l (check-and-extend-by-deduction-direct bad 'th-id '(.eq v0 v1)
                                                                       '((0 (.eq v0 v1) :hyp nil)))))
                           (check-and-extend l 'th 'th-not-id
                                             '((0 (.neg (.to (.eq v0 v1) (.eq v0 v1))) :axiom (EVERYTHING))))))))
                     '((a-and-not-a (th-id th-not-id))))
              t)
      (expect "a theorem still resting on a hypothesis does not count"
              (ledger-contradictions
               (admit-quietly
                (lambda ()
                  (check-and-extend l1 'th 'th-neq-hyp
                                    '((0 (.neg (.eq v0 v0)) :hyp nil))))))
              nil)))
  (let* ((bare (bootstrap-kernel-from-spec
                '((:wff-formation wff_to? ((wff? ?A) (wff? ?B)) (wff? (.to ?A ?B)))
                  (:axiom EVERYTHING ((wff? ?A)) (nil ?A)))))
         (l (check-and-extend bare 'th 'th-a '((0 A :axiom (EVERYTHING)))))
         (l (check-and-extend l 'th 'th-h '((0 H :axiom (EVERYTHING))))))
    (expect "a system that declares no contradiction has nothing to report"
            (ledger-contradictions l) nil)
    (let* ((bot (bootstrap-kernel-from-spec '((:contradiction falsum () (H))) :ledger bare)))
      (expect "a one-formula contradiction (a falsum H): proving H is reported"
              (equal (ledger-contradictions
                      (admit-quietly (lambda () (check-and-extend bot 'th 'th-h '((0 H :axiom (EVERYTHING)))))))
                     '((falsum (th-h))))
              t)
      (expect "... and proving A is not"
              (ledger-contradictions (check-and-extend bot 'th 'th-a '((0 A :axiom (EVERYTHING)))))
              nil)
      (expect "Attack: declaring the same contradiction twice -- must error"
              (handler-case (progn (bootstrap-kernel-from-spec '((:contradiction falsum () (A))) :ledger bot)
                                   :admitted)
                (error () :refused))
              :refused))))

(defun run-contradiction-self-tests ()
  "Declared contradictions and their detection."
  (test-contradiction-detection)
  (format t "~%Contradiction self-tests complete.~%"))
