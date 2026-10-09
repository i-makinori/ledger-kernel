;;;; _backup_tautology.lisp -- BACKUP (not loaded by any ASDF system)
;;;;
;;;; Removed from the kernel on 2026-10-09. PROVE-TAUTOLOGY builds proofs by
;;;; following Kalmar's proof of the completeness theorem, a meta-theorem;
;;;; generating proofs by relying on it is beyond what the kernel should
;;;; vouch for, so it is no longer part of the system. Axiom II.4 (the case
;;;; split), which existed for this construction, was removed from
;;;; 00-classical-fol-equality.system at the same time and is now the
;;;; theorem TH-CASE-SPLIT of 05-classical-logic.ledger.
;;;;
;;;; WHAT IT WAS
;;;;   PROVE-TAUTOLOGY: truth-table check of a propositional formula, then a
;;;;   Hilbert proof of it by Kalmar's Lemma (signed atoms prove the signed
;;;;   formula, by induction) and elimination of the atoms one at a time by
;;;;   the case split. Every emitted line was still checked by the kernel.
;;;;   hilbert-library/06-connectives.ledger was generated with it
;;;;   (_backup_generate-connectives-ledger.lisp); that file is ordinary
;;;;   checked proofs and no longer needs this code.
;;;;
;;;; HOW TO RESTORE
;;;;   1. Move this file back to src/tautology.lisp and add (:file "tautology")
;;;;      after "deduction" in ledger-kernel.asd; re-export PROVE-TAUTOLOGY.
;;;;   2. It emits ':axiom (ii.4)' lines (KALMAR-COMBINE). Either restore the
;;;;      II.4 axiom in the .system file, or emit ':th-ded (th-case-split)'
;;;;      instead (the same formula, with A and C matched schematically).
;;;;   3. Tests: _backup_tautology-tests.lisp (add (:file "tautology-tests")
;;;;      and call RUN-TACTICS-SELF-TESTS from tests/run.lisp); it also holds
;;;;      the PROVE-TAUTOLOGY tests that were in connectives-tests.lisp and
;;;;      empty-set-tests.lisp.
;;;;
;;;; ---------------------------------------------------------------------
;;;; Original code (src/tautology.lisp), verbatim:
;;;; ---------------------------------------------------------------------

;;;; tautology.lisp -- PROVE-TAUTOLOGY (Kalmar's completeness proof as a tactic)
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; PROVE-TAUTOLOGY checks a propositional formula by truth table and, if
;;; it is a tautology, builds a Hilbert proof of it. Every line it emits
;;; is checked by the kernel (CHECK-AND-EXTEND / CHECK-AND-EXTEND-BY-
;;; DEDUCTION-DIRECT), so the tactic itself need not be trusted.
;;;
;;; Construction (Kalmar):
;;;   - For valuation V let F^V be F if F is true under V, else (.NEG F).
;;;     Kalmar's Lemma: the V-signed atoms of F prove F^V, by induction on
;;;     F (KALMAR). .TO uses axiom II.1, TH-EX-FALSO and TH-NEG-IMPL; .NEG
;;;     uses TH-DNEG-INTRO.
;;;   - For a tautology F^V = F for every V. Atoms are then eliminated one
;;;     at a time by combining the P-true and P-false branches with the
;;;     II.4 case split (KALMAR-NODE / KALMAR-COMBINE), leaving |- F.
;;;
;;; Defined connectives (.AND/.OR/.IFF, from 00-connectives.system) are
;;; not atoms: each is handled through its one-level expansion E (KEXPAND).
;;; If true, the FOLD axiom E -> D gives D by MP. If false, (.neg E), the
;;; UNFOLD axiom D -> E and the contraposition lemma
;;; (D -> E) -> (.neg E -> .neg D) give (.neg D). That lemma is proved
;;; first by this same tactic and admitted as NAME.CONTRA.
;;;
;;; Atoms: any subformula that is not .TO/.NEG or a defined connective,
;;; e.g. A, (.in v0 v1), (.forall v0 A).
;;;
;;; Intermediate entries are named NAME.T1, NAME.F1, ... (interned, not
;;; GENSYMs) so a ledger that uses the tactic can be saved and reloaded.

(defun kto? (f) (and (consp f) (eq (car f) '.to) (= (length f) 3)))
(defun kneg? (f) (and (consp f) (eq (car f) '.neg) (= (length f) 2)))

(defun kdefined-connectives ()
  "Defined binary connectives the tactic sees through, as
(HEAD FOLD-AXIOM UNFOLD-AXIOM); see hilbert-library/00-connectives.system."
  '((.and and-fold and-unfold)
    (.or or-fold or-unfold)
    (.iff iff-fold iff-unfold)))

(defun kdefined? (f)
  "F's row in KDEFINED-CONNECTIVES if F is a defined-connective formula, else NIL."
  (and (consp f) (= (length f) 3) (assoc (car f) (kdefined-connectives))))

(defun kexpand (f)
  "The fixed expansion of a defined connective (one level only)."
  (destructuring-bind (head a b) f
    (ecase head
      (.and (list '.neg (list '.to a (list '.neg b))))
      (.or (list '.to (list '.neg a) b))
      (.iff (list '.and (list '.to a b) (list '.to b a))))))

(defun katoms-of (f &optional acc)
  "The distinct atoms of F."
  (cond
    ((kto? f) (katoms-of (third f) (katoms-of (second f) acc)))
    ((kneg? f) (katoms-of (second f) acc))
    ((kdefined? f) (katoms-of (third f) (katoms-of (second f) acc)))
    (t (adjoin f acc :test #'equal))))

(defun kuses-defined-p (f)
  "True if a defined connective occurs in F's propositional structure."
  (cond ((kdefined? f) t)
        ((kto? f) (or (kuses-defined-p (second f)) (kuses-defined-p (third f))))
        ((kneg? f) (kuses-defined-p (second f)))
        (t nil)))

(defun ktruth (f v)
  "Truth value of F under valuation V, an alist atom -> boolean."
  (cond
    ((kto? f) (or (not (ktruth (second f) v)) (ktruth (third f) v)))
    ((kneg? f) (not (ktruth (second f) v)))
    ((kdefined? f) (ktruth (kexpand f) v))
    (t (let ((cell (assoc f v :test #'equal)))
         (unless cell (error "KTRUTH: ~S not assigned in valuation ~S" f v))
         (cdr cell)))))

(defun ksigned (f v) (if (ktruth f v) f (list '.neg f)))

(defun kall-valuations (atoms)
  "Every total boolean valuation of ATOMS, as a list of alists."
  (if (null atoms)
      (list nil)
      (let ((rest (kall-valuations (cdr atoms))))
        (append (mapcar (lambda (r) (cons (cons (car atoms) t) r)) rest)
                (mapcar (lambda (r) (cons (cons (car atoms) nil) r)) rest)))))

(defvar *klines*)
(defvar *kindex*)
(defvar *kname*)
(defvar *kname-count*)
(defvar *kcontra* nil
  "Name of the contraposition lemma the defined-connective case cites.")

(defun knext-name (tag)
  "A fresh interned name *KNAME*.<TAG><n> for an intermediate entry."
  (let ((pkg (or (symbol-package *kname*) (find-package :ledger-kernel))))
    (intern (format nil "~A.~A~D" (symbol-name *kname*) tag (incf *kname-count*)) pkg)))

(defun kemit (formula role by)
  "Line number of FORMULA in the current branch, appending a line if it
has none yet (so no signed subformula is derived twice)."
  (or (gethash formula *kindex*)
      (let ((n (hash-table-count *kindex*)))
        (push (list n formula role by) *klines*)
        (setf (gethash formula *kindex*) n)
        n)))

(defun kalmar (f v)
  "Line number of a derivation of (KSIGNED F V) from the signed atoms
(Kalmar's Lemma, by induction on F). Atoms must already be hypotheses."
  (or (gethash (ksigned f v) *kindex*)
      (cond
        ((kto? f)
         (let ((b (second f)) (c (third f)))
           (cond
             ((ktruth c v)
              (let* ((cl (kalmar c v))
                     (ax (kemit (list '.to c (list '.to b c)) :axiom '(ii.1))))
                (kemit (list '.to b c) :ir (list 'mp ax cl))))
             ((not (ktruth b v))
              (let* ((nbl (kalmar b v))
                     (helper (kemit (list '.to (list '.neg b) (list '.to b c)) :th-ded '(th-ex-falso))))
                (kemit (list '.to b c) :ir (list 'mp helper nbl))))
             (t
              (let* ((bl (kalmar b v))
                     (ncl (kalmar c v))
                     (helper (kemit (list '.to (list '.neg c) (list '.neg (list '.to b c))) :th-ded (list 'th-neg-impl bl))))
                (kemit (list '.neg (list '.to b c)) :ir (list 'mp helper ncl)))))))
        ((kneg? f)
         (let ((b (second f)))
           (if (ktruth b v)
               (let* ((bl (kalmar b v))
                      (helper (kemit (list '.to b (list '.neg (list '.neg b))) :th-ded '(th-dneg-intro))))
                 (kemit (list '.neg (list '.neg b)) :ir (list 'mp helper bl)))
               (kalmar b v))))
        ((kdefined? f)
         (destructuring-bind (fold unfold) (cdr (kdefined? f))
           (let* ((e (kexpand f))
                  (el (kalmar e v)))
             (if (ktruth f v)
                 (let ((ax (kemit (list '.to e f) :axiom (list fold))))
                   (kemit f :ir (list 'mp ax el)))
                 (let* ((ax (kemit (list '.to f e) :axiom (list unfold)))
                        (ct (kemit (list '.to (list '.to f e) (list '.to (list '.neg e) (list '.neg f)))
                                   :th (list *kcontra*)))
                        (c2 (kemit (list '.to (list '.neg e) (list '.neg f)) :ir (list 'mp ct ax))))
                   (kemit (list '.neg f) :ir (list 'mp c2 el)))))))
        (t (error "KALMAR: atom ~S not pre-seeded for valuation ~S" f v)))))

(defun kalmar-branch (target full-v atoms-order)
  "Raw proof of TARGET from the atoms signed by FULL-V, as hypothesis lines
0..n-1 in ATOMS-ORDER."
  (let ((*klines* nil) (*kindex* (make-hash-table :test #'equal)))
    (dolist (a atoms-order) (kemit (ksigned a full-v) :hyp nil))
    (kalmar target full-v)
    (nreverse *klines*)))

(defun kalmar-combine (ledger k next-atom target raw-true raw-false log)
  "Admit RAW-TRUE (hypotheses PREFIX + NEXT-ATOM) and RAW-FALSE (PREFIX +
(.neg NEXT-ATOM)) as TH-DED entries, and return (VALUES LEDGER LINES):
five lines K..K+4 deriving TARGET from PREFIX by the II.4 case split.
LINES omits PREFIX's K hypothesis lines."
  (let* ((name-t (knext-name "T"))
         (name-f (knext-name "F"))
         (ledger (check-and-extend-by-deduction-direct ledger name-t next-atom raw-true log))
         (ledger (check-and-extend-by-deduction-direct ledger name-f (list '.neg next-atom) raw-false log))
         (gamma-idx (loop for i from 0 below k collect i))
         (line-t (list k (list '.to next-atom target) :th-ded (cons name-t gamma-idx)))
         (line-f (list (+ k 1) (list '.to (list '.neg next-atom) target) :th-ded (cons name-f gamma-idx)))
         (line-ax (list (+ k 2)
                         (list '.to (list '.to next-atom target)
                               (list '.to (list '.to (list '.neg next-atom) target) target))
                         :axiom '(ii.4)))
         (line-mp1 (list (+ k 3) (list '.to (list '.to (list '.neg next-atom) target) target)
                         :ir (list 'mp (+ k 2) k)))
         (line-mp2 (list (+ k 4) target :ir (list 'mp (+ k 3) (+ k 1)))))
    (values ledger (list line-t line-f line-ax line-mp1 line-mp2))))

(defun kalmar-node (ledger atoms-order prefix-v target &optional (log (silent-log)))
  "Return (VALUES LEDGER RAW-PROOF): a proof of TARGET whose only
hypotheses are the atoms fixed by PREFIX-V, signed, in ATOMS-ORDER; the
remaining atoms are eliminated by case splits."
  (let ((k (length prefix-v)) (n (length atoms-order)))
    (if (= k n)
        (values ledger (kalmar-branch target prefix-v atoms-order))
        (let ((next-atom (nth k atoms-order)))
          (multiple-value-bind (ledger raw-true)
              (kalmar-node ledger atoms-order (append prefix-v (list (cons next-atom t))) target log)
            (multiple-value-bind (ledger raw-false)
                (kalmar-node ledger atoms-order (append prefix-v (list (cons next-atom nil))) target log)
              (multiple-value-bind (ledger tail-lines)
                  (kalmar-combine ledger k next-atom target raw-true raw-false log)
                (let ((prefix-lines (loop for i from 0 below k
                                           collect (list i (ksigned (nth i atoms-order) prefix-v) :hyp nil))))
                  (values ledger (append prefix-lines tail-lines))))))))))

(defun prove-tautology (ledger target name &optional (log (silent-log)))
  "Admit tautology TARGET as theorem NAME, or signal an error if it is not
a tautology. LEDGER must already have TH-EX-FALSO, TH-DNEG-INTRO,
TH-NEG-IMPL and axiom II.4 (e.g. after 01-propositional-core.ledger and
05-classical-logic.ledger). Also admits NAME.T<n>, NAME.F<n>, and
NAME.CONTRA when a defined connective occurs."
  (let* ((atoms (sort (copy-list (katoms-of target)) #'string<
                      :key (lambda (a) (let ((*package* (find-package :ledger-kernel)))
                                         (prin1-to-string a)))))
         (pkg (or (symbol-package name) (find-package :ledger-kernel)))
         (contra (and (kuses-defined-p target)
                      (intern (format nil "~A.CONTRA" (symbol-name name)) pkg)))
         (ledger (progn
                   (dolist (v (kall-valuations atoms))
                     (unless (ktruth target v)
                       (error "PROVE-TAUTOLOGY: ~S is FALSE under ~S -- not a tautology, refusing."
                              target v)))
                   (if contra
                       (prove-tautology ledger '(.to (.to a b) (.to (.neg b) (.neg a))) contra log)
                       ledger))))
    (let ((*kname* name) (*kname-count* 0) (*kcontra* contra))
      (multiple-value-bind (ledger raw) (kalmar-node ledger atoms nil target log)
        (check-and-extend ledger 'th name raw log)))))
