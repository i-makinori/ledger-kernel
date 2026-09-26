;;;; tautology.lisp -- Section 15: PROVE-TAUTOLOGY (Kalmar's completeness theorem)
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 15. PROVE-TAUTOLOGY: Kalmar's completeness theorem as a tactic
;;; ---------------------------------------------------------------------
;;;
;;; Section 14 gave the kernel the handful of classical facts (TH-EX-
;;; FALSO, TH-DNEG-INTRO, TH-NEG-IMPL, II.4) that Lukasiewicz proved are
;;; enough, together with MP, to prove EVERY classical propositional
;;; tautology. This section cashes that fact in as a genuine tactic:
;;; PROVE-TAUTOLOGY takes any formula built from .TO/.NEG, checks it is
;;; actually a tautology by brute-force truth table, and if so
;;; mechanically constructs and ADMITS a real, fully checked Hilbert
;;; proof of it -- no different in kind from a hand-written one, since
;;; every line it emits still goes through CHECK-K-PROOF via ordinary
;;; CHECK-AND-EXTEND/CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT. Nothing here
;;; has to be trusted beyond what Sections 1-14 already established.
;;;
;;; The construction is Kalmar's Lemma plus a standard case-split
;;; combination:
;;;   - For a fixed valuation V and formula F, define F^V := F when F is
;;;     true under V, else (.NEG F). Kalmar's Lemma: the V-signed atoms
;;;     of F prove F^V, by structural induction on F --
;;;     KALMAR/KALMAR-BRANCH below. The .TO case needs TH-EX-FALSO
;;;     (consequent true, or antecedent false) and TH-NEG-IMPL
;;;     (antecedent true, consequent false); the .NEG case needs
;;;     TH-DNEG-INTRO.
;;;   - Since the target is an actual tautology, F^V is just F itself
;;;     for every V, so this gives {atom^V} |- F for EVERY valuation.
;;;     Eliminating the atoms one at a time via II.4's case-split
;;;     (KALMAR-COMBINE/KALMAR-NODE) -- for each atom P, combining the
;;;     P-true and P-false branches into one that no longer mentions P
;;;     -- ends with the fully closed theorem |- F.
;;; This is exactly the textbook proof of Post/Lukasiewicz completeness,
;;; run mechanically and checked at every step.
;;;
;;; DEFINED CONNECTIVES. When hilbert-library/00-connectives.system is
;;; loaded, .AND/.OR/.IFF are handled too, without treating them as
;;; atoms: each is evaluated through its fixed expansion (KEXPAND), and
;;; Kalmar's Lemma for (.AND A B) etc. is obtained from the lemma for its
;;; expansion E:
;;;   - true case:  E, and the FOLD axiom E -> D, give D by MP;
;;;   - false case: (.neg E), the UNFOLD axiom D -> E, and a contraposition
;;;     lemma (D -> E) -> (.neg E -> .neg D) give (.neg D) by MP twice.
;;; The contraposition lemma is itself proved first, by this same tactic,
;;; on the pure .TO/.NEG formula (A -> B) -> (.neg B -> .neg A).
;;;
;;; ATOMS. Any subformula that is not .TO/.NEG or a defined connective is
;;; an atom -- a bare atomic-wff symbol, but equally (.in v0 v1),
;;; (.forall v0 A) or (.exists1 v0 A). Only the propositional structure
;;; above the atoms is used.
;;;
;;; NAMES. The intermediate TH-DED entries the case-split admits are named
;;; NAME.T1, NAME.F1, NAME.T2, ... and the contraposition lemma
;;; NAME.CONTRA, where NAME is the theorem being proved -- interned,
;;; deterministic names, so a ledger built with this tactic can be written
;;; out with WRITE-LEDGER-TO-FILE and read back (an uninterned GENSYM would
;;; not read back as the same symbol at each citation).

(defun kto? (f) (and (consp f) (eq (car f) '.to) (= (length f) 3)))
(defun kneg? (f) (and (consp f) (eq (car f) '.neg) (= (length f) 2)))

(defun kdefined-connectives ()
  "Defined binary connectives the tactic sees through, as
(HEAD FOLD-AXIOM UNFOLD-AXIOM); see hilbert-library/00-connectives.system."
  '((.and and-fold and-unfold)
    (.or or-fold or-unfold)
    (.iff iff-fold iff-unfold)))

(defun kdefined? (f)
  (and (consp f) (= (length f) 3) (assoc (car f) (kdefined-connectives))))

(defun kexpand (f)
  "The fixed expansion of a defined connective (one level only)."
  (destructuring-bind (head a b) f
    (ecase head
      (.and (list '.neg (list '.to a (list '.neg b))))
      (.or (list '.to (list '.neg a) b))
      (.iff (list '.and (list '.to a b) (list '.to b a))))))

(defun katoms-of (f &optional acc)
  "All atomic (non-.TO, non-.NEG, non-defined-connective) subformulas of
F, deduplicated."
  (cond
    ((kto? f) (katoms-of (third f) (katoms-of (second f) acc)))
    ((kneg? f) (katoms-of (second f) acc))
    ((kdefined? f) (katoms-of (third f) (katoms-of (second f) acc)))
    (t (adjoin f acc :test #'equal))))

(defun kuses-defined-p (f)
  (cond ((kdefined? f) t)
        ((kto? f) (or (kuses-defined-p (second f)) (kuses-defined-p (third f))))
        ((kneg? f) (kuses-defined-p (second f)))
        (t nil)))

(defun ktruth (f v)
  "Ordinary two-valued truth evaluation of F under valuation V (an alist
atom -> generalized boolean)."
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
  "NAME.T<n> / NAME.F<n>: a fresh, interned name for an intermediate
entry of the theorem *KNAME* (see the NAMES note above)."
  (let ((pkg (or (symbol-package *kname*) (find-package :ledger-kernel))))
    (intern (format nil "~A.~A~D" (symbol-name *kname*) tag (incf *kname-count*)) pkg)))

(defun kemit (formula role by)
  "Append a new raw-proof line for FORMULA unless one already exists
(memoized on FORMULA itself, so KALMAR never re-derives the same
signed subformula twice within one branch). Returns its line number."
  (or (gethash formula *kindex*)
      (let ((n (hash-table-count *kindex*)))
        (push (list n formula role by) *klines*)
        (setf (gethash formula *kindex*) n)
        n)))

(defun kalmar (f v)
  "Ensures (KSIGNED F V) has a line in *KLINES*/*KINDEX*; returns its
line number. Structural induction on F, per Kalmar's Lemma (see this
section's header comment for the four cases)."
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
  "Flat raw-proof for {atom^v : atom in ATOMS-ORDER} |- TARGET, hyp lines
numbered 0..n-1 in ATOMS-ORDER's own order."
  (let ((*klines* nil) (*kindex* (make-hash-table :test #'equal)))
    (dolist (a atoms-order) (kemit (ksigned a full-v) :hyp nil))
    (kalmar target full-v)
    (nreverse *klines*)))

(defun kalmar-combine (ledger k next-atom target raw-true raw-false log)
  "Given RAW-TRUE (:hyp lines = PREFIX ++ [next-atom]) and RAW-FALSE
(:hyp lines = PREFIX ++ [not next-atom]), both concluding TARGET, admits
both as (gensym-named) TH-DED entries discharging NEXT-ATOM, then emits
a flat continuation proof (5 more lines, numbered K..K+4) combining them
via a II.4 case-split. Returns (VALUES LEDGER' LINES) -- LINES excludes
the K :hyp lines for PREFIX, which the caller (KALMAR-NODE) already
knows how to reconstruct."
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
  "Returns (VALUES LEDGER' RAW-PROOF), RAW-PROOF having exactly
(LENGTH PREFIX-V) :hyp lines -- (KSIGNED atom prefix-v) for each atom in
ATOMS-ORDER already fixed by PREFIX-V, in that order -- and concluding
TARGET, with every atom past that point already eliminated via KALMAR
plus a II.4 case-split."
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
  "Checks TARGET is a genuine classical tautology (brute-force truth
table over its own atoms), then mechanically builds and admits a real
checked Hilbert proof of it under NAME, returning the extended ledger.
TARGET is built from .TO/.NEG and, if hilbert-library/00-connectives.system
is loaded, .AND/.OR/.IFF, over arbitrary atoms (see the ATOMS note
above). LEDGER must already carry TH-EX-FALSO, TH-DNEG-INTRO, TH-NEG-IMPL
and axiom II.4 -- e.g. a ledger that has replayed 01-propositional-
core.ledger and 05-classical-logic.ledger, or TEST-CLASSICAL-LOGIC's
in-memory equivalent. Besides NAME itself, admits the intermediate
entries NAME.T<n>/NAME.F<n> (and NAME.CONTRA when a defined connective
occurs)."
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
