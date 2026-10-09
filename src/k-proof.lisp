;;;; k-proof.lisp -- checking proofs and admitting theorems (CHECK-AND-EXTEND)
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; A proof line is (NUMBERING FORMULA ROLE BY). ROLE and BY:
;;;   :HYP             BY ignored                -- an open hypothesis
;;;   :AXIOM           (axiom-name extra...)     -- an axiom instance
;;;   :IR              (irule-name n... extra...) -- a rule applied to lines n...
;;;   :TH or :TH-DED   (name n... [:inst binds]) -- cite a derived entry
;;; Any role other than :HYP/:AXIOM/:IR is treated as a derived citation,
;;; and either role finds a TH or TH-DED entry of that name.
;;;
;;; CHECK-K-PROOF checks lines in order. A line citing a derived entry is
;;; never trusted on a pattern match alone: the entry's stored proof is
;;; instantiated and re-verified recursively, bottoming out at primitive
;;; (axiom / irule) entries.

(defstruct k-line numbering formula role by)

(defun raw->k-line (raw)
  (destructuring-bind (numbering formula role by) raw
    (make-k-line :numbering numbering :formula formula :role role :by by)))

(defun find-proven (numbering proven-alist)
  (cdr (assoc numbering proven-alist :test #'equal)))

(defun match-templates-seq (pats vals binds)
  "MATCH-TEMPLATE each of PATS against the same-position VALS, threading
BINDS. +FAIL+ on any mismatch or a length difference."
  (cond
    ((match-fail-p binds) +fail+)
    ((and (null pats) (null vals)) binds)
    ((or (null pats) (null vals)) +fail+)
    (t (match-templates-seq (cdr pats) (cdr vals)
                             (match-template (car pats) (car vals) binds)))))

(defun resolve-cited (nums proven-alist)
  "The formulas proven at line numbers NUMS, or +FAIL+ if one is absent."
  (cond
    ((null nums) nil)
    (t (let ((actual (find-proven (car nums) proven-alist)))
         (if (null actual)
             +fail+
             (let ((rest (resolve-cited (cdr nums) proven-alist)))
               (if (match-fail-p rest) +fail+ (cons actual rest))))))))

(defun check-k-ir-line (line proven-alist ledger open-hyps)
  "Check an :IR line. BY = (irule-name cited-line... extra-arg...); an
irule's FORM is (PREMISE-PATS EXTRA-PATS :=> CONCLUSION-PAT). Extra args
are literal values, not line numbers: (Gen 0 v0) cites line 0 and passes
the variable v0. Premises, then extras, then LINE's formula are matched
in order; the side conditions may consult OPEN-HYPS (Gamma).
Tries every irule entry of that name."
  (destructuring-bind (irule-name . rest) (k-line-by line)
    (labels ((try-entries (entries)
               (and entries
                    (or (try-ir-entry (car entries) irule-name rest line proven-alist ledger open-hyps)
                        (try-entries (cdr entries))))))
      (try-entries (entries-of-kind 'irule ledger)))))

(defun try-ir-entry (entry irule-name rest line proven-alist ledger open-hyps)
  "T iff irule ENTRY justifies LINE (see CHECK-K-IR-LINE)."
  (destructuring-bind (name conditions form) (entry-payload entry)
    (and (eq name irule-name)
         (destructuring-bind (premise-pats extra-pats arrow concl-pat) form
           (declare (ignore arrow))
           (let ((n (length premise-pats)) (m (length extra-pats)))
             (and (= (length rest) (+ n m))
                  (let* ((cited (subseq rest 0 n))
                         (extras (subseq rest n))
                         (actuals (resolve-cited cited proven-alist)))
                    (and (not (match-fail-p actuals))
                         (let ((b1 (match-templates-seq premise-pats actuals
                                                        (seed-fresh nil actuals extras (k-line-formula line)))))
                           (and (not (match-fail-p b1))
                                (let ((b2 (match-templates-seq extra-pats extras b1)))
                                  (and (not (match-fail-p b2))
                                       (let ((b3 (match-template concl-pat (k-line-formula line) b2)))
                                         (and (not (match-fail-p b3))
                                              (nth-value 1 (check-conditions conditions b3 ledger nil open-hyps))))))))))))))))

(defun check-k-axiom-line (line ledger open-hyps)
  "Check an :AXIOM line. BY = (axiom-name extra-arg...), literal values
such as the term in (III.1 v2); axioms cite no lines. An axiom's FORM is
(EXTRA-PATS CONCLUSION-PAT). Extras are matched first so that a
meta-constructor in the conclusion, e.g. (@subst ?x ?t ?A), finds ?T
already bound -- no unification needed. Tries every axiom of that name."
  (destructuring-bind (axiom-name . extra-args) (k-line-by line)
    (labels ((try-entries (entries)
               (and entries
                    (or (try-axiom-entry (car entries) axiom-name extra-args line open-hyps ledger)
                        (try-entries (cdr entries))))))
      (try-entries (entries-of-kind 'axiom ledger)))))

(defun try-axiom-entry (entry axiom-name extra-args line open-hyps ledger)
  "T iff axiom ENTRY justifies LINE (see CHECK-K-AXIOM-LINE)."
  (destructuring-bind (name conditions form) (entry-payload entry)
    (and (eq name axiom-name)
         (destructuring-bind (extra-pats concl-pat) form
           (and (= (length extra-pats) (length extra-args))
                (let ((b1 (match-templates-seq extra-pats extra-args
                                               (seed-fresh nil extra-args (k-line-formula line)))))
                  (and (not (match-fail-p b1))
                       (let ((b2 (match-template concl-pat (k-line-formula line) b1)))
                         (and (not (match-fail-p b2))
                              (nth-value 1 (check-conditions conditions b2 ledger nil open-hyps)))))))))))

(defun proof-hypotheses (raw-proof)
  (mapcar #'k-line-formula
          (remove-if-not (lambda (l) (eq (k-line-role l) :hyp))
                          (mapcar #'raw->k-line raw-proof))))

(defun proof-conclusion (raw-proof)
  (k-line-formula (raw->k-line (car (last raw-proof)))))

;;; --- Optional logging -----------------------------------------------
;;;
;;; A LOG-CONFIG only gates printing; it never affects a verdict.
;;;   ERRORS       -- print each rejected line (number, role, cited name).
;;;   APPLICATIONS -- print each accepted line likewise, giving a trace.
;;; Both default to NIL (silent).

(defstruct (log-config (:constructor make-log-config (&key errors applications)))
  (errors nil) (applications nil))

(defun silent-log ()
  "The default LOG-CONFIG: neither flag set, nothing printed."
  (make-log-config))

(defun log-line-result (log line ok)
  "Print LINE's outcome OK if LOG's matching flag is set. LOG may be NIL."
  (when (and log (or (and ok (log-config-applications log))
                      (and (not ok) (log-config-errors log))))
    (format t "~&[~:[REJECT~;accept~]] line ~S (~S~@[ ~S~]).~%"
            ok (k-line-numbering line) (k-line-role line)
            (and (consp (k-line-by line)) (car (k-line-by line))))))

(defun log-admission-result (log name ok)
  "As LOG-LINE-RESULT, for the overall outcome of admitting entry NAME."
  (when (and log (or (and ok (log-config-applications log))
                      (and (not ok) (log-config-errors log))))
    (format t "~&[~:[REJECT~;accept~]] admission of ~S.~%" ok name)))

(defun check-k-proof (raw-proof ledger &optional (log (silent-log)))
  "Check RAW-PROOF, as written, against LEDGER; see %CHECK-K-PROOF. The
proof is first put in kernel form (NAMED->DB-PROOF), so bound variables
are compared up to renaming. A line holding a raw (:BV n) is rejected
(CONTAINS-RAW-INDEX-P)."
  (let ((raw-line (find-if #'contains-raw-index-p raw-proof)))
    (if raw-line
        (values nil (and (consp raw-line) (car raw-line)))
        (%check-k-proof (named->db-proof raw-proof ledger) ledger log))))

(defun %check-k-proof (raw-proof ledger &optional (log (silent-log)))
  "Check kernel-form RAW-PROOF against LEDGER, which the caller must already restrict
to entries earlier than the one being admitted (e.g. ENTRIES-UPTO).
Returns T, or (VALUES NIL n) where n is the first rejected line's number.
Gamma (the open hypotheses) starts empty and grows with each :HYP line;
a recursive check of a cited entry's proof starts its own empty Gamma.
LOG is passed into those recursive checks, so a trace shows the full
expansion."
  (labels ((walk (lines proven open-hyps)
             (if (null lines)
                 t
                 (let* ((line (raw->k-line (car lines)))
                        (ok
                          (case (k-line-role line)
                            ;; A hypothesis must be a wff, so garbage
                            ;; cannot be assumed.
                            (:hyp (%judgement? 'wff? (k-line-formula line) ledger))
                            (:axiom (check-k-axiom-line line ledger open-hyps))
                            (:ir (check-k-ir-line line proven ledger open-hyps))
                            ;; :TH, :TH-DED (and any other role): a derived
                            ;; citation, always fully re-verified.
                            (t (check-k-derived-line line proven ledger log)))))
                   (log-line-result log line ok)
                   (if ok
                       (walk (cdr lines)
                             (cons (cons (k-line-numbering line) (k-line-formula line)) proven)
                             (if (eq (k-line-role line) :hyp)
                                 (cons (k-line-formula line) open-hyps)
                                 open-hyps))
                       (values nil (k-line-numbering line)))))))
    (walk raw-proof nil nil)))

(defun match-schema-hyps-against-cited (pats nums proven-alist ledger binds)
  "MATCH-SCHEMA-ATOMS each premise pattern in PATS against the formula
proven at the same-position line number in NUMS, threading BINDS.
+FAIL+ on a mismatch, a missing line, or a length difference."
  (cond
    ((match-fail-p binds) +fail+)
    ((and (null pats) (null nums)) binds)
    ((or (null pats) (null nums)) +fail+)
    (t (let ((actual (find-proven (car nums) proven-alist)))
         (if (null actual)
             +fail+
             (match-schema-hyps-against-cited (cdr pats) (cdr nums) proven-alist ledger
                                               (match-schema-atoms (car pats) actual ledger binds)))))))

;;; --- Optional memoization of the recursive re-verification step --------
;;;
;;; Re-verifying a cited entry E instantiated with bindings B checks a
;;; proof determined by (E . B) against ENTRIES-UPTO(ENTRY-K E). The
;;; ledger is append-only, so E never changes and the entries before it
;;; are a fixed prefix: the verdict depends on (E . B) alone and can be
;;; cached without changing what is accepted. Without the cache, nested
;;; citations re-verify the same instances over and over, which can blow
;;; up exponentially. Off by default.

;;; The verdict also depends on vocabulary admitted AFTER E: ENTRIES-UPTO
;;; leaves the vocabulary kinds unbounded, so whether a cited instance is
;;; a wff can depend on a symbol declared later. Two ledgers can share E
;;; and differ only there (one declares kk a variable, another an atomic
;;; wff), so the key also holds LATEST-VOCABULARY-ENTRY: an entry is made
;;; by appending to one particular ledger, so that entry object fixes
;;; every entry before it, and none of the vocabulary kinds has a later one.

(defvar *derived-verify-cache* nil
  "NIL (no memoization, the default) or an EQUAL hash table mapping
(ENTRY LATEST-VOCABULARY-ENTRY . BINDS) to its CHECK-K-PROOF verdict.
The one piece of mutable global state in the system; it can only change
how fast a verdict is reached, never the verdict.")

(defun latest-vocabulary-entry (ledger)
  "The most recently admitted entry of a VOCABULARY-KIND-P kind in
LEDGER, ignoring its BOUND as ENTRIES-OF-KIND does for those kinds."
  (let ((best nil))
    (dolist (pair (ledger-by-kind ledger) best)
      (when (vocabulary-kind-p (car pair))
        (let ((node (cdr pair)))
          (loop while (and node (treap-node-right node))
                do (setf node (treap-node-right node)))
          (when (and node (or (null best) (> (entry-k (treap-node-value node)) (entry-k best))))
            (setf best (treap-node-value node))))))))

(defun verify-derived-instantiation (e binds instantiated ledger log)
  "Check INSTANTIATED (E's stored proof under BINDS) against the entries
before E, memoized when *DERIVED-VERIFY-CACHE* is set."
  (if *derived-verify-cache*
      (let ((key (list* e (latest-vocabulary-entry ledger) binds)))
        (multiple-value-bind (cached found) (gethash key *derived-verify-cache*)
          (if found
              cached
              (setf (gethash key *derived-verify-cache*)
                    (%check-k-proof instantiated (entries-upto (entry-k e) ledger) log)))))
      (%check-k-proof instantiated (entries-upto (entry-k e) ledger) log)))

(defun enable-derived-entry-memoization ()
  "Turn memoization on, with an empty cache."
  (setf *derived-verify-cache* (make-hash-table :test #'equal)))

(defun disable-derived-entry-memoization ()
  "Turn memoization off: always re-verify."
  (setf *derived-verify-cache* nil))

(defun reset-derived-entry-memoization ()
  "Empty the cache if memoization is on; otherwise do nothing."
  (when *derived-verify-cache*
    (setf *derived-verify-cache* (make-hash-table :test #'equal))))

;;; --- Instantiating a cited entry --------------------------------------
;;;
;;; Citing derived entry E at LINE:
;;;   1. RENAME      apply the citation's :INST variable renaming to E's
;;;                  stored proof (bound occurrences included).
;;;   2. MATCH       find schema bindings by matching E's hypotheses against
;;;                  the cited formulas and its conclusion against LINE,
;;;                  seeded with :INST's explicit bindings.
;;;   3. INSTANTIATE apply them to every formula and rule argument of the
;;;                  stored proof (not to line numbers).
;;;   4. COMPARE     instantiated hypotheses EQUAL the cited formulas and
;;;                  instantiated conclusion EQUAL LINE's formula.
;;;   5. RE-VERIFY   CHECK-K-PROOF the instantiated proof against the
;;;                  entries before E.
;;; Soundness rests on steps 4-5 only: LINE is then the conclusion of a
;;; checked proof from exactly the cited formulas. Steps 1-3 merely propose
;;; that proof; a bug there can reject a good citation, never accept a bad
;;; one.
;;;
;;; :INST syntax, e.g. (th-foo 3 4 :inst ((A (.eq v0 v1))
;;;                                       (P (v2) (.in v2 v1))
;;;                                       (v0 v7))):
;;;   (A formula)          atomic-wff symbol A := formula
;;;   (P (x1..xn) body)    predicate schema P := lambda; distinct variables,
;;;                        n = P's arity
;;;   (v0 t)               rename variable v0 to term t everywhere; if v0 is
;;;                        ever bound or generalized, t must be a variable
;;; Needed when matching cannot find a binding (a schema applied to
;;; non-variables, a symbol absent from the matched formulas) and for
;;; renaming, which matching never does.

(defun split-citation-inst (cited)
  "Split a citation's argument list into (VALUES LINE-REFS INST-LIST OK).
OK is NIL when :INST is present but not followed by exactly one list."
  (let ((pos (position :inst cited)))
    (if (null pos)
        (values cited nil t)
        (let ((tail (nthcdr (1+ pos) cited)))
          (values (subseq cited 0 pos) (car tail)
                  (and (= (length tail) 1) (listp (car tail))))))))

(defun parse-citation-inst (inst ledger)
  "Turn an :INST list into (VALUES RENAMING SCHEMA-BINDS OK): RENAMING an
alist variable -> term, SCHEMA-BINDS an alist in MATCH-SCHEMA-ATOMS'
format. OK is NIL if any item is malformed."
  (let ((renaming nil) (binds nil))
    (dolist (item inst (values (nreverse renaming) (nreverse binds) t))
      (unless (and (consp item) (symbolp (car item)) (listp (cdr item)))
        (return (values nil nil nil)))
      (let ((sym (car item)))
        (cond
          ((atomic-wff-symbol-p sym ledger)
           (unless (= (length item) 2) (return (values nil nil nil)))
           (push (cons sym (second item)) binds))
          ((variable-p sym ledger)
           (unless (= (length item) 2)
             (return (values nil nil nil)))
           (push (cons sym (second item)) renaming))
          ((predicate-schema-arity sym ledger)
           (unless (and (= (length item) 3) (listp (second item))
                        (= (length (second item)) (predicate-schema-arity sym ledger))
                        (distinct-variables-p (second item) ledger))
             (return (values nil nil nil)))
           (push (cons sym (list :lambda (second item) (third item))) binds))
          (t (return (values nil nil nil))))))))

(defun instantiate-raw-proof (raw-proof binds)
  "Apply BINDS to every formula and BY argument of RAW-PROOF, leaving rule
names and references to RAW-PROOF's own line numbers alone (steps 1, 3).
In a citation's :INST list, each item's head -- (A formula), (P (x) body),
(v term) -- names a symbol of the CITED entry, not of this proof, so only
the rest of the item is instantiated: re-instantiating the head would
re-target the citation (P := lambda (x). P x, with P bound outside, would
read as an application of P)."
  (let ((numbers (mapcar #'first raw-proof)))
    (flet ((inst-args (args)
             (let ((after-inst nil))
               (mapcar (lambda (arg)
                         (prog1
                             (cond
                               ((member arg numbers :test #'equal) arg)
                               ((eq arg :inst) arg)
                               ;; The list right after :INST: keep each head.
                               ((and after-inst (listp arg))
                                (mapcar (lambda (item)
                                          (if (consp item)
                                              (cons (car item) (instantiate-schema-atoms (cdr item) binds))
                                              item))
                                        arg))
                               (t (instantiate-schema-atoms arg binds)))
                           (setf after-inst (eq arg :inst))))
                       args))))
      (mapcar (lambda (raw)
                (destructuring-bind (num formula role by) raw
                  (list num
                        (instantiate-schema-atoms formula binds)
                        role
                        (if (consp by)
                            (cons (car by) (inst-args (cdr by)))
                            by))))
              raw-proof))))

(defun cited-formulas (nums proven-alist)
  "The formulas proven at line numbers NUMS, or :MISSING if one is absent."
  (let ((fs (mapcar (lambda (n) (find-proven n proven-alist)) nums)))
    (if (some #'null fs) :missing fs)))

;;; Steps 1 and 3 work on names, so before them the cited proof's own
;;; internal variables -- those absent from its hypotheses and conclusion,
;;; such as an eigenvariable it generalizes -- are renamed apart from every
;;; variable the citation brings in (its :INST renaming and the matched
;;; bindings): instantiating P := lambda (x). (.in x v3) into a proof that
;;; generalizes its own v3 would otherwise capture. A renaming of the
;;; cited proof is also handed down to the citations inside it, as :INST
;;; items, since matching never renames a variable. Both only propose: an
;;; unlucky choice can reject a good citation, never accept a bad one
;;; (step 5 still re-checks the result).

(defvar *internal-variables-cache* (make-hash-table :test #'eq)
  "Entry -> the variables of its stored proof absent from its statement.")

(defun tree-variables (x ledger)
  "The variables (VARIABLE-P) occurring as symbols anywhere in X."
  (let ((acc nil))
    (labels ((walk (y)
               (cond ((consp y) (walk (car y)) (walk (cdr y)))
                     ((and y (symbolp y) (not (keywordp y)) (variable-p y ledger))
                      (pushnew y acc :test #'eq)))))
      (walk x))
    acc))

(defun entry-internal-variables (e stored-proof ledger)
  (multiple-value-bind (vars found) (gethash e *internal-variables-cache*)
    (if found
        vars
        (setf (gethash e *internal-variables-cache*)
              (set-difference (tree-variables stored-proof ledger)
                              (tree-variables (cons (proof-conclusion stored-proof)
                                                    (proof-hypotheses stored-proof))
                                              ledger)
                              :test #'eq)))))

(defun propagate-renaming (proof renaming)
  "PROOF with, in each derived citation, an :INST item (v t) for every
(v . t) of RENAMING whose v the citation's :INST does not already name."
  (mapcar (lambda (line)
            (destructuring-bind (num formula role by) line
              (if (and (member role '(:th :th-ded)) (consp by))
                  (multiple-value-bind (cited inst ok) (split-citation-inst (cdr by))
                    (let ((new (loop for (v . term) in renaming
                                     unless (and ok (assoc v inst :test #'eq))
                                       collect (list v term))))
                      (if (and ok new)
                          (list num formula role
                                (append (list (car by)) cited (list :inst (append inst new))))
                          line)))
                  line)))
          proof))

(defun prepare-cited-proof (e stored-proof renaming binds ledger)
  "E's STORED-PROOF ready for step 3: internal variables renamed apart
from RENAMING and BINDS, then RENAMING applied (see above)."
  (let* ((internal (entry-internal-variables e stored-proof ledger))
         (clash (and internal
                     (intersection internal (tree-variables (list renaming binds) ledger) :test #'eq)))
         (proof stored-proof))
    (when clash
      (let* ((n (next-fresh-index stored-proof renaming binds))
             (apart (loop for v in clash for i from n collect (cons v (fresh-var i)))))
        (setf proof (propagate-renaming (instantiate-raw-proof proof apart) apart))))
    (if renaming
        (propagate-renaming (instantiate-raw-proof proof renaming) renaming)
        proof)))

(defun try-derived-entry (e cited line proven-alist ledger &optional (log (silent-log)) (inst nil))
  "T iff TH entry E, cited from lines CITED with :INST list INST, justifies
LINE (steps 1-5 above). LEDGER is used exactly as received: it may be a
restricted view, and widening it would let a proof reach later entries."
  (destructuring-bind (name stored) (entry-payload e)
    (declare (ignore name))
    (multiple-value-bind (renaming seed ok) (parse-citation-inst inst ledger)
      ;; The gates store kernel form, converted once against the ledger
      ;; the entry was admitted to. It is NOT converted again here: a
      ;; binder over a symbol that was not a variable then, but is in the
      ;; citing ledger, would change meaning.
      (let* ((stored-proof stored)
             (raw-proof (if renaming (instantiate-raw-proof stored-proof renaming) stored-proof))
             (schema-hyps (proof-hypotheses raw-proof))
             (schema-concl (proof-conclusion raw-proof))
             (actual-hyps (cited-formulas cited proven-alist)))
        (and ok
             (listp actual-hyps)
             (= (length schema-hyps) (length actual-hyps))
             (let ((b1 (match-schema-hyps-against-cited
                        schema-hyps cited proven-alist ledger
                        (seed-fresh seed raw-proof actual-hyps (k-line-formula line)))))
               (and (not (match-fail-p b1))
                    (let ((b2 (match-schema-atoms schema-concl (k-line-formula line) ledger b1)))
                      (and (not (match-fail-p b2))
                           (let ((instantiated (instantiate-raw-proof
                                                (prepare-cited-proof e stored-proof renaming b2 ledger)
                                                b2)))
                             (and (equal (proof-hypotheses instantiated) actual-hyps)
                                  (equal (proof-conclusion instantiated) (k-line-formula line))
                                  ;; Second value: the checked instance, for the
                                  ;; deduction meta-theorem (meta-theorem.lisp).
                                  (values (verify-derived-instantiation e (cons renaming b2) instantiated
                                                                        ledger log)
                                          instantiated))))))))))))

(defun try-deduction-entry (e cited line proven-alist ledger &optional (log (silent-log)) (inst nil))
  "As TRY-DERIVED-ENTRY, for a TH-DED entry E with payload (NAME H PROOF)
admitted by CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT, whose conclusion is
H -> PHI, written as the system's :DISCHARGE declaration says
(meta-theorem.lisp); a system without one cannot cite it. Only H is discharged: PROOF's other hypotheses (Gamma) remain
premises that must be cited, since the Deduction Theorem gives
Gamma |- H -> PHI, not |- H -> PHI. (Dropping Gamma would turn
A, (.to A B) |- B into the non-tautology (.to (.to A B) B).)"
  (destructuring-bind (name stored-hyp-0 stored-proof-0) (entry-payload e)
    (declare (ignore name))
    (multiple-value-bind (renaming seed ok) (parse-citation-inst inst ledger)
      ;; Kernel form as stored, not re-converted (see TRY-DERIVED-ENTRY).
      (let* ((stored-hyp stored-hyp-0)
             (stored-proof stored-proof-0)
             (hyp-formula (if renaming (instantiate-schema-atoms stored-hyp renaming) stored-hyp))
             (raw-proof (if renaming (instantiate-raw-proof stored-proof renaming) stored-proof))
             (gamma (remove hyp-formula (proof-hypotheses raw-proof) :test #'equal))
             (actual-hyps (cited-formulas cited proven-alist)))
        (and ok
             (listp actual-hyps)
             (= (length gamma) (length actual-hyps))
             (let ((b1 (match-schema-hyps-against-cited
                        gamma cited proven-alist ledger
                        (seed-fresh seed hyp-formula raw-proof actual-hyps (k-line-formula line)))))
               (and (not (match-fail-p b1))
                    (let* ((schema-concl (discharge-formula hyp-formula (proof-conclusion raw-proof) ledger))
                           (b2 (if schema-concl
                                   (match-schema-atoms schema-concl (k-line-formula line) ledger b1)
                                   +fail+)))
                      (and (not (match-fail-p b2))
                           (let ((instantiated (instantiate-raw-proof
                                                (prepare-cited-proof e stored-proof renaming b2 ledger)
                                                b2))
                                 (inst-hyp (instantiate-schema-atoms hyp-formula b2)))
                             (and (member inst-hyp (proof-hypotheses instantiated) :test #'equal)
                                  (equal (mapcar (lambda (g) (instantiate-schema-atoms g b2)) gamma)
                                         actual-hyps)
                                  (equal (discharge-formula inst-hyp (proof-conclusion instantiated) ledger)
                                         (k-line-formula line))
                                  ;; Second value: the checked instance, for the
                                  ;; deduction meta-theorem (meta-theorem.lisp).
                                  (values (verify-derived-instantiation e (cons renaming b2) instantiated
                                                                        ledger log)
                                          instantiated
                                          inst-hyp))))))))))))

(defun check-k-derived-line (line proven-alist ledger &optional (log (silent-log)))
  "Check a derived citation: BY = (name cited-line... [:inst binds]).
Tries every TH/TH-DED entry of that name, since a hand-built ledger may
hold duplicates despite CHECK-AND-EXTEND's name check. Candidates come
from the BY-DERIVED-NAME index (O(log n), honoring LEDGER's BOUND)
instead of a scan of the whole ledger."
  (destructuring-bind (rule-name . args) (k-line-by line)
    (multiple-value-bind (cited inst ok) (split-citation-inst args)
      (and ok
           (let ((candidates (treap-values-below (alist-get (ledger-by-derived-name ledger) rule-name)
                                                  (ledger-bound ledger))))
             (nth-value 0 (derived-citation-instance candidates cited line proven-alist
                                                     ledger log inst)))))))

(defun derived-citation-instance (candidates cited line proven-alist ledger log inst)
  "The first of CANDIDATES (TH / TH-DED entries) that justifies LINE, as
(VALUES T INSTANTIATED-PROOF ENTRY HYP), HYP being a TH-DED's discharged
hypothesis as instantiated, or NIL."
  (dolist (e candidates nil)
    (multiple-value-bind (ok instantiated inst-hyp)
        (if (eq (entry-kind e) 'th-ded)
            (try-deduction-entry e cited line proven-alist ledger log inst)
            (try-derived-entry e cited line proven-alist ledger log inst))
      (when ok (return (values t instantiated e inst-hyp))))))

(defun derived-line-instance (line proven-alist ledger)
  "For a derived citation LINE already accepted by CHECK-K-PROOF:
(VALUES INSTANTIATED-PROOF ENTRY CITED-LINE-NUMBERS HYP), the checked
instance of the cited entry that justifies it (HYP: a TH-DED's discharged
hypothesis, instantiated)."
  (destructuring-bind (rule-name . args) (k-line-by line)
    (multiple-value-bind (cited inst ok) (split-citation-inst args)
      (when ok
        (multiple-value-bind (found instantiated e inst-hyp)
            (derived-citation-instance
             (treap-values-below (alist-get (ledger-by-derived-name ledger) rule-name)
                                 (ledger-bound ledger))
             cited line proven-alist ledger (silent-log) inst)
          (and found (values instantiated e cited inst-hyp)))))))

(defun derived-rule-name-taken-p (name ledger)
  "T iff NAME already labels a TH or TH-DED entry. Both kinds are cited
by bare name, so a reused name would make citations ambiguous and let a
new entry shadow an old one. O(log n) via the BY-DERIVED-NAME index."
  (not (null (treap-values-below (alist-get (ledger-by-derived-name ledger) name) (ledger-bound ledger)))))

(defun check-and-extend (ledger kind name raw-proof &optional (log (silent-log)))
  "Check RAW-PROOF against LEDGER and return a new ledger with TH entry
NAME appended, payload (NAME RAW-PROOF); its conclusion is the last line.
Signals an error if KIND is not TH (other kinds need other payload
shapes), NAME is taken, or the proof is rejected. LOG traces the check
and the overall verdict."
  (unless (eq kind 'th)
    (error "CHECK-AND-EXTEND: KIND must be TH, got ~S." kind))
  (admit-theorem ledger name raw-proof log nil))

(defun admit-theorem (ledger name raw-proof log origin-tail)
  "CHECK-AND-EXTEND's work. ORIGIN-TAIL is appended to the entry's
ORIGIN (:DERIVED RAW-PROOF . ORIGIN-TAIL); (:BY-DESCRIPTION) marks a
theorem generated by DEFINE-FUNCTION-BY-DESCRIPTION, which is saved as
that command rather than on its own."
  (when (derived-rule-name-taken-p name ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND: the name ~S is already used by an existing ~
            TH/TH-DED entry -- refused to avoid an ambiguous or ~
            shadowing citation." name))
  (when (contains-raw-index-p raw-proof)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND: proof of ~S contains a raw (:bv n); write ~
            bound variables by name." name))
  ;; LEDGER does not yet contain the new entry, so it is already the
  ;; "entries strictly before" view. The payload, which citations read,
  ;; is the kernel form; the ORIGIN keeps the proof as written, for
  ;; display and saving (ENTRY-SOURCE-PAYLOAD).
  (let ((db-proof (named->db-proof raw-proof ledger)))
    (unless (%check-k-proof db-proof ledger log)
      (log-admission-result log name nil)
      (error "CHECK-AND-EXTEND: proof of ~S rejected." name))
    (log-admission-result log name t)
    (ledger-append ledger 'th (list name db-proof) (list* :derived raw-proof origin-tail))))
