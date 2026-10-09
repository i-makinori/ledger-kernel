;;;; ledger.lisp -- the ledger: entries, indexes, Sigma, growth paths

(in-package :ledger-kernel)

;;; ENTRY-K       -- 1-based position in the ledger (Goedel's y).
;;; ENTRY-KIND    -- an open set of tags: WFF?, VAR?, IRULE, AXIOM, TH,
;;;                  TH-DED, VARIABLE-SYMBOL, ...
;;; ENTRY-PAYLOAD -- for rule-like kinds, (NAME SIDE-CONDITIONS FORM); for
;;;                  symbol kinds, the symbol (or (NAME ARITY)).
;;; ENTRY-ORIGIN  -- (:PRIMITIVE . note), (:DERIVED <k-proof>) or
;;;                  (:DECLARED). A :DERIVED entry keeps its proof so it
;;;                  can always be re-checked. :DECLARED is for a fresh
;;;                  vocabulary symbol: there is nothing to prove, and its
;;;                  admission criterion is freshness (see
;;;                  FRESH-SYMBOL-NAME-P).

(defstruct (entry (:constructor %make-entry (k kind payload origin)))
  (k 0 :type integer)
  kind
  payload
  origin)

;;; Print only a summary; the default printer would dump whole proofs.
(defmethod print-object ((e entry) stream)
  (print-unreadable-object (e stream :type t)
    (format stream "K=~D KIND=~S ORIGIN=~S" (entry-k e) (entry-kind e) (car (entry-origin e)))))

;;; A ledger is an immutable value: LEDGER-APPEND returns a new ledger and
;;; every function takes the ledger as an argument, so old ledgers stay
;;; valid and nothing is hidden in global state. It is indexed by treaps
;;; so that append, "entries of kind K" and "theorems named N" are
;;; O(log n) rather than full scans:
;;;   COUNT           -- entries ever appended (ignoring BOUND); the K of
;;;                      the last one.
;;;   ALL             -- treap k -> entry.
;;;   BY-KIND         -- alist kind -> treap (k -> entry), so
;;;                      ENTRIES-OF-KIND comes out in admission order.
;;;   BY-DERIVED-NAME -- alist name -> treap (k -> entry) over TH and TH-DED
;;;                      entries, which share one citation namespace.
;;;   BOUND           -- NIL, or B meaning only entries with K < B are
;;;                      visible (see ENTRIES-UPTO). Readers prune by it
;;;                      while walking, so setting it rebuilds nothing.

(defstruct (ledger (:constructor %make-ledger (count all by-kind by-derived-name bound)))
  (count 0 :type integer)
  all
  by-kind
  by-derived-name
  bound)

;;; Print only the size and bound; the default printer would dump every
;;; index. Use LEDGER-COMMANDS to see a ledger's content.
(defmethod print-object ((l ledger) stream)
  (print-unreadable-object (l stream :type t)
    (format stream "~D ~:[entries~;entry~]~@[, bound<~D~]"
            (ledger-count l) (= (ledger-count l) 1) (ledger-bound l))))

(defun empty-ledger ()
  "The unique starting point of every ledger: no entries, no bound."
  (%make-ledger 0 nil nil nil nil))

(defun ledger-append (ledger kind payload origin)
  "The only way to add an entry: return a new ledger with entry K =
1 + (LEDGER-COUNT LEDGER) appended and every index updated in O(log n).
TH/TH-DED entries (payload CAR = citation name) also go into
BY-DERIVED-NAME. Signals an error on a bounded view."
  (when (ledger-bound ledger)
    (error "LEDGER-APPEND: cannot append to a bound (read-only, ~
            ENTRIES-UPTO-restricted) ledger view."))
  (let* ((k (1+ (ledger-count ledger)))
         (e (%make-entry k kind payload origin))
         (new-all (treap-insert (ledger-all ledger) k e))
         (new-by-kind (alist-put (ledger-by-kind ledger) kind
                                  (treap-insert (alist-get (ledger-by-kind ledger) kind) k e)))
         (derived-name (and (member kind '(th th-ded) :test #'eq) (car payload)))
         (new-by-derived-name
           (if derived-name
               (alist-put (ledger-by-derived-name ledger) derived-name
                          (treap-insert (alist-get (ledger-by-derived-name ledger) derived-name) k e))
               (ledger-by-derived-name ledger))))
    (%make-ledger k new-all new-by-kind new-by-derived-name nil)))

(defun vocabulary-kind-p (kind)
  "Kinds that only say what is well-formed (Sigma's symbols and the
TERM?/WFF?/VAR? formation rules), as opposed to kinds that justify proof
steps (AXIOM, IRULE, TH, ...)."
  (member kind '(atomic-wff-symbol variable-symbol predicate-schema-symbol wff? term? var?
                 abbreviation)
          :test #'eq))

(defun entries-of-kind (kind ledger)
  "Entries of KIND, in admission order. For a VOCABULARY-KIND-P kind the
ENTRIES-UPTO bound is ignored; see ENTRIES-UPTO for why."
  (treap-values-below (alist-get (ledger-by-kind ledger) kind)
                      (if (vocabulary-kind-p kind) nil (ledger-bound ledger))))

(defun entries-upto (k ledger)
  "O(1) read-only view of LEDGER in which only entries at positions below K
are visible to justifying kinds; used when re-checking a stored proof so it
cannot cite itself or anything later. Vocabulary kinds (VOCABULARY-KIND-P)
ignore the bound, so a theorem proved early can be re-checked at an
instance using later vocabulary. This is sound: well-formedness justifies
nothing by itself, and every proof step still comes from an entry before K."
  (let ((new-bound (if (ledger-bound ledger) (min k (ledger-bound ledger)) k)))
    (%make-ledger (ledger-count ledger) (ledger-all ledger) (ledger-by-kind ledger)
                  (ledger-by-derived-name ledger) new-bound)))

;;; --- Sigma (vocabulary) as projections of the ledger ------------------

(defun sigma-atomic-symbols (ledger)
  "Declared atomic-wff symbols."
  (mapcar #'entry-payload (entries-of-kind 'atomic-wff-symbol ledger)))

(defun sigma-variable-symbols (ledger)
  "Declared variable symbols."
  (mapcar #'entry-payload (entries-of-kind 'variable-symbol ledger)))

;;; Gamma (open hypotheses) is not stored here: it is the OPEN-HYPS
;;; argument threaded from CHECK-K-PROOF (one cons per :HYP line) down to
;;; the meta-predicates that read it. Every CHECK-K-PROOF call, including
;;; re-checking a cited entry's proof, starts with empty Gamma, so
;;; hypotheses never leak between proofs.

(defun atomic-wff-symbol-p (x ledger)
  "True iff X is a declared atomic-wff symbol."
  (member x (sigma-atomic-symbols ledger) :test #'eq))

;;; Predicate schema symbols P of arity N >= 1: (P t1 ... tN) is a wff.
;;; In a theorem they stand for any formula with N argument places, and
;;; citing it substitutes one (MATCH-SCHEMA-ATOMS). Unlike an atomic wff,
;;; x is free in (P x), so free-variable side conditions see it.

(defun sigma-predicate-schemas (ledger)
  "Declared predicate schema symbols, as a list of (NAME ARITY)."
  (mapcar #'entry-payload (entries-of-kind 'predicate-schema-symbol ledger)))

(defun predicate-schema-arity (x ledger)
  "ARITY if X is a declared predicate schema symbol, else NIL."
  (and (symbolp x)
       (second (assoc x (sigma-predicate-schemas ledger) :test #'eq))))

(defun variable-p (x ledger)
  "True iff X is a declared variable symbol, or one of the kernel's fresh
variables %0, %1, ... (debruijn.lisp), which are variables of every
ledger and can never be declared as anything else."
  (or (fresh-var-name-p x)
      (member x (sigma-variable-symbols ledger) :test #'eq)))

;;; --- Growth paths -------------------------------------------------------
;;;
;;; :PRIMITIVE entries are admitted only by BOOTSTRAP-KERNEL-FROM-SPEC(-FILE)
;;; while loading a .system file. After that the ledger grows only by
;;; checked theorems (CHECK-AND-EXTEND, CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT)
;;; and fresh declarations (DECLARE-*-SYMBOL).

;;; --- Growing Sigma --------------------------------------------------------
;;;
;;; Introducing an unused name proves nothing about existing vocabulary
;;; (conservative extension by a fresh constant), so the only admission
;;; criterion is freshness: not already declared, and not a symbol the
;;; matcher or rule syntax gives fixed meaning (?-pattern variables,
;;; @-meta-tags, reserved heads such as .TO/.EQ/:=> and binders).

(defun binder-heads ()
  "Heads that bind the variable in position 1 over the body in position 2:
(.forall x A) and the term (.iota x A),
\"the x such that A\". The binder machinery (FREE-VARS-WFF, SUBSTITUTE-WFF,
...) does not care whether the expression is a wff or a term. Adding a
binder requires editing this list. Binders such as .EXISTS and .EXISTS1
are abbreviations (abbreviation.lisp), expanded before the kernel sees
them."
  '(.forall .iota))

(defun at-symbol-p (sym)
  "True iff SYM is an @-prefixed meta-tag."
  (and (symbolp sym) (> (length (symbol-name sym)) 1)
       (char= (char (symbol-name sym) 0) #\@)))

(defun reserved-head-symbol-p (sym)
  "True iff SYM is a head with fixed meaning to the kernel, and so can
never be declared. (BINDER-HEADS) must be LIST*'s last argument."
  (member sym (list* :=> '.to '.eq '.neg (binder-heads)) :test #'eq))

(defun fresh-symbol-name-p (sym ledger)
  "T iff SYM may be declared: a non-NIL, non-keyword symbol that is not a pattern variable,
meta-tag or reserved head, and not already declared in any Sigma
namespace (atomic wffs, variables and predicate schemas share one pool),
nor a fresh variable %n."
  (and (symbolp sym)
       ;; NIL ends every list and keywords (:BV, :INST, :LAMBDA, :HYP,
       ;; ...) are the kernel's own markers; a declared NIL would make
       ;; the schema matcher treat the end of every list as an atom.
       sym
       (not (eq sym t))
       (not (eq sym +fail+))            ; the matcher's failure sentinel
       (not (keywordp sym))
       (not (pat-var-p sym))
       (not (at-symbol-p sym))
       (not (reserved-head-symbol-p sym))
       (not (fresh-var-name-p sym))
       (not (atomic-wff-symbol-p sym ledger))
       (not (variable-p sym ledger))
       (not (predicate-schema-arity sym ledger))
       (not (abbreviation-head-p sym ledger))))

(defun symbol-used-in-ledger-p (sym ledger)
  "T iff SYM occurs anywhere in the payload of an entry of LEDGER."
  (some (lambda (e) (occurs-symbol-p sym (entry-payload e)))
        (treap-values-below (ledger-all ledger) (ledger-bound ledger))))

(defun declare-atomic-wff-symbol (ledger sym)
  "Return LEDGER with fresh SYM declared as an atomic-wff symbol
(origin :DECLARED). Allowed at any time; signals an error if not fresh."
  (unless (fresh-symbol-name-p sym ledger)
    (error "DECLARE-ATOMIC-WFF-SYMBOL: ~S is not available for ~
            declaration (already declared, or reserved by the kernel ~
            itself)." sym))
  (ledger-append ledger 'atomic-wff-symbol sym (list :declared)))

(defun declare-predicate-schema-symbol (ledger sym arity)
  "As DECLARE-ATOMIC-WFF-SYMBOL, for a predicate schema of positive ARITY."
  (unless (fresh-symbol-name-p sym ledger)
    (error "DECLARE-PREDICATE-SCHEMA-SYMBOL: ~S is not available for ~
            declaration (already declared, or reserved by the kernel ~
            itself)." sym))
  (unless (and (integerp arity) (plusp arity))
    (error "DECLARE-PREDICATE-SCHEMA-SYMBOL: arity ~S is not a positive integer." arity))
  (ledger-append ledger 'predicate-schema-symbol (list sym arity) (list :declared)))

(defun declare-variable-symbol (ledger sym)
  "As DECLARE-ATOMIC-WFF-SYMBOL, for a variable symbol."
  (unless (fresh-symbol-name-p sym ledger)
    (error "DECLARE-VARIABLE-SYMBOL: ~S is not available for ~
            declaration (already declared, or reserved by the kernel ~
            itself)." sym))
  (ledger-append ledger 'variable-symbol sym (list :declared)))
