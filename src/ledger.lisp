;;;; ledger.lisp -- Section 2: the ledger itself
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 2. The ledger itself
;;; ---------------------------------------------------------------------
;;;
;;; ENTRY-K       -- position in the ledger (Goedel's y). 1-indexed.
;;; ENTRY-KIND    -- a tag: e.g. WFF?, VAR?, IRULE, AXIOM, ITH, TH,
;;;                  DEF-ABBREV, HYP. The vocabulary of kinds is open;
;;;                  new kinds can be introduced by future primitives.
;;; ENTRY-PAYLOAD -- kind-specific data. For rule-like kinds this is a
;;;                  (NAME SIDE-CONDITIONS FORM) triple. For HYP entries
;;;                  it is the hypothesis WFF itself.
;;; ENTRY-ORIGIN  -- (:PRIMITIVE), (:DERIVED <k-proof>), or (:DECLARED).
;;;                  A proof is a list of raw k-lines, kept so that any
;;;                  :DERIVED entry is, in principle, fully
;;;                  auditable/re-checkable from first primitives.
;;;                  :DECLARED covers growing SIGMA itself (a fresh
;;;                  atomic-wff symbol or variable) after bootstrap.
;;;                  Declaring a brand-new, previously-unused name has no
;;;                  proposition to prove, so it would be dishonest to tag
;;;                  it :DERIVED; it is also not :PRIMITIVE, which is
;;;                  reserved for the bootstrap-time trusted base and
;;;                  refused afterward on purpose. :DECLARED entries carry
;;;                  their own admission criterion, FRESHNESS (the name
;;;                  must not already be in Sigma or collide with a symbol
;;;                  the kernel's matcher/binder machinery gives fixed
;;;                  meaning to) -- the classical conservative-extension-
;;;                  by-a-fresh-constant move. See DECLARE-ATOMIC-WFF-SYMBOL
;;;                  / DECLARE-VARIABLE-SYMBOL.

(defstruct (entry (:constructor %make-entry (k kind payload origin)))
  (k 0 :type integer)
  kind
  payload
  origin)

;;; ENTRY's default structure-printer would print PAYLOAD/ORIGIN in full,
;;; which for a :DERIVED entry means its whole (possibly large,
;;; especially if built by @DEDUCTION -- see section 11) raw K-proof. A
;;; concise summary is all a REPL echo or debugging PRINT ever actually
;;; wants; ENTRY-PAYLOAD/ENTRY-K/etc. remain the real, full-fidelity
;;; accessors for any code that needs the data itself -- this only
;;; changes how an ENTRY is *displayed*, never what it *is*.
(defmethod print-object ((e entry) stream)
  (print-unreadable-object (e stream :type t)
    (format stream "K=~D KIND=~S ORIGIN=~S" (entry-k e) (entry-kind e) (car (entry-origin e)))))

;;; The ledger is an ordinary immutable value: LEDGER-APPEND takes the
;;; current ledger and returns a NEW one with the entry appended, and
;;; every function that reads or grows the ledger takes it as an explicit
;;; argument and, where it grows the ledger, returns the new one as its
;;; result. Sigma/Gamma are still computed from it on demand rather than
;;; stored separately.
;;;
;;; Internally, a ledger is not a plain list: it is indexed three ways
;;; (via the TREAP of section 1.5) so that the operations this file
;;; actually performs -- append one entry, list every entry of a given
;;; KIND, find every ITH/TH/DEF-ABBREV entry sharing a citation NAME --
;;; are all O(log n) in the ledger's total size, instead of the O(n) full
;;; scan a plain list would force on every single one of them:
;;;   COUNT           -- how many entries have ever been appended
;;;                      (ignoring BOUND); ENTRY-K of the next one.
;;;   ALL             -- a treap, k -> entry, every entry keyed by
;;;                      position.
;;;   BY-KIND         -- an alist, kind -> treap (k -> entry): the
;;;                      entries of that one kind, still keyed by
;;;                      position, so ENTRIES-OF-KIND returns them in
;;;                      original insertion order.
;;;   BY-DERIVED-NAME -- an alist, name -> treap (k -> entry), spanning
;;;                      ITH/TH/DEF-ABBREV entries together, since those
;;;                      three kinds share one citation namespace (see
;;;                      DERIVED-RULE-NAME-TAKEN-P).
;;;   BOUND           -- NIL for an ordinary, unrestricted ledger, or an
;;;                      integer B meaning "only entries with K < B are
;;;                      visible": the read-only view ENTRIES-UPTO
;;;                      returns. Setting BOUND is O(1) -- none of
;;;                      ALL/BY-KIND/BY-DERIVED-NAME is rebuilt; every
;;;                      read consults BOUND and prunes while it walks
;;;                      its own treap (TREAP-VALUES-BELOW), so the
;;;                      restriction costs nothing until something is
;;;                      actually read out of it, and even then only in
;;;                      proportion to what is read.

(defstruct (ledger (:constructor %make-ledger (count all by-kind by-derived-name bound)))
  (count 0 :type integer)
  all
  by-kind
  by-derived-name
  bound)

;;; As with ENTRY above: LEDGER's default structure-printer would walk
;;; and print all three treap indices in full -- the SAME entries,
;;; reachable three separate ways (ALL / BY-KIND / BY-DERIVED-NAME),
;;; printed without structure-sharing by default, easily tens of
;;; thousands of lines for a ledger of any real size. A REPL echo of a
;;; returned LEDGER value should say what it minimally needs to: how many
;;; entries, and whether it is a bounded (ENTRIES-UPTO-restricted) view.
;;; LEDGER-COMMANDS remains the way to see (or persist) a ledger's actual
;;; logical content.
(defmethod print-object ((l ledger) stream)
  (print-unreadable-object (l stream :type t)
    (format stream "~D ~:[entries~;entry~]~@[, bound<~D~]"
            (ledger-count l) (= (ledger-count l) 1) (ledger-bound l))))

(defun empty-ledger ()
  "The unique starting point of every ledger: no entries, no bound."
  (%make-ledger 0 nil nil nil nil))

(defun ledger-append (ledger kind payload origin)
  "The ONLY way an entry is added to the ledger. Returns a NEW ledger
(LEDGER with the fresh entry appended) rather than mutating anything.
Enforces K = 1 + (LEDGER-COUNT LEDGER), so K literally IS the ledger
position -- Goedel's y. Also extends the BY-KIND index, and (for an
ITH/TH/DEF-ABBREV/TH-DED entry, whose PAYLOAD's CAR is always its citation
name) the BY-DERIVED-NAME index, incrementally -- each an O(log n)
treap insert into one bucket, never a full rescan.

TH-DED (see Section 11.5, CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT) shares the
same by-name citation bucket as ITH/TH/DEF-ABBREV -- CHECK-K-DERIVED-LINE's
candidate lookup is already kind-agnostic (it just fetches the bucket for a
rule-name and tries each candidate), so a TH-DED entry is found the exact
same way; only the per-candidate TRY-*-ENTRY logic differs by kind."
  (when (ledger-bound ledger)
    (error "LEDGER-APPEND: cannot append to a bound (read-only, ~
            ENTRIES-UPTO-restricted) ledger view."))
  (let* ((k (1+ (ledger-count ledger)))
         (e (%make-entry k kind payload origin))
         (new-all (treap-insert (ledger-all ledger) k e))
         (new-by-kind (alist-put (ledger-by-kind ledger) kind
                                  (treap-insert (alist-get (ledger-by-kind ledger) kind) k e)))
         (derived-name (and (member kind '(ith th def-abbrev th-ded) :test #'eq) (car payload)))
         (new-by-derived-name
           (if derived-name
               (alist-put (ledger-by-derived-name ledger) derived-name
                          (treap-insert (alist-get (ledger-by-derived-name ledger) derived-name) k e))
               (ledger-by-derived-name ledger))))
    (%make-ledger k new-all new-by-kind new-by-derived-name nil)))

(defun vocabulary-kind-p (kind)
  "Entry kinds that only say what is well-formed -- Sigma's symbols and
the TERM?/WFF?/VAR? formation rules -- as opposed to kinds that justify
proof steps (AXIOM, IRULE, TH, ...)."
  (member kind '(atomic-wff-symbol variable-symbol predicate-schema-symbol wff? term? var?)
          :test #'eq))

(defun entries-of-kind (kind ledger)
  "Entries of KIND, in admission order. For a VOCABULARY-KIND-P kind the
ENTRIES-UPTO bound is ignored; see ENTRIES-UPTO for why."
  (treap-values-below (alist-get (ledger-by-kind ledger) kind)
                      (if (vocabulary-kind-p kind) nil (ledger-bound ledger))))

(defun entries-upto (k ledger)
  "A read-only VIEW of LEDGER showing only entries with position strictly
less than K -- used when re-verifying a proof, so nothing can (even
accidentally) depend on itself or on anything defined later. O(1): see
LEDGER's BOUND field, above.

The bound applies to every kind that can JUSTIFY a proof line (axioms,
inference rules, derived theorems, ...), not to vocabulary: symbols and
TERM?/WFF?/VAR? formation rules admitted later stay visible (see
VOCABULARY-KIND-P / ENTRIES-OF-KIND). That is what lets a theorem
proved early -- say A & B -> A -- be cited, and its stored proof be
re-verified, at an instance that mentions vocabulary introduced later,
such as (.in v0 (empty)). This is sound: a well-formedness judgement
never justifies anything by itself, every proof step of the re-verified
proof still has to come from an entry strictly before K, and all the
entries it can use exist in the full ledger too, so its conclusion is a
theorem of the full ledger. The bound on justifying entries is what
rules out circular citation, and it is unchanged."
  (let ((new-bound (if (ledger-bound ledger) (min k (ledger-bound ledger)) k)))
    (%make-ledger (ledger-count ledger) (ledger-all ledger) (ledger-by-kind ledger)
                  (ledger-by-derived-name ledger) new-bound)))

;;; --- Sigma and Gamma as projections -----------------------------------

(defun sigma-atomic-symbols (ledger)
  "Declared atomic-WFF symbols: the projection of all WFF?-kind entries
whose payload names a bare declared symbol."
  (mapcar #'entry-payload (entries-of-kind 'atomic-wff-symbol ledger)))

(defun sigma-variable-symbols (ledger)
  (mapcar #'entry-payload (entries-of-kind 'variable-symbol ledger)))

;;; Gamma (the open hypotheses of the proof currently being checked) is
;;; threaded explicitly: an ordinary OPEN-HYPS argument, passed down from
;;; CHECK-K-PROOF (where it is built up, one CONS per :HYP line) through
;;; CHECK-K-IR-LINE/CHECK-K-AXIOM-LINE/CHECK-CONDITIONS/CHECK-CONDITION/
;;; JUDGEMENT?/JUDGEMENT-BIND, down to whichever meta-predicate actually
;;; reads it (META-NOT-FREE-IN-DEPENDENCIES?, META-PROVEN?; see section
;;; 4). Unlike Sigma (genuinely global, since declaring a symbol is
;;; permanent), Gamma is local to one proof in progress: a hypothesis is
;;; only ever "open" for the duration of the derivation that assumed it.
;;; CHECK-K-PROOF starts every call, including a recursive
;;; re-verification of some cited :DERIVED entry's own stored proof, from
;;; a fresh empty OPEN-HYPS of its own, so an outer proof's hypotheses
;;; never leak into an inner one and vice versa.

(defun atomic-wff-symbol-p (x ledger)
  (member x (sigma-atomic-symbols ledger) :test #'eq))

;;; Predicate schema symbols: P, Q, ... of a fixed arity N >= 1, so that
;;; (P t1 ... tN) is a wff for any terms t1..tN. In a stored theorem they
;;; stand for an arbitrary formula with N argument places ("A(x)"), and
;;; citing the theorem substitutes a concrete formula for them (see
;;; MATCH-SCHEMA-ATOMS / INSTANTIATE-SCHEMA-ATOMS). Unlike an atomic-wff
;;; symbol, (P x) shows its dependence on x: x occurs free in (P x), so
;;; free-variable side conditions (Gen, EXISTS-ELIM, III.1, ...) see it.

(defun sigma-predicate-schemas (ledger)
  "Declared predicate schema symbols, as a list of (NAME ARITY)."
  (mapcar #'entry-payload (entries-of-kind 'predicate-schema-symbol ledger)))

(defun predicate-schema-arity (x ledger)
  "ARITY if X is a declared predicate schema symbol, else NIL."
  (and (symbolp x)
       (second (assoc x (sigma-predicate-schemas ledger) :test #'eq))))

(defun variable-p (x ledger)
  (member x (sigma-variable-symbols ledger) :test #'eq))

;;; --- Growth paths -------------------------------------------------------
;;;
;;; There are exactly two ways to grow the ledger:
;;;   ADMIT-PRIMITIVE  -- bootstrap only, no proof required.
;;;   CHECK-AND-EXTEND -- the general path; requires a K-proof that
;;;                       CHECK-K-PROOF re-verifies against entries
;;;                       strictly earlier than the new entry's own k.

;;; :PRIMITIVE-origin admission is private to BOOTSTRAP-KERNEL's own
;;; lexical scope: it binds its own private ADMIT function via LABELS,
;;; reachable by nothing outside its body. The publicly-exported
;;; ADMIT-PRIMITIVE below exists only so a caller who tries that name
;;; gets a clear, permanent refusal.

(defun admit-primitive (kind payload)
  "There is no 'still open' case: :PRIMITIVE-origin admission is private
to BOOTSTRAP-KERNEL's own lexical scope (see its LABELS-bound ADMIT),
which this public name never has access to. Signals an error
unconditionally."
  (declare (ignore kind payload))
  (error "ADMIT-PRIMITIVE cannot be called directly -- :PRIMITIVE-origin ~
          admission is private to BOOTSTRAP-KERNEL's own lexical scope, ~
          available only at kernel-authoring time. All growth must go ~
          through CHECK-AND-EXTEND, CHECK-AND-EXTEND-ABBREV, or (for ~
          Sigma itself) DECLARE-ATOMIC-WFF-SYMBOL / ~
          DECLARE-VARIABLE-SYMBOL."))

;;; --- Growing Sigma itself, after bootstrap -----------------------------
;;;
;;; BOOTSTRAP-KERNEL's :ATOMIC-SYMBOLS/:VARIABLES keyword arguments only
;;; supply the SEED vocabulary available at kernel-authoring time. Sigma
;;; also needs a growth path usable AFTER bootstrap, the same way
;;; CHECK-AND-EXTEND lets theorems grow and CHECK-AND-EXTEND-ABBREV lets
;;; definitions grow.
;;;
;;; Declaring a fresh symbol is unlike either of those: there is no
;;; proposition to prove about introducing a hitherto-unused name (the
;;; classical "conservative extension by a fresh constant" move), so the
;;; only real admission criterion is FRESHNESS -- the name must not
;;; collide with anything already in Sigma, nor with a symbol the
;;; kernel's own pattern matcher, binder logic, or rule syntax already
;;; gives fixed structural meaning to (?-prefixed pattern variables,
;;; @-prefixed meta-tags, and reserved heads like .TO/.FORALL/.EQ/:=>).

(defun binder-heads ()
  "Which head symbols introduce a bound variable in position 1, body in
position 2: (.forall x A), (.exists x A), (.iota x A). The last of these
is a TERM, not a WFF -- (.iota x A) denotes \"the x such that A\" (see
Section 7's IOTA/III.3 commentary and Section 19) -- but it binds x in A
in exactly the same structural position, so the same convention (and the
same FREE-VARS-WFF/SUBSTITUTE-WFF/COUNT-BOUND-OCCURRENCES machinery)
covers it with no further change: those functions never actually care
whether the binder-headed expression they are walking sits in a WFF
position or a TERM position, only where ITS OWN bound variable and body
are. A fixed fact about the kernel's own syntax, never mutated at
runtime; adding a new binder always means adding to this list, whether
or not the new binder's own axioms/rules could otherwise be expressed as
pure data (see the .system file commentary, Section 18, and its own
express caveat about this).

(.exists1 x A), \"there is exactly one x such that A\", is listed here
only so that it is treated as a binder. Its formation rule and its
meaning (fold/unfold axioms against the expansion
Ex (A & Au (A[u/x] -> u = x))) live entirely in
hilbert-library/00-connectives.system; without that file loaded, no
(.exists1 ...) expression is a wff at all."
  '(.forall .exists .iota .exists1))

(defun at-symbol-p (sym)
  (and (symbolp sym) (> (length (symbol-name sym)) 1)
       (char= (char (symbol-name sym) 0) #\@)))

(defun reserved-head-symbol-p (sym)
  "Symbols the kernel's own matching/binder/rule machinery already gives
fixed structural meaning to -- never available for a fresh Sigma
declaration, regardless of what Sigma itself currently contains.
NOTE: (BINDER-HEADS) must be spliced in as LIST*'s final (tail)
argument, not passed as a middle argument -- LIST* conses every argument
except the last as a single element."
  (member sym (list* :=> '.to '.eq '.neg (binder-heads)) :test #'eq))

(defun fresh-symbol-name-p (sym ledger)
  "T iff SYM is safe to declare as a new Sigma symbol: an ordinary
symbol, not shaped like a pattern variable or meta-tag, not a reserved
structural head, and not already declared (as EITHER an atomic-wff
symbol or a variable -- the two namespaces share one pool of names, so
a symbol can't quietly be both)."
  (and (symbolp sym)
       (not (pat-var-p sym))
       (not (at-symbol-p sym))
       (not (reserved-head-symbol-p sym))
       (not (atomic-wff-symbol-p sym ledger))
       (not (variable-p sym ledger))
       (not (predicate-schema-arity sym ledger))))

(defun declare-atomic-wff-symbol (ledger sym)
  "The general (non-bootstrap) growth path for Sigma's atomic-wff
symbols: admits SYM with ORIGIN = (:DECLARED) once FRESH-SYMBOL-NAME-P
confirms it is available, and returns the NEW ledger. Usable at any
time, including long after BOOTSTRAP-KERNEL has closed -- unlike
ADMIT-PRIMITIVE, this is not bootstrap-gated, because a fresh
declaration cannot compromise soundness: it adds a name nothing else yet
mentions, so it proves nothing new about the existing vocabulary."
  (unless (fresh-symbol-name-p sym ledger)
    (error "DECLARE-ATOMIC-WFF-SYMBOL: ~S is not available for ~
            declaration (already declared, or reserved by the kernel ~
            itself)." sym))
  (ledger-append ledger 'atomic-wff-symbol sym (list :declared)))

(defun declare-predicate-schema-symbol (ledger sym arity)
  "As DECLARE-ATOMIC-WFF-SYMBOL, but for a predicate schema symbol of the
given ARITY (a positive integer): afterwards (SYM t1 ... tARITY) is a wff
for any terms t1..tARITY."
  (unless (fresh-symbol-name-p sym ledger)
    (error "DECLARE-PREDICATE-SCHEMA-SYMBOL: ~S is not available for ~
            declaration (already declared, or reserved by the kernel ~
            itself)." sym))
  (unless (and (integerp arity) (plusp arity))
    (error "DECLARE-PREDICATE-SCHEMA-SYMBOL: arity ~S is not a positive integer." arity))
  (ledger-append ledger 'predicate-schema-symbol (list sym arity) (list :declared)))

(defun declare-variable-symbol (ledger sym)
  "As DECLARE-ATOMIC-WFF-SYMBOL, but for Sigma's variable symbols."
  (unless (fresh-symbol-name-p sym ledger)
    (error "DECLARE-VARIABLE-SYMBOL: ~S is not available for ~
            declaration (already declared, or reserved by the kernel ~
            itself)." sym))
  (ledger-append ledger 'variable-symbol sym (list :declared)))
