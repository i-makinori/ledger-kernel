;;;; ledger_kernel.lisp
;;;;
;;;; Bw(x,y) made literal: a single append-only "ledger" of k-indexed
;;;; entries, where an entry's ORIGIN is either :PRIMITIVE (admitted by
;;;; fiat, bootstrap only) or :DERIVED (admitted only after a full K-proof
;;;; re-verified from scratch against strictly earlier ledger entries).
;;;;
;;;; Design decisions this file honors:
;;;;  - Sigma (vocabulary) and Gamma (open hypotheses) are NOT separately
;;;;    threaded state; they are two independent read-only projections
;;;;    over the same ledger (filter-by-kind).
;;;;  - A "side condition" is just a rule of a specially-tagged kind.
;;;;    A side condition whose verification genuinely needs meta-level
;;;;    computation (e.g. not-free-in, substitution) is instead defined
;;;;    as a plain Lisp DEFUN and invoked via an @-tagged meta-predicate;
;;;;    it is never itself a ledger entry.
;;;;  - Proofs are always fully expanded: a :DERIVED entry's use in a
;;;;    later proof is checked by instantiating its schema variables with
;;;;    the concrete bindings in play and re-running the full K-proof
;;;;    checker on the instantiated proof -- never trusted at the
;;;;    schema/pattern level alone.
;;;;  - All state (the ledger, Gamma, pattern bindings, the cycle guard)
;;;;    is threaded explicitly as ordinary function arguments and return
;;;;    values -- no DEFVAR/DEFPARAMETER, no SETF/SETQ, no dynamic
;;;;    rebinding anywhere in the file.
;;;;  - Meta predicates/constructors are plain Lisp DEFUNs, dispatched by
;;;;    the @ prefix; they are fixed and never part of the extensible
;;;;    rule database.
;;;;  - ORIGIN is modeled as a two-constructor type, Curry-Howard style:
;;;;      :PRIMITIVE  -- axiom-like, carries no proof
;;;;      :DERIVED    -- carries a full K-proof that was checked
;;;;  - Abbreviation/definition entries are ALSO ledger objects requiring
;;;;    a (conservativity) proof, unlike Goedel's own meta-level
;;;;    definitions.
;;;;  - Every time a proof or definition is admitted, k increases by
;;;;    exactly one. K IS the ledger position; ENTRY-K IS Goedel's y.

;;; ---------------------------------------------------------------------
;;; 0. Utilities
;;; ---------------------------------------------------------------------

(defpackage :ledger-kernel
  (:use :cl)
  (:export #:bootstrap-kernel #:entry-k #:entry-kind #:entry-payload
           #:entry-origin #:ledger-append #:admit-primitive #:check-and-extend
           #:check-and-extend-abbrev #:declare-atomic-wff-symbol
           #:declare-variable-symbol #:judgement? #:run-self-tests
           #:make-log-config #:silent-log
           #:ledger-commands #:ledger-from-commands
           #:write-ledger-to-file #:read-ledger-from-file
           #:write-commands-to-file
           #:@deduction #:check-and-extend-by-deduction
           #:check-and-extend-by-deduction-direct
           #:prove-tautology
           #:find-named-entry #:rename-symbol-everywhere
           #:alpha-rename-entry #:alpha-rename-forall
           #:enable-derived-entry-memoization
           #:disable-derived-entry-memoization
           #:reset-derived-entry-memoization
           #:bootstrap-kernel-from-spec
           #:read-system-spec-from-file
           #:bootstrap-kernel-from-spec-file))

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 1. Pattern matching
;;; ---------------------------------------------------------------------
;;;
;;; A pattern variable is any symbol whose name begins with "?" (e.g. ?A,
;;; ?x, ?t). Matching produces an alist of (pat-var . value) bindings, or
;;; the distinguished value +FAIL+ if no consistent match exists. NIL is a
;;; legitimate "matched, zero bindings" result, so it must not be
;;; conflated with failure -- hence the dedicated sentinel.

(defconstant +fail+ '+fail+)

(defun match-fail-p (x) (eq x +fail+))

(defun pat-var-p (x)
  (and (symbolp x)
       (> (length (symbol-name x)) 1)
       (char= (char (symbol-name x) 0) #\?)))

(defun lookup-binding (var binds)
  (assoc var binds :test #'eq))

(defun template-free-pattern-vars (pat)
  "All pattern variables occurring anywhere in PAT."
  (cond ((pat-var-p pat) (list pat))
        ((consp pat) (union (template-free-pattern-vars (car pat))
                             (template-free-pattern-vars (cdr pat))
                             :test #'eq))
        (t nil)))

(defun meta-constructor-p (sym)
  "Alist entry (@name . function) for meta-forms that EXPAND to a value
(e.g. @subst) rather than testing a boolean (e.g. @subst-ok?), or NIL if
SYM names none. META-CONSTRUCTORS-TABLE (section 4) builds the table
fresh on every call rather than caching it in a special variable."
  (assoc sym (meta-constructors-table) :test #'eq))

(defun instantiate-with-binds (pat binds)
  "Replace every pattern variable in PAT with its binding. A pattern
variable with no binding is left as-is (caller's responsibility to check
completeness first)."
  (cond
    ((pat-var-p pat)
     (let ((b (lookup-binding pat binds)))
       (if b (cdr b) pat)))
    ((consp pat)
     (cons (instantiate-with-binds (car pat) binds)
           (instantiate-with-binds (cdr pat) binds)))
    (t pat)))

(defun match-template (pat expr &optional (binds nil))
  "Match PAT against EXPR, extending BINDS. Returns an alist of bindings,
or +FAIL+. A repeated pattern variable must match consistently (EQUAL)
across occurrences.

PAT may contain an embedded meta-constructor call, e.g. (@subst ?x ?t
?A) inside axiom III.1's conclusion pattern. Such a node is evaluated --
not structurally matched -- once ALL of its arguments are already ground
under BINDS (typically because an earlier part of the same template
bound them, matched left-to-right, or they were seeded in beforehand as
an axiom's extra parameter). If some argument is still a free pattern
variable at this point, matching FAILS outright rather than trying to
unify/back-solve it: the caller must supply it from outside (see
CHECK-K-AXIOM-LINE's EXTRA-ARGS) instead of the matcher guessing it."
  (cond
    ((match-fail-p binds) +fail+)
    ((pat-var-p pat)
     (let ((existing (lookup-binding pat binds)))
       (if existing
           (if (equal (cdr existing) expr) binds +fail+)
           (cons (cons pat expr) binds))))
    ((and (consp pat) (meta-constructor-p (car pat)))
     (let ((inst-args (mapcar (lambda (a) (instantiate-with-binds a binds)) (cdr pat))))
       (if (some #'template-free-pattern-vars inst-args)
           +fail+
           (let ((value (apply (cdr (meta-constructor-p (car pat))) inst-args)))
             (match-template value expr binds)))))
    ((and (consp pat) (consp expr))
     (let ((b1 (match-template (car pat) (car expr) binds)))
       (if (match-fail-p b1) +fail+
           (match-template (cdr pat) (cdr expr) b1))))
    ((and (null pat) (null expr)) binds)
    ((equal pat expr) binds)
    (t +fail+)))

(defun match-schema-atoms (pat expr ledger &optional (binds nil))
  "Like MATCH-TEMPLATE, but the pattern variables are declared ATOMIC-WFF
SYMBOLS (A, B, C, ... per Sigma) rather than ?-prefixed symbols. This is
the matcher used for a :DERIVED entry's own stored proof, whose schema
hypotheses/conclusion were written using bare atomic-wff symbols as
schema placeholders. Declared VARIABLE symbols (v0, v1, ...) are
deliberately NOT treated as schema placeholders here: a schema's own
bound/generalized variables are always written as concrete literals,
matched structurally as-is."
  (cond
    ((match-fail-p binds) +fail+)
    ((and (symbolp pat) (atomic-wff-symbol-p pat ledger))
     (let ((existing (lookup-binding pat binds)))
       (if existing
           (if (equal (cdr existing) expr) binds +fail+)
           (cons (cons pat expr) binds))))
    ((and (consp pat) (consp expr))
     (let ((b1 (match-schema-atoms (car pat) (car expr) ledger binds)))
       (if (match-fail-p b1) +fail+
           (match-schema-atoms (cdr pat) (cdr expr) ledger b1))))
    ((and (null pat) (null expr)) binds)
    ((equal pat expr) binds)
    (t +fail+)))

(defun instantiate-schema-atoms (template binds)
  "Substitute bound atomic-wff schema symbols throughout TEMPLATE using
BINDS (an alist produced by MATCH-SCHEMA-ATOMS). An unbound schema atom
is left as-is."
  (cond
    ((and (symbolp template) (lookup-binding template binds)) (cdr (lookup-binding template binds)))
    ((consp template) (cons (instantiate-schema-atoms (car template) binds)
                             (instantiate-schema-atoms (cdr template) binds)))
    (t template)))

;;; ---------------------------------------------------------------------
;;; 1.5. A persistent ordered map (treap), used to index the ledger
;;; ---------------------------------------------------------------------
;;;
;;; A plain list, scanned linearly, makes every ledger lookup (every
;;; entry of a given kind, every entry sharing a citation name) O(n) in
;;; the TOTAL number of entries the ledger has ever accumulated, however
;;; few of them are actually relevant. A TREAP is a binary search tree
;;; whose shape is kept balanced (in expectation) by tagging every node
;;; with a random priority and maintaining heap order on priority as well
;;; as BST order on key; unlike AVL/red-black trees it needs no rotation
;;; bookkeeping beyond "does my new child now outrank me", which keeps a
;;; purely functional (structure-sharing, non-mutating) implementation
;;; short. Every operation below returns a NEW treap and never mutates an
;;; existing node, so old ledger values, however deeply nested in a
;;; caller's LET*, remain exactly as they were.

(defstruct (treap-node (:constructor %make-treap-node (key value priority left right)))
  key value priority left right)

(defun treap-rotate-right (node)
  "NODE's left child outranks NODE: bring it up, giving it NODE (holding
the left child's old right subtree) as its new right child."
  (let ((l (treap-node-left node)))
    (%make-treap-node (treap-node-key l) (treap-node-value l) (treap-node-priority l)
                       (treap-node-left l)
                       (%make-treap-node (treap-node-key node) (treap-node-value node) (treap-node-priority node)
                                         (treap-node-right l) (treap-node-right node)))))

(defun treap-rotate-left (node)
  "Mirror image of TREAP-ROTATE-RIGHT, for when NODE's right child outranks it."
  (let ((r (treap-node-right node)))
    (%make-treap-node (treap-node-key r) (treap-node-value r) (treap-node-priority r)
                       (%make-treap-node (treap-node-key node) (treap-node-value node) (treap-node-priority node)
                                         (treap-node-left node) (treap-node-left r))
                       (treap-node-right r))))

(defun treap-insert (node key value)
  "Functional insert of KEY -> VALUE into the treap rooted at NODE (NIL
for an empty treap), giving KEY a fresh random priority. Every ledger
key used in this file (an ENTRY-K) is in fact always strictly greater
than every key already present -- entries are only ever appended -- but
this function makes no such assumption; it is an ordinary persistent
treap insert, expected O(log n) for a treap of N nodes regardless of
insertion order. Returns a NEW treap; NODE itself is untouched."
  (cond
    ((null node) (%make-treap-node key value (random most-positive-fixnum) nil nil))
    ((< key (treap-node-key node))
     (let* ((new-left (treap-insert (treap-node-left node) key value))
            (grown (%make-treap-node (treap-node-key node) (treap-node-value node) (treap-node-priority node)
                                      new-left (treap-node-right node))))
       (if (> (treap-node-priority new-left) (treap-node-priority grown))
           (treap-rotate-right grown)
           grown)))
    ((> key (treap-node-key node))
     (let* ((new-right (treap-insert (treap-node-right node) key value))
            (grown (%make-treap-node (treap-node-key node) (treap-node-value node) (treap-node-priority node)
                                      (treap-node-left node) new-right)))
       (if (> (treap-node-priority new-right) (treap-node-priority grown))
           (treap-rotate-left grown)
           grown)))
    (t
     ;; KEY already present (never happens for ENTRY-K, which is always
     ;; fresh, but this keeps TREAP-INSERT correct as a general map).
     (%make-treap-node key value (treap-node-priority node) (treap-node-left node) (treap-node-right node)))))

(defun treap-values-below (node bound)
  "Ascending-by-key list of the values stored in the treap rooted at
NODE, restricted to keys strictly less than BOUND (or every value, in
ascending key order, if BOUND is NIL). Because NODE's key order is a
genuine BST order, a node whose OWN key is already >= BOUND guarantees
its entire right subtree (all keys strictly greater still) is excluded
too, so that subtree is never even visited -- only the left spine down
to the boundary is walked eagerly; everything actually returned is
visited exactly once. This is what makes ENTRIES-UPTO's restriction
cheap: it costs nothing until something is actually read out of the
restricted view, and even then only in proportion to what is read,
O(log n + result size) rather than O(n)."
  (labels ((walk (n tail)
             (cond
               ((null n) tail)
               ((and bound (>= (treap-node-key n) bound))
                (walk (treap-node-left n) tail))
               (t (walk (treap-node-left n) (cons (treap-node-value n) (walk (treap-node-right n) tail)))))))
    (walk node nil)))

;;; A small persistent alist-as-map, used for LEDGER's BY-KIND and
;;; BY-DERIVED-NAME indices below. The number of distinct KEYs here (rule
;;; kinds, or distinct ITH/TH/DEF-ABBREV citation names) is what is
;;; small, not the ledger itself, so a linear ALIST lookup/update at this
;;; outer level is not the O(ledger-size) cost this section exists to
;;; eliminate -- the real saving is that each lookup narrows down to one
;;; single bucket's treap before doing any per-entry work.

(defun alist-put (alist key value)
  "Functional update: a NEW alist with KEY mapped to VALUE, replacing any
existing entry for KEY (compared with EQ -- kinds and names are always
symbols here)."
  (acons key value (remove key alist :key #'car :test #'eq)))

(defun alist-get (alist key)
  (cdr (assoc key alist :test #'eq)))

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

(defun entries-of-kind (kind ledger)
  (treap-values-below (alist-get (ledger-by-kind ledger) kind) (ledger-bound ledger)))

(defun entries-upto (k ledger)
  "A read-only VIEW of LEDGER showing only entries with position strictly
less than K -- used when re-verifying a proof, so nothing can (even
accidentally) depend on itself or on anything defined later. O(1): see
LEDGER's BOUND field, above."
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
express caveat about this)."
  '(.forall .exists .iota))

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
       (not (variable-p sym ledger))))

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

(defun declare-variable-symbol (ledger sym)
  "As DECLARE-ATOMIC-WFF-SYMBOL, but for Sigma's variable symbols."
  (unless (fresh-symbol-name-p sym ledger)
    (error "DECLARE-VARIABLE-SYMBOL: ~S is not available for ~
            declaration (already declared, or reserved by the kernel ~
            itself)." sym))
  (ledger-append ledger 'variable-symbol sym (list :declared)))

;;; ---------------------------------------------------------------------
;;; 3. Side conditions: object-level rules vs. meta-level predicates
;;; ---------------------------------------------------------------------
;;;
;;; A rule's payload is (NAME SIDE-CONDITIONS FORM). Each element of
;;; SIDE-CONDITIONS is either:
;;;   - an ordinary object-level judgement to recurse into, e.g. (wff? ?A)
;;;     -- checked via JUDGEMENT?, extensible by adding more ledger
;;;     entries of the relevant kind;
;;;   - an @-tagged meta-form, e.g. (@not-free-in? ?x ?A) or
;;;     (@subst-ok? ?x ?t ?A) -- dispatched immediately to a fixed Lisp
;;;     DEFUN in *META-PREDICATES*, because verifying it needs
;;;     computation (free-variable traversal, substitution) that doesn't
;;;     reduce to "does some entry in the ledger match".

(defun at-tagged-p (form)
  (and (consp form) (symbolp (car form))
       (> (length (symbol-name (car form))) 1)
       (char= (char (symbol-name (car form)) 0) #\@)))

;; META-CONSTRUCTOR-P is declared up in section 1 (MATCH-TEMPLATE needs it
;; already defined); META-CONSTRUCTORS-TABLE, its table-building
;; counterpart, lives at the end of this section, alongside
;; META-PREDICATES-TABLE below.

(defun meta-predicate-p (sym)
  "Alist entry (@name . function) for an @-tagged side condition, or NIL
if SYM names none."
  (assoc sym (meta-predicates-table) :test #'eq))

(defun expand-meta-constructors (form binds)
  "Recursively replace any fully-bound @-tagged meta-constructor call
inside FORM with its computed value. Used to resolve things like
(@subst ?x ?t ?A) appearing inside a rule's FORM before matching it
against a target expression."
  (cond
    ((and (consp form) (meta-constructor-p (car form)))
     (let* ((args (mapcar (lambda (a) (instantiate-with-binds a binds)) (cdr form)))
            (fn (cdr (meta-constructor-p (car form)))))
       (apply fn args)))
    ((consp form)
     (cons (expand-meta-constructors (car form) binds)
           (expand-meta-constructors (cdr form) binds)))
    (t form)))

(defun check-condition (cond-form binds ledger &optional (seen nil) (open-hyps nil))
  "Check one side condition under BINDS against LEDGER. Returns (values
new-binds ok-p). Object-level conditions may extend BINDS (e.g. matching
(wff? ?A) can bind ?A if it wasn't already bound); meta conditions never
extend bindings -- they only test.

SEEN is JUDGEMENT-BIND's cycle guard, threaded through here so that an
object-level condition -- which recurses back into JUDGEMENT? -- continues
the SAME cycle-detection chain as whatever outer JUDGEMENT-BIND call is
currently checking conditions, rather than starting a fresh one.

OPEN-HYPS is Gamma (see the comment above ATOMIC-WFF-SYMBOL-P), passed
along unconditionally as a meta-predicate's second argument so that
META-NOT-FREE-IN-DEPENDENCIES?/META-PROVEN? can consult it without any
special variable."
  (cond
    ((at-tagged-p cond-form)
     (let ((fn (cdr (meta-predicate-p (car cond-form)))))
       (unless fn (error "Unknown meta-predicate: ~S" (car cond-form)))
       (let ((args (mapcar (lambda (a) (instantiate-with-binds a binds)) (cdr cond-form))))
         (values binds (apply fn ledger open-hyps args)))))
    (t
     ;; Object-level: (kind arg). ARG's pattern variables were already
     ;; bound by matching the rule's own FORM against the target
     ;; expression, so instantiate ARG under BINDS first, then verify the
     ;; resulting concrete judgement.
     (let ((inst-arg (instantiate-with-binds (second cond-form) binds)))
       (values binds (judgement? (car cond-form) inst-arg ledger seen open-hyps))))))

(defun check-conditions (conditions binds ledger &optional (seen nil) (open-hyps nil))
  "Thread BINDS through all of CONDITIONS in order, short-circuiting on
first failure. Returns (values final-binds ok-p)."
  (if (null conditions)
      (values binds t)
      (multiple-value-bind (b1 ok1) (check-condition (car conditions) binds ledger seen open-hyps)
        (if (not ok1)
            (values binds nil)
            (check-conditions (cdr conditions) b1 ledger seen open-hyps)))))

;;; ---------------------------------------------------------------------
;;; 4. Meta predicates and constructors (plain DEFUNs)
;;; ---------------------------------------------------------------------


(defun free-vars-wff (wff ledger)
  "Structural free-variable collector. Any leaf symbol that is a
declared variable (per current Sigma, LEDGER) and not under a matching
binder is free. Non-variable leaves and rule-name heads contribute
nothing."
  (labels ((walk (form bound)
             (cond
               ((and (symbolp form) (variable-p form ledger) (not (member form bound :test #'eq)))
                (list form))
               ((symbolp form) nil)
               ((and (consp form) (member (car form) (binder-heads) :test #'eq))
                (let ((x (second form)) (body (third form)))
                  (walk body (cons x bound))))
               ((consp form)
                (union (walk (car form) bound) (walk (cdr form) bound) :test #'eq))
               (t nil))))
    (walk wff nil)))

(defun meta-not-free-in? (ledger open-hyps var wff)
  (declare (ignore open-hyps))
  (not (member var (free-vars-wff wff ledger) :test #'eq)))

(defun meta-not-free-in-dependencies? (ledger open-hyps var)
  "GEN's restriction (Verallgemeinerungsverbot): VAR must not occur free
in any hypothesis still open in the CURRENT proof (Gamma, threaded in as
OPEN-HYPS)."
  (every (lambda (hyp-wff) (meta-not-free-in? ledger nil var hyp-wff)) open-hyps))

(defun count-bound-occurrences (var wff)
  "How many times VAR would be captured (occur under a binder for VAR)
if substituted into WFF as-is. Used for the substitution side condition."
  (labels ((walk (form)
             (cond
               ((and (consp form) (member (car form) (binder-heads) :test #'eq))
                (+ (if (eq (second form) var) 1 0) (walk (third form))))
               ((consp form) (+ (walk (car form)) (walk (cdr form))))
               (t 0))))
    (walk wff)))

(defun substitute-wff (var term wff)
  (cond
    ((eq wff var) term)
    ((and (consp wff) (member (car wff) (binder-heads) :test #'eq))
     (if (eq (second wff) var)
         wff ;; var is shadowed here; substitution does not descend
         (list (first wff) (second wff) (substitute-wff var term (third wff)))))
    ((consp wff) (cons (substitute-wff var term (car wff)) (substitute-wff var term (cdr wff))))
    (t wff)))

(defun meta-subst-ok? (ledger open-hyps var term wff)
  "Capture-avoidance: substituting TERM for VAR into WFF must not
increase the count of variable occurrences that fall under a binder
(Maehara's substitution condition)."
  (declare (ignore open-hyps))
  (let ((before (count-bound-occurrences var wff))
        (term-vars (free-vars-wff term ledger)))
    (declare (ignore before))
    ;; No free variable of TERM may become captured by a binder in WFF
    ;; at the substitution site(s).
    (labels ((walk (form)
               (cond
                 ((eq form var) t)
                 ((and (consp form) (member (car form) (binder-heads) :test #'eq))
                  (if (eq (second form) var)
                      t ;; shadowed: fine, no substitution happens here
                      (and (not (member (second form) term-vars :test #'eq))
                           (walk (third form)))))
                 ((consp form) (and (walk (car form)) (walk (cdr form))))
                 (t t))))
      (walk wff))))

(defun meta-subst (ledger var term wff)
  (declare (ignore ledger))
  (substitute-wff var term wff))

(defun substitute-wff-multi (vars terms wff)
  "As SUBSTITUTE-WFF, but simultaneously: every var in VARS is replaced by
the correspondingly-positioned term in TERMS, in ONE pass, rather than
one substitution after another (which could let an earlier substitution's
own free variables be mistaken for a later VAR to replace). Implemented
via a standard two-hop trick: swap each VAR for a fresh, guaranteed-unused
placeholder symbol first, then swap each placeholder for its real TERM --
since nothing in WFF or TERMS could possibly already mention a freshly
GENSYM'd symbol, the two hops can never interfere with each other or with
one another's order. Needed for N-ARY inductive predicates (Section 20):
their induction motive depends on all of a tuple's argument positions at
once, and the single-variable @SUBST used everywhere else in this file
cannot express \"replace x1 with t1 AND x2 with t2, together\"."
  (let ((temps (mapcar (lambda (v) (gensym (symbol-name v))) vars)))
    (let ((swapped (reduce (lambda (w pair) (substitute-wff (car pair) (cdr pair) w))
                            (mapcar #'cons vars temps) :initial-value wff)))
      (reduce (lambda (w pair) (substitute-wff (car pair) (cdr pair) w))
              (mapcar #'cons temps terms) :initial-value swapped))))

(defun meta-subst-multi-ok? (ledger open-hyps vars terms wff)
  "As META-SUBST-OK?, but for the whole VARS/TERMS tuple SUBSTITUTE-WFF-
MULTI would apply at once: capture-safe iff EVERY individual (var . term)
pair in the tuple would itself be capture-safe against the ORIGINAL WFF
-- the two-hop GENSYM trick means the substitutions never interact, so
checking each pair independently against the untouched WFF is exactly
right, not an approximation."
  (declare (ignore open-hyps))
  (every (lambda (v tm) (meta-subst-ok? ledger nil v tm wff)) vars terms))

(defun meta-substitutes? (ledger open-hyps var term wff result)
  "T iff RESULT is exactly WFF with TERM substituted for VAR -- i.e. RESULT
= (@subst VAR TERM WFF). Used where a rule needs to relate two ALREADY
STRUCTURALLY BOUND schema variables (one a citer-supplied concrete
formula, the other computed) by the substitution relation, as a SIDE
CONDITION to check AFTER matching, rather than as an embedded (@subst ...)
meta-constructor to EVALUATE DURING matching -- EXISTS-ELIM (Section 21)
needs exactly this: its second premise pattern must bind ?Ac purely
structurally (matching a citer-supplied, already-concrete antecedent),
because at premise-matching time its own witness variable ?c is not bound
yet (?c only arrives afterward, as an EXTRA-PARAM) and so could not
already be substituted into an embedded (@subst ?x ?c ?A) the way III.1's
own conclusion-side @subst can rely on ?x/?t/?A all being ground by the
time it is reached."
  (declare (ignore ledger open-hyps))
  (equal (substitute-wff var term wff) result))

(defun meta-proven? (ledger open-hyps wff)
  "Is WFF currently an open hypothesis in the proof being checked (Gamma,
OPEN-HYPS), or the conclusion of some already-admitted :TH/:ITH ledger
entry? Used only inside side conditions of DERIVED rules being checked
against entries strictly earlier than themselves (see CHECK-AND-EXTEND).
Consults only the TH/ITH buckets of LEDGER's kind index (ENTRIES-OF-KIND),
never the whole ledger -- there is no index on a conclusion FORMULA
itself, so within those two buckets this still checks each candidate in
turn, but it no longer pays for every unrelated WFF?/AXIOM/IRULE/etc.
entry along the way."
  (or (member wff open-hyps :test #'equal)
      (some (lambda (e) (equal (proof-conclusion (second (entry-payload e))) wff))
            (append (entries-of-kind 'th ledger) (entries-of-kind 'ith ledger)))))

(defun meta-predicates-table ()
  "The dispatch table CHECK-CONDITION/META-PREDICATE-P look up @-tagged
side conditions in."
  (list (cons '@not-free-in? #'meta-not-free-in?)
        (cons '@not-free-in-dependencies? #'meta-not-free-in-dependencies?)
        (cons '@subst-ok? #'meta-subst-ok?)
        (cons '@proven? #'meta-proven?)
        (cons '@substitutes? #'meta-substitutes?)
        (cons '@substn-ok? #'meta-subst-multi-ok?)))

(defun meta-constructors-table ()
  "As META-PREDICATES-TABLE, but for meta-constructors (META-CONSTRUCTOR-P,
used by MATCH-TEMPLATE)."
  (list (cons '@subst (lambda (var term wff) (substitute-wff var term wff)))
        (cons '@substn (lambda (vars terms wff) (substitute-wff-multi vars terms wff)))))

;;; ---------------------------------------------------------------------
;;; 5. JUDGEMENT?: the core recursive checker
;;; ---------------------------------------------------------------------
;;;
;;; (judgement? kind expr ledger) is T iff some entry of KIND in LEDGER
;;; matches EXPR under bindings that satisfy that entry's side
;;; conditions. This subsumes wff?, var?, term?, and (for kinds like
;;; irule/axiom/ith/th) is invoked as part of applying an inference --
;;; see section 6.

(defun judgement-bind (kind args binds ledger &optional (seen nil) (open-hyps nil))
  "Try every KIND-tagged rule entry in LEDGER; for a matching one, check
its side conditions can be satisfied (extending BINDS further), and if
so also check that ARGS themselves match the rule's FORM once expanded
under the resulting bindings. Returns (values new-binds ok-p).

SEEN is the cycle guard: an explicit list of (kind . args) pairs
currently being checked somewhere up the call chain, to avoid infinite
recursion through mutually-referential rules. It keys on (KIND . ARGS)
-- the concrete problem instance being proved -- extended ONCE for the
whole attempt (across every candidate entry), not per entry. Keying on
the rule's own fixed FORM instead would be wrong: the same formation
rule (e.g. WFF_TO?) is legitimately reused at every nesting depth of a
formula, so two structurally different subgoals that happen to try the
same rule are NOT the same recursion and must not be conflated. Keying
on the actual target ARGS correctly identifies a genuine repeat (the
same subgoal recurring on itself) while leaving distinct subgoals free
to proceed.

OPEN-HYPS is Gamma, passed straight through to CHECK-CONDITIONS
unchanged (this function never extends it -- only CHECK-K-PROOF's own
:HYP handling does that)."
  (let ((key (cons kind args)))
    (if (member key seen :test #'equal)
        (values binds nil)
        (let ((seen (cons key seen)))
          (labels ((try-entries (entries)
                     (if (null entries)
                         (values binds nil)
                         (multiple-value-bind (b ok)
                             (try-judgement-entry (car entries) kind args binds ledger seen open-hyps)
                           (if ok
                               (values b t)
                               (try-entries (cdr entries)))))))
            (try-entries (entries-of-kind kind ledger)))))))

(defun try-judgement-entry (entry kind args binds ledger seen open-hyps)
  "Try a single KIND-tagged rule ENTRY against ARGS/BINDS, as described in
JUDGEMENT-BIND. Returns (values new-binds ok-p)."
  (destructuring-bind (name conditions form) (entry-payload entry)
    (declare (ignore name))
    (let ((b0 (match-template form (cons kind args) binds)))
      (if (match-fail-p b0)
          (values binds nil)
          (check-conditions conditions b0 ledger seen open-hyps)))))

(defun judgement? (kind expr ledger &optional (seen nil) (open-hyps nil))
  "Boolean convenience wrapper: does some KIND-rule justify EXPR (a full,
concrete, pattern-variable-free expression) against LEDGER? SEEN, when
supplied, continues an already-in-progress cycle-detection chain (see
JUDGEMENT-BIND); an ordinary top-level caller leaves it NIL. OPEN-HYPS is
Gamma, likewise NIL for a call made outside of any proof currently being
checked."
  (nth-value 1 (judgement-bind kind (list expr) nil ledger seen open-hyps)))

;;; ---------------------------------------------------------------------
;;; 6. K-proofs and CHECK-AND-EXTEND
;;; ---------------------------------------------------------------------
;;;
;;; A raw k-line is (NUMBERING FORMULA ROLE BY):
;;;   ROLE is one of :HYP, :AXIOM, :IR, :ITH, :TH, :DEF-ABBREV.
;;;   BY carries role-specific justification data, e.g.
;;;     (:AXIOM axiom-name)
;;;     (:IR irule-name cited-numbering...)
;;;     (:ITH ith-name cited-numbering...)
;;;     (:TH th-name)
;;;     (:HYP)
;;;
;;; CHECK-K-PROOF walks the lines in order, maintaining a local
;;; "proven-so-far" list (numbering -> formula), and for each line
;;; dispatches on ROLE. Crucially, when a line cites a DERIVED ledger
;;; entry (an :ITH/:TH-kind rule), it does NOT trust the schema/pattern
;;; match alone -- it fully instantiates that entry's own stored proof
;;; with the concrete bindings and re-verifies it via a recursive
;;; CHECK-K-PROOF call, bottoming out at :PRIMITIVE entries and object-
;;; level side conditions.

(defstruct k-line numbering formula role by)

(defun raw->k-line (raw)
  (destructuring-bind (numbering formula role by) raw
    (make-k-line :numbering numbering :formula formula :role role :by by)))

(defun find-proven (numbering proven-alist)
  (cdr (assoc numbering proven-alist :test #'equal)))

(defun match-templates-seq (pats vals binds)
  "Match each of PATS against the correspondingly-positioned VALS, in
order, threading BINDS left-to-right through MATCH-TEMPLATE. Returns the
final bindings, or +FAIL+ as soon as any pair fails to match or the two
lists have different lengths."
  (cond
    ((match-fail-p binds) +fail+)
    ((and (null pats) (null vals)) binds)
    ((or (null pats) (null vals)) +fail+)
    (t (match-templates-seq (cdr pats) (cdr vals)
                             (match-template (car pats) (car vals) binds)))))

(defun resolve-cited (nums proven-alist)
  "Look up each of NUMS (proof-line citations) in PROVEN-ALIST via
FIND-PROVEN, returning the list of formulas found in the same order, or
+FAIL+ if any citation does not yet resolve to a previously-proven line."
  (cond
    ((null nums) nil)
    (t (let ((actual (find-proven (car nums) proven-alist)))
         (if (null actual)
             +fail+
             (let ((rest (resolve-cited (cdr nums) proven-alist)))
               (if (match-fail-p rest) +fail+ (cons actual rest))))))))

(defun check-k-ir-line (line proven-alist ledger open-hyps)
  "ROLE = :IR. BY = (irule-name . rest), where REST splits into two
groups: leading PROOF-LINE CITATIONS (numbers resolved to formulas via
PROVEN-ALIST) followed by LITERAL EXTRA PARAMETERS -- values supplied
directly rather than cited from earlier lines. This split is needed
because a rule like Gen takes both a premise line AND a bare variable
argument that never appeared as its own proof line: (Gen 0 v0) cites
line 0 as the premise and passes v0 as the variable to generalize on.
An irule's FORM therefore has the shape
  (PREMISE-PATTERNS EXTRA-PARAM-PATTERNS :=> CONCLUSION-PATTERN)
where PREMISE-PATTERNS match the cited formulas (in order), and
EXTRA-PARAM-PATTERNS match the literal extra arguments (in order, after
all citations). Once every pattern variable is bound this way, the
CONCLUSION-PATTERN is matched against LINE's own formula, and finally
the rule's side conditions are checked (which can consult Gamma, passed
in as OPEN-HYPS, via @not-free-in-dependencies?)."
  (destructuring-bind (irule-name . rest) (k-line-by line)
    (labels ((try-entries (entries)
               (and entries
                    (or (try-ir-entry (car entries) irule-name rest line proven-alist ledger open-hyps)
                        (try-entries (cdr entries))))))
      (try-entries (entries-of-kind 'irule ledger)))))

(defun try-ir-entry (entry irule-name rest line proven-alist ledger open-hyps)
  "Try a single :IRULE-kind ledger ENTRY against LINE, as described in
CHECK-K-IR-LINE. Returns T if ENTRY justifies LINE, else NIL."
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
                         (let ((b1 (match-templates-seq premise-pats actuals nil)))
                           (and (not (match-fail-p b1))
                                (let ((b2 (match-templates-seq extra-pats extras b1)))
                                  (and (not (match-fail-p b2))
                                       (let ((b3 (match-template concl-pat (k-line-formula line) b2)))
                                         (and (not (match-fail-p b3))
                                              (nth-value 1 (check-conditions conditions b3 ledger nil open-hyps))))))))))))))))

(defun check-k-axiom-line (line ledger open-hyps)
  "ROLE = :AXIOM. BY = (axiom-name . extra-args), where EXTRA-ARGS are
literal values supplied directly by the citing proof -- e.g. axiom
III.1's substituted term, (III.1 v2) -- analogous to an IRULE's
EXTRA-PARAM-PATTERNS. Axioms never cite earlier proof lines, so unlike
CHECK-K-IR-LINE there is no citation-splitting step: all of BY's cdr is
EXTRA-ARGS.

An axiom's FORM has the shape (EXTRA-PARAM-PATTERNS CONCLUSION-PATTERN).
EXTRA-PARAM-PATTERNS are matched against EXTRA-ARGS FIRST, seeding their
bindings into BINDS before CONCLUSION-PATTERN is matched against the
line's own formula -- this is what lets a meta-constructor embedded in
CONCLUSION-PATTERN (axiom III.1's (@subst ?x ?t ?A)) find ?T already
ground when MATCH-TEMPLATE reaches it, without any unification."
  (destructuring-bind (axiom-name . extra-args) (k-line-by line)
    (labels ((try-entries (entries)
               (and entries
                    (or (try-axiom-entry (car entries) axiom-name extra-args line open-hyps ledger)
                        (try-entries (cdr entries))))))
      (try-entries (entries-of-kind 'axiom ledger)))))

(defun try-axiom-entry (entry axiom-name extra-args line open-hyps ledger)
  "Try a single :AXIOM-kind ledger ENTRY against LINE, as described in
CHECK-K-AXIOM-LINE. Returns T if ENTRY justifies LINE, else NIL."
  (destructuring-bind (name conditions form) (entry-payload entry)
    (and (eq name axiom-name)
         (destructuring-bind (extra-pats concl-pat) form
           (and (= (length extra-pats) (length extra-args))
                (let ((b1 (match-templates-seq extra-pats extra-args nil)))
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
;;; CHECK-K-PROOF's own soundness logic never consults a LOG-CONFIG: a
;;; missing, silent, or even wrongly-configured logger can never turn a
;;; rejected proof into an accepted one, or vice versa -- LOG-CONFIG only
;;; ever gates a side-effecting PRINT, layered strictly on top of the
;;; existing T/NIL verdicts. Two independent flags, matching what a
;;; reader of a rejected or accepted proof actually wants to ask:
;;;   ERRORS       -- when a line is REJECTED, print which line, its
;;;                   role, and (for :AXIOM/:IR/:ITH/:TH/:DEF-ABBREV
;;;                   lines) which name it tried to cite.
;;;   APPLICATIONS -- the same, when a line is ACCEPTED -- turning a
;;;                   successful run into a readable, step-by-step trace
;;;                   of which rule justified which line.
;;; Both default to NIL (silent), so every existing call site that never
;;; passes a LOG-CONFIG behaves exactly as before this section existed.

(defstruct (log-config (:constructor make-log-config (&key errors applications)))
  (errors nil) (applications nil))

(defun silent-log ()
  "The default LOG-CONFIG: neither flag set, nothing printed."
  (make-log-config))

(defun log-line-result (log line ok)
  "Print one diagnostic line for LINE's outcome, gated on whichever of
LOG's two flags applies. LOG may be NIL (treated the same as
(SILENT-LOG)), so callers written before this section still pass."
  (when (and log (or (and ok (log-config-applications log))
                      (and (not ok) (log-config-errors log))))
    (format t "~&[~:[REJECT~;accept~]] line ~S (~S~@[ ~S~]).~%"
            ok (k-line-numbering line) (k-line-role line)
            (and (consp (k-line-by line)) (car (k-line-by line))))))

(defun log-admission-result (log name ok)
  "As LOG-LINE-RESULT, but for the top-level accept/reject of an entire
CHECK-AND-EXTEND/CHECK-AND-EXTEND-ABBREV admission, identified by NAME
rather than by a line number."
  (when (and log (or (and ok (log-config-applications log))
                      (and (not ok) (log-config-errors log))))
    (format t "~&[~:[REJECT~;accept~]] admission of ~S.~%" ok name)))

(defun check-k-proof (raw-proof ledger &optional (log (silent-log)))
  "Re-verify RAW-PROOF from scratch against LEDGER (entries strictly
earlier than whatever is being admitted; caller is responsible for
passing an appropriately-restricted ledger view, e.g. via
ENTRIES-UPTO). Returns T iff every line checks out. Gamma (the open
hypotheses) starts fresh as NIL here, local to this call, and is threaded
explicitly through WALK below as an ordinary accumulator argument: a
:HYP line extends it (by consing) for the REST of this proof only, and a
recursive re-verification of some cited :DERIVED entry's own stored
proof (via TRY-DERIVED-ENTRY, which calls this function again) starts
this same function again from its own fresh NIL, so it gets its own
Gamma rather than inheriting or leaking into the caller's.

LOG, when non-silent, prints a line-by-line trace (see LOG-LINE-RESULT
above); it is threaded into the same recursive re-verification of a
cited :DERIVED entry's own stored proof, so a request to trace
applications or errors sees the FULL expansion this file always performs
anyway -- all the way down to :PRIMITIVE entries -- not just the
top-level proof's own lines."
  (labels ((walk (lines proven open-hyps)
             (if (null lines)
                 t
                 (let* ((line (raw->k-line (car lines)))
                        (ok
                          (case (k-line-role line)
                            ;; A :HYP line must itself be a well-formed
                            ;; formula, so a malformed or undeclared
                            ;; "formula" can never be smuggled in as an
                            ;; assumption. Whether it is added to
                            ;; OPEN-HYPS for the rest of the walk is
                            ;; decided below, once OK is known.
                            (:hyp (judgement? 'wff? (k-line-formula line) ledger))
                            (:axiom (check-k-axiom-line line ledger open-hyps))
                            (:ir (check-k-ir-line line proven ledger open-hyps))
                            ;; :ITH, :TH, and :DEF-ABBREV all fall
                            ;; through to the catch-all: all three are
                            ;; DERIVED entries (proof required at
                            ;; admission, full re-expansion required at
                            ;; every use), and CHECK-K-DERIVED-LINE's own
                            ;; kind filter covers all three uniformly.
                            ;; There is deliberately no weaker,
                            ;; axiom-like ("trust the schema match
                            ;; alone") path for DEF-ABBREV, which would
                            ;; let an abbreviation whose admission proof
                            ;; is unrelated to its claimed definiens
                            ;; assert an arbitrary formula for free --
                            ;; CHECK-AND-EXTEND-ABBREV closes that by
                            ;; requiring the proof's own conclusion to
                            ;; match DEFINIENS at admission time.
                            (t (check-k-derived-line line proven ledger log)))))
                   (log-line-result log line ok)
                   (and ok
                        (walk (cdr lines)
                              (cons (cons (k-line-numbering line) (k-line-formula line)) proven)
                              (if (eq (k-line-role line) :hyp)
                                  (cons (k-line-formula line) open-hyps)
                                  open-hyps)))))))
    (walk raw-proof nil nil)))

(defun match-schema-hyps-against-cited (pats nums proven-alist ledger binds)
  "Match each of PATS (a list of schema-hypothesis formulas some entry
requires as premises) against the formula cited by the corresponding
entry of NUMS (proof-line numbers, resolved via FIND-PROVEN against
PROVEN-ALIST), threading BINDS left-to-right through MATCH-SCHEMA-ATOMS.
Shared by TRY-DERIVED-ENTRY (ITH/TH/DEF-ABBREV, whose schema-hyps are
ALL of the stored proof's :HYP lines) and TRY-DEDUCTION-ENTRY (TH-DED,
Section 11.5, whose schema-hyps are the stored proof's :HYP lines MINUS
the one already discharged into the conclusion) -- both need to match
some list of required premises against citations the identical way."
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
;;; TRY-DERIVED-ENTRY and TRY-DEDUCTION-ENTRY both end the same way: once
;;; an entry E's schema is matched against the citing LINE (and, if E has
;;; any required premises, against CITED), the resulting bindings B2
;;; instantiate E's own stored RAW-PROOF, which is then re-verified from
;;; scratch via CHECK-K-PROOF against ENTRIES-UPTO(ENTRY-K E). Nothing
;;; about that re-verification's OUTCOME depends on where the citation
;;; came from: it is a pure function of (E . B2) alone. Two facts make
;;; this precise:
;;;
;;;   1. E, once appended to the ledger, is an immutable structure that
;;;      is never mutated and never reused as a *different* entry
;;;      elsewhere -- ENTRY-K assigns it one fixed position forever.
;;;   2. ENTRIES-UPTO(ENTRY-K E) -- the "entries strictly before E" view
;;;      E's own proof is checked against -- is, by the ledger's
;;;      append-only design, exactly the same frozen prefix no matter
;;;      which later LEDGER value, or which call site, asks for it: it
;;;      can only ever contain what already existed at the moment E was
;;;      admitted.
;;;
;;; So memoizing CHECK-K-PROOF's verdict for a given (E . B2) pair is
;;; sound: it changes nothing about WHAT the checker accepts, only skips
;;; literally repeating an already-completed, deterministic computation.
;;; This matters most for entries with NO required premises (an ordinary
;;; zero-Gamma TH/TH-DED citation, e.g. "(th-identity)" with no cited
;;; line numbers): there, B2 is derived purely from the citing LINE's own
;;; formula, so the SAME entry cited with the SAME instantiation
;;; anywhere in the ledger -- however many times, however deeply nested
;;; -- is verified only once. An entry with required premises (Gamma) can
;;; still be memoized exactly the same way -- B2 is just as deterministic
;;; once CITED has been resolved into concrete bindings -- but in
;;; practice sees fewer cache hits, since B2 there also depends on
;;; whatever happened to be proven earlier in the CITING proof.
;;;
;;; OFF by default: ordinary use of this kernel, including every
;;; RUN-*-SELF-TESTS call, exercises the original always-re-verify path
;;; with no behavioural difference whatsoever. This is a pure performance
;;; layer bolted on top of the trusted core, never a relaxation of it --
;;; see TEST-DERIVED-ENTRY-MEMOIZATION below for a differential check
;;; (same verdicts, cache on vs. off) plus a demonstration of the speedup
;;; on exactly the exponential-blowup pattern that motivated this.

(defvar *derived-verify-cache* nil
  "NIL (the default): no memoization, identical to this kernel's original
behaviour. Otherwise an EQUAL hash table mapping (ENTRY . BINDS) to the
CHECK-K-PROOF verdict already computed for that pair. Set via
ENABLE-DERIVED-ENTRY-MEMOIZATION / DISABLE-DERIVED-ENTRY-MEMOIZATION.")

(defun verify-derived-instantiation (e binds instantiated ledger log)
  "The recursive re-verification step shared by TRY-DERIVED-ENTRY and
TRY-DEDUCTION-ENTRY: re-checks INSTANTIATED (E's own stored proof, with
schema bindings BINDS already substituted throughout) against entries
strictly before E. Memoized on (E . BINDS) whenever *DERIVED-VERIFY-
CACHE* is non-NIL; see the section header for why that's sound."
  (if *derived-verify-cache*
      (let ((key (cons e binds)))
        (multiple-value-bind (cached found) (gethash key *derived-verify-cache*)
          (if found
              cached
              (setf (gethash key *derived-verify-cache*)
                    (check-k-proof instantiated (entries-upto (entry-k e) ledger) log)))))
      (check-k-proof instantiated (entries-upto (entry-k e) ledger) log)))

(defun enable-derived-entry-memoization ()
  "Turns on (E . BINDS) memoization (see above) for the rest of this
image, or until DISABLE-DERIVED-ENTRY-MEMOIZATION is called. Starts from
an empty cache."
  (setf *derived-verify-cache* (make-hash-table :test #'equal)))

(defun disable-derived-entry-memoization ()
  "Reverts to this kernel's original always-re-verify behaviour."
  (setf *derived-verify-cache* nil))

(defun reset-derived-entry-memoization ()
  "Clears accumulated cache entries without disabling memoization (a
no-op if memoization is currently off)."
  (when *derived-verify-cache*
    (setf *derived-verify-cache* (make-hash-table :test #'equal))))

(defun try-derived-entry (e cited line proven-alist ledger &optional (log (silent-log)))
  "Try exactly ONE candidate DERIVED entry E as the justification for
LINE. Returns T iff E's schema hypotheses match the CITED formulas, its
schema conclusion matches LINE's own formula, and the fully-instantiated
proof re-verifies via CHECK-K-PROOF. Failure here means only \"this
particular entry doesn't work\", not \"no entry works\" -- see
CHECK-K-DERIVED-LINE, which tries every candidate in turn.

LEDGER is threaded through exactly as received. CHECK-K-DERIVED-LINE is
sometimes called with a LEDGER already restricted via ENTRIES-UPTO
(recursively re-verifying a cited entry's own stored proof, so it can
only see entries strictly before that entry's own K); using an
unrestricted ledger here would let a proof reach entries admitted AFTER
the one being re-checked. LOG is passed straight through into the
recursive CHECK-K-PROOF call, so a trace request follows the full
expansion into E's own stored proof too."
  (declare (ignorable log))
  (destructuring-bind (name raw-proof) (entry-payload e)
    (declare (ignore name))
    (let* ((schema-hyps (proof-hypotheses raw-proof))
           (schema-concl (proof-conclusion raw-proof)))
      (and (= (length schema-hyps) (length cited))
           (let ((b1 (match-schema-hyps-against-cited schema-hyps cited proven-alist ledger nil)))
             (and (not (match-fail-p b1))
                  (let ((b2 (match-schema-atoms schema-concl (k-line-formula line) ledger b1)))
                    (and (not (match-fail-p b2))
                         (let ((instantiated (mapcar (lambda (raw)
                                                        (destructuring-bind (num formula role by) raw
                                                          (list num (instantiate-schema-atoms formula b2) role by)))
                                                      raw-proof)))
                           (verify-derived-instantiation e b2 instantiated ledger log))))))))))

(defun try-deduction-entry (e cited line proven-alist ledger &optional (log (silent-log)))
  "Try a single :TH-DED-kind ledger ENTRY (admitted by
CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT, Section 11.5) as the justification
for LINE. A TH-DED entry's payload is (NAME HYP-FORMULA RAW-PROOF), not
(NAME RAW-PROOF).

CORRECTNESS NOTE (this is the one point where an earlier version of this
function was WRONG, caught before it was ever relied on): HYP-FORMULA is
only the ONE hypothesis the Deduction Theorem discharged into the
conclusion (.to HYP-FORMULA PHI) -- RAW-PROOF may still have OTHER open
hypotheses (Gamma) that were never discharged at all. The Deduction
Theorem gives Gamma |- H -> PHI, NOT |- H -> PHI outright; treating Gamma
as vanished (as an earlier draft of this function did) would let a proof
of, say, A, (.to A B) |- B get cited as the unconditional \"theorem\"
(.to (.to A B) B) -- which is not a tautology (false under A=false,
B=false). So Gamma's formulas remain genuine required premises here,
matched against CITED exactly the way TRY-DERIVED-ENTRY matches an
ordinary entry's schema-hypotheses (via the shared
MATCH-SCHEMA-HYPS-AGAINST-CITED). Only HYP-FORMULA itself -- filtered out
of RAW-PROOF's own hypothesis list below -- is exempt from citation,
because it alone has been folded into the object-level implication.

Once Gamma is matched and the schema conclusion (.to HYP-FORMULA PHI) is
matched against LINE's own formula, RAW-PROOF -- including HYP-FORMULA's
own internal :HYP line -- is instantiated and independently re-verified
via CHECK-K-PROOF from a fresh empty OPEN-HYPS, exactly as for any other
DERIVED entry's stored proof."
  (destructuring-bind (name hyp-formula raw-proof) (entry-payload e)
    (declare (ignore name))
    (let ((gamma (remove hyp-formula (proof-hypotheses raw-proof) :test #'equal)))
      (and (= (length gamma) (length cited))
           (let ((b1 (match-schema-hyps-against-cited gamma cited proven-alist ledger nil)))
             (and (not (match-fail-p b1))
                  (let* ((schema-concl (list '.to hyp-formula (proof-conclusion raw-proof)))
                         (b2 (match-schema-atoms schema-concl (k-line-formula line) ledger b1)))
                    (and (not (match-fail-p b2))
                         (let ((instantiated (mapcar (lambda (raw)
                                                        (destructuring-bind (num formula role by) raw
                                                          (list num (instantiate-schema-atoms formula b2) role by)))
                                                      raw-proof)))
                           (verify-derived-instantiation e b2 instantiated ledger log))))))))))

(defun check-k-derived-line (line proven-alist ledger &optional (log (silent-log)))
  "ROLE is :ITH, :TH, :DEF-ABBREV, or :TH-DED: BY = (rule-name .
cited-numbering...). Look up EVERY DERIVED entry named RULE-NAME (ITH,
TH, DEF-ABBREV, and TH-DED all share one name-citation syntax) and try
each in turn, accepting on the first that fully checks out. An ITH/TH/
DEF-ABBREV candidate goes through TRY-DERIVED-ENTRY (schema hypotheses
matched against the cited formulas AND schema conclusion matched against
LINE's own formula, then the fully-instantiated proof re-verified); a
TH-DED candidate goes through TRY-DEDUCTION-ENTRY instead, whose required
premises are the stored proof's OTHER open hypotheses (everything except
the one formula already discharged into the conclusion's antecedent) --
see its own docstring for why that distinction matters. Neither ever
trusts the schema/pattern match by itself; both bottom out in a real
CHECK-K-PROOF re-verification.

Trying every candidate (rather than stopping at the first NAME match)
matters once more than one entry can share a name: CHECK-AND-EXTEND
refuses to admit a genuinely colliding name, but a stale or
adversarially-constructed ledger could still contain duplicates, and
CHECK-K-AXIOM-LINE/CHECK-K-IR-LINE already backtrack across same-named
axiom/irule entries the same way.

Candidates come from LEDGER's BY-DERIVED-NAME index -- an O(log n)
lookup of the one bucket already keyed by RULE-NAME, honoring LEDGER's
BOUND -- rather than a scan of every entry in the ledger regardless of
kind or name."
  (destructuring-bind (rule-name . cited) (k-line-by line)
    (let ((candidates (treap-values-below (alist-get (ledger-by-derived-name ledger) rule-name)
                                           (ledger-bound ledger))))
      (some (lambda (e)
              (if (eq (entry-kind e) 'th-ded)
                  (try-deduction-entry e cited line proven-alist ledger log)
                  (try-derived-entry e cited line proven-alist ledger log)))
            candidates))))

(defun derived-rule-name-taken-p (name ledger)
  "T iff NAME already labels some ITH/TH/DEF-ABBREV/TH-DED entry. These
share one name-citation syntax (a :ITH/:TH/:DEF-ABBREV/:TH-DED line's BY
is just (name . args), with no kind tag of its own to disambiguate), so
letting
a new entry silently reuse an existing name would make
CHECK-K-DERIVED-LINE's candidate search ambiguous and let a later,
possibly weaker or unrelated proof shadow an earlier one under the same
citable name. Checked by CHECK-AND-EXTEND and CHECK-AND-EXTEND-ABBREV
before admitting anything. An O(log n) BY-DERIVED-NAME lookup, like
CHECK-K-DERIVED-LINE above."
  (not (null (treap-values-below (alist-get (ledger-by-derived-name ledger) name) (ledger-bound ledger)))))

(defun check-and-extend (ledger kind name raw-proof &optional (log (silent-log)))
  "The general (non-bootstrap) growth path for ITH/TH entries. RAW-PROOF's
conclusion (last line) becomes the new entry's payload; the whole raw
proof is stored so the entry is fully auditable. The proof is checked
against LEDGER AS IT STANDS RIGHT NOW (all strictly earlier entries) --
nothing in RAW-PROOF may depend on the entry it is trying to create.
Returns the NEW ledger.

KIND must be ITH or TH: CHECK-AND-EXTEND always stores its payload as
(NAME RAW-PROOF), which is the shape CHECK-K-DERIVED-LINE expects for
ITH/TH/DEF-ABBREV entries -- calling it with, say, KIND='AXIOM would
silently create a malformed axiom entry (axioms need a (NAME CONDITIONS
FORM) payload) that would later crash CHECK-K-AXIOM-LINE's
DESTRUCTURING-BIND the first time it was scanned. DEF-ABBREV entries
have their own dedicated admission path, CHECK-AND-EXTEND-ABBREV
(definitions carry an extra DEFINIENS argument to cross-check), so it is
excluded here too -- use that instead for abbreviations.

LOG, when non-silent, traces CHECK-K-PROOF's line-by-line verdicts (see
LOG-LINE-RESULT) as it re-verifies RAW-PROOF, plus one final line for
this admission's own overall accept/reject (LOG-ADMISSION-RESULT)."
  (unless (member kind '(ith th) :test #'eq)
    (error "CHECK-AND-EXTEND: KIND must be ITH or TH, got ~S. (Axioms/irules ~
            need their own (NAME CONDITIONS FORM) payload shape and are ~
            admitted only via ADMIT-PRIMITIVE at bootstrap; abbreviations ~
            go through CHECK-AND-EXTEND-ABBREV.)" kind))
  (when (derived-rule-name-taken-p name ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND: the name ~S is already used by an existing ~
            ITH/TH/DEF-ABBREV entry -- refused to avoid an ambiguous or ~
            shadowing citation." name))
  ;; LEDGER here is already exactly "every entry strictly earlier than
  ;; the one about to be created" -- it doesn't contain that entry yet --
  ;; so passing it straight through is ENTRIES-UPTO's restriction for
  ;; free, without even the O(1) cost of constructing a bounded view.
  (unless (check-k-proof raw-proof ledger log)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND: proof of ~S rejected." name))
  (log-admission-result log name t)
  (ledger-append ledger kind (list name raw-proof) (list :derived raw-proof)))

(defun check-and-extend-abbrev (ledger name definiens raw-proof &optional (log (silent-log)))
  "Abbreviation/definition admission: this is ALSO a ledger object
requiring a proof, unlike Goedel's own meta-level definitions. DEFINIENS
is the schema NAME is meant to stand for (written using atomic-wff-symbol
schema atoms, e.g. A, exactly like an ITH/TH schema); RAW-PROOF must be a
genuine K-proof whose OWN CONCLUSION (last line) matches DEFINIENS via
MATCH-SCHEMA-ATOMS, checked in BOTH directions.

Requiring RAW-PROOF's actual conclusion to match DEFINIENS is what makes
this sound: DEF-ABBREV lines are checked via CHECK-K-DERIVED-LINE against
the STORED PROOF's own real conclusion, never against the caller's
DEFINIENS claim directly, so a mismatched DEFINIENS cannot be used to
assert anything false. But a ONE-DIRECTIONAL schema match alone would
still leave a labeling-honesty gap: a bare, unconstrained schema atom
like DEFINIENS = 'A matches ANY conclusion at all, so an entry could be
admitted whose recorded DEFINIENS bears no real relationship to what it
actually proves. Matching in the OTHER direction too (conclusion-as-
pattern against definiens-as-expr) closes this: a bare atom on either
side only matches a compound expression as a STRUCTURED schema, so
matching the actual conclusion's real structure against a too-vague
DEFINIENS fails wherever DEFINIENS omits structure the conclusion
actually has.

LOG is as in CHECK-AND-EXTEND, above."
  (when (derived-rule-name-taken-p name ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-ABBREV: the name ~S is already used by an ~
            existing ITH/TH/DEF-ABBREV entry -- refused to avoid an ~
            ambiguous or shadowing citation." name))
  (unless (judgement? 'wff? definiens ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-ABBREV: definiens ~S is not a well-formed formula." definiens))
  ;; As in CHECK-AND-EXTEND: LEDGER is already the right restriction.
  (unless (check-k-proof raw-proof ledger log)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-ABBREV: proof for ~S rejected." name))
  (let ((concl (proof-conclusion raw-proof)))
    (when (or (match-fail-p (match-schema-atoms definiens concl ledger nil))
              (match-fail-p (match-schema-atoms concl definiens ledger nil)))
      (log-admission-result log name nil)
      (error "CHECK-AND-EXTEND-ABBREV: the supplied proof's conclusion (~S) ~
              does not match the claimed definiens ~S for ~S -- refused ~
              (an abbreviation's proof must actually establish its own ~
              definiens, as the SAME schema in both directions, or it ~
              would let ~S be cited under a misleading description of ~
              what it really proves)."
             concl definiens name name)))
  (log-admission-result log name t)
  (ledger-append ledger 'def-abbrev (list name raw-proof) (list :derived raw-proof)))

;;; ---------------------------------------------------------------------
;;; 7. Bootstrap: populate the primitive Hilbert system
;;; ---------------------------------------------------------------------
;;;
;;; wff?/var?/term? formation, MP, Gen (with its generalization
;;; restriction), and axioms II.1-III.2. Declared atomic symbols/variables
;;; are also admitted as primitive ledger entries, so Sigma is a real
;;; projection from day one rather than a hardcoded list.
;;;
;;; :ATOMIC-SYMBOLS/:VARIABLES below are only the SEED vocabulary -- how
;;; much of Sigma exists the moment the kernel is born. They are NOT the
;;; only way Sigma can ever grow: DECLARE-ATOMIC-WFF-SYMBOL and
;;; DECLARE-VARIABLE-SYMBOL (section 2) remain usable for the whole life
;;; of the kernel, letting new symbols be added one at a time, on demand,
;;; long after bootstrap has closed.

(defun bootstrap-kernel (&key (atomic-symbols '(A B C D E F G H)) (variables '(v0 v1 v2 v3 v4 v5))
                               (arithmetic nil))
  "Returns the freshly-built ledger: a pure function whose result IS the
kernel -- the caller (RUN-SELF-TESTS, or anyone else) captures it and
threads it onward into every later check or growth call.

ARITHMETIC, when true, additionally admits the Peano vocabulary (ZERO, S,
+, *) and axioms (P1-P7, Section 7.5) on top of the always-present
equality axioms (IV.1-IV.2). Default NIL, so every existing caller (every
self-test, and both HILBERT-LIBRARY modules) gets EXACTLY the same
kernel as before this parameter existed."
  (labels ((admit (ledger kind payload)
             "The ONLY place in the whole file that can create a
:PRIMITIVE-origin entry -- a LABELS binding local to BOOTSTRAP-KERNEL's
own call, so nothing outside this function's own body can ever reach it.
Returns the new ledger, like LEDGER-APPEND."
             (ledger-append ledger kind payload (list :primitive)))
           (admit-each (ledger kind syms)
             (if (null syms)
                 ledger
                 (admit-each (admit ledger kind (car syms)) kind (cdr syms))))
           (bootstrap-formation-rules (ledger)
             "TERM?/WFF? formation rules: variables are terms, and the
connectives/binders/relation that build WFFs out of smaller WFFs, terms
and variables.

NOTE: there is deliberately no generic \"(wff? ?A)\"/\"(var? ?x)\"
primitive rule with no side condition here -- such a rule would match
ANY single argument, so it would accept even an undeclared symbol as a
wff/var. Bare declared symbols are instead recognized directly against
Sigma via ATOMIC-WFF-SYMBOL-P/VARIABLE-P in the JUDGEMENT-BIND override
in section 8, below."
             (let* ((ledger (admit ledger 'term? (list 'var-term '((var? ?x)) '(term? ?x))))
                    ;; (.iota x A): "the x such that A" -- a TERM-producing
                    ;; binder (see Section 19). Its formation rule is
                    ;; exactly as inert on its own as .EXISTS's own
                    ;; formation rule below was before III.3/IOTA existed:
                    ;; a bare (var? ?x)(wff? ?A) => term? (.iota ?x ?A)
                    ;; rule, with all of the actual meaning supplied by
                    ;; IOTA (Section 7's BOOTSTRAP-INFERENCE-RULES) and by
                    ;; BINDER-HEADS already listing .IOTA so free-variable/
                    ;; substitution/capture-avoidance machinery treats it
                    ;; correctly wherever it occurs, including nested
                    ;; inside an ordinary WFF as an argument term.
                    (ledger (admit ledger 'term? (list 'iota-term '((var? ?x) (wff? ?A)) '(term? (.iota ?x ?A)))))
                    (ledger (admit ledger 'wff? (list 'wff_to? '((wff? ?A) (wff? ?B)) '(wff? (.to ?A ?B)))))
                    (ledger (admit ledger 'wff? (list 'wff_neg? '((wff? ?A)) '(wff? (.neg ?A)))))
                    (ledger (admit ledger 'wff? (list 'wff_forall? '((var? ?x) (wff? ?A)) '(wff? (.forall ?x ?A)))))
                    ;; .EXISTS's SYNTAX: (var? x)(wff? A) => wff? (.exists x A).
                    ;; *BINDER-HEADS* already lists .EXISTS, so FREE-VARS-WFF/
                    ;; SUBSTITUTE-WFF/COUNT-BOUND-OCCURRENCES already treat it as a
                    ;; genuine binder. Unlike when this comment was first written,
                    ;; .EXISTS now DOES have a piece of real proof theory on top of
                    ;; this formation rule -- III.3, existential generalization
                    ;; (Section 7's BOOTSTRAP-AXIOMS) -- though still no full
                    ;; existential ELIMINATION/instantiation rule; see Section 19's
                    ;; own header for exactly what that still leaves out.
                    (ledger (admit ledger 'wff? (list 'wff_exists? '((var? ?x) (wff? ?A)) '(wff? (.exists ?x ?A)))))
                    ;; A minimal atomic relation on terms, so that a bare variable can
                    ;; legitimately occur FREE inside a genuine well-formed formula
                    ;; (without some relation symbol, a variable standing alone is a
                    ;; TERM, not a WFF).
                    (ledger (admit ledger 'wff? (list 'wff_eq? '((term? ?s) (term? ?t)) '(wff? (.eq ?s ?t))))))
               ledger))
           (bootstrap-inference-rules (ledger)
             "MP and Gen (WITH the generalization restriction), plus IOTA
(definite-description elimination -- Section 19) and EXISTS-ELIM
(genuine existential elimination -- Section 21).
FORM shape: (PREMISE-PATTERNS EXTRA-PARAM-PATTERNS :=> CONCLUSION-PATTERN)."
             (let* ((ledger (admit ledger 'irule (list 'MP '((wff? ?A) (wff? ?B))
                                                        '(((.to ?A ?B) ?A) nil :=> ?B))))
                    (ledger (admit ledger 'irule (list 'Gen '((var? ?x) (wff? ?A) (@not-free-in-dependencies? ?x))
                                                        '((?A) (?x) :=> (.forall ?x ?A)))))
                    ;; IOTA: from (a) EXISTENCE, (.exists ?x ?A), and (b)
                    ;; UNIQUENESS, (.forall ?y (.forall ?z (.to (@subst ?x
                    ;; ?y ?A) (.to (@subst ?x ?z ?A) (.eq ?y ?z))))) --
                    ;; "any two things satisfying A are equal" -- BOTH
                    ;; cited as already-proven premise lines (however they
                    ;; were established; IOTA does not care), conclude
                    ;; A[(.iota ?x ?A)/?x]: the iota-term itself satisfies
                    ;; A. Note this is an IRULE, not an AXIOM, precisely
                    ;; BECAUSE it needs premises cited from the current
                    ;; proof (the way MP/Gen do) rather than holding as a
                    ;; bare schema on its own -- existence and uniqueness
                    ;; are facts about a PARTICULAR A, not universal
                    ;; truths. ?Y and ?Z are bound purely from matching the
                    ;; UNIQUENESS premise's own outer .FORALL structure
                    ;; (MATCH-TEMPLATE processes a pattern's CAR before its
                    ;; CDR, left to right, exactly as III.1's (@subst ?x ?t
                    ;; ?A) conclusion pattern already relies on ?x/?A being
                    ;; bound before it is reached) -- ?X and ?A are already
                    ;; ground by the time the UNIQUENESS premise is
                    ;; matched, since EXISTENCE is listed first and
                    ;; MATCH-SCHEMA-HYPS-AGAINST-CITED threads bindings
                    ;; across premises strictly in the order given.
                    (ledger (admit ledger 'irule
                                   (list 'IOTA
                                         '((var? ?x) (wff? ?A) (@subst-ok? ?x (.iota ?x ?A) ?A))
                                         '(((.exists ?x ?A)
                                            (.forall ?y (.forall ?z (.to (@subst ?x ?y ?A)
                                                                         (.to (@subst ?x ?z ?A) (.eq ?y ?z))))))
                                           nil :=>
                                           (@subst ?x (.iota ?x ?A) ?A)))))
                    ;; EXISTS-ELIM (Section 21): the genuine existential
                    ;; ELIMINATION rule III.3 always lacked. From (a)
                    ;; EXISTENCE, (.exists ?x ?A), and (b) a proof that
                    ;; some already-established formula ?Ac (which the
                    ;; side conditions verify really is A with x
                    ;; instantiated to a FRESH witness variable ?w)
                    ;; implies C -- (.to ?Ac ?C) -- conclude C outright,
                    ;; discharging the witness. This is the standard
                    ;; Hilbert-style "existential instantiation" rule
                    ;; (Mendelson's Rule C, or natural deduction's
                    ;; exists-elim flattened into one step since the
                    ;; DEDUCTION THEOREM already lets a caller build
                    ;; "A[w/x] -> C" from a genuine sub-proof assuming
                    ;; A[w/x] -- see CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT).
                    ;; (Named ?w, not ?c: a pattern variable ?c and ?C are
                    ;; THE SAME SYMBOL once read -- Common Lisp's default
                    ;; reader case-normalizes to upper case -- so ?w keeps
                    ;; the witness variable and the conclusion schema
                    ;; variable properly distinct.)
                    ;;
                    ;; UNLIKE IOTA/III.1's own embedded (@subst ...)
                    ;; conclusion patterns, this rule cannot write
                    ;; (@subst ?x ?w ?A) directly inside its SECOND PREMISE
                    ;; pattern: PREMISE-PATTERNS are all matched BEFORE
                    ;; EXTRA-PARAM-PATTERNS (see TRY-IR-ENTRY), so ?w --
                    ;; supplied only as an extra citation argument, the
                    ;; way GEN's own ?x is -- is not yet bound at the
                    ;; point the second premise would need to evaluate
                    ;; @subst. The fix: match ?Ac PURELY STRUCTURALLY
                    ;; (no embedded meta-constructor at all) against
                    ;; whatever concrete antecedent the citing proof
                    ;; supplies, then verify AS A SIDE CONDITION -- once
                    ;; ?x/?A/?w are all ground -- that ?Ac genuinely does
                    ;; equal A[w/x], via the new @substitutes? meta-
                    ;; predicate (a boolean CHECK, unlike @subst itself,
                    ;; which is a meta-CONSTRUCTOR evaluated during
                    ;; matching).
                    ;;
                    ;; Freshness (?w must be a genuinely NEW name, standing
                    ;; for "whichever thing A holds of", never confused
                    ;; with anything already in play) is exactly Gen's own
                    ;; @not-free-in-dependencies? restriction, PLUS two
                    ;; more: ?w must not leak into the CONCLUSION ?C (or
                    ;; the "witness" would illegitimately survive past the
                    ;; elimination step) and must not already occur free
                    ;; in ?A itself (or "instantiating x to w" could
                    ;; collide with an unrelated, already-meaningful
                    ;; occurrence of w inside A). @subst-ok? additionally
                    ;; guards the substitution itself against capture by
                    ;; some OTHER binder inside A, exactly as everywhere
                    ;; else @subst is used.
                    (ledger (admit ledger 'irule
                                   (list 'EXISTS-ELIM
                                         '((var? ?x) (var? ?w) (wff? ?A) (wff? ?Ac) (wff? ?C)
                                           (@substitutes? ?x ?w ?A ?Ac)
                                           (@subst-ok? ?x ?w ?A)
                                           (@not-free-in? ?w ?A)
                                           (@not-free-in? ?w ?C)
                                           (@not-free-in-dependencies? ?w))
                                         '(((.exists ?x ?A) (.to ?Ac ?C))
                                           (?w) :=>
                                           ?C)))))
               ledger))
           (bootstrap-axioms (ledger)
             "Axioms II.1-II.3 (propositional) and III.1-III.2 (predicate).
FORM shape: (EXTRA-PARAM-PATTERNS CONCLUSION-PATTERN) -- see
CHECK-K-AXIOM-LINE. Only III.1 actually takes an extra parameter (the
substituted term); the rest take none.

II.1-II.3 are the standard K/S/contraposition basis for classical
implicational logic (this replaces an earlier K/K/B-composition basis
that, as a combinator system, could not even derive the identity schema
A -> A: {B, K} alone are not combinatorially complete -- neither is
{B, C, K} (BCK logic is contraction-free and still lacks the sharing
S provides), so the discharge/MP cases of any Deduction-Theorem-style
meta-rule were unimplementable underneath it. II.2 (S) restores that:
     II.1  A -> (B -> A)                                     [K]
     II.2  (A -> (B -> C)) -> ((A -> B) -> (A -> C))          [S]
     II.3  (.neg B -> .neg A) -> (A -> B)                     [contraposition]
II.3 is the first axiom to mention .NEG; see BOOTSTRAP-FORMATION-RULES
above for its (otherwise inert) formation rule.

{II.1, II.2, II.3} is exactly Lukasiewicz's classical 3-axiom basis
(rename A:=q, B:=p in II.3 and it reads (.neg p -> .neg q) -> (q -> p),
his A3 verbatim), which he proved POST-COMPLETE for classical
propositional logic: every classical tautology -- including case-split,
double-negation elimination, and Peirce's law -- IS already a theorem
of {II.1,II.2,II.3,MP} alone, with no further axiom needed in
principle. In that sense II.4 below is REDUNDANT, unlike IV.3/IV.4 or
P8-P10 above/below, which were proven IMPOSSIBLE to derive from what
preceded them. The distinction matters and is recorded here rather than
glossed over: II.4 could be derived, but its shortest known derivations
from {II.1,II.2,II.3} alone run to dozens of raw MP/axiom steps (this
is a well-documented curiosity of Lukasiewicz-style bases -- automated
provers have spent real effort just finding short proofs of facts like
not-not-p -> p from them), and a bounded forward-chaining search tried
here during development did not converge on one in practical time. Ad-
mitting it directly, clearly labelled as classically-redundant-but-not-
reconstructed, is the honest and practical choice: it keeps kernel
proofs usable for actual work (Kalmar's completeness construction,
below) without either pretending the shortcut doesn't exist or forcing
a many-dozen-line combinator proof into every citing theorem's history.
     II.4  (A -> C) -> ((.neg A -> C) -> C)                   [case-split]"
             (let* ((ledger (admit ledger 'axiom (list 'II.1 '((wff? ?A) (wff? ?B))
                                                        '(nil (.to ?A (.to ?B ?A))))))
                    (ledger (admit ledger 'axiom (list 'II.2 '((wff? ?A) (wff? ?B) (wff? ?C))
                                                        '(nil (.to (.to ?A (.to ?B ?C)) (.to (.to ?A ?B) (.to ?A ?C)))))))
                    (ledger (admit ledger 'axiom (list 'II.3 '((wff? ?A) (wff? ?B))
                                                        '(nil (.to (.to (.neg ?B) (.neg ?A)) (.to ?A ?B))))))
                    (ledger (admit ledger 'axiom (list 'II.4 '((wff? ?A) (wff? ?C))
                                                        '(nil (.to (.to ?A ?C) (.to (.to (.neg ?A) ?C) ?C))))))
                    ;; III.1: universal instantiation, forall x A -> A[t/x], for an
                    ;; ARBITRARY term t supplied as the citing proof's extra argument
                    ;; (e.g. (III.1 v2)). (@subst ?x ?t ?A) is evaluated by
                    ;; MATCH-TEMPLATE once ?x and ?A are bound (from matching
                    ;; (.forall ?x ?A) against the antecedent, which happens first,
                    ;; left-to-right) and ?t is bound (seeded from EXTRA-ARGS before
                    ;; CONCLUSION-PATTERN is even matched) -- never by unification.
                    ;; @subst-ok? still guards against capturing t's free variables
                    ;; under a binder inside A.
                    (ledger (admit ledger 'axiom (list 'III.1 '((var? ?x) (wff? ?A) (term? ?t) (@subst-ok? ?x ?t ?A))
                                                        '((?t) (.to (.forall ?x ?A) (@subst ?x ?t ?A))))))
                    (ledger (admit ledger 'axiom (list 'III.2 '((var? ?x) (wff? ?A) (wff? ?B) (@not-free-in? ?x ?A))
                                                        '(nil (.to (.forall ?x (.to ?A ?B)) (.to ?A (.forall ?x ?B)))))))
                    ;; III.3: existential generalization, A[t/x] -> exists x. A --
                    ;; the direct dual of III.1 (universal INSTANTIATION), but for
                    ;; introducing .EXISTS rather than eliminating .FORALL, and
                    ;; UNCONDITIONAL (no Gen-style freshness restriction: unlike
                    ;; universally generalizing an arbitrary A into forall x. A,
                    ;; concluding "something satisfies A" from "THIS PARTICULAR
                    ;; witness t satisfies A" is always safe). Before this axiom,
                    ;; .EXISTS had a formation rule but no way to ever actually PROVE
                    ;; a .EXISTS-headed formula at all -- see BOOTSTRAP-FORMATION-
                    ;; RULES' updated commentary. Still not a full existential
                    ;; ELIMINATION/instantiation rule (Section 19's own header notes
                    ;; exactly what that gap still leaves out) -- but it, together
                    ;; with IOTA below, is exactly what makes IOTA practically usable:
                    ;; IOTA's EXISTENCE premise needs to come from SOMEWHERE, and this
                    ;; is that somewhere.
                    ;;
                    ;; UNLIKE III.1, ?X and ?A cannot be left to be bound
                    ;; structurally from the CONCLUSION-PATTERN match: here the
                    ;; binder (.exists ?x ?A) sits in the CONSEQUENT, while the
                    ;; META-CONSTRUCTOR (@subst ?x ?t ?A) sits in the ANTECEDENT --
                    ;; and MATCH-TEMPLATE processes a (.to ANTECEDENT CONSEQUENT)
                    ;; pattern's antecedent strictly before its consequent, left to
                    ;; right. So by the time @subst is reached, ?x/?A would still be
                    ;; unbound and matching would fail outright (never back-solved).
                    ;; The fix: like GEN's own variable argument, ?X and ?A are
                    ;; supplied directly as extra citation arguments -- e.g.
                    ;; (III.3 v0 (.eq v0 v1) v1) -- seeding BINDS before
                    ;; CONCLUSION-PATTERN is matched at all, exactly as EXTRA-ARGS
                    ;; already do for ?T in both this axiom and III.1.
                    (ledger (admit ledger 'axiom (list 'III.3 '((var? ?x) (wff? ?A) (term? ?t) (@subst-ok? ?x ?t ?A))
                                                        '((?x ?A ?t) (.to (@subst ?x ?t ?A) (.exists ?x ?A))))))
                    ;; IV.1-IV.4: first-order equality. .EQ has existed as a
                    ;; WFF-formation rule since BOOTSTRAP-FORMATION-RULES
                    ;; (wff_eq?), but until now it was semantically INERT --
                    ;; no axiom ever said what (.eq ?s ?t) actually MEANS.
                    ;;   IV.1  t = t                          [reflexivity]
                    ;;   IV.2  x = t -> (A -> A[t/x])          [Leibniz substitution]
                    ;;   IV.3  s = t -> t = s                  [symmetry]
                    ;;   IV.4  s = t -> (t = u -> s = u)        [transitivity]
                    ;; IV.2 reuses EXACTLY the same @subst/@subst-ok?
                    ;; machinery III.1 already established (capture-avoidance
                    ;; included, for free) -- the only difference from III.1's
                    ;; own conclusion pattern is that here the antecedent is
                    ;; (.eq ?x ?t) rather than (.forall ?x ?A), and ?t is an
                    ;; ordinary schema TERM here (not an axiom extra-param),
                    ;; since (unlike III.1) there is a WFF, not a binder, to
                    ;; bind ?x and ?A structurally before @subst is evaluated.
                    ;;
                    ;; IV.3/IV.4 are ADMITTED DIRECTLY rather than derived
                    ;; from IV.1+IV.2 -- and this is a deliberate, checked
                    ;; decision, not laziness. SUBSTITUTE-WFF replaces EVERY
                    ;; free occurrence of ?x throughout ?A uniformly, so
                    ;; FV(@subst ?x ?t ?A) subset-of (FV(?A) \ {?x}) union
                    ;; FV(?t): ?x can NEVER survive into the result of an
                    ;; IV.2 application. Symmetry's conclusion (t = s)
                    ;; necessarily still mentions s -- so if ?x is bound to
                    ;; s (forced, to match a hypothesis s=t via MP), s can
                    ;; never appear in the output of THAT step, for ANY
                    ;; choice of ?A: proving t=s from s=t via IV.2 is not
                    ;; merely hard here, it is FORMALLY UNREACHABLE this way
                    ;; (confirmed by hand and by attempted construction
                    ;; before writing this comment). The usual textbook
                    ;; trick instead substitutes into ONE of several
                    ;; DESIGNATED occurrences of a multi-argument predicate
                    ;; (Mendelson's congruence-per-symbol axioms), which is
                    ;; a genuinely different, finer-grained schema than
                    ;; SUBSTITUTE-WFF's "replace every free occurrence"
                    ;; semantics -- implementing that generally was judged
                    ;; not worth the complexity here, so symmetry and
                    ;; transitivity are simply their own primitive axioms.
                    ;; IV.2 remains useful in its own right wherever ?A has
                    ;; only ONE free occurrence of ?x to begin with (no
                    ;; occurrence-selection issue arises), which is exactly
                    ;; how axiom P3 (induction, Section 7.5) uses @subst.
                    (ledger (admit ledger 'axiom (list 'IV.1 '((term? ?t))
                                                        '(nil (.eq ?t ?t)))))
                    (ledger (admit ledger 'axiom (list 'IV.2 '((var? ?x) (wff? ?A) (term? ?t) (@subst-ok? ?x ?t ?A))
                                                        '(nil (.to (.eq ?x ?t) (.to ?A (@subst ?x ?t ?A)))))))
                    (ledger (admit ledger 'axiom (list 'IV.3 '((term? ?s) (term? ?t))
                                                        '(nil (.to (.eq ?s ?t) (.eq ?t ?s))))))
                    (ledger (admit ledger 'axiom (list 'IV.4 '((term? ?s) (term? ?t) (term? ?u))
                                                        '(nil (.to (.eq ?s ?t) (.to (.eq ?t ?u) (.eq ?s ?u))))))))
               ledger))
           (bootstrap-peano-vocabulary (ledger)
             "Term-formation rules for elementary arithmetic's four fixed
function symbols: ZERO (arity 0), S (successor, arity 1), + and * (arity
2). Only admitted when BOOTSTRAP-KERNEL is called with :ARITHMETIC T --
these are one specific theory's vocabulary, not part of the generic
kernel, so every existing self-test/library file that never asks for
:ARITHMETIC sees an unchanged TERM? rule set (just VAR-TERM, as before)."
             (let* ((ledger (admit ledger 'term? (list 'zero-term nil '(term? zero))))
                    (ledger (admit ledger 'term? (list 'succ-term '((term? ?x)) '(term? (S ?x)))))
                    (ledger (admit ledger 'term? (list 'plus-term '((term? ?x) (term? ?y)) '(term? (+ ?x ?y)))))
                    (ledger (admit ledger 'term? (list 'times-term '((term? ?x) (term? ?y)) '(term? (* ?x ?y))))))
               ledger))
           (bootstrap-peano-axioms (ledger)
             "The Peano axioms proper (P1-P2: successor's basic properties;
P3: induction; P4-P7: the recursive defining equations for + and *, which
in this system -- unlike a system with recursive DEFINITIONS -- must be
stated as axioms, since there is no primitive recursion mechanism other
than proof; P8-P10: congruence of S/+/* under equality).

P8-P10 exist for the SAME reason IV.3/IV.4 (symmetry/transitivity) are
their own primitive axioms rather than IV.2 (Leibniz) instances: IV.2
cannot hold one occurrence of a variable fixed while changing another
occurrence of the SAME variable elsewhere (SUBSTITUTE-WFF replaces every
free occurrence uniformly), and congruence -- \"x=y implies S(x)=S(y)\" --
is exactly that shape (x appears on both the hypothesis and, unchanged in
ROLE but needing its OWN copy, the conclusion). Stated directly as axioms
instead, matching Mendelson's own per-function-symbol congruence scheme.

P3 (induction) is stated CURRIED -- (A[0/x] -> ((forall x (A -> A[Sx/x]))
-> (forall x A))) -- rather than with a conjunction of the base case and
step case, because this kernel has never had a .AND connective (see
BOOTSTRAP-FORMATION-RULES' own commentary on .EXISTS: adding connective
syntax without wiring in more axioms is safe, but here it is simply
unnecessary -- currying an implication is logically equivalent to
conjoining its antecedents and is already expressible with .TO alone).

Unlike III.1 (where ?t is an axiom extra-param because there is no WFF
structure available to bind ?x/?A from first), P3 needs BOTH ?x and ?A
supplied as extra-params: its conclusion pattern's very first component
is (@subst ?x zero ?A), and MATCH-TEMPLATE evaluates a meta-constructor
node only once ALL of its arguments are already ground -- so ?x and ?A
must already be bound before matching even starts, exactly the same
reason III.1 seeds ?t from EXTRA-ARGS rather than leaving it to
structural matching. A citation therefore looks like (P3 v0 (.eq v0 v0)),
supplying the induction variable and the full schema formula explicitly."
             (let* ((ledger (admit ledger 'axiom (list 'P1 '((term? ?x))
                                                        '(nil (.neg (.eq (S ?x) zero))))))
                    (ledger (admit ledger 'axiom (list 'P2 '((term? ?x) (term? ?y))
                                                        '(nil (.to (.eq (S ?x) (S ?y)) (.eq ?x ?y))))))
                    (ledger (admit ledger 'axiom (list 'P3 '((var? ?x) (wff? ?A) (term? zero) (term? (S ?x))
                                                              (@subst-ok? ?x zero ?A) (@subst-ok? ?x (S ?x) ?A))
                                                        '((?x ?A)
                                                          (.to (@subst ?x zero ?A)
                                                               (.to (.forall ?x (.to ?A (@subst ?x (S ?x) ?A)))
                                                                    (.forall ?x ?A)))))))
                    (ledger (admit ledger 'axiom (list 'P4 '((term? ?x))
                                                        '(nil (.eq (+ ?x zero) ?x)))))
                    (ledger (admit ledger 'axiom (list 'P5 '((term? ?x) (term? ?y))
                                                        '(nil (.eq (+ ?x (S ?y)) (S (+ ?x ?y)))))))
                    (ledger (admit ledger 'axiom (list 'P6 '((term? ?x))
                                                        '(nil (.eq (* ?x zero) zero)))))
                    (ledger (admit ledger 'axiom (list 'P7 '((term? ?x) (term? ?y))
                                                        '(nil (.eq (* ?x (S ?y)) (+ (* ?x ?y) ?x))))))
                    (ledger (admit ledger 'axiom (list 'P8 '((term? ?x) (term? ?y))
                                                        '(nil (.to (.eq ?x ?y) (.eq (S ?x) (S ?y)))))))
                    (ledger (admit ledger 'axiom (list 'P9 '((term? ?x1) (term? ?y1) (term? ?x2) (term? ?y2))
                                                        '(nil (.to (.eq ?x1 ?y1)
                                                                   (.to (.eq ?x2 ?y2) (.eq (+ ?x1 ?x2) (+ ?y1 ?y2))))))))
                    (ledger (admit ledger 'axiom (list 'P10 '((term? ?x1) (term? ?y1) (term? ?x2) (term? ?y2))
                                                        '(nil (.to (.eq ?x1 ?y1)
                                                                   (.to (.eq ?x2 ?y2) (.eq (* ?x1 ?x2) (* ?y1 ?y2)))))))))
               ledger)))
    (let* ((ledger (admit-each (empty-ledger) 'atomic-wff-symbol atomic-symbols))
           (ledger (admit-each ledger 'variable-symbol variables))
           (ledger (bootstrap-formation-rules ledger))
           (ledger (bootstrap-inference-rules ledger))
           (ledger (bootstrap-axioms ledger))
           (ledger (if arithmetic (bootstrap-peano-vocabulary ledger) ledger))
           (ledger (if arithmetic (bootstrap-peano-axioms ledger) ledger)))
      ledger)))

;;; ---------------------------------------------------------------------
;;; 8. WFF?/VAR? special-casing for bare declared symbols
;;; ---------------------------------------------------------------------
;;;
;;; A bare atomic-wff or variable symbol (e.g. A, v0) has no internal
;;; structure to pattern-match against a rule's FORM, so JUDGEMENT-BIND's
;;; generic dispatch is extended here to consult Sigma directly for the
;;; base cases of the WFF?/VAR? judgements, as a projection instead of a
;;; hardcoded list.

(let ((orig #'judgement-bind))
  (setf (symbol-function 'judgement-bind)
        (lambda (kind args binds ledger &optional (seen nil) (open-hyps nil))
          (if (and (= (length args) 1) (symbolp (car args))
                   (or (and (eq kind 'wff?) (atomic-wff-symbol-p (car args) ledger))
                       (and (eq kind 'var?) (variable-p (car args) ledger))
                       (and (eq kind 'term?) (variable-p (car args) ledger))))
              (values binds t)
              (funcall orig kind args binds ledger seen open-hyps)))))

;;; ---------------------------------------------------------------------
;;; 9. Self tests
;;; ---------------------------------------------------------------------

(defun expect (label got expected)
  (format t "[~:[FAIL~;pass~]] ~A~%" (eql (not (null got)) (not (null expected))) label))

(defun test-basic-formation (ledger)
  "Basic formation checks; does not grow the ledger."
  (expect "A is a wff" (judgement? 'wff? 'A ledger) t)
  (expect "v0 is a var" (judgement? 'var? 'v0 ledger) t)
  (expect "(.to A B) is a wff" (judgement? 'wff? '(.to A B) ledger) t)
  (expect "(.forall v0 A) is a wff" (judgement? 'wff? '(.forall v0 A) ledger) t)
  (expect "Z is NOT a wff (undeclared)" (judgement? 'wff? 'Z ledger) nil)
  ledger)

(defun test-axiom-and-inference (ledger)
  "Axiom II.1, MP, and Gen (legal and illegal); does not grow the ledger."
  (expect "II.1 instance: (.to A (.to A A))"
          (check-k-proof '((0 (.to A (.to A A)) :axiom (II.1))) ledger) t)
  (expect "MP: A, (.to A B) |- B"
          (check-k-proof '((0 A :hyp nil)
                            (1 (.to A B) :hyp nil)
                            (2 B :ir (MP 1 0)))
                          ledger)
          t)
  (expect "Gen legal: A |- forall v0 A (v0 not free in any open hyp)"
          (check-k-proof '((0 A :hyp nil)
                            (1 (.forall v0 A) :ir (Gen 0 v0)))
                          ledger)
          t)
  (expect "Gen illegal (attack): open hyp (.eq v0 v1) has v0 free -- must reject"
          (check-k-proof '((0 (.eq v0 v1) :hyp nil)
                            (1 (.forall v0 (.eq v0 v1)) :ir (Gen 0 v0)))
                          ledger)
          nil)
  ledger)

(defun test-vacuous-gen-and-bad-ith (ledger)
  "Derives th-gen-vacuous via CHECK-AND-EXTEND and uses it in a later
proof, then defines ith-bad-gen (whose schema alone is legitimate) and
confirms a capturing instantiation of it is rejected on full
re-expansion. Returns the ledger extended with both new entries."
  (let* ((ledger (check-and-extend ledger 'th 'th-gen-vacuous
                                    '((0 A :hyp nil)
                                      (1 (.forall v0 A) :ir (Gen 0 v0))))))
    (expect "Using th-gen-vacuous legally: B |- forall v0 B"
            (check-k-proof '((X B :hyp nil)
                              (Y (.forall v0 B) :th (th-gen-vacuous X)))
                            ledger)
            t)
    (let* ((ledger (handler-case
                        (let ((new-ledger (check-and-extend ledger 'ith 'ith-bad-gen
                                                             '((0 A :hyp nil)
                                                               (1 (.forall v0 A) :ir (Gen 0 v0))))))
                          (format t "[pass] ith-bad-gen defines cleanly (vacuous case is legitimate on its own)~%")
                          new-ledger)
                      (error (e)
                        (format t "[FAIL] ith-bad-gen unexpectedly rejected at definition time: ~A~%" e)
                        ledger))))
      (expect "Attack: instantiate ith-bad-gen with A := (.eq v0 v1) -- must reject"
              (check-k-proof '((X (.eq v0 v1) :hyp nil)
                                (Y (.forall v0 (.eq v0 v1)) :ith (ith-bad-gen X)))
                              ledger)
              nil)
      ledger)))

(defun test-admit-primitive-closed (ledger)
  "ADMIT-PRIMITIVE must be unreachable post-bootstrap."
  (expect "ADMIT-PRIMITIVE is closed post-bootstrap"
          (handler-case (progn (admit-primitive 'atomic-wff-symbol 'SHOULD-FAIL) nil)
            (error () t))
          t)
  ledger)

(defun test-sigma-growth (ledger)
  "Post-bootstrap growth of Sigma: a brand-new symbol is unusable as a
wff until declared, then becomes usable immediately after
DECLARE-ATOMIC-WFF-SYMBOL/DECLARE-VARIABLE-SYMBOL (no bootstrap
reopening, no proof obligation); freshness is enforced both ways,
rejecting a re-declared or reserved-shape name. Returns the ledger
extended with the freshly-declared Q and w0."
  (expect "Q is NOT yet a wff (not declared)" (judgement? 'wff? 'Q ledger) nil)
  (let* ((ledger (declare-atomic-wff-symbol ledger 'Q)))
    (expect "Q IS a wff after DECLARE-ATOMIC-WFF-SYMBOL (post-bootstrap growth)"
            (judgement? 'wff? 'Q ledger) t)
    (expect "(.to Q A) is a wff, combining the freshly-declared Q with A"
            (judgement? 'wff? '(.to Q A) ledger) t)
    (let* ((ledger (declare-variable-symbol ledger 'w0)))
      (expect "w0 is a var after DECLARE-VARIABLE-SYMBOL" (judgement? 'var? 'w0 ledger) t)
      (expect "Gen over the freshly-declared w0: Q |- forall w0 Q"
              (check-k-proof '((0 Q :hyp nil) (1 (.forall w0 Q) :ir (Gen 0 w0))) ledger)
              t)
      (expect "Re-declaring A (already in Sigma) is rejected"
              (handler-case (progn (declare-atomic-wff-symbol ledger 'A) nil) (error () t))
              t)
      (expect "Declaring .forall (reserved binder head) is rejected"
              (handler-case (progn (declare-atomic-wff-symbol ledger '.forall) nil) (error () t))
              t)
      (expect "Declaring ?X (pattern-variable shape) is rejected"
              (handler-case (progn (declare-variable-symbol ledger '?x) nil) (error () t))
              t)
      (expect "Declaring @foo (meta-tag shape) is rejected"
              (handler-case (progn (declare-atomic-wff-symbol ledger '@foo) nil) (error () t))
              t)
      ledger)))

(defun test-abbrev-usage (ledger)
  "Admits my-ax1 as a genuinely-connected label for the II.1 schema (the
supplied proof's own conclusion IS the claimed definiens), uses it at
several instances, and confirms a mismatched instance, an undefined
name, and an unrelated definiens ('evil') are all rejected -- the last
is the critical regression guarding CHECK-AND-EXTEND-ABBREV itself (see
its docstring). Returns the ledger extended with my-ax1."
  (let* ((ledger (check-and-extend-abbrev ledger 'my-ax1 '(.to A (.to A A))
                                           '((0 (.to A (.to A A)) :axiom (II.1))))))
    (expect "Using my-ax1 at B: (.to B (.to B B)) via :def-abbrev"
            (check-k-proof '((0 (.to B (.to B B)) :def-abbrev (my-ax1))) ledger)
            t)
    (expect "Using my-ax1 at the freshly-declared Q: (.to Q (.to Q Q))"
            (check-k-proof '((0 (.to Q (.to Q Q)) :def-abbrev (my-ax1))) ledger)
            t)
    (expect "Attack: (.to B (.to C B)) is not an instance of my-ax1 (A<>A mismatch) -- must reject"
            (check-k-proof '((0 (.to B (.to C B)) :def-abbrev (my-ax1))) ledger)
            nil)
    (expect "Attack: citing an undefined abbreviation name -- must reject"
            (check-k-proof '((0 (.to B (.to B B)) :def-abbrev (no-such-abbrev))) ledger)
            nil)
    (expect "Attack: 'evil' abbreviation with an unrelated proof -- must be REFUSED at admission"
            (handler-case
                (progn (check-and-extend-abbrev ledger 'evil 'A '((0 (.to A (.to A A)) :axiom (II.1))))
                       nil)
              (error () t))
            t)
    (expect "Attack payload: citing 'evil' must never assert an arbitrary formula for free"
            (check-k-proof '((0 (.forall v0 (.eq v0 v1)) :def-abbrev (evil))) ledger)
            nil)
    ledger))

(defun test-axiom-iii1 (ledger)
  "Axiom III.1 (universal instantiation): the genuine case (instantiating
x:=v0 with the genuinely different term t:=v2), the degenerate case
(t=x), and a capturing-substitution attack (t:=v1 captured by an inner
(.forall v1 ...) binder), which @subst-ok? exists to block. Does not
grow the ledger."
  (expect "III.1 genuine instantiation: forall v0 (.eq v0 v1) -> (.eq v2 v1) via (III.1 v2)"
          (check-k-proof '((0 (.to (.forall v0 (.eq v0 v1)) (.eq v2 v1)) :axiom (III.1 v2))) ledger)
          t)
  (expect "III.1 degenerate case t=x still works: forall v0 (.eq v0 v1) -> (.eq v0 v1)"
          (check-k-proof '((0 (.to (.forall v0 (.eq v0 v1)) (.eq v0 v1)) :axiom (III.1 v0))) ledger)
          t)
  (expect "Attack: III.1 with a capturing substitution (t:=v1 captured by inner forall v1) -- must reject"
          (check-k-proof '((0 (.to (.forall v0 (.forall v1 (.eq v0 v1)))
                                   (.forall v1 (.eq v1 v1)))
                              :axiom (III.1 v1)))
                          ledger)
          nil)
  ledger)

(defun test-hyp-wellformedness (ledger)
  ":HYP lines must be genuine, declared, well-formed formulas."
  (expect "Attack: an undeclared symbol as a :HYP formula -- must reject"
          (check-k-proof '((0 totally-undeclared-garbage :hyp nil)) ledger)
          nil)
  (expect "Attack: a malformed (non-wff-shaped) :HYP formula -- must reject"
          (check-k-proof '((0 (.bogus-head v0 v1) :hyp nil)) ledger)
          nil)
  (expect "Sanity: a genuine wff as :HYP still works"
          (check-k-proof '((0 (.eq v0 v1) :hyp nil)) ledger)
          t)
  ledger)

(defun test-exists-formation (ledger)
  ".EXISTS formation, free/bound-variable tracking, and Gen's restriction
seeing straight through .exists the same as .forall."
  (expect "(.exists v0 (.eq v0 v1)) is a wff" (judgement? 'wff? '(.exists v0 (.eq v0 v1)) ledger) t)
  (expect "v0 is bound (not free) under .exists v0"
          (not (member 'v0 (free-vars-wff '(.exists v0 (.eq v0 v1)) ledger) :test #'eq))
          t)
  (expect "v1 IS free under .exists v0 (.eq v0 v1)"
          (member 'v1 (free-vars-wff '(.exists v0 (.eq v0 v1)) ledger) :test #'eq)
          t)
  (expect "Gen restriction still applies with .exists in the open hyp -- must reject"
          (check-k-proof '((0 (.exists v1 (.eq v0 v1)) :hyp nil)
                            (1 (.forall v0 (.exists v1 (.eq v0 v1))) :ir (Gen 0 v0)))
                          ledger)
          nil)
  ledger)

(defun test-negation-and-new-axioms (ledger)
  "(.neg A) formation, plus the K/S/contraposition basis (II.1/II.2/II.3):
a II.3 instance genuinely needs .NEG, and -- the whole point of the
switch away from the old K/K/B-composition basis -- A -> A is now
actually derivable via K (II.1) and S (II.2) alone. Does not grow the
ledger."
  (expect "(.neg A) is a wff" (judgement? 'wff? '(.neg A) ledger) t)
  (expect "(.neg (.to A B)) is a wff (.neg nests over any wff)"
          (judgement? 'wff? '(.neg (.to A B)) ledger) t)
  (expect "II.1 (K) instance with A<>B: (.to A (.to B A))"
          (check-k-proof '((0 (.to A (.to B A)) :axiom (II.1))) ledger) t)
  (expect "II.2 (S) instance: (.to A (.to B C)) -> ((.to A B) -> (.to A C))"
          (check-k-proof '((0 (.to (.to A (.to B C)) (.to (.to A B) (.to A C))) :axiom (II.2))) ledger)
          t)
  (expect "II.3 (contraposition) instance, needs .neg: (.to (.neg B) (.neg A)) -> (.to A B)"
          (check-k-proof '((0 (.to (.to (.neg B) (.neg A)) (.to A B)) :axiom (II.3))) ledger)
          t)
  (expect "A -> A is now derivable from K and S alone (impossible under the old K/K/B basis)"
          (check-k-proof
           '((0 (.to (.to A (.to (.to A A) A)) (.to (.to A (.to A A)) (.to A A))) :axiom (II.2))
             (1 (.to A (.to (.to A A) A)) :axiom (II.1))
             (2 (.to (.to A (.to A A)) (.to A A)) :ir (MP 0 1))
             (3 (.to A (.to A A)) :axiom (II.1))
             (4 (.to A A) :ir (MP 2 3)))
           ledger)
          t)
  ledger)

(defun test-name-uniqueness (ledger)
  "ITH/TH/DEF-ABBREV names must be unique, and CHECK-AND-EXTEND must
refuse a non-ITH/TH kind."
  (expect "Re-using an existing name (my-ax1) for a new TH -- must be refused"
          (handler-case
              (progn (check-and-extend ledger 'th 'my-ax1 '((0 (.to A (.to A A)) :axiom (II.1)))) nil)
            (error () t))
          t)
  (expect "Re-using an existing name (th-gen-vacuous) for a new DEF-ABBREV -- must be refused"
          (handler-case
              (progn (check-and-extend-abbrev ledger 'th-gen-vacuous 'A
                                               '((0 A :hyp nil) (1 (.forall v0 A) :ir (Gen 0 v0))))
                     nil)
            (error () t))
          t)
  (expect "CHECK-AND-EXTEND refuses a non-ITH/TH kind (e.g. AXIOM)"
          (handler-case
              (progn (check-and-extend ledger 'axiom 'sneaky '((0 A :hyp nil))) nil)
            (error () t))
          t)
  ledger)

(defun test-backtracking-and-self-ref (ledger)
  "Simulates a stale/adversarial ledger, bypassing CHECK-AND-EXTEND's own
uniqueness guard via LEDGER-APPEND directly, with TWO entries named
'dup: an unusable first one and a working second one, confirming
backtracking finds the working one; then confirms a proof trying to
cite ITSELF by name, before that name exists in the ledger at all,
fails by construction (the ENTRIES-UPTO boundary)."
  (let* ((ledger (ledger-append ledger 'th
                                 (list 'dup '((0 A :hyp nil) (1 A :ir (Gen 0 v0))))
                                 (list :derived '((0 A :hyp nil) (1 A :ir (Gen 0 v0))))))
         (ledger (ledger-append ledger 'th
                                 (list 'dup '((0 A :hyp nil) (1 (.forall v0 A) :ir (Gen 0 v0))))
                                 (list :derived '((0 A :hyp nil) (1 (.forall v0 A) :ir (Gen 0 v0)))))))
    (expect "Backtracking: citing 'dup' finds the SECOND, working entry after the first fails"
            (check-k-proof '((X B :hyp nil) (Y (.forall v0 B) :th (dup X))) ledger)
            t)
    (expect "Attack: a theorem's own proof citing itself by name -- must be refused"
            (handler-case
                (progn (check-and-extend ledger 'th 'self-ref
                                          '((0 A :hyp nil) (1 A :th (self-ref 0))))
                       nil)
              (error () t))
            t)
    ledger))

(defun run-self-tests ()
  "Threads the ledger explicitly through each growth step via a single
flat LET*, calling one named test-phase function per step: each phase
takes the ledger as it stood after the previous phase and returns the
ledger as it should stand afterward (unchanged, for a phase that only
checks; extended, for one that also grows Sigma or the ledger itself)."
  (let* ((ledger (bootstrap-kernel))
         (ledger (test-basic-formation ledger))
         (ledger (test-axiom-and-inference ledger))
         (ledger (test-vacuous-gen-and-bad-ith ledger))
         (ledger (test-admit-primitive-closed ledger))
         (ledger (test-sigma-growth ledger))
         (ledger (test-abbrev-usage ledger))
         (ledger (test-axiom-iii1 ledger))
         (ledger (test-hyp-wellformedness ledger))
         (ledger (test-exists-formation ledger))
         (ledger (test-negation-and-new-axioms ledger))
         (ledger (test-name-uniqueness ledger))
         (ledger (test-deduction-theorem ledger))
         (ledger (test-deduction-theorem-direct ledger))
         ;; TEST-PERSISTENCE-ROUND-TRIP must run on a ledger built
         ;; entirely through the ordinary growth API (CHECK-AND-EXTEND/
         ;; CHECK-AND-EXTEND-ABBREV/DECLARE-*) -- exactly what it is
         ;; checking WRITE-LEDGER-TO-FILE/READ-LEDGER-FROM-FILE can
         ;; faithfully round-trip. It therefore runs BEFORE
         ;; TEST-BACKTRACKING-AND-SELF-REF, which deliberately injects an
         ;; adversarial, never-verified entry via LEDGER-APPEND directly
         ;; (bypassing CHECK-AND-EXTEND's own checks) to exercise
         ;; backtracking -- exactly the kind of stale/unsound entry
         ;; persistence's replay-through-the-real-gates design is
         ;; SUPPOSED to refuse to resurrect, so it must never be asked to
         ;; round-trip that ledger.
         (ledger (test-persistence-round-trip ledger))
         (ledger (test-chained-module-loading ledger))
         (ledger (test-backtracking-and-self-ref ledger)))
    (declare (ignorable ledger))
    (format t "~%Self-tests complete.~%"))
  ;; Section 13's equality/Peano self-tests run against their OWN
  ;; separately-bootstrapped (:ARITHMETIC T) ledger -- see
  ;; RUN-ARITHMETIC-SELF-TESTS' own docstring -- so they are simply
  ;; appended here rather than threaded through the LET* above.
  (run-arithmetic-self-tests))

;;; ---------------------------------------------------------------------
;;; 10. Persistence: a ledger as a flat "assembly" command stream
;;; ---------------------------------------------------------------------
;;;
;;; The persisted form of a ledger is deliberately NOT a dump of ENTRY
;;; structs, and certainly not of the treap/alist indices LEDGER-APPEND
;;; happens to maintain for speed (section 1.5/2) -- none of that is
;;; meaningful outside this file's own memory. It is a flat list of
;;; COMMANDS: the exact sequence of calls to the growth API
;;; (DECLARE-ATOMIC-WFF-SYMBOL, DECLARE-VARIABLE-SYMBOL, CHECK-AND-EXTEND,
;;; CHECK-AND-EXTEND-ABBREV) that built the ledger, replayed against a
;;; freshly bootstrapped kernel to reconstruct it. This is the lowest
;;; layer any higher-level surface syntax -- infix notation, LaTeX-like
;;; rendering, whatever a friendlier front end wants -- should be defined
;;; as SUGAR over: a translation down into this same flat stream of
;;; DECLARE/DEF-ABBREV/K-proof elements, never something this file itself
;;; needs to know about.
;;;
;;; A command is one of:
;;;   (:declare-atomic-wff-symbol SYM)
;;;   (:declare-variable-symbol SYM)
;;;   (:th   NAME RAW-PROOF)
;;;   (:ith  NAME RAW-PROOF)
;;;   (:def-abbrev NAME DEFINIENS RAW-PROOF)
;;; :PRIMITIVE entries are never part of the stream: nothing outside
;;; BOOTSTRAP-KERNEL's own lexical scope can create one (ADMIT-PRIMITIVE
;;; is closed, by design -- see section 2), and BOOTSTRAP-KERNEL is
;;; deterministic given the same :ATOMIC-SYMBOLS/:VARIABLES, so replaying
;;; a command stream always starts from a fresh (BOOTSTRAP-KERNEL) call,
;;; never from a saved copy of the primitive base itself.
;;;
;;; Loading a saved ledger is NOT privileged access: every replayed
;;; command goes back through the ordinary CHECK-AND-EXTEND/
;;; CHECK-AND-EXTEND-ABBREV/DECLARE-* gates, fully re-verified, exactly
;;; as if a live caller had just typed it -- a corrupted or hand-edited
;;; file can at worst fail to load, never smuggle in an unverified entry.

(defun ledger-commands (ledger)
  "The command stream that reconstructs LEDGER, in original admission
order, from a freshly bootstrapped kernel. Reads straight off LEDGER's
own ALL index (in K order, honoring BOUND), so it is always in sync with
whatever LEDGER actually contains -- never off some separately
maintained log that could drift from it. A DEF-ABBREV entry does not
itself store the DEFINIENS its admitter originally supplied (only its
NAME and RAW-PROOF do), so its command instead uses the proof's own
conclusion (PROOF-CONCLUSION) as DEFINIENS -- CHECK-AND-EXTEND-ABBREV's
own admission check already establishes that this is schema-equivalent
to whatever the original definiens was, so replaying it this way passes
the identical check again."
  (let ((grown-entries
          ;; Skip :PRIMITIVE-origin entries outright: they are BOOTSTRAP-
          ;; KERNEL's own doing (the seed atomic-wff-symbols/variables,
          ;; plus TERM?/WFF?/IRULE/AXIOM formation rules), reconstructed
          ;; simply by calling BOOTSTRAP-KERNEL again in
          ;; LEDGER-FROM-COMMANDS -- never by a DECLARE-* command, which
          ;; would wrongly treat an already-seeded symbol as a fresh one
          ;; and be refused.
          (remove-if (lambda (e) (eq (car (entry-origin e)) :primitive))
                     (treap-values-below (ledger-all ledger) (ledger-bound ledger)))))
    (loop for e in grown-entries
          for cmd = (case (entry-kind e)
                      (atomic-wff-symbol (list :declare-atomic-wff-symbol (entry-payload e)))
                      (variable-symbol (list :declare-variable-symbol (entry-payload e)))
                      ((th ith)
                       (destructuring-bind (name raw-proof) (entry-payload e)
                         (list (if (eq (entry-kind e) 'th) :th :ith) name raw-proof)))
                      (def-abbrev
                       (destructuring-bind (name raw-proof) (entry-payload e)
                         (list :def-abbrev name (proof-conclusion raw-proof) raw-proof)))
                      (th-ded
                       (destructuring-bind (name hyp-formula raw-proof) (entry-payload e)
                         (list :th-ded name hyp-formula raw-proof)))
                      (t nil))
          when cmd collect cmd)))

(defun ledger-from-commands (commands &key (atomic-symbols '(A B C D E F G H))
                                            (variables '(v0 v1 v2 v3 v4 v5))
                                            (log (silent-log))
                                            (ledger nil))
  "The inverse of LEDGER-COMMANDS: starting from LEDGER (a freshly
bootstrapped kernel, with the given seed vocabulary, if LEDGER is not
supplied -- this must match whatever the ORIGINAL ledger was bootstrapped
with, since :PRIMITIVE entries are never themselves part of COMMANDS),
replay COMMANDS against it in order via the ordinary growth API.

Passing an already-grown LEDGER (rather than always starting over from
BOOTSTRAP-KERNEL) is what lets one COMMANDS stream build on top of
another's result -- separate files as separate, linkable \"modules\" of
one growing Hilbert system, the same way an assembler links separately
compiled object files rather than only ever assembling one monolithic
source. Nothing about this is privileged: LEDGER, whatever grew it, is
still just an ordinary ledger, and every command here still goes through
the same CHECK-AND-EXTEND/CHECK-AND-EXTEND-ABBREV/DECLARE-* gates."
  (let ((ledger (or ledger (bootstrap-kernel :atomic-symbols atomic-symbols :variables variables))))
    (dolist (cmd commands ledger)
      (destructuring-bind (op . args) cmd
        (setf ledger
              (case op
                (:declare-atomic-wff-symbol (declare-atomic-wff-symbol ledger (first args)))
                (:declare-variable-symbol (declare-variable-symbol ledger (first args)))
                ((:th :ith) (destructuring-bind (name raw-proof) args
                              (check-and-extend ledger (if (eq op :th) 'th 'ith) name raw-proof log)))
                (:def-abbrev (destructuring-bind (name definiens raw-proof) args
                               (check-and-extend-abbrev ledger name definiens raw-proof log)))
                (:th-ded (destructuring-bind (name hyp-formula raw-proof) args
                           (check-and-extend-by-deduction-direct ledger name hyp-formula raw-proof log)))
                (t (error "LEDGER-FROM-COMMANDS: unknown command ~S" cmd))))))))

(defun write-commands-to-file (commands path)
  "Write COMMANDS (a plain list, as LEDGER-COMMANDS returns, or any
hand-assembled subset/concatenation of one) to PATH as plain
S-expressions, one per line, readable back by ordinary READ -- no custom
file format, no special escaping, nothing but Lisp printing its own
data. *PACKAGE* is bound explicitly to :LEDGER-KERNEL so that names like
A, v0, .forall, Gen print (and, in READ-LEDGER-FROM-FILE, read back) as
the same symbols this file itself uses, regardless of which package the
caller happens to be in. This is the layer WRITE-LEDGER-TO-FILE is built
on; it is exported in its own right because a MODULE file -- one Hilbert-
system source file among several, meant to be linked with others via
READ-LEDGER-FROM-FILE's :LEDGER argument -- is naturally a hand-picked or
generated COMMANDS list, not always the full command stream of some
already-built ledger."
  (with-open-file (out path :direction :output :if-exists :supersede :if-does-not-exist :create)
    (let ((*package* (find-package :ledger-kernel))
          (*print-case* :downcase))
      (dolist (cmd commands)
        (prin1 cmd out)
        (terpri out))))
  path)

(defun write-ledger-to-file (ledger path)
  "Write LEDGER's own full command stream (LEDGER-COMMANDS) to PATH; see
WRITE-COMMANDS-TO-FILE for the actual writing."
  (write-commands-to-file (ledger-commands ledger) path))

(defun read-ledger-from-file (path &key (atomic-symbols '(A B C D E F G H))
                                         (variables '(v0 v1 v2 v3 v4 v5))
                                         (log (silent-log))
                                         (ledger nil))
  "Read a command stream written by WRITE-LEDGER-TO-FILE back into a
genuine, freshly re-verified ledger (LEDGER-FROM-COMMANDS) -- reloading a
ledger costs exactly as much re-verification work as building it live
did, by design (see the section header above).

LEDGER, when supplied, is the starting point PATH's commands are replayed
onto (see LEDGER-FROM-COMMANDS) instead of a fresh BOOTSTRAP-KERNEL --
this is how several files chain into one growing ledger, module by
module: (READ-LEDGER-FROM-FILE \"b.ledger\" :LEDGER (READ-LEDGER-FROM-FILE
\"a.ledger\"))."
  (let ((*package* (find-package :ledger-kernel)))
    (with-open-file (in path :direction :input)
      (let ((commands (loop for form = (read in nil :eof)
                             until (eq form :eof)
                             collect form)))
        (ledger-from-commands commands :atomic-symbols atomic-symbols
                                        :variables variables :log log
                                        :ledger ledger)))))

;;; ---------------------------------------------------------------------
;;; 11. Meta-theorems: the Deduction (Meta-)Theorem, as @DEDUCTION
;;; ---------------------------------------------------------------------
;;;
;;; Gamma, A |- B  implies  Gamma |- A -> B.
;;;
;;; @DEDUCTION is a genuinely new kind of meta-level operation for this
;;; file: unlike @NOT-FREE-IN?/@SUBST/etc. (Section 4), which are meta-
;;; PREDICATES/meta-CONSTRUCTORS dispatched from inside CHECK-CONDITION/
;;; MATCH-TEMPLATE while a single line of a proof is being matched,
;;; @DEDUCTION operates on an entire RAW-PROOF at once, as a
;;; preprocessing/rewriting step that runs BEFORE CHECK-AND-EXTEND or
;;; CHECK-K-PROOF ever sees the result.
;;;
;;; It does not need to be trusted. This file's LCF-style trust boundary
;;; already guarantees that: @DEDUCTION's own correctness is assumed
;;; NOWHERE else in this file. Whatever raw-proof it hands back is
;;; re-verified from scratch, line by line, by the very same CHECK-K-PROOF
;;; that verifies any other proof, the instant CHECK-AND-EXTEND-BY-
;;; DEDUCTION (below) passes it along. A bug in @DEDUCTION can only ever
;;; produce a proof that gets REJECTED -- it can never cause one to be
;;; wrongly ACCEPTED.
;;;
;;; SCOPE: RAW-PROOF's lines may be :HYP, :AXIOM, or :IR citing MP or GEN.
;;; A line that is :ITH/:TH/:DEF-ABBREV is refused with a clear error: it
;;; cites an existing derived rule that may itself take any number of
;;; hypothesis-patterns by line-citation the same way MP takes two;
;;; generalizing the MP case below to an arbitrary derived rule's arity is
;;; possible in principle but is not implemented here.
;;;
;;; GEN's KNOWN EDGE CASE: GEN's own free-variable restriction (the
;;; Verallgemeinerungsverbot) is checked, at ORIGINAL admission time,
;;; against Gamma AS IT STOOD AT THAT LINE -- only the :HYP lines strictly
;;; earlier in RAW-PROOF, since CHECK-K-PROOF accumulates Gamma top-down.
;;; If HYP-FORMULA's own :HYP line happens to come AFTER some GEN line
;;; that generalizes a variable X, then X's freedom in HYP-FORMULA was
;;; never checked by the ORIGINAL proof at all (HYP-FORMULA was not yet
;;; open at that point) -- Case 4 below still builds a III.2 step that
;;; needs X not free in HYP-FORMULA, and in that specific (unusual)
;;; ordering, X could in fact occur free in it. @DEDUCTION does not check
;;; this in advance (it never receives a LEDGER, by design -- it stays a
;;; pure syntactic transform); CHECK-K-PROOF's own re-verification of that
;;; III.2 instance's @NOT-FREE-IN? side condition is what actually decides
;;; it, for real, against the genuine formula. Exactly the same LCF
;;; guarantee as everywhere else in this file: at worst, an unusual
;;; ordering makes @DEDUCTION's output get REJECTED; it is never a route
;;; to a wrongly ACCEPTED one.
;;;
;;; CONSTRUCTION: structural induction over RAW-PROOF's lines, in order,
;;; threading a fresh line-number counter and a MAPPING (alist: original
;;; numbering -> (new-conclusion-line-number . original-formula) -- the
;;; ORIGINAL formula is kept alongside the new line number because the MP
;;; and GEN cases below need to recover their own citations' original
;;; formulas from it, not just a line number). Four cases:
;;;
;;;   1. The line IS the discharged hypothesis itself (:HYP, formula
;;;      equal to HYP-FORMULA, call it H): its replacement conclusion is
;;;      H -> H, proved from K (II.1) and S (II.2) alone -- exactly the
;;;      classical textbook derivation of A -> A (see BOOTSTRAP-AXIOMS'
;;;      own commentary on why the OLD K/K/B-composition basis could not
;;;      derive this at all, and why the CURRENT K/S/contraposition basis
;;;      can):
;;;        n0  (H->((H->H)->H)) -> ((H->(H->H))->(H->H))  [II.2 ?A=H ?B=(.to H H) ?C=H]
;;;        n1  H -> ((H -> H) -> H)                         [II.1 ?A=H ?B=(.to H H)]
;;;        n2  (H -> (H -> H)) -> (H -> H)                  [MP n0 n1]
;;;        n3  H -> (H -> H)                                [II.1 ?A=H ?B=H]
;;;        n4  H -> H                                        [MP n2 n3]
;;;
;;;   2. The line is any OTHER :HYP, or is an :AXIOM (its truth does not
;;;      depend on Gamma at all): call its formula PHI. PHI remains
;;;      available unconditionally in the new proof (an axiom instance is
;;;      simply replicated; a hypothesis other than the discharged one
;;;      stays open), so plain K-weakening gets H -> PHI:
;;;        n0  PHI                                [the original line, unchanged]
;;;        n1  PHI -> (H -> PHI)                   [II.1 ?A=PHI ?B=H]
;;;        n2  H -> PHI                            [MP n1 n0]
;;;
;;;   3. The line is :IR citing (MP I J): original line I's formula is
;;;      (PSI -> PHI) and line J's formula is PSI, concluding PHI. By
;;;      induction the new proof already contains H -> (PSI -> PHI) (I's
;;;      new conclusion) and H -> PSI (J's new conclusion); S combines
;;;      them:
;;;        n0  (H->(PSI->PHI)) -> ((H->PSI)->(H->PHI))  [II.2 ?A=H ?B=PSI ?C=PHI]
;;;        n1  (H -> PSI) -> (H -> PHI)                  [MP n0 I-CONCL]
;;;        n2  H -> PHI                                   [MP n1 J-CONCL]
;;;
;;;   4. The line is :IR citing (GEN I X): original line I's formula is
;;;      B, and this line's own formula is (.forall X B). By induction the
;;;      new proof already contains H -> B (I's new conclusion). GEN
;;;      itself is still legal on it (see "GEN's KNOWN EDGE CASE" above:
;;;      Gamma in the new proof is a SUBSET of Gamma in the original proof
;;;      at the corresponding point, either identical or missing exactly
;;;      H, so whatever variable-freedom check justified the ORIGINAL GEN
;;;      application still justifies this one); axiom III.2 then moves H
;;;      across the quantifier:
;;;        n0  (.forall X (H -> B))                      [GEN I-CONCL X]
;;;        n1  (.forall X (H->B)) -> (H -> (.forall X B)) [III.2 ?x=X ?A=H ?B=B]
;;;        n2  H -> (.forall X B)                          [MP n1 n0]
;;;
;;; Every case's final line's formula is (H -> <original line's formula>),
;;; so MAPPING is always extended with (original-numbering . (that final
;;; line's new number . original-formula)).

(defun @deduction-p-implies-p-block (h n)
  "Case 1's five lines (see the section header): H -> H from K and S
alone. Returns (VALUES new-lines next-counter final-line-number)."
  (let ((n0 n) (n1 (1+ n)) (n2 (+ n 2)) (n3 (+ n 3)) (n4 (+ n 4))
        (h-to-h (list '.to h h)))
    (values
     (list (list n0 (list '.to (list '.to h (list '.to h-to-h h))
                                (list '.to (list '.to h h-to-h) (list '.to h h)))
                 :axiom '(II.2))
           (list n1 (list '.to h (list '.to h-to-h h)) :axiom '(II.1))
           (list n2 (list '.to (list '.to h h-to-h) (list '.to h h)) :ir (list 'MP n0 n1))
           (list n3 (list '.to h h-to-h) :axiom '(II.1))
           (list n4 (list '.to h h) :ir (list 'MP n2 n3)))
     (+ n 5)
     n4)))

(defun @deduction-weaken-block (h phi role by n)
  "Case 2's three lines: H -> PHI from PHI (ROLE/BY replicated, but
RENUMBERED to N -- reusing the original line's own numbering here would
collide with this walk's own fresh counter, e.g. under a second, nested
@DEDUCTION call re-numbering an already-transformed proof) via plain
K-weakening. Returns (VALUES new-lines next-counter final-line-number)."
  (let ((n0 n) (n1 (1+ n)) (n2 (+ n 2)))
    (values
     (list (list n0 phi role by)
           (list n1 (list '.to phi (list '.to h phi)) :axiom '(II.1))
           (list n2 (list '.to h phi) :ir (list 'MP n1 n0)))
     (+ n 3)
     n2)))

(defun @deduction-mp-block (h psi phi i-concl-n j-concl-n n)
  "Case 3's three lines: H -> PHI from H -> (PSI -> PHI) (at I-CONCL-N)
and H -> PSI (at J-CONCL-N) via S. Returns (VALUES new-lines next-counter
final-line-number)."
  (let ((n0 n) (n1 (1+ n)) (n2 (+ n 2)))
    (values
     (list (list n0 (list '.to (list '.to h (list '.to psi phi))
                                (list '.to (list '.to h psi) (list '.to h phi)))
                 :axiom '(II.2))
           (list n1 (list '.to (list '.to h psi) (list '.to h phi)) :ir (list 'MP n0 i-concl-n))
           (list n2 (list '.to h phi) :ir (list 'MP n1 j-concl-n)))
     (+ n 3)
     n2)))

(defun @deduction-gen-block (h x b i-concl-n n)
  "Case 4's three lines: H -> (.forall X B) from H -> B (at I-CONCL-N,
where B is the pre-generalization formula) via GEN followed by axiom
III.2. Returns (VALUES new-lines next-counter final-line-number)."
  (let ((n0 n) (n1 (1+ n)) (n2 (+ n 2))
        (h-to-b (list '.to h b)))
    (values
     (list (list n0 (list '.forall x h-to-b) :ir (list 'GEN i-concl-n x))
           (list n1 (list '.to (list '.forall x h-to-b) (list '.to h (list '.forall x b)))
                 :axiom '(III.2))
           (list n2 (list '.to h (list '.forall x b)) :ir (list 'MP n1 n0)))
     (+ n 3)
     n2)))

(defun @deduction-walk (h lines n mapping acc)
  "The induction itself: LINES is what remains of the original RAW-PROOF
(each already a (NUMBERING FORMULA ROLE BY) list, not yet a K-LINE
struct); ACC accumulates new lines in reverse. See the section header for
MAPPING's shape and the three cases."
  (if (null lines)
      (reverse acc)
      (destructuring-bind (num formula role by) (car lines)
        (cond
          ((and (eq role :hyp) (equal formula h))
           (multiple-value-bind (new-lines next concl) (@deduction-p-implies-p-block h n)
             (@deduction-walk h (cdr lines) next (acons num (cons concl formula) mapping)
                              (append (reverse new-lines) acc))))
          ((or (eq role :hyp) (eq role :axiom))
           (multiple-value-bind (new-lines next concl)
               (@deduction-weaken-block h formula role by n)
             (@deduction-walk h (cdr lines) next (acons num (cons concl formula) mapping)
                              (append (reverse new-lines) acc))))
          ((and (eq role :ir) (consp by) (eq (car by) 'MP))
           (destructuring-bind (mp-tag i j) by
             (declare (ignore mp-tag))
             (let ((i-entry (cdr (assoc i mapping :test #'equal)))
                   (j-entry (cdr (assoc j mapping :test #'equal))))
               (unless (and i-entry j-entry)
                 (error "@DEDUCTION: line ~S cites ~S/~S out of order or unknown." num i j))
               (multiple-value-bind (new-lines next concl)
                   (@deduction-mp-block h (cdr j-entry) formula (car i-entry) (car j-entry) n)
                 (@deduction-walk h (cdr lines) next (acons num (cons concl formula) mapping)
                                  (append (reverse new-lines) acc))))))
          ((and (eq role :ir) (consp by) (eq (car by) 'GEN))
           (destructuring-bind (gen-tag i x) by
             (declare (ignore gen-tag))
             (let ((i-entry (cdr (assoc i mapping :test #'equal))))
               (unless i-entry
                 (error "@DEDUCTION: line ~S cites ~S out of order or unknown." num i))
               (multiple-value-bind (new-lines next concl)
                   (@deduction-gen-block h x (cdr i-entry) (car i-entry) n)
                 (@deduction-walk h (cdr lines) next (acons num (cons concl formula) mapping)
                                  (append (reverse new-lines) acc))))))
          (t
           (error "@DEDUCTION: line ~S has role ~S, which this construction ~
                   does not (yet) support -- only :HYP, :AXIOM, and :IR ~
                   citing MP or GEN are handled. A cited :ITH/:TH/:DEF-ABBREV ~
                   may itself take premises by line-citation the way MP ~
                   does, which this version does not generalize to."
                  num role))))))

(defun @deduction (hyp-formula raw-proof)
  "Transform RAW-PROOF (a K-proof deriving some formula from an open-
hypothesis set that includes HYP-FORMULA) into a new raw K-proof deriving
(HYP-FORMULA -> <RAW-PROOF's own conclusion>) from RAW-PROOF's other open
hypotheses alone -- the Deduction (Meta-)Theorem. See the section header
above for the construction and its scope. Untrusted: the result is only
ever accepted if CHECK-K-PROOF re-verifies it from scratch, exactly like
any other raw-proof (see CHECK-AND-EXTEND-BY-DEDUCTION)."
  (@deduction-walk hyp-formula raw-proof 0 nil nil))

(defun check-and-extend-by-deduction (ledger kind name hyp-formula raw-proof &optional (log (silent-log)))
  "Convenience wrapper: admit (HYP-FORMULA -> <RAW-PROOF's conclusion>)
as a new KIND/NAME ledger entry, built via @DEDUCTION from a proof of
RAW-PROOF's conclusion under an open-hypothesis set including HYP-
FORMULA. Exactly as trustworthy as calling CHECK-AND-EXTEND directly on
some other raw-proof -- @DEDUCTION's output is re-verified from scratch,
never taken on faith."
  (check-and-extend ledger kind name (@deduction hyp-formula raw-proof) log))

;;; ---------------------------------------------------------------------
;;; 11.5. CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT -- trusting the Deduction
;;;       Theorem itself, instead of compiling it away
;;; ---------------------------------------------------------------------
;;;
;;; @DEDUCTION (above) treats the Deduction Theorem as something that must
;;; be COMPILED: it rewrites RAW-PROOF into a brand-new, K/S-only raw-proof
;;; of (HYP-FORMULA -> PHI) with no open hypotheses left, so CHECK-AND-
;;; EXTEND never has to know anything special happened -- but every line
;;; of the original proof gets replaced by ~3 new ones, and this compounds
;;; multiplicatively over repeated discharges (5 lines -> 17 -> 53 -> 161
;;; across three successive discharges of one small syllogism -- see the
;;; session's own diagnostic run). The other honest option, discussed at
;;; length before this section exists to realize it: treat the Deduction
;;; Theorem itself as a TRUSTED meta-mathematical fact -- established once,
;;; here, never re-derived per use -- and admit (HYP-FORMULA -> PHI)
;;; directly from a CHECKED proof of Gamma,HYP-FORMULA |- PHI, without ever
;;; materializing an expanded K,S-only proof of the implication at all.
;;;
;;; WHY THIS IS SOUND, using only machinery CHECK-K-PROOF already has:
;;;
;;;   RAW-PROOF here is an ordinary ND-style raw-proof (:HYP/:AXIOM/
;;;   :IR(MP)/:IR(GEN) lines, exactly what CHECK-K-PROOF already knows how
;;;   to verify) with HYP-FORMULA as one of its own :HYP lines. CHECK-AND-
;;;   EXTEND-BY-DEDUCTION-DIRECT calls CHECK-K-PROOF on it UNCHANGED -- no
;;;   transformation, no expansion. GEN's own Verallgemeinerungsverbot
;;;   (META-NOT-FREE-IN-DEPENDENCIES?, Section 5) already checks, line by
;;;   line as CHECK-K-PROOF walks the proof top-down, that a generalized
;;;   variable is free in none of the hypotheses OPEN AT THAT POINT -- and
;;;   that is EXACTLY the side condition the Deduction Theorem requires
;;;   (Mendelson's formulation: no Gen on a variable free in a hypothesis
;;;   the generalized line actually depends on). Because OPEN-HYPS only
;;;   ever contains :HYP lines strictly earlier in the linear proof, a Gen
;;;   line that comes BEFORE HYP-FORMULA's own :HYP line is automatically,
;;;   correctly unconstrained by HYP-FORMULA -- there is no coarser,
;;;   blanket "check every Gen against HYP-FORMULA regardless of order"
;;;   approximation here, unlike @DEDUCTION's per-line Case 4 (see its own
;;;   "GEN's KNOWN EDGE CASE" commentary above), which reconstructs H -> B
;;;   for EVERY line uniformly and so can spuriously demand X not free in H
;;;   even when the original Gen came before H was ever introduced. TEST-
;;;   DEDUCTION-THEOREM-DIRECT below constructs exactly that scenario and
;;;   confirms @DEDUCTION rejects it while this function accepts it.
;;;
;;;   The ONE thing that is trusted rather than checked, here, is the
;;;   bridge itself: "a checked proof of Gamma,H |- PHI, with Gen already
;;;   honoring Gamma as open-hyps, justifies asserting Gamma |- H -> PHI."
;;;   That is a fixed fact about THIS proof system, established once by
;;;   the classical Deduction Theorem argument (structural induction on
;;;   the same four cases @DEDUCTION's own construction embodies -- HYP,
;;;   weakening, MP, Gen -- which is precisely why that construction is
;;;   always POSSIBLE, whatever its cost); it is never re-derived inside
;;;   this function, the same way ADMIT-PRIMITIVE's axioms are trusted
;;;   once at bootstrap rather than re-proven on every citation.
;;;
;;;   Everything else stays LCF-style, checked, never taken on faith: the
;;;   stored payload is (NAME HYP-FORMULA RAW-PROOF) -- the ORIGINAL,
;;;   small, unexpanded proof -- and TRY-DEDUCTION-ENTRY (Section 6) fully
;;;   re-verifies an instantiated copy of it via CHECK-K-PROOF from a fresh
;;;   OPEN-HYPS every single time the resulting :TH-DED entry is cited. A
;;;   bug in the one trusted bridging step above could make this function
;;;   admit an unsound (.to HYP-FORMULA PHI); it can never make a later
;;;   citation of an already-admitted entry go unverified.
;;;
;;; SCOPE: identical to @DEDUCTION's -- RAW-PROOF's lines may be :HYP,
;;; :AXIOM, or :IR citing MP or GEN; a line citing an existing ITH/TH/
;;; DEF-ABBREV/TH-DED entry is out of scope (CHECK-K-PROOF would still
;;; verify such a proof directly since it is not @DEDUCTION-transformed at
;;; all, but the Deduction Theorem's own textbook proof only inducts on
;;; HYP/AXIOM/MP/GEN, so citing a derived rule mid-proof is not covered by
;;; the trusted bridging step here either -- this function does not special-
;;; case or forbid it, but nothing has verified the bridge is sound in that
;;; case, so it is simply not something to rely on).

(defun check-and-extend-by-deduction-direct (ledger name hyp-formula raw-proof &optional (log (silent-log)))
  "Admit (.to HYP-FORMULA PHI), where PHI is RAW-PROOF's own conclusion, as
a new :TH-DED/NAME ledger entry -- by trusting the Deduction Theorem
itself (see the section header above), never by constructing an explicit
K,S-only expansion the way CHECK-AND-EXTEND-BY-DEDUCTION/@DEDUCTION do.
RAW-PROOF must be an ordinary :HYP/:AXIOM/:IR(MP)/:IR(GEN) raw-proof
containing HYP-FORMULA as one of its own :HYP lines; it is checked EXACTLY
as it stands, via CHECK-K-PROOF, with no transformation at all. RAW-PROOF
may have OTHER open hypotheses (Gamma) besides HYP-FORMULA -- they are NOT
discharged, and remain genuine required premises that a later citation of
this entry must still supply (see TRY-DEDUCTION-ENTRY). Returns the NEW
ledger."
  (when (derived-rule-name-taken-p name ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: the name ~S is already ~
            used by an existing ITH/TH/DEF-ABBREV/TH-DED entry -- refused ~
            to avoid an ambiguous or shadowing citation." name))
  (unless (judgement? 'wff? hyp-formula ledger)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: HYP-FORMULA ~S is not a ~
            well-formed formula." hyp-formula))
  (unless (member hyp-formula (proof-hypotheses raw-proof) :test #'equal)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: HYP-FORMULA ~S does not ~
            occur as one of RAW-PROOF's own :HYP lines -- nothing would be ~
            discharged." hyp-formula))
  (unless (check-k-proof raw-proof ledger log)
    (log-admission-result log name nil)
    (error "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT: proof of ~S rejected." name))
  (log-admission-result log name t)
  (ledger-append ledger 'th-ded (list name hyp-formula raw-proof)
                 (list :derived-by-deduction hyp-formula raw-proof)))

(defun test-deduction-theorem (ledger)
  "@DEDUCTION end to end: discharging TWICE over the ordinary MP proof of
A, (.to A B) |- B recovers the fully closed combinator theorem
A -> ((.to A B) -> B); discharging over a GEN-based proof (both the
self-generalizing case, where the discharged hypothesis is itself the
formula being generalized over vacuously, and the case where GEN cites a
DIFFERENT, still-open hypothesis) recovers the corresponding
quantified theorems -- all admitted and re-citable as real ledger
THEOREMs (not just in-memory raw-proofs); plus the one remaining
documented rejection path (a :TH line). Grows the ledger by four
entries."
  (let* ((mp-proof '((0 A :hyp nil)
                      (1 (.to A B) :hyp nil)
                      (2 B :ir (MP 1 0))))
         (discharge-1 (@deduction '(.to A B) mp-proof)))
    (expect "Sanity: the plain MP proof itself still checks"
            (check-k-proof mp-proof ledger) t)
    (expect "After discharging (.to A B): A |- (.to A B) -> B"
            (check-k-proof discharge-1 ledger) t)
    (expect "...and its conclusion is exactly that"
            (equal (proof-conclusion discharge-1) '(.to (.to A B) B)) t)
    (let ((discharge-2 (@deduction 'A discharge-1)))
      (expect "After discharging A too: |- A -> ((.to A B) -> B), no open hyps left"
              (check-k-proof discharge-2 ledger) t)
      (expect "...and its conclusion is exactly that"
              (equal (proof-conclusion discharge-2) '(.to A (.to (.to A B) B))) t)
      (let ((ledger (check-and-extend-by-deduction
                     (check-and-extend-by-deduction ledger 'th 'th-deduction-demo-step1
                                                     '(.to A B) mp-proof)
                     'th 'th-deduction-demo 'A discharge-1)))
        (expect "TH-DEDUCTION-DEMO is now a real, re-citable ledger theorem"
                (check-k-proof '((0 (.to C (.to (.to C D) D)) :th (th-deduction-demo))) ledger)
                t)
        (expect "Attack: citing it with mismatched A<>B halves -- must reject"
                (check-k-proof '((0 (.to C (.to (.to D D) D)) :th (th-deduction-demo))) ledger)
                nil)
        (expect "@DEDUCTION rejects a :TH line (out of scope, see section header)"
                (handler-case (progn (@deduction 'A `((0 A :hyp nil)
                                                        (1 (.to A B) :th (my-ax1))))
                                      nil)
                  (error () t))
                t)
        (let* ((gen-self-proof '((0 A :hyp nil) (1 (.forall v0 A) :ir (Gen 0 v0))))
               (gen-self-discharge (@deduction 'A gen-self-proof)))
          (expect "Sanity: the vacuous-Gen proof itself still checks (A |- forall v0 A)"
                  (check-k-proof gen-self-proof ledger) t)
          (expect "Case 4 (GEN) on the SELF-discharged hypothesis: |- A -> (forall v0 A)"
                  (check-k-proof gen-self-discharge ledger) t)
          (expect "...and its conclusion is exactly that"
                  (equal (proof-conclusion gen-self-discharge) '(.to A (.forall v0 A))) t)
          (let ((ledger (check-and-extend-by-deduction ledger 'th 'th-gen-self-discharge
                                                         'A gen-self-proof)))
            (expect "TH-GEN-SELF-DISCHARGE is a real, re-citable ledger theorem"
                    (check-k-proof '((0 (.to C (.forall v0 C)) :th (th-gen-self-discharge))) ledger)
                    t)
            (let* ((gen-other-proof '((0 A :hyp nil) (1 B :hyp nil)
                                       (2 (.forall v0 B) :ir (Gen 1 v0))))
                   (gen-other-discharge-1 (@deduction 'A gen-other-proof)))
              (expect "Case 4 (GEN) discharging a hyp OTHER than the one GEN cites: A |- B still open"
                      (check-k-proof gen-other-discharge-1 ledger) t)
              (expect "...and its conclusion is exactly that (A -> forall v0 B), with B still open"
                      (equal (proof-conclusion gen-other-discharge-1) '(.to A (.forall v0 B))) t)
              (let* ((gen-other-discharge-2 (@deduction 'B gen-other-discharge-1)))
                (expect "Discharging B too closes it: |- B -> (A -> forall v0 B)"
                        (check-k-proof gen-other-discharge-2 ledger) t)
                (let ((ledger (check-and-extend-by-deduction ledger 'th 'th-gen-other-discharge
                                                              'B gen-other-discharge-1)))
                  (expect "TH-GEN-OTHER-DISCHARGE is a real, re-citable ledger theorem"
                          (check-k-proof '((0 (.to C (.to D (.forall v0 C))) :th (th-gen-other-discharge)))
                                          ledger)
                          t)
                  ledger)))))))))

(defun test-deduction-theorem-direct (ledger)
  "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT (Section 11.5) end to end: the same
basic MP discharge as TEST-DEDUCTION-THEOREM, but confirming (a) NO
expansion ever happens -- the stored proof is exactly RAW-PROOF, unchanged
size -- and (b) the GEN edge case @DEDUCTION cannot avoid (documented in
Section 11's header, and in Section 11.5's own header) is genuinely fixed
here, not merely papered over: a proof where Gen generalizes a variable
BEFORE the hypothesis being discharged is even introduced, where that
variable IS free in the hypothesis, so @DEDUCTION's own per-line
Case-4 construction spuriously rejects it, while CHECK-AND-EXTEND-BY-
DEDUCTION-DIRECT -- never touching CHECK-K-PROOF's own already-correct,
order-sensitive OPEN-HYPS tracking -- correctly accepts it. Grows the
ledger by two entries."
  (let* ((mp-proof '((0 A :hyp nil)
                      (1 (.to A B) :hyp nil)
                      (2 B :ir (MP 1 0))))
         (ledger (check-and-extend-by-deduction-direct ledger 'th-direct-mp-demo '(.to A B) mp-proof)))
    (expect "TH-DIRECT-MP-DEMO is a real, re-citable ledger theorem (citing Gamma=A as C)"
            (check-k-proof '((0 C :hyp nil)
                              (1 (.to (.to C D) D) :th-ded (th-direct-mp-demo 0)))
                            ledger)
            t)
    (expect "Attack: citing it with mismatched C<>D halves -- must reject"
            (check-k-proof '((0 C :hyp nil)
                              (1 (.to (.to C D) E) :th-ded (th-direct-mp-demo 0)))
                            ledger)
            nil)
    (expect "Attack (regression for the earlier caught bug): omitting the ~
             required Gamma premise (A) entirely -- must reject, since ~
             (.to (.to C D) D) is NOT a tautology on its own"
            (check-k-proof '((0 (.to (.to C D) D) :th-ded (th-direct-mp-demo))) ledger)
            nil)
    (expect "No expansion happened: the stored proof is exactly RAW-PROOF's own 3 lines"
            (= (length (third (entry-payload (car (entries-of-kind 'th-ded ledger))))) 3)
            t)
    ;; The GEN edge case, made concrete: H = (v0 .eq v1), with v0 free in
    ;; H. Line 1 generalizes v0 -- legally, since at that point OPEN-HYPS
    ;; is just {(v4 .eq v1)}, which does not mention v0 -- BEFORE H itself
    ;; is introduced at line 2. @DEDUCTION's Case 4 would still rebuild
    ;; "H -> (forall v0 (v4 .eq v1))" via axiom III.2 for that line, which
    ;; demands v0 not free in H -- false here -- so it must reject the
    ;; result even though the underlying mathematics is perfectly sound.
    (let* ((h '(.eq v0 v1))
           (edge-proof '((0 (.eq v4 v1) :hyp nil)
                         (1 (.forall v0 (.eq v4 v1)) :ir (Gen 0 v0))
                         (2 (.eq v0 v1) :hyp nil)
                         (3 (.to (.forall v0 (.eq v4 v1)) (.eq v4 v1)) :axiom (III.1 v4))
                         (4 (.eq v4 v1) :ir (MP 3 1)))))
      (expect "Sanity: the edge-case proof itself checks (Gamma,H |- PHI)"
              (check-k-proof edge-proof ledger) t)
      (expect "@DEDUCTION genuinely fails here -- the documented edge case, concretely demonstrated"
              (check-k-proof (@deduction h edge-proof) ledger) nil)
      (let ((ledger (check-and-extend-by-deduction-direct ledger 'th-edge-case-fixed h edge-proof)))
        (expect "CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT correctly admits it (citing Gamma=(.eq v4 v1))"
                (check-k-proof '((0 (.eq v4 v1) :hyp nil)
                                  (1 (.to (.eq v0 v1) (.eq v4 v1)) :th-ded (th-edge-case-fixed 0)))
                                ledger)
                t)
        ledger))))

;;; ---------------------------------------------------------------------
;;; 12. Regression tests for Section 10 (file I/O / persistence)
;;; ---------------------------------------------------------------------
;;;
;;; LEDGER-COMMANDS/LEDGER-FROM-COMMANDS/WRITE-LEDGER-TO-FILE/READ-LEDGER-
;;; FROM-FILE (Section 10) were exercised only by hand, in scratch scripts,
;;; when they were first written -- never wired into RUN-SELF-TESTS
;;; itself, so nothing would have caught a later regression there. This
;;; section closes that gap: a genuine round trip through the filesystem
;;; (not just in-memory COMMANDS/FROM-COMMANDS), checked three ways --
;;; byte-for-byte command-stream fidelity, a real re-citation of a THEOREM
;;; that itself came from @DEDUCTION, and a tamper-resistance check
;;; showing a corrupted file can only ever fail to load, never smuggle in
;;; an unsound entry.

(defun tree-subst (old new tree)
  "Blind structural substitution (no notion of binders/capture, unlike
SUBSTITUTE-WFF in Section 4) -- used here only to build a deliberately
corrupted test fixture, never inside the kernel's own trusted logic."
  (cond
    ((eq tree old) new)
    ((consp tree) (cons (tree-subst old new (car tree)) (tree-subst old new (cdr tree))))
    (t tree)))

(defun test-persistence-round-trip (ledger)
  "WRITE-LEDGER-TO-FILE / READ-LEDGER-FROM-FILE, genuinely through the
filesystem (not just LEDGER-COMMANDS/LEDGER-FROM-COMMANDS in memory).
Does not grow the ledger (writes/reads a temp file as a side effect, then
removes it)."
  (let ((path "/tmp/ledger-kernel-self-test-persistence.tmp")
        (bad-path "/tmp/ledger-kernel-self-test-persistence-tampered.tmp"))
    (unwind-protect
         (progn
           (write-ledger-to-file ledger path)
           (let ((reloaded (read-ledger-from-file path)))
             (expect "Reload preserves the entry count exactly"
                     (= (ledger-count reloaded) (ledger-count ledger)) t)
             (expect "Reload's own command stream is identical to the original's"
                     (equal (ledger-commands reloaded) (ledger-commands ledger)) t)
             (expect "A plain axiom-instance judgement still holds after reload"
                     (judgement? 'wff? '(.to A B) reloaded) t)
             (expect "TH-DEDUCTION-DEMO (built via @DEDUCTION) is still citable after reload"
                     (check-k-proof '((0 (.to C (.to (.to C D) D)) :th (th-deduction-demo))) reloaded)
                     t)
             (expect "MY-AX1 (a DEF-ABBREV) is still citable after reload"
                     (check-k-proof '((0 (.to Q (.to Q Q)) :def-abbrev (my-ax1))) reloaded)
                     t)
             (expect "TH-DIRECT-MP-DEMO (a TH-DED entry, built via CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT) is still citable after reload"
                     (check-k-proof '((0 F :hyp nil)
                                       (1 (.to (.to F G) G) :th-ded (th-direct-mp-demo 0)))
                                     reloaded)
                     t))
           ;; Tamper-resistance: corrupt one grown entry's proof (blindly
           ;; swap B for Z inside the last :TH command's raw-proof, which
           ;; breaks its own internal citations/schema) and confirm
           ;; loading it can only fail, never quietly succeed.
           (let* ((commands (ledger-commands ledger))
                  (victim (find-if (lambda (c) (eq (car c) :th)) commands :from-end t)))
             (when victim
               (let* ((tampered (tree-subst victim (tree-subst 'B 'Z victim) commands)))
                 (write-commands-to-file tampered bad-path)
                 (expect "A tampered command stream is refused outright, not silently accepted"
                         (handler-case (progn (read-ledger-from-file bad-path) nil)
                           (error () t))
                         t))))
           ledger)
      (ignore-errors (delete-file path))
      (ignore-errors (delete-file bad-path)))))

(defun test-chained-module-loading (ledger)
  "READ-LEDGER-FROM-FILE's :LEDGER argument: splitting one ledger's own
command stream into two files and loading them back CHAINED (the second
file's commands replayed onto the first file's already-reloaded result,
rather than each starting over from a fresh BOOTSTRAP-KERNEL) reconstructs
the SAME ledger a single-file reload would -- confirming several \"module\"
files can stand in for one, exactly as the next step (an actual
multi-file Hilbert-system source library) needs. Does not grow the
ledger (writes/reads two temp files as a side effect, then removes them)."
  (let ((path-a "/tmp/ledger-kernel-self-test-module-a.tmp")
        (path-b "/tmp/ledger-kernel-self-test-module-b.tmp"))
    (unwind-protect
         (let* ((commands (ledger-commands ledger))
                (half (floor (length commands) 2))
                (commands-a (subseq commands 0 half))
                (commands-b (subseq commands half)))
           (write-commands-to-file commands-a path-a)
           (write-commands-to-file commands-b path-b)
           (let* ((ledger-a (read-ledger-from-file path-a))
                  (chained (read-ledger-from-file path-b :ledger ledger-a)))
             (expect "Chained two-file load reaches the same entry count as the original"
                     (= (ledger-count chained) (ledger-count ledger)) t)
             (expect "...and the identical command stream"
                     (equal (ledger-commands chained) commands) t)
             (expect "TH-DEDUCTION-DEMO is still citable in the two-file chained result"
                     (check-k-proof '((0 (.to C (.to (.to C D) D)) :th (th-deduction-demo))) chained)
                     t)))
      (ignore-errors (delete-file path-a))
      (ignore-errors (delete-file path-b)))
    ledger))

;;; ---------------------------------------------------------------------
;;; 13. Regression tests for equality (IV.1-IV.4) and Peano arithmetic
;;;     (Section 7.5, bootstrap-kernel :arithmetic t)
;;; ---------------------------------------------------------------------
;;;
;;; These run against their OWN, separately-bootstrapped arithmetic-
;;; enabled ledger (BOOTSTRAP-KERNEL :ARITHMETIC T) rather than threading
;;; through RUN-SELF-TESTS' main LEDGER chain: :ARITHMETIC's extra
;;; vocabulary/axioms are one specific theory's business, not the generic
;;; kernel's, so every other self-test above continues to run against the
;;; exact same plain kernel it always has.

(defun test-equality-axioms (ledger)
  "IV.1 (reflexivity), IV.2 (Leibniz), IV.3 (symmetry), IV.4
(transitivity). Does not grow the ledger."
  (expect "IV.1: zero = zero" (check-k-proof '((0 (.eq zero zero) :axiom (IV.1))) ledger) t)
  (expect "IV.1: v0 = v0" (check-k-proof '((0 (.eq v0 v0) :axiom (IV.1))) ledger) t)
  (expect "IV.3: v0=v1 -> v1=v0"
          (check-k-proof '((0 (.to (.eq v0 v1) (.eq v1 v0)) :axiom (IV.3))) ledger) t)
  (expect "IV.4: v0=v1 -> (v1=v2 -> v0=v2)"
          (check-k-proof '((0 (.to (.eq v0 v1) (.to (.eq v1 v2) (.eq v0 v2))) :axiom (IV.4))) ledger)
          t)
  (expect "IV.2 (Leibniz), single-occurrence use: v0=v1 -> (forall v2(v2=v0) -> forall v2(v2=v1))"
          (check-k-proof '((0 (.to (.eq v0 v1)
                                   (.to (.forall v2 (.eq v2 v0)) (.forall v2 (.eq v2 v1))))
                               :axiom (IV.2)))
                          ledger)
          t)
  ledger)

(defun test-peano-axioms (ledger)
  "P1-P2 (successor), P4-P7 (recursive +/*), P8-P10 (congruence), and one
instantiation of P3 (induction). Does not grow the ledger."
  (expect "P1: S(v0) =/= 0" (check-k-proof '((0 (.neg (.eq (S v0) zero)) :axiom (P1))) ledger) t)
  (expect "P2: S(v0)=S(v1) -> v0=v1"
          (check-k-proof '((0 (.to (.eq (S v0) (S v1)) (.eq v0 v1)) :axiom (P2))) ledger) t)
  (expect "P4: v0+0 = v0" (check-k-proof '((0 (.eq (+ v0 zero) v0) :axiom (P4))) ledger) t)
  (expect "P5: v0+S(v1) = S(v0+v1)"
          (check-k-proof '((0 (.eq (+ v0 (S v1)) (S (+ v0 v1))) :axiom (P5))) ledger) t)
  (expect "P6: v0*0 = 0" (check-k-proof '((0 (.eq (* v0 zero) zero) :axiom (P6))) ledger) t)
  (expect "P7: v0*S(v1) = (v0*v1)+v0"
          (check-k-proof '((0 (.eq (* v0 (S v1)) (+ (* v0 v1) v0)) :axiom (P7))) ledger) t)
  (expect "P8: v0=v1 -> S(v0)=S(v1)"
          (check-k-proof '((0 (.to (.eq v0 v1) (.eq (S v0) (S v1))) :axiom (P8))) ledger) t)
  (expect "P9: v0=v1 -> (v2=v3 -> v0+v2=v1+v3)"
          (check-k-proof '((0 (.to (.eq v0 v1) (.to (.eq v2 v3) (.eq (+ v0 v2) (+ v1 v3)))) :axiom (P9)))
                          ledger)
          t)
  (expect "P3, instantiated at A(x):=(0+x=x): well-typed and accepted"
          (check-k-proof `((0 (.to (.eq (+ zero zero) zero)
                                   (.to (.forall v0 (.to (.eq (+ zero v0) v0) (.eq (+ zero (S v0)) (S v0))))
                                        (.forall v0 (.eq (+ zero v0) v0))))
                               :axiom (P3 v0 (.eq (+ zero v0) v0))))
                          ledger)
          t)
  ledger)

(defun test-peano-induction-proof (ledger)
  "End to end: PROVE 0+x=x by genuine induction (P3), not just check that
P3's schema type-checks -- a base case (P4), a step case discharged via
CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT (chaining IV.4/P5/P8, no expansion),
GEN, then one MP against the P3 instance itself. Grows the ledger by
three entries (the base fact, the step-case TH-DED lemma, and the final
induction theorem)."
  (let* ((base-proof '((0 (.eq (+ zero zero) zero) :axiom (P4))))
         (ledger (check-and-extend ledger 'th 'th-zero-plus-zero base-proof))
         (step-hyp '(.eq (+ zero v0) v0))
         (step-proof '((0 (.eq (+ zero v0) v0) :hyp nil)
                       (1 (.eq (+ zero (S v0)) (S (+ zero v0))) :axiom (P5))
                       (2 (.to (.eq (+ zero v0) v0) (.eq (S (+ zero v0)) (S v0))) :axiom (P8))
                       (3 (.eq (S (+ zero v0)) (S v0)) :ir (MP 2 0))
                       (4 (.to (.eq (+ zero (S v0)) (S (+ zero v0)))
                               (.to (.eq (S (+ zero v0)) (S v0))
                                    (.eq (+ zero (S v0)) (S v0))))
                          :axiom (IV.4))
                       (5 (.to (.eq (S (+ zero v0)) (S v0)) (.eq (+ zero (S v0)) (S v0)))
                          :ir (MP 4 1))
                       (6 (.eq (+ zero (S v0)) (S v0)) :ir (MP 5 3)))))
    (expect "step-case ND proof (0+v0=v0 |- 0+S(v0)=S(v0)) checks"
            (check-k-proof step-proof ledger) t)
    (let* ((ledger (check-and-extend-by-deduction-direct
                    ledger 'th-zero-plus-step step-hyp step-proof))
           (step-concl (list '.to step-hyp (proof-conclusion step-proof)))
           (full-proof
             `((0 ,step-concl :th-ded (th-zero-plus-step))
               (1 (.forall v0 ,step-concl) :ir (Gen 0 v0))
               (2 (.to (.eq (+ zero zero) zero)
                       (.to (.forall v0 ,step-concl) (.forall v0 (.eq (+ zero v0) v0))))
                  :axiom (P3 v0 (.eq (+ zero v0) v0)))
               (3 (.eq (+ zero zero) zero) :th-ded (th-zero-plus-zero))
               (4 (.to (.forall v0 ,step-concl) (.forall v0 (.eq (+ zero v0) v0))) :ir (MP 2 3))
               (5 (.forall v0 (.eq (+ zero v0) v0)) :ir (MP 4 1)))))
      (expect "full induction proof of forall v0 (0+v0=v0) checks"
              (check-k-proof full-proof ledger) t)
      (let ((ledger (check-and-extend ledger 'th 'th-zero-plus-identity full-proof)))
        (expect "TH-ZERO-PLUS-IDENTITY is a real, re-citable ledger theorem"
                (check-k-proof '((0 (.forall v0 (.eq (+ zero v0) v0)) :th (th-zero-plus-identity))) ledger)
                t)
        ledger))))

(defun run-arithmetic-self-tests ()
  "As RUN-SELF-TESTS, but against a BOOTSTRAP-KERNEL :ARITHMETIC T ledger
-- equality theory and Peano arithmetic, Sections 7.5/13."
  (let* ((ledger (bootstrap-kernel :arithmetic t))
         (ledger (test-equality-axioms ledger))
         (ledger (test-peano-axioms ledger))
         (ledger (test-peano-induction-proof ledger)))
    (declare (ignorable ledger))
    (format t "~%Arithmetic self-tests complete.~%")))

;;; ---------------------------------------------------------------------
;;; 14. Classical propositional completeness lemmas (II.4 and friends)
;;; ---------------------------------------------------------------------
;;;
;;; Re-derives, in-memory, exactly the chain also persisted as
;;; hilbert-library/05-classical-logic.ledger: TH-EX-FALSO, TH-DNEG-ELIM,
;;; TH-DNEG-INTRO, and the reductio ladder TH-RAA-S1/TH-RAA-S3/TH-RAA
;;; ending in TH-NEG-IMPL. These are the handful of classical facts
;;; Kalmar's completeness construction (tactics layer, on top of this
;;; kernel) needs and that are NOT reachable from {II.1,II.2,II.3} within
;;; any practical proof-search budget -- see BOOTSTRAP-AXIOMS' comment on
;;; II.4 for why that axiom exists at all despite being, in principle,
;;; redundant.

(defun test-classical-logic (ledger)
  ;; TH-IDENTITY (A -> A) isn't part of BOOTSTRAP-KERNEL itself -- it
  ;; only exists as the first line of hilbert-library/01-propositional-
  ;; core.ledger -- but TH-DNEG-ELIM and TH-RAA-S3 below cite it, so it
  ;; is re-derived here too, exactly as that file defines it.
  (let ((ledger (check-and-extend-by-deduction-direct
                 ledger 'th-identity 'a '((0 a :hyp nil)))))
  (let ((ledger (check-and-extend-by-deduction-direct
                 ledger 'th-ex-falso '(.neg a)
                 '((0 (.neg a) :hyp nil)
                   (1 (.to (.neg a) (.to (.neg b) (.neg a))) :axiom (II.1))
                   (2 (.to (.neg b) (.neg a)) :ir (MP 1 0))
                   (3 (.to (.to (.neg b) (.neg a)) (.to a b)) :axiom (II.3))
                   (4 (.to a b) :ir (MP 3 2))))))
    (expect "TH-EX-FALSO: not-a |- (a -> b), any b"
            (check-k-proof '((0 (.neg C) :hyp nil)
                              (1 (.to (.neg C) (.to C D)) :th-ded (th-ex-falso))
                              (2 (.to C D) :ir (MP 1 0)))
                            ledger)
            t)
    (let ((ledger (check-and-extend-by-deduction-direct
                   ledger 'th-dneg-elim '(.neg (.neg a))
                   '((0 (.neg (.neg a)) :hyp nil)
                     (1 (.to a a) :th-ded (th-identity))
                     (2 (.to (.to a a) (.to (.to (.neg a) a) a)) :axiom (II.4))
                     (3 (.to (.to (.neg a) a) a) :ir (MP 2 1))
                     (4 (.to (.neg (.neg a)) (.to (.neg a) a)) :th-ded (th-ex-falso))
                     (5 (.to (.neg a) a) :ir (MP 4 0))
                     (6 a :ir (MP 3 5))))))
      (expect "TH-DNEG-ELIM: not-not-C |- C"
              (check-k-proof '((0 (.neg (.neg C)) :hyp nil)
                                (1 (.to (.neg (.neg C)) C) :th-ded (th-dneg-elim))
                                (2 C :ir (MP 1 0)))
                              ledger)
              t)
      (let ((ledger (check-and-extend
                     ledger 'th 'th-dneg-intro
                     '((0 (.to (.neg (.neg (.neg a))) (.neg a)) :th-ded (th-dneg-elim))
                       (1 (.to (.to (.neg (.neg (.neg a))) (.neg a)) (.to a (.neg (.neg a)))) :axiom (II.3))
                       (2 (.to a (.neg (.neg a))) :ir (MP 1 0))))))
        (expect "TH-DNEG-INTRO: C |- not-not-C"
                (check-k-proof '((0 C :hyp nil)
                                  (1 (.to C (.neg (.neg C))) :th-ded (th-dneg-intro))
                                  (2 (.neg (.neg C)) :ir (MP 1 0)))
                                ledger)
                t)
        (let* ((ledger (check-and-extend-by-deduction-direct
                        ledger 'th-raa-s1 'a
                        '((0 (.to a b) :hyp nil)
                          (1 (.to a (.neg b)) :hyp nil)
                          (2 a :hyp nil)
                          (3 b :ir (MP 0 2))
                          (4 (.neg b) :ir (MP 1 2))
                          (5 (.to (.neg b) (.to b (.neg a))) :th-ded (th-ex-falso))
                          (6 (.to b (.neg a)) :ir (MP 5 4))
                          (7 (.neg a) :ir (MP 6 3)))))
               (ledger (check-and-extend-by-deduction-direct
                        ledger 'th-raa-s3 '(.to a (.neg b))
                        '((0 (.to a b) :hyp nil)
                          (1 (.to a (.neg b)) :hyp nil)
                          (2 (.to a (.neg a)) :th-ded (th-raa-s1 0 1))
                          (3 (.to (.neg a) (.neg a)) :th-ded (th-identity))
                          (4 (.to (.to a (.neg a)) (.to (.to (.neg a) (.neg a)) (.neg a))) :axiom (II.4))
                          (5 (.to (.to (.neg a) (.neg a)) (.neg a)) :ir (MP 4 2))
                          (6 (.neg a) :ir (MP 5 3)))))
               (ledger (check-and-extend-by-deduction-direct
                        ledger 'th-raa '(.to a b)
                        '((0 (.to a b) :hyp nil)
                          (1 (.to (.to a (.neg b)) (.neg a)) :th-ded (th-raa-s3 0))))))
          (expect "TH-RAA: (C->D) |- ((C-> not-D) -> not-C), fully closed"
                  (check-k-proof '((0 (.to (.to C D) (.to (.to C (.neg D)) (.neg C))) :th-ded (th-raa))) ledger)
                  t)
          (let* ((ledger (check-and-extend-by-deduction-direct
                          ledger 'th-mp-flip '(.to a c)
                          '((0 a :hyp nil)
                            (1 (.to a c) :hyp nil)
                            (2 c :ir (MP 1 0)))))
                 (ledger (check-and-extend-by-deduction-direct
                          ledger 'th-neg-impl '(.neg c)
                          '((0 a :hyp nil)
                            (1 (.neg c) :hyp nil)
                            (2 (.to (.to a c) c) :th-ded (th-mp-flip 0))
                            (3 (.to (.neg c) (.to (.to a c) (.neg c))) :axiom (II.1))
                            (4 (.to (.to a c) (.neg c)) :ir (MP 3 1))
                            (5 (.to (.to (.to a c) c) (.to (.to (.to a c) (.neg c)) (.neg (.to a c)))) :th-ded (th-raa))
                            (6 (.to (.to (.to a c) (.neg c)) (.neg (.to a c))) :ir (MP 5 2))
                            (7 (.neg (.to a c)) :ir (MP 6 4))))))
            (expect "TH-NEG-IMPL: C, not-D |- not(C->D)"
                    (check-k-proof '((0 C :hyp nil)
                                      (1 (.neg D) :hyp nil)
                                      (2 (.to (.neg D) (.neg (.to C D))) :th-ded (th-neg-impl 0))
                                      (3 (.neg (.to C D)) :ir (MP 2 1)))
                                    ledger)
                    t)
            ledger)))))))

(defun run-classical-logic-self-tests ()
  "As RUN-SELF-TESTS, but exercising the classical completeness lemmas
built on top of a plain (non-arithmetic) BOOTSTRAP-KERNEL -- Section 14."
  (let* ((ledger (bootstrap-kernel))
         (ledger (test-classical-logic ledger)))
    (declare (ignorable ledger))
    (format t "~%Classical-logic self-tests complete.~%")))

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

(defun kto? (f) (and (consp f) (eq (car f) '.to) (= (length f) 3)))
(defun kneg? (f) (and (consp f) (eq (car f) '.neg) (= (length f) 2)))

(defun katoms-of (f &optional acc)
  "All atomic (non-.TO, non-.NEG) subformulas of F, deduplicated."
  (cond
    ((kto? f) (katoms-of (third f) (katoms-of (second f) acc)))
    ((kneg? f) (katoms-of (second f) acc))
    (t (adjoin f acc :test #'equal))))

(defun ktruth (f v)
  "Ordinary two-valued truth evaluation of F under valuation V (an alist
atom -> generalized boolean)."
  (cond
    ((kto? f) (or (not (ktruth (second f) v)) (ktruth (third f) v)))
    ((kneg? f) (not (ktruth (second f) v)))
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
  (let* ((name-t (gensym "KT"))
         (name-f (gensym "KF"))
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
TARGET must be built from .TO/.NEG only (propositional; no quantifiers)
and LEDGER must already carry TH-EX-FALSO, TH-DNEG-INTRO, TH-NEG-IMPL
and axiom II.4 -- e.g. a ledger that has replayed 01-propositional-
core.ledger and 05-classical-logic.ledger, or TEST-CLASSICAL-LOGIC's
in-memory equivalent."
  (let* ((atoms (sort (copy-list (katoms-of target)) #'string< :key #'symbol-name)))
    (dolist (v (kall-valuations atoms))
      (unless (ktruth target v)
        (error "PROVE-TAUTOLOGY: ~S is FALSE under ~S -- not a tautology, refusing." target v)))
    (multiple-value-bind (ledger raw) (kalmar-node ledger atoms nil target log)
      (check-and-extend ledger 'th name raw log))))

(defun test-prove-tautology (ledger)
  (let ((hs (list '.to (list '.to 'b 'c) (list '.to (list '.to 'a 'b) (list '.to 'a 'c))))
        (peirce (list '.to (list '.to (list '.to 'a 'b) 'a) 'a))
        (contra (list '.to (list '.to 'a 'b) (list '.to (list '.neg 'b) (list '.neg 'a)))))
    (let ((ledger (prove-tautology ledger hs 'th-hyp-syll-auto)))
      (expect "PROVE-TAUTOLOGY re-derives hypothetical syllogism's tautology automatically"
              (check-k-proof `((0 ,hs :th (th-hyp-syll-auto))) ledger) t)
      (let ((ledger (prove-tautology ledger peirce 'th-peirce-auto)))
        (expect "PROVE-TAUTOLOGY proves Peirce's law, ((A->B)->A)->A, automatically"
                (check-k-proof `((0 ,peirce :th (th-peirce-auto))) ledger) t)
        (let ((ledger (prove-tautology ledger contra 'th-contra-auto)))
          (expect "PROVE-TAUTOLOGY proves contraposition, (A->B)->(not-B->not-A), automatically"
                  (check-k-proof `((0 ,contra :th (th-contra-auto))) ledger) t)
          (expect "PROVE-TAUTOLOGY refuses a genuine non-tautology (A->B alone)"
                  (handler-case (progn (prove-tautology ledger '(.to a b) 'th-bad-auto) :admitted)
                    (error () :refused))
                  :refused)
          ledger)))))

(defun run-tactics-self-tests ()
  "As RUN-SELF-TESTS, but exercising PROVE-TAUTOLOGY on top of a ledger
that already carries the classical lemmas -- Section 15."
  (let* ((ledger (bootstrap-kernel))
         (ledger (test-classical-logic ledger))
         (ledger (test-prove-tautology ledger)))
    (declare (ignorable ledger))
    (format t "~%Tactics self-tests complete.~%")))

;;; ---------------------------------------------------------------------
;;; 16. Alpha-conversion: renaming bound variables, free variables, and
;;;     atomic-wff-symbols throughout an existing ledger entry
;;; ---------------------------------------------------------------------
;;;
;;; Motivation: the kernel deliberately has NO automatic alpha-equivalence.
;;; Formulas are matched purely structurally (EQUAL / MATCH-SCHEMA-ATOMS),
;;; so (.forall v0 A) and (.forall v1 A) are entirely different, unrelated
;;; formulas to CHECK-K-PROOF -- citing THEOREM under a differently-named
;;; bound variable than it was originally proved with simply fails to
;;; match. That is correct, principled behaviour for a structural checker,
;;; not a bug, but it means a person working with the library needs an
;;; explicit, honest way to get "the same theorem, renamed" when they
;;; actually want that.
;;;
;;; Design: never trust the rename itself. Build a candidate raw-proof by
;;; renaming OLD-SYM -> NEW-SYM through every formula, then re-admit it via
;;; the ordinary checked growth functions (CHECK-AND-EXTEND /
;;; CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT / CHECK-AND-EXTEND-ABBREV) exactly
;;; as if it were freshly hand-written. A bad rename -- one that causes
;;; variable capture, or breaks GEN's freshness side-condition partway
;;; through a longer proof -- is simply rejected by the ordinary checker;
;;; nothing new has to be trusted, and the LCF discipline ("always
;;; re-verify") is preserved exactly.
;;;
;;; Two complementary constructs:
;;;
;;;   ALPHA-RENAME-ENTRY   -- general purpose. Renames a symbol (bound
;;;     variable, free variable, OR atomic-wff-symbol -- these are treated
;;;     uniformly, since propositional letters never occupy binder
;;;     position) throughout an EXISTING named entry's stored proof and
;;;     re-admits it under a new name. TRANSITIVE: if the proof cites
;;;     another TH/ITH/TH-DED/DEF-ABBREV entry BY NAME WITH NO ARGUMENTS
;;;     (a "zero-premise" citation, which only checks by exact structural
;;;     match against that entry's own fixed conclusion), and OLD-SYM
;;;     occurs in that dependency's own conclusion too, the dependency is
;;;     recursively alpha-renamed first (memoized, so a dependency shared
;;;     by several lines is only renamed once) and the citation is
;;;     rewritten to point at the renamed copy. A dependency that doesn't
;;;     mention OLD-SYM at all is left cited exactly as before.
;;;
;;;   ALPHA-RENAME-FORALL  -- narrower, axiom-based. Directly constructs
;;;     the general schema-level implication (forall x. A) -> (forall y.
;;;     A[x:=y]) from scratch via III.1 + Gen + MP, discharged through
;;;     CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT, with no pre-existing proof to
;;;     rename. Useful as a standalone renaming LEMMA one can MP against
;;;     any existing (forall x. A) theorem, rather than rebuilding that
;;;     theorem's whole proof under a new name.
;;;
;;; Known limitation: .EXISTS currently has only a formation rule in this
;;; kernel (no existential instantiation/generalization axioms), so there
;;; is no ALPHA-RENAME-EXISTS counterpart to ALPHA-RENAME-FORALL --
;;; ALPHA-RENAME-ENTRY still works on a proof that happens to mention
;;; .EXISTS, since it never needs to prove anything ABOUT .EXISTS itself,
;;; only re-verify the (unchanged) proof that produced it.

(defun rename-symbol-everywhere (old new tree)
  "Literal, unconditional symbol rename through an arbitrary S-expression:
every occurrence of OLD becomes NEW, INCLUDING when OLD sits in binder
head position (e.g. the V0 in (.forall v0 ...)) and including occurrences
below that binder. Deliberately NOT the same operation as SUBSTITUTE-WFF:
substitution must skip under a binder that re-binds the same name (that
name there refers to a different, locally-bound variable, and capture
must be avoided), whereas alpha-conversion renames one specific
bound/free variable or atomic-wff-symbol EVERYWHERE it occurs, including
the binder itself, uniformly and unconditionally through the whole
formula."
  (cond ((eq tree old) new)
        ((consp tree) (cons (rename-symbol-everywhere old new (car tree))
                             (rename-symbol-everywhere old new (cdr tree))))
        (t tree)))

(defun find-named-entry (ledger name)
  "Most recent (highest-K) ITH/TH/DEF-ABBREV/TH-DED entry citable under
NAME, or NIL. Uses the same by-name index (LEDGER-BY-DERIVED-NAME) and
backtracking-friendly TREAP-VALUES-BELOW lookup that citation checking and
DERIVED-RULE-NAME-TAKEN-P already rely on internally."
  (let ((candidates (treap-values-below (alist-get (ledger-by-derived-name ledger) name) (ledger-bound ledger))))
    (car (sort (copy-list candidates) #'> :key #'entry-k))))

(defun entry-public-formula (e)
  "The single formula an entry is 'known by' when cited with no extra
arguments: a TH/ITH's stored conclusion, a TH-DED's (hyp -> conclusion),
or a DEF-ABBREV's definiens. NIL for entries with no such notion (e.g.
AXIOM, IRULE)."
  (case (entry-kind e)
    ((th ith)
     (destructuring-bind (name raw-proof) (entry-payload e)
       (declare (ignore name))
       (proof-conclusion raw-proof)))
    (th-ded
     (destructuring-bind (name hyp-formula raw-proof) (entry-payload e)
       (declare (ignore name))
       (list '.to hyp-formula (proof-conclusion raw-proof))))
    (def-abbrev
     (destructuring-bind (name raw-proof) (entry-payload e)
       (declare (ignore name))
       (proof-conclusion raw-proof)))
    (t nil)))

(defun alpha-dep-name (old-name old-sym new-sym)
  "Deterministic derived name for an auto-renamed transitive dependency,
so re-running the same rename twice reuses the same auxiliary entry
rather than growing the ledger unboundedly."
  (intern (format nil "~A|~A->~A" old-name old-sym new-sym) (symbol-package old-name)))

(defun rename-raw-proof-transitively (ledger raw-proof old-sym new-sym memo log)
  "Renames OLD-SYM -> NEW-SYM through every formula of RAW-PROOF. For any
:TH/:ITH/:TH-DED/:DEF-ABBREV citation whose cited entry's PUBLIC formula
contains OLD-SYM, recursively alpha-renames that dependency first (via
ALPHA-RENAME-ENTRY-1, memoized in MEMO) and rewrites the citation to the
renamed name; a dependency not mentioning OLD-SYM is cited unchanged.
:AXIOM/:IR citation arguments (schema instantiation formulas / MP-or-Gen
line numbers and variables) are renamed directly since they are never
entry names. Returns (values possibly-extended-ledger renamed-raw-proof)."
  (let ((ledger ledger))
    (let ((new-lines
            (mapcar
             (lambda (line)
               (destructuring-bind (num formula role by) line
                 (list num
                       (rename-symbol-everywhere old-sym new-sym formula)
                       role
                       (case role
                         ((:axiom :ir)
                          (cons (car by) (mapcar (lambda (x) (rename-symbol-everywhere old-sym new-sym x)) (cdr by))))
                         ((:th :ith :th-ded :def-abbrev)
                          (if (null by)
                              by
                              (multiple-value-bind (ledger2 final-name)
                                  (alpha-rename-entry-1 ledger (car by) old-sym new-sym memo log)
                                (setf ledger ledger2)
                                (cons final-name (cdr by)))))
                         (t by)))))
             raw-proof)))
      (values ledger new-lines))))

(defun alpha-rename-entry-1 (ledger old-name old-sym new-sym memo log)
  "Internal worker for transitive dependency renaming, called by
RENAME-RAW-PROOF-TRANSITIVELY. Returns (values new-ledger name-to-cite).
If OLD-NAME's entry doesn't mention OLD-SYM (or isn't a
TH/ITH/TH-DED/DEF-ABBREV at all -- e.g. names an :AXIOM or :IRULE, which
are cited differently), it's returned unchanged. Memoized on OLD-NAME so a
dependency shared by several lines or entries is renamed only once."
  (multiple-value-bind (cached found) (gethash old-name memo)
    (when found (return-from alpha-rename-entry-1 (values ledger cached))))
  (let ((e (find-named-entry ledger old-name)))
    (unless e
      (error "ALPHA-RENAME-ENTRY: no ITH/TH/DEF-ABBREV/TH-DED entry named ~S." old-name))
    (unless (and (member (entry-kind e) '(th ith th-ded def-abbrev))
                 (symbol-occurs-p old-sym (entry-public-formula e)))
      (setf (gethash old-name memo) old-name)
      (return-from alpha-rename-entry-1 (values ledger old-name)))
    (let ((new-name (alpha-dep-name old-name old-sym new-sym)))
      (when (find-named-entry ledger new-name)
        (setf (gethash old-name memo) new-name)
        (return-from alpha-rename-entry-1 (values ledger new-name)))
      ;; Bind before recursing: harmless even in the (currently impossible,
      ;; ledger is append-only/acyclic) case of a citation cycle.
      (setf (gethash old-name memo) new-name)
      (case (entry-kind e)
        ((th ith)
         (destructuring-bind (name raw-proof) (entry-payload e)
           (declare (ignore name))
           (multiple-value-bind (ledger2 renamed-proof)
               (rename-raw-proof-transitively ledger raw-proof old-sym new-sym memo log)
             (values (check-and-extend ledger2 (entry-kind e) new-name renamed-proof log) new-name))))
        (th-ded
         (destructuring-bind (name hyp-formula raw-proof) (entry-payload e)
           (declare (ignore name))
           (multiple-value-bind (ledger2 renamed-proof)
               (rename-raw-proof-transitively ledger raw-proof old-sym new-sym memo log)
             (values (check-and-extend-by-deduction-direct
                      ledger2 new-name (rename-symbol-everywhere old-sym new-sym hyp-formula)
                      renamed-proof log)
                     new-name))))
        (def-abbrev
         (destructuring-bind (name raw-proof) (entry-payload e)
           (declare (ignore name))
           (multiple-value-bind (ledger2 renamed-proof)
               (rename-raw-proof-transitively ledger raw-proof old-sym new-sym memo log)
             (values (check-and-extend-abbrev ledger2 new-name (proof-conclusion renamed-proof) renamed-proof log)
                     new-name))))))))

(defun symbol-occurs-p (sym tree)
  "T if SYM occurs anywhere in TREE (an arbitrary S-expression)."
  (cond ((eq tree sym) t)
        ((consp tree) (or (symbol-occurs-p sym (car tree)) (symbol-occurs-p sym (cdr tree))))
        (t nil)))

(defun alpha-rename-entry (ledger old-name new-name old-sym new-sym &optional (log (silent-log)))
  "Public entry point. Renames OLD-SYM -> NEW-SYM (a bound variable, a
free variable, or an atomic-wff-symbol -- all handled uniformly by
RENAME-SYMBOL-EVERYWHERE) throughout OLD-NAME's stored proof and
re-admits the result under NEW-NAME, transitively renaming any dependency
that needs it (see section header). Fully re-verified via the ordinary
checked growth functions; a rename that causes capture or an invalid
proof step is simply rejected by the checker, exactly like any other
malformed submission."
  (let ((e (find-named-entry ledger old-name)))
    (unless e
      (error "ALPHA-RENAME-ENTRY: no ITH/TH/DEF-ABBREV/TH-DED entry named ~S." old-name))
    (unless (member (entry-kind e) '(th ith th-ded def-abbrev))
      (error "ALPHA-RENAME-ENTRY: ~S names a ~S entry, not ITH/TH/DEF-ABBREV/TH-DED." old-name (entry-kind e)))
    (let ((memo (make-hash-table :test #'eq)))
      (case (entry-kind e)
        ((th ith)
         (destructuring-bind (name raw-proof) (entry-payload e)
           (declare (ignore name))
           (multiple-value-bind (ledger2 renamed-proof)
               (rename-raw-proof-transitively ledger raw-proof old-sym new-sym memo log)
             (check-and-extend ledger2 (entry-kind e) new-name renamed-proof log))))
        (th-ded
         (destructuring-bind (name hyp-formula raw-proof) (entry-payload e)
           (declare (ignore name))
           (multiple-value-bind (ledger2 renamed-proof)
               (rename-raw-proof-transitively ledger raw-proof old-sym new-sym memo log)
             (check-and-extend-by-deduction-direct
              ledger2 new-name (rename-symbol-everywhere old-sym new-sym hyp-formula)
              renamed-proof log))))
        (def-abbrev
         (destructuring-bind (name raw-proof) (entry-payload e)
           (declare (ignore name))
           (multiple-value-bind (ledger2 renamed-proof)
               (rename-raw-proof-transitively ledger raw-proof old-sym new-sym memo log)
             (check-and-extend-abbrev ledger2 new-name (proof-conclusion renamed-proof) renamed-proof log))))))))

(defun alpha-rename-forall (ledger x y a name &optional (log (silent-log)))
  "Standalone, axiom-based construction of the general schema-level
theorem (forall x. A) -> (forall y. A[x:=y]), built directly from III.1 +
Gen + MP via the deduction-direct discharge mechanism, with no
pre-existing proof to rename. (Y must be fresh for A per III.1's own side
condition and Gen's freshness condition against the open hypothesis
(forall x. A); the checker rejects the construction outright if not --
e.g. if Y already occurs free in A, renaming X to Y would capture it.)"
  (check-and-extend-by-deduction-direct
   ledger name (list '.forall x a)
   `((0 (.forall ,x ,a) :hyp nil)
     (1 (.to (.forall ,x ,a) ,(substitute-wff x y a)) :axiom (III.1 ,y))
     (2 ,(substitute-wff x y a) :ir (MP 1 0))
     (3 (.forall ,y ,(substitute-wff x y a)) :ir (Gen 2 ,y)))
   log))

(defun test-alpha-conversion (ledger)
  "Exercises ALPHA-RENAME-ENTRY (on TH, TH-DED-derived TH, and DEF-ABBREV
entries, including the transitive-dependency case) and ALPHA-RENAME-FORALL,
plus both intended failure modes (name collision, capture attempt). LEDGER
must already carry Peano arithmetic and TH-ZERO-PLUS-IDENTITY (Section 13)."
  ;; The concrete motivating example: TH-ZERO-PLUS-IDENTITY was proved with
  ;; bound variable V0; citing it under V1 must fail (no auto-alpha), but
  ;; ALPHA-RENAME-ENTRY can mechanically produce the V1 version, re-verified
  ;; from scratch -- including transitively renaming TH-ZERO-PLUS-STEP,
  ;; which TH-ZERO-PLUS-IDENTITY cites by name with no arguments and whose
  ;; own induction hypothesis also mentions V0.
  (expect "citing TH-ZERO-PLUS-IDENTITY under the wrong bound-variable name (V1) fails, as expected (no auto-alpha)"
          (check-k-proof '((0 (.forall v1 (.eq (+ zero v1) v1)) :th (th-zero-plus-identity))) ledger)
          nil)
  (let ((ledger (alpha-rename-entry ledger 'th-zero-plus-identity 'th-zero-plus-identity-v1 'v0 'v1)))
    (expect "ALPHA-RENAME-ENTRY: renamed TH-ZERO-PLUS-IDENTITY-V1 is citable, and now matches under V1"
            (check-k-proof '((0 (.forall v1 (.eq (+ zero v1) v1)) :th (th-zero-plus-identity-v1))) ledger)
            t)
    (expect "...while the original TH-ZERO-PLUS-IDENTITY (bound V0) is untouched and still citable"
            (check-k-proof '((0 (.forall v0 (.eq (+ zero v0) v0)) :th (th-zero-plus-identity))) ledger)
            t)
    ;; def-abbrev path, with the same transitive V0 dependency.
    (let* ((ledger (check-and-extend-abbrev
                    ledger 'my-zero-identity-abbrev '(.forall v0 (.eq (+ zero v0) v0))
                    '((0 (.forall v0 (.eq (+ zero v0) v0)) :th (th-zero-plus-identity)))))
           (ledger (alpha-rename-entry ledger 'my-zero-identity-abbrev 'my-zero-identity-abbrev-v1 'v0 'v1)))
      (expect "ALPHA-RENAME-ENTRY on a DEF-ABBREV entry: renamed abbrev is citable under V1"
              (check-k-proof '((0 (.forall v1 (.eq (+ zero v1) v1)) :def-abbrev (my-zero-identity-abbrev-v1))) ledger)
              t)
      ;; atomic-wff-symbol renaming (propositional letter, not a variable).
      (let* ((ledger (check-and-extend ledger 'th 'th-tiny-k '((0 (.to A (.to B A)) :axiom (II.1)))))
             (ledger (alpha-rename-entry ledger 'th-tiny-k 'th-tiny-k-g 'a 'g)))
        (expect "ALPHA-RENAME-ENTRY on an atomic-wff-symbol (A -> G, a propositional letter, not a variable)"
                (check-k-proof '((0 (.to G (.to B G)) :th (th-tiny-k-g))) ledger)
                t)
        ;; ALPHA-RENAME-FORALL: a standalone renaming lemma, usable via MP
        ;; against any (forall v0 ...) theorem, without rebuilding its proof.
        (let ((ledger (alpha-rename-forall ledger 'v0 'v1 '(.eq (+ zero v0) v0) 'th-forall-rename-v0-v1)))
          (expect "ALPHA-RENAME-FORALL builds (forall v0 A)->(forall v1 A[v0:=v1]) as a real, re-citable theorem"
                  (check-k-proof
                   '((0 (.to (.forall v0 (.eq (+ zero v0) v0)) (.forall v1 (.eq (+ zero v1) v1)))
                        :th (th-forall-rename-v0-v1)))
                   ledger)
                  t)
          (expect "...and it actually composes via MP against TH-ZERO-PLUS-IDENTITY to reprove the V1 form"
                  (check-k-proof
                   '((0 (.forall v0 (.eq (+ zero v0) v0)) :th (th-zero-plus-identity))
                     (1 (.to (.forall v0 (.eq (+ zero v0) v0)) (.forall v1 (.eq (+ zero v1) v1)))
                        :th (th-forall-rename-v0-v1))
                     (2 (.forall v1 (.eq (+ zero v1) v1)) :ir (MP 1 0)))
                   ledger)
                  t)
          ;; Attack 1: NEW-NAME collides with an already-used name -- must
          ;; be refused by the ordinary CHECK-AND-EXTEND name-collision
          ;; guard, not silently overwrite or shadow the existing entry.
          (expect "attack: ALPHA-RENAME-ENTRY refuses a NEW-NAME that collides with an existing entry"
                  (handler-case (progn (alpha-rename-entry ledger 'th-zero-plus-identity 'th-identity 'v0 'v1) :admitted)
                    (error () :refused))
                  :refused)
          ;; Attack 2: ALPHA-RENAME-FORALL where Y is not actually fresh
          ;; for A (Y already occurs free in A) -- renaming X to Y would
          ;; capture it, so III.1's own side condition must reject this.
          (expect "attack: ALPHA-RENAME-FORALL refuses a capturing rename (Y already free in A)"
                  (handler-case
                      (progn (alpha-rename-forall ledger 'v0 'v1 '(.exists v1 (.eq v0 v1)) 'th-bad-capture) :admitted)
                    (error () :refused))
                  :refused)
          ledger)))))

(defun run-alpha-conversion-self-tests ()
  "As RUN-SELF-TESTS, but against a BOOTSTRAP-KERNEL :ARITHMETIC T ledger
carrying Peano arithmetic and TH-ZERO-PLUS-IDENTITY -- Section 16."
  (let* ((ledger (bootstrap-kernel :arithmetic t))
         (ledger (test-equality-axioms ledger))
         (ledger (test-peano-axioms ledger))
         (ledger (test-peano-induction-proof ledger))
         (ledger (test-alpha-conversion ledger)))
    (declare (ignorable ledger))
    (format t "~%Alpha-conversion self-tests complete.~%")))

;;; ---------------------------------------------------------------------
;;; 17. Differential check for the optional DERIVED-entry memoization
;;;     layer (see the "Optional memoization" subsection right before
;;;     TRY-DERIVED-ENTRY, Section 6)
;;; ---------------------------------------------------------------------
;;;
;;; Confirms VERIFY-DERIVED-INSTANTIATION's cache changes no verdict --
;;; only how fast it's reached -- on exactly the pathological citation
;;; pattern that motivated it: a "doubling chain" of TH entries, each of
;;; whose 2-line proof cites the previous THEOREM twice (redundantly),
;;; which costs 2^depth work to verify without memoization even though
;;; every formula involved is purely propositional (.to A (.to B A)) via
;;; a single axiom, with no quantifiers and no side conditions anywhere
;;; -- demonstrating that the re-verification cost this section addresses
;;; comes from DERIVED-entry citation, not from side-condition checking
;;; (see the README's discussion of this distinction).

(defun build-doubling-chain (n &optional (prefix "THDBL"))
  "N TH entries T_0..T_(n-1), all proving (.to A (.to B A)) via axiom
II.1; T_0 cites the axiom directly, and every T_i (i>0) cites T_(i-1)
TWICE (two separate, redundant lines) -- the worst case for a checker
with no memoization."
  (let ((ledger (bootstrap-kernel))
        (concl '(.to A (.to B A))))
    (setf ledger (check-and-extend ledger 'th (intern (format nil "~A0" prefix))
                                    (list (list 0 concl :axiom (list 'II.1)))))
    (loop for i from 1 below n
          for prev = (intern (format nil "~A~D" prefix (1- i)))
          do (setf ledger
                   (check-and-extend ledger 'th (intern (format nil "~A~D" prefix i))
                                      (list (list 0 concl :th (list prev))
                                            (list 1 concl :th (list prev))))))
    ledger))

(defun test-derived-entry-memoization ()
  "Builds the doubling chain at a depth deep enough to matter but
shallow enough that a memoization-OFF run still finishes in a self-
test's time budget, checks it both ways, and confirms IDENTICAL verdicts
-- the cache changes nothing about what is accepted. Then pushes
memoization ON alone to a depth (2^60 worth of naive work) that would be
entirely infeasible without it, to demonstrate the actual point."
  (disable-derived-entry-memoization)
  (let* ((depth 16)
         (ledger (build-doubling-chain depth))
         (goal (list (list 0 '(.to A (.to B A)) :th (list (intern (format nil "THDBL~D" (1- depth)))))))
         (t0 (get-internal-real-time))
         (verdict-off (check-k-proof goal ledger))
         (t1 (get-internal-real-time)))
    (format t "  [memo off] doubling-chain depth ~D: ~A in ~,3Fs~%"
            depth verdict-off (/ (- t1 t0) (float internal-time-units-per-second)))
    (enable-derived-entry-memoization)
    (let* ((ledger2 (build-doubling-chain depth "THDBL2"))
           (goal2 (list (list 0 '(.to A (.to B A)) :th (list (intern (format nil "THDBL2~D" (1- depth)))))))
           (t2 (get-internal-real-time))
           (verdict-on (check-k-proof goal2 ledger2))
           (t3 (get-internal-real-time)))
      (format t "  [memo on ] doubling-chain depth ~D: ~A in ~,3Fs~%"
              depth verdict-on (/ (- t3 t2) (float internal-time-units-per-second)))
      (expect "memoization changes no verdict: same doubling-chain, on vs off"
              (eq verdict-off verdict-on) t)
      (expect "memoization ON: the doubling-chain checks out (T)" verdict-on t))
    (reset-derived-entry-memoization)
    (let* ((deep 60)
           (ledger3 (build-doubling-chain deep "THDBL3"))
           (goal3 (list (list 0 '(.to A (.to B A)) :th (list (intern (format nil "THDBL3~D" (1- deep)))))))
           (t4 (get-internal-real-time))
           (verdict-deep (check-k-proof goal3 ledger3))
           (t5 (get-internal-real-time)))
      (format t "  [memo on ] doubling-chain depth ~D (2^~D work if unmemoized): ~A in ~,3Fs~%"
              deep deep verdict-deep (/ (- t5 t4) (float internal-time-units-per-second)))
      (expect "memoization ON: a depth utterly infeasible without it still checks out (T)" verdict-deep t))
    (disable-derived-entry-memoization)))

(defun run-derived-entry-memoization-self-tests ()
  "As RUN-SELF-TESTS, but exercising the optional memoization layer --
Section 17. Leaves memoization OFF when done, so it never silently
changes behaviour for anything that runs after it (including every other
RUN-*-SELF-TESTS call in this same trailing auto-run form)."
  (test-derived-entry-memoization)
  (format t "~%Derived-entry memoization self-tests complete.~%"))

;;; ---------------------------------------------------------------------
;;; 18. Describing a whole system (not just its theorems) as a file
;;; ---------------------------------------------------------------------
;;;
;;; Everything BOOTSTRAP-KERNEL admits is already, internally, plain data:
;;; a TERM?/WFF? formation rule is (NAME CONDITIONS RESULT-PATTERN), an
;;; AXIOM is (NAME CONDITIONS (EXTRA-PARAM-PATTERNS CONCLUSION-PATTERN)),
;;; an IRULE is (NAME CONDITIONS (PREMISE-PATTERNS EXTRA-PARAM-PATTERNS
;;; :=> CONCLUSION-PATTERN)) -- see BOOTSTRAP-KERNEL's own body, Section 7.
;;; The only reason a DIFFERENT logical system has meant editing this
;;; Lisp file up to now is that those literals are hand-written directly
;;; into BOOTSTRAP-KERNEL's source. This section externalizes exactly
;;; that data into a file format -- a SYSTEM SPEC -- read the same
;;; READ-based way a .ledger module already is (Section 10), and
;;; interpreted by BOOTSTRAP-KERNEL-FROM-SPEC below.
;;;
;;; A system-spec command is one of:
;;;   (:atomic-wff-symbols SYM...)
;;;   (:variable-symbols SYM...)
;;;   (:term-formation NAME CONDITIONS RESULT-PATTERN)
;;;   (:wff-formation   NAME CONDITIONS RESULT-PATTERN)
;;;   (:axiom NAME CONDITIONS (EXTRA-PARAM-PATTERNS CONCLUSION-PATTERN))
;;;   (:irule NAME CONDITIONS (PREMISE-PATTERNS EXTRA-PARAM-PATTERNS
;;;                            :=> CONCLUSION-PATTERN))
;;;
;;; CONDITIONS/patterns may freely use VAR?/WFF?/TERM? and any existing
;;; meta-predicate/meta-constructor (@SUBST, @SUBST-OK?, @NOT-FREE-IN?,
;;; @NOT-FREE-IN-DEPENDENCIES?, ...) by name -- the SAME fixed, closed
;;; catalog CHECK-CONDITION/MATCH-TEMPLATE already dispatch on (Section
;;; 3/4). A spec file can freely ASSEMBLE a new system out of that
;;; vocabulary (a different propositional basis, a different quantifier
;;; theory, brand-new connective/relation syntax such as a modal .BOX),
;;; but it cannot introduce a genuinely NEW meta-predicate -- one backed
;;; by new Lisp code -- from data alone; that remains a kernel-source-
;;; level extension, same as always.
;;;
;;; THE CRITICAL DIFFERENCE FROM A .LEDGER MODULE FILE, stated plainly:
;;; a .ledger file's THEOREMS are independently re-verified by CHECK-K-
;;; PROOF on every load, so a corrupted or dishonest .ledger file can at
;;; worst fail to load -- it can never smuggle in something false (see
;;; Section 10's own header). A system-spec file is not like that. It
;;; mints entries with ORIGIN = :PRIMITIVE -- admitted by fiat, exactly
;;; as BOOTSTRAP-KERNEL's own hardcoded axioms are, with NOTHING to check
;;; them against. Loading a system-spec file is not verification; it is
;;; an act of trust in whoever wrote it, in exactly the same sense that
;;; reading and trusting BOOTSTRAP-KERNEL's own Lisp source already was.
;;; An inconsistent axiom set (e.g. one that lets a WFF and its own
;;; negation both be proved) is not something CHECK-K-PROOF can detect
;;; from inside the system it defines -- that is Goedel's second
;;; incompleteness theorem, not a gap in this checker. What DOES stay
;;; true, and matters just as much here as anywhere else in this file:
;;; BOOTSTRAP-KERNEL-FROM-SPEC is the only function that can turn a spec
;;; command into a :PRIMITIVE entry (its own private LABELS-bound ADMIT,
;;; exactly like BOOTSTRAP-KERNEL's -- see Section 2's ADMIT-PRIMITIVE
;;; commentary), so loading a spec file is at least as auditable an act
;;; as calling BOOTSTRAP-KERNEL was: everything downstream of it (every
;;; :DERIVED theorem built on top) is still fully, independently
;;; re-verified against whatever the spec turned out to admit.

(defun bootstrap-kernel-from-spec (spec &key (atomic-symbols '(A B C D E F G H))
                                              (variables '(v0 v1 v2 v3 v4 v5))
                                              (ledger nil))
  "Builds a ledger by interpreting SPEC (a list of system-spec commands,
see the section header) instead of BOOTSTRAP-KERNEL's own hardcoded
axiom/rule literals. LEDGER, when supplied, is the starting point (an
already-bootstrapped-or-spec-built ledger) SPEC's commands are admitted
onto -- this is how a base system-spec file (say, propositional +
predicate + equality) and an add-on one (say, Peano arithmetic's
vocabulary and axioms) chain into a single growing PRIMITIVE base, the
same way READ-LEDGER-FROM-FILE's :LEDGER argument chains .ledger MODULE
files together (Section 10) -- except everything admitted here is
:PRIMITIVE, not :DERIVED, so nothing is or could be re-verified: see the
section header's trust-model note. When LEDGER is NIL, a fresh EMPTY-
LEDGER is seeded with ATOMIC-SYMBOLS/VARIABLES first, exactly as
BOOTSTRAP-KERNEL's own first two ADMIT-EACH calls do."
  (labels ((admit (ledger kind payload)
             "Mirrors BOOTSTRAP-KERNEL's own private ADMIT exactly (see
Section 2/7): the only two places in this whole file able to create a
:PRIMITIVE-origin entry are this LABELS binding and BOOTSTRAP-KERNEL's
own, neither reachable from outside its own lexical scope."
             (ledger-append ledger kind payload (list :primitive)))
           (admit-each (ledger kind syms)
             (if (null syms)
                 ledger
                 (admit-each (admit ledger kind (car syms)) kind (cdr syms)))))
    (let ((ledger (or ledger
                       (admit-each (admit-each (empty-ledger) 'atomic-wff-symbol atomic-symbols)
                                   'variable-symbol variables))))
      (dolist (cmd spec ledger)
        (setf ledger
              (case (car cmd)
                (:atomic-wff-symbols (admit-each ledger 'atomic-wff-symbol (cdr cmd)))
                (:variable-symbols (admit-each ledger 'variable-symbol (cdr cmd)))
                (:term-formation (destructuring-bind (name conditions result-pattern) (cdr cmd)
                                    (admit ledger 'term? (list name conditions result-pattern))))
                (:wff-formation (destructuring-bind (name conditions result-pattern) (cdr cmd)
                                   (admit ledger 'wff? (list name conditions result-pattern))))
                (:axiom (destructuring-bind (name conditions form) (cdr cmd)
                          (admit ledger 'axiom (list name conditions form))))
                (:irule (destructuring-bind (name conditions form) (cdr cmd)
                          (admit ledger 'irule (list name conditions form))))
                (t (error "BOOTSTRAP-KERNEL-FROM-SPEC: unknown system-spec command ~S" cmd))))))))

(defun read-system-spec-from-file (path)
  "Reads PATH as a flat list of system-spec commands (plain S-expressions,
one or more per file, read back exactly as WRITE-COMMANDS-TO-FILE-style
tooling would write them) -- the same *PACKAGE*-bound READ loop
READ-LEDGER-FROM-FILE uses for .ledger MODULE files (Section 10), so
symbols like A, v0, .forall print and read back identically."
  (let ((*package* (find-package :ledger-kernel)))
    (with-open-file (in path :direction :input)
      (loop for form = (read in nil :eof)
            until (eq form :eof)
            collect form))))

(defun bootstrap-kernel-from-spec-file (path &key (atomic-symbols '(A B C D E F G H))
                                                   (variables '(v0 v1 v2 v3 v4 v5))
                                                   (ledger nil))
  "READ-SYSTEM-SPEC-FROM-FILE plus BOOTSTRAP-KERNEL-FROM-SPEC in one call
-- the system-spec analogue of READ-LEDGER-FROM-FILE."
  (bootstrap-kernel-from-spec (read-system-spec-from-file path)
                               :atomic-symbols atomic-symbols :variables variables :ledger ledger))

(defun test-bootstrap-from-spec ()
  "Loads hilbert-library/00-classical-fol-equality.system (the exact same
formation rules / MP / Gen / II.1-4 / III.1-2 / IV.1-4 BOOTSTRAP-KERNEL's
own Lisp source hardcodes, now expressed purely as data) chained with
hilbert-library/00-peano-arithmetic.system (likewise mirroring
BOOTSTRAP-PEANO-VOCABULARY/BOOTSTRAP-PEANO-AXIOMS), and confirms the
result is the SAME ledger BOOTSTRAP-KERNEL's hardcoded :ARITHMETIC T path
produces: not just \"behaves the same on a few checks\", but entry for
entry, the same (KIND PAYLOAD ORIGIN) content in the same K order (a
straight EQUALP of the two LEDGER structs would NOT be meaningful here,
and deliberately isn't what's checked -- TREAP-INSERT assigns each node a
RANDOM balancing priority, so two ledgers built by separate sequences of
inserts, however identical their logical content, almost certainly end
up as different tree SHAPES internally; comparing entries in K-order
instead checks exactly the thing that actually matters here and nothing
about incidental internal representation). Then, for good measure,
re-runs a representative slice of Section 9's own hardcoded-bootstrap
self-test battery against the spec-loaded ledger unchanged -- the very
same TEST-* functions, looking for the very same things, now aimed at a
ledger this file's author never hand-wrote a single AXIOM/IRULE form
for."
  (let ((hardcoded (bootstrap-kernel :arithmetic t))
        (from-spec (bootstrap-kernel-from-spec-file
                    "hilbert-library/00-peano-arithmetic.system"
                    :ledger (bootstrap-kernel-from-spec-file
                             "hilbert-library/00-classical-fol-equality.system"))))
    (flet ((entry-content-list (ledger)
             (mapcar (lambda (e) (list (entry-kind e) (entry-payload e) (entry-origin e)))
                     (treap-values-below (ledger-all ledger) (ledger-bound ledger)))))
      (expect "a system-spec-loaded ledger has IDENTICAL entries, in the identical order, to BOOTSTRAP-KERNEL's own hardcoded one"
              (equal (entry-content-list hardcoded) (entry-content-list from-spec)) t))
    (let* ((ledger from-spec)
           (ledger (test-basic-formation ledger))
           (ledger (test-axiom-and-inference ledger))
           (ledger (test-vacuous-gen-and-bad-ith ledger))
           (ledger (test-admit-primitive-closed ledger))
           (ledger (test-sigma-growth ledger))
           (ledger (test-abbrev-usage ledger))
           (ledger (test-axiom-iii1 ledger))
           (ledger (test-hyp-wellformedness ledger))
           (ledger (test-exists-formation ledger))
           (ledger (test-negation-and-new-axioms ledger))
           (ledger (test-name-uniqueness ledger))
           (ledger (test-deduction-theorem ledger))
           (ledger (test-deduction-theorem-direct ledger))
           (ledger (test-equality-axioms ledger))
           (ledger (test-peano-axioms ledger))
           (ledger (test-peano-induction-proof ledger)))
      (declare (ignorable ledger))
      ledger)))

(defun run-bootstrap-from-spec-self-tests ()
  "As RUN-SELF-TESTS, but against a ledger built entirely from the
system-spec files -- Section 18."
  (test-bootstrap-from-spec)
  (format t "~%Bootstrap-from-spec self-tests complete.~%"))

;;; ---------------------------------------------------------------------
;;; 19. IOTA (definite description): formation, III.3 (existential
;;;     generalization), a worked uniqueness derivation, and the IOTA
;;;     irule itself -- plus attack tests.
;;;
;;; What this gives you: given (a) a proof of (.exists ?x ?A) and (b) a
;;; proof that "any two things satisfying A are equal" (curried, since
;;; there is no AND connective: (.forall ?y (.forall ?z (.to A[y/x] (.to
;;; A[z/x] (.eq ?y ?z)))))), the IOTA irule concludes A[(.iota ?x ?A)/?x]
;;; -- the iota-term itself satisfies A. Concretely worked below: from
;;; exists v0(v0=v1) and "any two things equal to v1 are equal to each
;;; other", conclude (.iota v0 (.eq v0 v1)) = v1 -- i.e. "the x such that
;;; x=v1" behaves exactly as v1 itself does, without ever requiring v1 be
;;; produced as a syntactically distinguished witness.
;;;
;;; What this deliberately still does NOT give you (see Section 7's own
;;; commentary on III.3/IOTA for the reasoning): no general definitional
;;; mechanism that lets you write "let y := the x such that A(x)" and
;;; have y become a fresh, reusable name -- every use of (.iota ?x ?A)
;;; must independently re-cite BOTH an existence and a uniqueness proof
;;; for that exact A; no total/junk-value convention for when uniqueness
;;; fails (this kernel simply never lets you apply IOTA without proving
;;; it first, sidestepping the question rather than answering it); and
;;; still no full existential ELIMINATION/instantiation rule (III.3 only
;;; ever INTRODUCES .EXISTS from a witness, it never lets you extract one
;;; back out of an already-proven .EXISTS).

(defun test-iota-formation (ledger)
  "(.iota x A) forms as a TERM (via ITOA-TERM) but never as a WFF -- it is
a description of AN OBJECT ('the x such that A'), not a proposition."
  (expect "(.iota v0 (.eq v0 v1)) is a term" (judgement? 'term? '(.iota v0 (.eq v0 v1)) ledger) t)
  (expect "(.iota v0 (.eq v0 v1)) is NOT a wff" (judgement? 'wff? '(.iota v0 (.eq v0 v1)) ledger) nil)
  (expect "(.eq (.iota v0 (.eq v0 v1)) v1) IS a wff (iota-term used as an ordinary term argument)"
          (judgement? 'wff? '(.eq (.iota v0 (.eq v0 v1)) v1) ledger) t)
  ledger)

(defun test-axiom-iii3 (ledger)
  "III.3: A[t/x] -> exists x. A, unconditional (no Gen-style freshness
side condition -- see its own commentary in BOOTSTRAP-AXIOMS for why
that's sound). EXTRA-PARAM-PATTERNS are (?x ?A ?t), NOT just (?t) like
III.1 -- ?x/?A must be supplied directly since the binder here sits in
the CONSEQUENT while @subst sits in the ANTECEDENT (MATCH-TEMPLATE
processes antecedent before consequent, so ?x/?A can't be left to bind
structurally the way III.1's own (.forall ?x ?A) antecedent does)."
  (expect "III.3: v1=v1 -> exists v0(v0=v1)"
          (check-k-proof '((0 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1))) :axiom (III.3 v0 (.eq v0 v1) v1))) ledger)
          t)
  (let ((ledger (check-and-extend ledger 'th 'th-exists-v0-eq-v1
                                   '((0 (.eq v1 v1) :axiom (IV.1))
                                     (1 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1))) :axiom (III.3 v0 (.eq v0 v1) v1))
                                     (2 (.exists v0 (.eq v0 v1)) :ir (MP 1 0)))
                                   (silent-log))))
    (expect "TH-EXISTS-V0-EQ-V1 is a real, re-citable ledger theorem"
            (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :th (th-exists-v0-eq-v1))) ledger) t)
    (expect "Attack: III.3 with a MISMATCHED extra-arg t (v2 instead of v1) -- must reject"
            (check-k-proof '((0 (.to (.eq v1 v1) (.exists v0 (.eq v0 v1))) :axiom (III.3 v0 (.eq v0 v1) v2))) ledger)
            nil)
    ledger))

(defun test-iota-irule (ledger)
  "The full worked example: derive UNIQ-FULL (any two things equal to v1
are equal to each other, i.e. |- forall v2 forall v3 (v2=v1 -> (v3=v1 ->
v2=v3))) via the same multi-step deduction-theorem-direct chaining
pattern 05-classical-logic.ledger already uses for TH-RAA, then cite it
alongside TH-EXISTS-V0-EQ-V1 as IOTA's two premises to conclude
(.iota v0 (.eq v0 v1)) = v1."
  (let* ((inner '((0 (.eq v2 v1) :hyp nil)
                  (1 (.eq v3 v1) :hyp nil)
                  (2 (.to (.eq v3 v1) (.eq v1 v3)) :axiom (IV.3))
                  (3 (.eq v1 v3) :ir (MP 2 1))
                  (4 (.to (.eq v2 v1) (.to (.eq v1 v3) (.eq v2 v3))) :axiom (IV.4))
                  (5 (.to (.eq v1 v3) (.eq v2 v3)) :ir (MP 4 0))
                  (6 (.eq v2 v3) :ir (MP 5 3))))
         (ledger (check-and-extend-by-deduction-direct ledger 'uniq-step1 '(.eq v3 v1) inner (silent-log)))
         (step2 '((0 (.eq v2 v1) :hyp nil)
                  (1 (.to (.eq v3 v1) (.eq v2 v3)) :th-ded (uniq-step1 0))))
         (ledger (check-and-extend-by-deduction-direct ledger 'uniq-step2 '(.eq v2 v1) step2 (silent-log)))
         (ledger (check-and-extend ledger 'th 'uniq-gen-v3
                                    '((0 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))) :th-ded (uniq-step2))
                                      (1 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3)))) :ir (Gen 0 v3)))
                                    (silent-log)))
         (ledger (check-and-extend ledger 'th 'uniq-full
                                    '((0 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3)))) :th (uniq-gen-v3))
                                      (1 (.forall v2 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))))) :ir (Gen 0 v2)))
                                    (silent-log))))
    (expect "UNIQ-FULL is a real, re-citable ledger theorem (any two things =v1 are equal)"
            (check-k-proof '((0 (.forall v2 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))))) :th (uniq-full))) ledger)
            t)
    (expect "IOTA: from exists v0(v0=v1) and uniq-full, conclude (iota v0 (v0=v1)) = v1"
            (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :th (th-exists-v0-eq-v1))
                              (1 (.forall v2 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))))) :th (uniq-full))
                              (2 (.eq (.iota v0 (.eq v0 v1)) v1) :ir (IOTA 0 1)))
                            ledger)
            t)
    (expect "Attack: IOTA citing the SAME line twice (existence as both premises) -- must reject"
            (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :th (th-exists-v0-eq-v1))
                              (1 (.eq (.iota v0 (.eq v0 v1)) v1) :ir (IOTA 0 0)))
                            ledger)
            nil)
    (expect "Attack: IOTA with existence/uniqueness premises SWAPPED -- must reject"
            (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :th (th-exists-v0-eq-v1))
                              (1 (.forall v2 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))))) :th (uniq-full))
                              (2 (.eq (.iota v0 (.eq v0 v1)) v1) :ir (IOTA 1 0)))
                            ledger)
            nil)
    (expect "Attack: IOTA citing a uniqueness formula about a DIFFERENT A than the existence line -- must reject"
            (check-k-proof '((0 (.exists v0 (.eq v0 v5)) :hyp nil)
                              (1 (.forall v2 (.forall v3 (.to (.eq v2 v1) (.to (.eq v3 v1) (.eq v2 v3))))) :th (uniq-full))
                              (2 (.eq (.iota v0 (.eq v0 v5)) v1) :ir (IOTA 0 1)))
                            ledger)
            nil)
    (let* ((A '(.to (.eq v0 v4) (.forall v4 (.eq v0 v4))))
           (existence (list '.exists 'v0 A))
           (uniqueness '(.forall v2 (.forall v3
                         (.to (.to (.eq v2 v4) (.forall v4 (.eq v2 v4)))
                              (.to (.to (.eq v3 v4) (.forall v4 (.eq v3 v4)))
                                   (.eq v2 v3)))))))
      (expect "Attack (capture-avoidance): IOTA where substituting the iota-term would capture a
free variable under a nested same-named binder inside A -- @subst-ok? must block it"
              (check-k-proof (list (list 0 existence :hyp nil)
                                    (list 1 uniqueness :hyp nil)
                                    (list 2 (list '.to (list '.eq (list '.iota 'v0 A) 'v4)
                                                  (list '.forall 'v4 (list '.eq (list '.iota 'v0 A) 'v4)))
                                          :ir '(IOTA 0 1)))
                              ledger)
              nil))
    ledger))

(defun run-iota-self-tests ()
  "Section 19: IOTA formation, III.3, the worked uniqueness-chain example,
and attack tests."
  (let* ((ledger (bootstrap-kernel))
         (ledger (test-iota-formation ledger))
         (ledger (test-axiom-iii3 ledger))
         (ledger (test-iota-irule ledger)))
    (declare (ignorable ledger))
    (format t "~%IOTA self-tests complete.~%")))

;;; ---------------------------------------------------------------------
;;; 20. General inductive predicate definitions
;;; ---------------------------------------------------------------------
;;;
;;; P3 (Peano induction, Section 7) is hand-written for one specific
;;; shape: a domain built from exactly two constructors (ZERO, S), with
;;; every term automatically "in" the domain (there is no separate "is a
;;; natural number" predicate to check -- the whole term universe already
;;; plays that role). DEFINE-INDUCTIVE-PREDICATE generalizes this to an
;;; arbitrary, user-specified inductively defined UNARY PREDICATE over the
;;; existing term universe: "EVEN(x)", "PRIME(x)", "REACHABLE(x)",
;;; whatever the caller wants, given as a finite list of INTRODUCTION
;;; CLAUSES (base facts and recursive step rules) -- and, from those
;;; clauses alone, mechanically derives:
;;;   (a) a WFF-formation rule for the new predicate,
;;;   (b) one AXIOM (base case) or IRULE (step case, since it needs to
;;;       cite an already-established premise line, exactly like MP/Gen)
;;;       per clause, and
;;;   (c) the INDUCTION AXIOM itself: the generalization of P3 to however
;;;       many clauses were given, complete with the appropriate
;;;       @SUBST-OK? capture-avoidance side condition per clause.
;;;
;;; TRUST MODEL: exactly as Section 18's own .system-file mechanism, this
;;; is built entirely on top of BOOTSTRAP-KERNEL-FROM-SPEC -- the only
;;; two places in this file able to mint a :PRIMITIVE-origin ledger entry
;;; are BOOTSTRAP-KERNEL's own LABELS-bound ADMIT and this one, and
;;; DEFINE-INDUCTIVE-PREDICATE reaches the ledger through the latter, not
;;; some new privileged back door. So: introducing a new inductively
;;; defined predicate is exactly as trusted-by-fiat as introducing a new
;;; Peano axiom by hand would be -- nothing here is or could be
;;; independently re-verified against anything else. Unlike Peano's own
;;; P1-P10, whose SOUNDNESS this file's author checked by hand before
;;; hardcoding them, an arbitrary caller-supplied clause set could in
;;; principle be inconsistent (e.g. two clauses whose conclusions
;;; contradict each other structurally aren't detected as suspicious by
;;; anything below) -- this mechanism makes it *convenient* to state a new
;;; inductive definition, it does not make it *safe by construction*
;;; (there is no automated relative-consistency check here, matching the
;;; same honest limitation Section 18's own header already documents for
;;; hand-written .system files).
;;;
;;; A CLAUSE is a 3-element list (REC-VARS EXTRA-VARS RESULT-TERM), where
;;; REC-VARS and EXTRA-VARS are lists of ordinary ?-PREFIXED SCHEMA
;;; PATTERN VARIABLES (exactly the same kind already used throughout every
;;; other AXIOM/IRULE in this file, e.g. ?x, ?A -- nothing new to learn):
;;;   - REC-VARS: variables standing for a term ALREADY KNOWN to satisfy
;;;     the predicate being defined -- each contributes a premise
;;;     (NAME ?r) that the citing proof must supply as an already-proven
;;;     line, and an inductive hypothesis A[?r/x] inside the induction
;;;     axiom.
;;;   - EXTRA-VARS: any other schema variables RESULT-TERM needs that are
;;;     NOT themselves required to satisfy the predicate (there usually
;;;     are none, for the common "unary constructor" shape).
;;;   - RESULT-TERM: the term such that the clause concludes
;;;     (NAME RESULT-TERM), built from REC-VARS/EXTRA-VARS plus whatever
;;;     ordinary ground vocabulary (S, +, zero, ...) already exists.
;;; A clause with empty REC-VARS is a base case (admitted as an AXIOM); a
;;; clause with nonempty REC-VARS is a step case (admitted as an IRULE, so
;;; a citing proof must supply the recursive premise(s) as earlier proof
;;; lines, the same way MP/Gen do).
;;;
;;; Worked example, EVEN: "zero is even; if x is even, so is S(S(x))":
;;;   (define-inductive-predicate ledger 'even
;;;     '((nil nil zero)            ; EVEN(zero)
;;;       ((?x) nil (S (S ?x)))))   ; EVEN(x) -> EVEN(S(S(x)))
;;; produces EVEN-INTRO-1 (axiom: EVEN(zero)), EVEN-INTRO-2 (irule:
;;; EVEN(?x) |- EVEN(S(S(?x)))), and EVEN-IND, the induction axiom:
;;;   A[zero/x] -> ((forall y (EVEN(y) -> (A[y/x] -> A[S(S(y))/x])))
;;;                 -> forall x (EVEN(x) -> A))
;;; (see TEST-INDUCTIVE-EVEN below for citing EVEN-IND to actually prove
;;; something with it, mirroring TEST-PEANO-INDUCTION-PROOF's own
;;; base/step/GEN/MP-twice usage pattern for P3).

;;; --- General form: n-ary, possibly mutually recursive predicates -------
;;;
;;; The worked example above (EVEN) is the common case: one, unary,
;;; self-recursive predicate. DEFINE-INDUCTIVE-PREDICATES generalizes this
;;; along both axes at once:
;;;   - N-ARY: a predicate need not take a single term -- CLAUSE's own
;;;     RESULT becomes RESULT-TERMS, a list of as many terms as the
;;;     predicate's declared ARITY, e.g. a binary DOUBLE-OF(x,y) relation.
;;;   - MUTUAL RECURSION: several predicates can be defined TOGETHER as a
;;;     GROUP, each one's clauses free to cite ANY predicate in the group
;;;     as a recursive premise -- not only itself -- e.g. EVEN/ODD, each
;;;     defined via the OTHER's own step case.
;;; A CLAUSE is now (REC-SPECS EXTRA-VARS RESULT-TERMS):
;;;   - REC-SPECS: a list of (PRED-NAME VAR1 ... VARk), one per recursive
;;;     premise, PRED-NAME any predicate in the GROUP (itself, for
;;;     ordinary self-recursion, or another member, for genuine mutual
;;;     recursion) and VAR1..VARk that many fresh schema variables naming
;;;     PRED-NAME's own arguments at this call site. Each contributes a
;;;     premise (PRED-NAME VAR1...VARk) the citing proof must supply, and
;;;     -- inside the induction axioms -- an inductive hypothesis
;;;     "PRED-NAME's own motive holds of VAR1...VARk", using PRED-NAME's
;;;     OWN motive (not necessarily the clause's own predicate's motive:
;;;     this is exactly what makes mutual induction mutual).
;;;   - EXTRA-VARS/RESULT-TERMS: as before, just RESULT-TERMS is now a
;;;     TUPLE (one term per argument position) rather than a single term.
;;; GROUP is a list of (PRED-NAME ARITY . CLAUSES) triples. Simultaneous
;;; substitution into an n-ary motive (needed once ARITY > 1, since
;;; @SUBST only ever replaces ONE variable) uses the new @SUBSTN/
;;; @SUBSTN-OK? meta-forms (this section's header, Section 4).
;;;
;;; DEFINE-INDUCTIVE-PREDICATE (singular, below) remains exactly as
;;; before -- a thin wrapper for the common unary/non-mutual case, so
;;; every existing caller (TEST-INDUCTIVE-EVEN/TEST-INDUCTIVE-GENERALITY
;;; included) keeps working unchanged.

(defun rename-inductive-clause-vars (clause tag)
  "As before, generalized to CLAUSE = (REC-SPECS EXTRA-VARS RESULT-TERMS):
alpha-renames every VAR occurring across all of REC-SPECS' own
VAR1...VARk lists, plus EXTRA-VARS, to fresh schema pattern variables
tagged with TAG, leaving each REC-SPEC's own PRED-NAME and RESULT-TERMS'
ground vocabulary otherwise untouched (RESULT-TERMS are walked and
renamed consistently, since they may reuse the same var symbols)."
  (destructuring-bind (rec-specs extra-vars result-terms) clause
    (let* ((all-vars (append (mapcan (lambda (s) (copy-list (rest s))) rec-specs) extra-vars))
           (renaming (mapcar (lambda (v)
                                (cons v (intern (format nil "?C~A-~A" tag (subseq (symbol-name v) 1))
                                                 (symbol-package v))))
                              all-vars)))
      (labels ((ren (form)
                 (cond ((and (pat-var-p form) (assoc form renaming)) (cdr (assoc form renaming)))
                       ((consp form) (cons (ren (car form)) (ren (cdr form))))
                       (t form))))
        (list (mapcar (lambda (s) (cons (first s) (mapcar (lambda (v) (cdr (assoc v renaming))) (rest s))))
                      rec-specs)
              (mapcar (lambda (v) (cdr (assoc v renaming))) extra-vars)
              (mapcar #'ren result-terms))))))

(defun inductive-intro-command (pred-name idx clause)
  "As before, generalized to CLAUSE = (REC-SPECS EXTRA-VARS RESULT-TERMS)
and an N-ARY PRED-NAME: an (:AXIOM ...) command for a base case (empty
REC-SPECS), an (:IRULE ...) command for a step case, whose premise
patterns are now (QNAME VAR1...VARk) per REC-SPEC (QNAME possibly a
DIFFERENT predicate in the group, for mutual recursion) and whose
conclusion is (PRED-NAME . RESULT-TERMS)."
  (destructuring-bind (rec-specs extra-vars result-terms) clause
    (let ((intro-name (intern (format nil "~A-INTRO-~D" (symbol-name pred-name) idx) (symbol-package pred-name))))
      (if (null rec-specs)
          (list :axiom intro-name
                (mapcar (lambda (v) (list 'term? v)) extra-vars)
                (list nil (cons pred-name result-terms)))
          (list :irule intro-name
                (mapcar (lambda (v) (list 'term? v)) extra-vars)
                (list (mapcar (lambda (s) (cons (first s) (rest s))) rec-specs)
                      extra-vars
                      :=>
                      (cons pred-name result-terms)))))))

(defun inductive-hyp-pattern (target-pred motive-table clause)
  "As before, generalized: MOTIVE-TABLE is an alist PRED-NAME -> (SUBJECT-
VARS . MOTIVE-VAR) for every predicate in the GROUP (SUBJECT-VARS a list
of that predicate's own ARITY-many schema variables, one per argument
position). Builds one antecedent from an ALREADY ALPHA-RENAMED CLAUSE,
using @SUBSTN (not @SUBST) throughout so this works uniformly whether
TARGET-PRED (the predicate CLAUSE's own RESULT-TERMS conclude about) or
any REC-SPEC's own PRED-NAME is unary or N-ARY, and using EACH recursive
premise's OWN predicate's OWN motive for its inductive hypothesis -- the
mechanism that makes mutual induction mutual: EVEN's own induction axiom
still needs ODD's motive available wherever an EVEN clause recurses
through an ODD premise."
  (destructuring-bind (rec-specs extra-vars result-terms) clause
    (let* ((tgt (cdr (assoc target-pred motive-table)))
           (body (list '@substn (car tgt) result-terms (cdr tgt))))
      (dolist (spec (reverse rec-specs))
        (destructuring-bind (qname . qvars) spec
          (let ((q (cdr (assoc qname motive-table))))
            (setf body (list '.to (cons qname qvars)
                              (list '.to (list '@substn (car q) qvars (cdr q)) body))))))
      (dolist (v (reverse (append (mapcan (lambda (s) (copy-list (rest s))) rec-specs) extra-vars)))
        (setf body (list '.forall v body)))
      body)))

(defun check-inductive-group-well-formed (ledger group)
  "Validates GROUP (see DEFINE-INDUCTIVE-PREDICATES' own header for its
format) BEFORE any entry is minted, refusing -- via ERROR, atomically,
nothing partially applied -- a GROUP that would otherwise go through
silently and produce either a confusing internal crash deep inside
INDUCTIVE-HYP-PATTERN, a subtly WRONG axiom, or (the concrete bug this
section's own worked examples actually hit during development, when the
mutual EVEN/ODD example first reused the name EVEN already minted by
TEST-INDUCTIVE-EVEN on the same threaded ledger) two DIFFERENT
predicates' rules silently sharing one name and letting
TRY-AXIOM-ENTRY/TRY-IR-ENTRY match against whichever one happens to come
first in the ledger:

  1. NAME COLLISION: none of the fresh entry-names GROUP is about to mint
     (each predicate's own WFF-formation rule name, each clause's own
     INTRO-name, each predicate's own IND-name) may already be in use by
     an existing TERM?/WFF?/AXIOM/IRULE entry in LEDGER.
  2. SHAPE: predicate names are pairwise distinct within GROUP; each
     ARITY is a positive integer; every REC-SPEC's own PRED-NAME actually
     names a member of GROUP (not a typo, and not some other, unrelated
     predicate already in the ledger -- ASSOC silently returning NIL here
     is exactly what would otherwise turn into a wrong axiom, not a
     crash); every REC-SPEC's own variable count matches that target
     predicate's declared ARITY; every clause's own RESULT-TERMS length
     matches ITS OWN predicate's declared ARITY; every REC-SPEC/EXTRA-VAR
     is a genuine schema pattern variable (PAT-VAR-P).
  3. GROUNDEDNESS: every predicate in GROUP must be reachable from SOME
     chain of base clauses -- the least fixed point of \"has at least one
     clause whose REC-SPECS are ALL already-known-inhabited\" (base
     clauses, with empty REC-SPECS, are inhabited immediately -- exactly
     the same fixpoint computation as \"which nonterminals of a grammar
     can produce at least one string\") must eventually cover every
     predicate in GROUP. A predicate that can never actually be
     introduced (no base case anywhere in its own dependency closure --
     a forgotten base clause, or a mutual-recursion cycle that never
     bottoms out) would still get a technically SOUND induction axiom
     (vacuously true, about the empty relation), so this isn't a
     soundness gap -- but it is almost certainly not what was intended,
     so it's refused rather than silently accepted.

Note what this does NOT try to guarantee: it does not (and, given how
this file's clause format works, does not need to) check strict
positivity in the usual inductive-definition sense -- REC-SPECS are
always plain predicate-application PREMISES, never embedded negated or
higher-order inside a RESULT-TERM, so there is no way for this
particular mechanism to build a non-monotone operator whose least fixed
point wouldn't exist in the first place. What CAN still go wrong here is
purely definitional/bookkeeping mistakes, which is exactly what the
three checks above catch."
  (let ((pred-names (mapcar #'first group)))
    (unless (= (length pred-names) (length (remove-duplicates pred-names)))
      (error "DEFINE-INDUCTIVE-PREDICATES: duplicate predicate name(s) within GROUP: ~S" pred-names))
    ;; -- 2: shape --
    (dolist (g group)
      (destructuring-bind (name arity . clauses) g
        (unless (and (integerp arity) (plusp arity))
          (error "DEFINE-INDUCTIVE-PREDICATES: ~S's ARITY must be a positive integer, got ~S" name arity))
        (dolist (clause clauses)
          (destructuring-bind (rec-specs extra-vars result-terms) clause
            (unless (= (length result-terms) arity)
              (error "DEFINE-INDUCTIVE-PREDICATES: a clause of ~S has ~D RESULT-TERM(S) but ~S's own declared ARITY is ~D~%  clause: ~S"
                     name (length result-terms) name arity clause))
            (dolist (v extra-vars)
              (unless (pat-var-p v)
                (error "DEFINE-INDUCTIVE-PREDICATES: EXTRA-VAR ~S in a clause of ~S is not a schema pattern variable (must start with ?)~%  clause: ~S"
                       v name clause)))
            (dolist (spec rec-specs)
              (destructuring-bind (qname . qvars) spec
                (let ((tgt (assoc qname group)))
                  (unless tgt
                    (error "DEFINE-INDUCTIVE-PREDICATES: a REC-SPEC in a clause of ~S cites ~S, which is not a member of this GROUP~%  clause: ~S~%  GROUP predicates: ~S"
                           name qname clause pred-names))
                  (unless (= (length qvars) (second tgt))
                    (error "DEFINE-INDUCTIVE-PREDICATES: a REC-SPEC in a clause of ~S cites ~S with ~D variable(s), but ~S's own declared ARITY is ~D~%  clause: ~S"
                           name qname (length qvars) qname (second tgt) clause)))
                (dolist (v qvars)
                  (unless (pat-var-p v)
                    (error "DEFINE-INDUCTIVE-PREDICATES: REC-SPEC variable ~S in a clause of ~S is not a schema pattern variable (must start with ?)~%  clause: ~S"
                           v name clause)))))))))
    ;; -- 1: name collisions against the LIVE ledger --
    (let ((existing (mapcan (lambda (k) (mapcar (lambda (e) (first (entry-payload e))) (entries-of-kind k ledger)))
                             '(term? wff? axiom irule))))
      (dolist (g group)
        (destructuring-bind (name arity . clauses) g
          (declare (ignore arity))
          (let ((wff-name (intern (format nil "WFF_~A?" (symbol-name name)) (symbol-package name)))
                (ind-name (intern (format nil "~A-IND" (symbol-name name)) (symbol-package name)))
                (intro-names (loop for c in clauses for i from 1
                                    collect (intern (format nil "~A-INTRO-~D" (symbol-name name) i)
                                                     (symbol-package name)))))
            (dolist (nm (list* wff-name ind-name intro-names))
              (when (member nm existing)
                (error "DEFINE-INDUCTIVE-PREDICATES: refusing to define ~S -- the name ~S is already in use by an existing TERM?/WFF?/AXIOM/IRULE entry (defining it again would silently make TRY-AXIOM-ENTRY/TRY-IR-ENTRY try BOTH the old and the new rule under the same shared name)"
                       name nm)))))))
    ;; -- 3: groundedness (least fixed point over the whole GROUP) --
    (let ((inhabited nil) (changed t))
      (loop while changed do
        (setf changed nil)
        (dolist (g group)
          (destructuring-bind (name arity . clauses) g
            (declare (ignore arity))
            (unless (member name inhabited)
              (when (some (lambda (c) (every (lambda (spec) (member (first spec) inhabited)) (first c))) clauses)
                (push name inhabited)
                (setf changed t))))))
      (dolist (g group)
        (let ((name (first g)))
          (unless (member name inhabited)
            (error "DEFINE-INDUCTIVE-PREDICATES: ~S can never actually be derived -- no chain of clauses within this GROUP bottoms out in a base case for it (a forgotten base clause, or a mutual-recursion cycle with no way to get started). Predicates that DO bottom out: ~S"
                   name inhabited))))))
  t)

(defun define-inductive-predicates (ledger group)
  "General public entry point (see this subsection's own header for the
GROUP/CLAUSE format and DEFINE-INDUCTIVE-PREDICATE, below, for the common
unary/non-mutual convenience wrapper). Extends LEDGER, via BOOTSTRAP-
KERNEL-FROM-SPEC exactly as the unary case already did, with: one WFF-
formation rule and one induction axiom PER predicate in GROUP, and one
introduction AXIOM/IRULE per clause across every predicate -- the
induction axioms all share the SAME antecedent list (built from every
clause in the whole GROUP, not just their own predicate's), differing
only in which predicate's own motive their final conclusion is about,
which is exactly what makes proving any ONE of a mutually recursive
group's properties require establishing the induction step for ALL of
them together. CHECK-INDUCTIVE-GROUP-WELL-FORMED (above) is run FIRST
and refuses the whole call before anything is minted if GROUP is
malformed or would collide with LEDGER's existing entries."
  (check-inductive-group-well-formed ledger group)
  (let* ((motive-table
           (mapcar (lambda (g)
                     (destructuring-bind (name arity . clauses) g
                       (declare (ignore clauses))
                       (cons name (cons (loop for i from 1 to arity
                                              collect (intern (format nil "?IND-X-~A-~D" (symbol-name name) i)
                                                               (symbol-package name)))
                                         (intern (format nil "?IND-A-~A" (symbol-name name)) (symbol-package name))))))
                   group))
         (wff-cmds
           (mapcar (lambda (g)
                     (destructuring-bind (name arity . clauses) g
                       (declare (ignore clauses))
                       (let ((args (loop for i from 1 to arity
                                         collect (intern (format nil "?A~D" i) (symbol-package name)))))
                         (list :wff-formation (intern (format nil "WFF_~A?" (symbol-name name)) (symbol-package name))
                               (mapcar (lambda (a) (list 'term? a)) args)
                               (list 'wff? (cons name args))))))
                   group))
         (intro-cmds
           (mapcan (lambda (g)
                     (destructuring-bind (name arity . clauses) g
                       (declare (ignore arity))
                       (loop for c in clauses for i from 1 collect (inductive-intro-command name i c))))
                   group))
         ;; A single running counter across EVERY clause in the whole
         ;; group, so alpha-renamed variables from two different clauses
         ;; -- even ones belonging to two different predicates -- can
         ;; never collide once spliced together into the shared
         ;; antecedent list every induction axiom below is built from.
         (tag 0)
         (renamed (mapcan (lambda (g)
                             (destructuring-bind (name arity . clauses) g
                               (declare (ignore arity))
                               (mapcar (lambda (c) (incf tag) (cons name (rename-inductive-clause-vars c tag)))
                                       clauses)))
                           group))
         (hyps (mapcar (lambda (r) (inductive-hyp-pattern (car r) motive-table (cdr r))) renamed))
         (subst-ok-conditions
           (mapcar (lambda (r) (let ((tgt (cdr (assoc (car r) motive-table))))
                                  (list '@substn-ok? (car tgt) (third (cdr r)) (cdr tgt))))
                   renamed))
         (var-wff-conditions
           (mapcan (lambda (g) (let ((tgt (cdr (assoc (first g) motive-table))))
                                  (append (mapcar (lambda (v) (list 'var? v)) (car tgt))
                                          (list (list 'wff? (cdr tgt))))))
                   group))
         (all-conditions (append var-wff-conditions subst-ok-conditions))
         (all-extra-params (mapcan (lambda (g) (let ((tgt (cdr (assoc (first g) motive-table))))
                                                  (append (car tgt) (list (cdr tgt)))))
                                    group))
         (ind-cmds
           (mapcar (lambda (g)
                     (destructuring-bind (name arity . clauses) g
                       (declare (ignore arity clauses))
                       (let* ((tgt (cdr (assoc name motive-table)))
                              (concl (list '.to (cons name (car tgt)) (cdr tgt))))
                         (dolist (v (reverse (car tgt))) (setf concl (list '.forall v concl)))
                         (let ((body concl))
                           (dolist (h (reverse hyps)) (setf body (list '.to h body)))
                           (list :axiom (intern (format nil "~A-IND" (symbol-name name)) (symbol-package name))
                                 all-conditions
                                 (list all-extra-params body))))))
                   group)))
    (bootstrap-kernel-from-spec (append wff-cmds intro-cmds ind-cmds) :ledger ledger)))

(defun define-inductive-predicate (ledger name clauses)
  "Backward-compatible convenience wrapper over DEFINE-INDUCTIVE-
PREDICATES for the common case: a single, non-mutually-recursive, UNARY
predicate. CLAUSES keep the original 2-part shape (REC-VARS EXTRA-VARS
RESULT) -- REC-VARS are all implicitly recursive premises of NAME ITSELF
(there is no other predicate in a singleton, non-mutual group to
reference), and RESULT is a single term (not a tuple), since the
predicate is unary. See this section's own header for the clause format
and the worked EVEN example."
  (define-inductive-predicates
   ledger
   (list (list* name 1
                (mapcar (lambda (c)
                          (destructuring-bind (rec-vars extra-vars result) c
                            (list (mapcar (lambda (v) (list name v)) rec-vars) extra-vars (list result))))
                        clauses)))))

(defun test-inductive-even (ledger)
  "Worked example: EVEN(zero); EVEN(x) -> EVEN(S(S(x))). Exercises
formation, both flavors of introduction rule (AXIOM for the base case,
IRULE for the step case), attack tests, and a genuine induction proof --
mirroring TEST-PEANO-INDUCTION-PROOF's own base/step/GEN/MP-twice usage
pattern for P3, but now for a predicate that P3 knows nothing about,
generated entirely from data by DEFINE-INDUCTIVE-PREDICATE itself."
  (let ((ledger (define-inductive-predicate ledger 'even '((nil nil zero) ((?x) nil (S (S ?x)))))))
    (expect "(EVEN v0) is a wff" (judgement? 'wff? '(even v0) ledger) t)
    (expect "EVEN(zero) via the base-case AXIOM"
            (check-k-proof '((0 (even zero) :axiom (even-intro-1))) ledger) t)
    (let* ((proof2 '((0 (even zero) :axiom (even-intro-1))
                      (1 (even (S (S zero))) :ir (even-intro-2 0))))
           (ledger2 (check-and-extend ledger 'th 'th-even-2 proof2)))
      (expect "EVEN(S(S(zero))) via the step-case IRULE, citing EVEN(zero)"
              (check-k-proof proof2 ledger2) t)
      (expect "EVEN(S(S(S(S(zero))))) chaining the step-case IRULE twice"
              (check-k-proof '((0 (even zero) :axiom (even-intro-1))
                                (1 (even (S (S zero))) :ir (even-intro-2 0))
                                (2 (even (S (S (S (S zero))))) :ir (even-intro-2 1)))
                              ledger2)
              t)
      (expect "Attack: the step-case IRULE citing a line that ISN'T (EVEN ...) at all -- must reject"
              (check-k-proof '((0 (.eq zero zero) :axiom (IV.1))
                                (1 (even (S (S zero))) :ir (even-intro-2 0)))
                              ledger2)
              nil))
    ;; The induction proof itself: forall v0 (EVEN(v0) -> v0=v0). Trivial
    ;; (reflexivity), chosen so the STEP case's own inductive hypothesis
    ;; and recursive premise are legitimately available but simply unused
    ;; (weakened away via II.1/K) -- exactly the case that most exercises
    ;; whether the generated EVEN-IND axiom threads a genuinely UNUSED
    ;; hypothesis through correctly, matching this project's own "prove
    ;; the wiring, not just the arithmetic" testing style.
    (let* ((step-lemma-proof
             '((0 (.eq (S (S v1)) (S (S v1))) :axiom (IV.1))
               (1 (.to (.eq (S (S v1)) (S (S v1))) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))) :axiom (II.1))
               (2 (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1)))) :ir (MP 1 0))
               (3 (.to (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))
                       (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))))
                  :axiom (II.1))
               (4 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))) :ir (MP 3 2))))
           (ledger (check-and-extend ledger 'th 'th-even-step-lemma step-lemma-proof)))
      (expect "step lemma (no open hyps -- a closed tautological derivation) checks"
              (check-k-proof step-lemma-proof ledger) t)
      (progn
        (expect "GEN v1 on the step lemma checks (v1 free in no open hyp: the lemma is closed)"
                (check-k-proof `((0 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))) :th (th-even-step-lemma))
                                  (1 (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1)))))) :ir (Gen 0 v1)))
                                ledger)
                t)
        (expect "full induction proof of forall v0 (EVEN(v0) -> v0=v0), via the GENERATED EVEN-IND axiom"
                (check-k-proof `((0 (.eq zero zero) :axiom (IV.1))
                                  (1 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))) :th (th-even-step-lemma))
                                  (2 (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1)))))) :ir (Gen 1 v1))
                                  (3 (.to (.eq zero zero)
                                          (.to (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))))
                                               (.forall v0 (.to (even v0) (.eq v0 v0)))))
                                     :axiom (even-ind v0 (.eq v0 v0)))
                                  (4 (.to (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))))
                                          (.forall v0 (.to (even v0) (.eq v0 v0))))
                                     :ir (MP 3 0))
                                  (5 (.forall v0 (.to (even v0) (.eq v0 v0))) :ir (MP 4 2)))
                                ledger)
                t)
        (expect "Attack: EVEN-IND cited with a WRONG base term (S(zero) instead of zero) -- must reject"
                (check-k-proof `((0 (.to (.eq (S zero) (S zero))
                                        (.to (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1))))))
                                             (.forall v0 (.to (even v0) (.eq v0 v0)))))
                                     :axiom (even-ind v0 (.eq v0 v0))))
                                ledger)
                nil)
        (expect "Attack: EVEN-IND's step antecedent MISSING the recursive (EVEN v1) premise -- must reject"
                (check-k-proof `((0 (.to (.eq zero zero)
                                        (.to (.forall v1 (.to (.eq v1 v1) (.eq (S (S v1)) (S (S v1)))))
                                             (.forall v0 (.to (even v0) (.eq v0 v0)))))
                                     :axiom (even-ind v0 (.eq v0 v0))))
                                ledger)
                nil)
        ledger))))

(defun test-inductive-generality (ledger)
  "A SECOND, differently-shaped inductive predicate (POS: S(zero) is
positive; if x is positive so is S(x) -- successor closure starting from
1, not 0), defined via the exact same DEFINE-INDUCTIVE-PREDICATE, to
confirm nothing about EVEN's own S-of-S shape was accidentally baked into
the generator. Formation and introduction only, kept short."
  (let ((ledger (define-inductive-predicate ledger 'pos '((nil nil (S zero)) ((?x) nil (S ?x))))))
    (expect "(POS v0) is a wff" (judgement? 'wff? '(pos v0) ledger) t)
    (expect "POS(S(zero)) via the base-case AXIOM"
            (check-k-proof '((0 (pos (S zero)) :axiom (pos-intro-1))) ledger) t)
    (expect "POS(S(S(zero))) via the step-case IRULE, citing POS(S(zero))"
            (check-k-proof '((0 (pos (S zero)) :axiom (pos-intro-1))
                              (1 (pos (S (S zero))) :ir (pos-intro-2 0)))
                            ledger)
            t)
    (expect "Attack: POS-INTRO-1 does not admit POS(zero) (that's EVEN's base case, not POS's)"
            (check-k-proof '((0 (pos zero) :axiom (pos-intro-1))) ledger)
            nil)
    ledger))

(defun test-inductive-mutual-even-odd (ledger)
  "Worked example for MUTUAL RECURSION: EVEN and ODD defined TOGETHER as a
2-member GROUP, each citing the OTHER in its own step case:
  EVEN(zero);  ODD(x) -> EVEN(S(x));  EVEN(x) -> ODD(S(x))
via
  (define-inductive-predicates ledger
    '((even 1 (nil nil (zero)) (((odd ?x)) nil ((S ?x))))
      (odd 1 (((even ?x)) nil ((S ?x))))))
Exercises formation of both predicates, introduction (AXIOM for EVEN's
base case, IRULE for both step cases, each threading through the OTHER
predicate's own premise), an attack test, and -- the real point of this
example -- a genuine MUTUAL induction proof: EVEN-IND's own antecedent
chain mentions ODD's motive (in its EVEN-step hyp) and EVEN's motive (in
its ODD-step hyp) alongside EVEN's own base hyp, so citing it correctly
requires supplying trivial motives for BOTH EVEN and ODD at once, and
BOTH (previously proven, mutually shaped) step-lemmas as premises --
proving forall v0 (EVEN(v0) -> v0=v0) is impossible without ODD's own
half of the machinery, even though ODD never appears in the final
conclusion. Mirrors TEST-INDUCTIVE-EVEN's own reflexivity trick (A(x) :=
x=x) so the recursive premises/hypotheses are legitimately available yet
simply unused, isolating the WIRING rather than any arithmetic content."
  (let ((ledger (define-inductive-predicates
                 ledger
                 '((even 1 (nil nil (zero)) (((odd ?x)) nil ((S ?x))))
                   (odd 1 (((even ?x)) nil ((S ?x))))))))
    (expect "(EVEN v0) is a wff" (judgement? 'wff? '(even v0) ledger) t)
    (expect "(ODD v0) is a wff" (judgement? 'wff? '(odd v0) ledger) t)
    (expect "EVEN(zero) via the base-case AXIOM"
            (check-k-proof '((0 (even zero) :axiom (even-intro-1))) ledger) t)
    (let* ((proof2 '((0 (even zero) :axiom (even-intro-1))
                      (1 (odd (S zero)) :ir (odd-intro-1 0))))
           (ledger2 (check-and-extend ledger 'th 'th-odd-1 proof2)))
      (expect "ODD(S(zero)) via ODD's step IRULE, citing EVEN(zero)"
              (check-k-proof proof2 ledger2) t)
      (expect "EVEN(S(S(zero))) via EVEN's step IRULE, citing ODD(S(zero))"
              (check-k-proof '((0 (even zero) :axiom (even-intro-1))
                                (1 (odd (S zero)) :ir (odd-intro-1 0))
                                (2 (even (S (S zero))) :ir (even-intro-2 1)))
                              ledger2)
              t)
      (expect "Attack: EVEN's step IRULE citing EVEN itself instead of ODD -- must reject"
              (check-k-proof '((0 (even zero) :axiom (even-intro-1))
                                (1 (even (S (S zero))) :ir (even-intro-2 0)))
                              ledger2)
              nil))
    ;; The mutual induction proof itself: forall v0 (EVEN(v0) -> v0=v0),
    ;; citing EVEN-IND with BOTH motives A_even(x):=x=x and A_odd(x):=x=x
    ;; supplied at once (extra params, in group order: x_even, A_even,
    ;; x_odd, A_odd), and needing BOTH mutual step-lemmas as premises.
    (let* ((step-lemma-even
             '((0 (.eq (S v1) (S v1)) :axiom (IV.1))
               (1 (.to (.eq (S v1) (S v1)) (.to (.eq v1 v1) (.eq (S v1) (S v1)))) :axiom (II.1))
               (2 (.to (.eq v1 v1) (.eq (S v1) (S v1))) :ir (MP 1 0))
               (3 (.to (.to (.eq v1 v1) (.eq (S v1) (S v1)))
                       (.to (odd v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                  :axiom (II.1))
               (4 (.to (odd v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))) :ir (MP 3 2))))
           (ledger (check-and-extend ledger 'th 'th-mutual-even-step-lemma step-lemma-even))
           (step-lemma-odd
             '((0 (.eq (S v1) (S v1)) :axiom (IV.1))
               (1 (.to (.eq (S v1) (S v1)) (.to (.eq v1 v1) (.eq (S v1) (S v1)))) :axiom (II.1))
               (2 (.to (.eq v1 v1) (.eq (S v1) (S v1))) :ir (MP 1 0))
               (3 (.to (.to (.eq v1 v1) (.eq (S v1) (S v1)))
                       (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                  :axiom (II.1))
               (4 (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))) :ir (MP 3 2))))
           (ledger (check-and-extend ledger 'th 'th-mutual-odd-step-lemma step-lemma-odd)))
      (expect "step-lemma-even (closed tautological derivation) checks"
              (check-k-proof step-lemma-even ledger) t)
      (expect "step-lemma-odd (closed tautological derivation) checks"
              (check-k-proof step-lemma-odd ledger) t)
      (expect "full MUTUAL induction proof of forall v0 (EVEN(v0) -> v0=v0), via the GENERATED EVEN-IND axiom, needing BOTH mutual step-lemmas"
              (check-k-proof
               `((0 (.eq zero zero) :axiom (IV.1))
                 (1 (.to (odd v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))) :th (th-mutual-even-step-lemma))
                 (2 (.forall v1 (.to (odd v1) (.to (.eq v1 v1) (.eq (S v1) (S v1))))) :ir (Gen 1 v1))
                 (3 (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))) :th (th-mutual-odd-step-lemma))
                 (4 (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1))))) :ir (Gen 3 v1))
                 (5 (.to (.eq zero zero)
                         (.to (.forall v1 (.to (odd v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                              (.to (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                                   (.forall v0 (.to (even v0) (.eq v0 v0))))))
                    :axiom (even-ind v0 (.eq v0 v0) v0 (.eq v0 v0)))
                 (6 (.to (.forall v1 (.to (odd v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                         (.to (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                              (.forall v0 (.to (even v0) (.eq v0 v0)))))
                    :ir (MP 5 0))
                 (7 (.to (.forall v1 (.to (even v1) (.to (.eq v1 v1) (.eq (S v1) (S v1)))))
                         (.forall v0 (.to (even v0) (.eq v0 v0))))
                    :ir (MP 6 2))
                 (8 (.forall v0 (.to (even v0) (.eq v0 v0))) :ir (MP 7 4)))
               ledger)
              t)
      ledger)))

(defun test-inductive-nary-sumr (ledger)
  "Worked example for N-ARY relations: SUMR(x,y,z), the graph of addition
(\"x+y=z\"), defined as a ternary predicate WITHOUT reference to the +
function symbol at all:
  SUMR(x,zero,x);   SUMR(x,y,z) -> SUMR(x,S(y),S(z))
via
  (define-inductive-predicates ledger
    '((sumr 3 (nil (?x) (?x zero ?x))
             (((sumr ?x ?y ?z)) nil (?x (S ?y) (S ?z))))))
Exercises: an ARITY-3 predicate (RESULT-TERMS a genuine 3-tuple), a base
clause using EXTRA-VARS (?x, which the predicate depends on but which is
not itself required to satisfy anything recursively), a self-recursive
step clause whose single REC-SPEC premise and conclusion both mention
all 3 argument positions at once (exercising @SUBSTN's SIMULTANEOUS,
not one-at-a-time, substitution), and an attack test."
  (let ((ledger (define-inductive-predicates
                 ledger
                 '((sumr 3 (nil (?x) (?x zero ?x))
                          (((sumr ?x ?y ?z)) nil (?x (S ?y) (S ?z))))))))
    (expect "(SUMR v0 v1 v2) is a wff" (judgement? 'wff? '(sumr v0 v1 v2) ledger) t)
    (expect "SUMR(v0,zero,v0) via the base-case AXIOM (x+0=x)"
            (check-k-proof '((0 (sumr v0 zero v0) :axiom (sumr-intro-1))) ledger) t)
    (let* ((proof2 '((0 (sumr v0 zero v0) :axiom (sumr-intro-1))
                      (1 (sumr v0 (S zero) (S v0)) :ir (sumr-intro-2 0))))
           (ledger2 (check-and-extend ledger 'th 'th-sumr-1 proof2)))
      (expect "SUMR(v0,S(zero),S(v0)) via the step-case IRULE (x+1=S(x))"
              (check-k-proof proof2 ledger2) t)
      (expect "SUMR(v0,S(S(zero)),S(S(v0))) chaining the step-case IRULE twice (x+2=S(S(x)))"
              (check-k-proof '((0 (sumr v0 zero v0) :axiom (sumr-intro-1))
                                (1 (sumr v0 (S zero) (S v0)) :ir (sumr-intro-2 0))
                                (2 (sumr v0 (S (S zero)) (S (S v0))) :ir (sumr-intro-2 1)))
                              ledger2)
              t)
      (expect "Attack: SUMR's step IRULE with a wrong (non-successor) output slot -- must reject"
              (check-k-proof '((0 (sumr v0 zero v0) :axiom (sumr-intro-1))
                                (1 (sumr v0 (S zero) v0) :ir (sumr-intro-2 0)))
                              ledger2)
              nil))
    ledger))

(defun test-inductive-consistency-checks (ledger)
  "CHECK-INDUCTIVE-GROUP-WELL-FORMED's own self-tests: every one of its
three refusal categories (name collision, shape, groundedness), each
provoked deliberately and confirmed to signal an ERROR rather than
silently minting something wrong or crashing somewhere deeper, plus a
sanity check that legitimate GROUPs (fresh mutual and n-ary examples,
using names distinct from any already on LEDGER) still succeed."
  (flet ((must-signal-error (thunk)
           (handler-case (progn (funcall thunk) :no-error)
             (error () :caught-error))))
    ;; -- 1: name collision. LEDGER already has EVEN (from TEST-INDUCTIVE-
    ;; EVEN, threaded in by RUN-INDUCTIVE-DEFINITION-SELF-TESTS below) --
    ;; this is the EXACT bug this whole check exists to catch.
    (expect "Attack: redefining EVEN on a ledger that already has it -- must error, not silently double-mint EVEN-INTRO-1/2"
            (must-signal-error
             (lambda () (define-inductive-predicates
                         ledger '((even 1 (nil nil (zero)) (((even ?x)) nil ((S ?x))))))))
            :caught-error)
    ;; -- 2: shape --
    (expect "Attack: a clause's RESULT-TERMS length doesn't match its own predicate's declared ARITY -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates ledger '((cf1 2 (nil nil (zero)) nil)))))
            :caught-error)
    (expect "Attack: a REC-SPEC citing a predicate name that isn't in this GROUP at all -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates
                         ledger '((cf2 1 (nil nil (zero)) (((not-in-group ?x)) nil ((S ?x))))))))
            :caught-error)
    (expect "Attack: a REC-SPEC's variable count not matching its target predicate's own declared ARITY -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates
                         ledger '((cf3 2 (nil nil (zero zero)) (((cf3 ?x)) nil ((S ?x) (S ?x))))))))
            :caught-error)
    (expect "Attack: an EXTRA-VAR that isn't a genuine schema pattern variable -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates ledger '((cf4 1 (nil (not-a-var) (zero)))))))
            :caught-error)
    (expect "Attack: two predicates in the same GROUP sharing one name -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates
                         ledger '((cf5 1 (nil nil (zero))) (cf5 1 (nil nil (zero)))))))
            :caught-error)
    (expect "Attack: a non-positive-integer ARITY -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates ledger '((cf6 0 (nil nil nil))))))
            :caught-error)
    ;; -- 3: groundedness --
    (expect "Attack: pure self-recursion with NO base clause at all -- can never be derived, must error"
            (must-signal-error
             (lambda () (define-inductive-predicates
                         ledger '((cf7 1 (((cf7 ?x)) nil ((S ?x))))))))
            :caught-error)
    (expect "Attack: a 2-predicate mutual cycle with no base case anywhere in it -- must error"
            (must-signal-error
             (lambda () (define-inductive-predicates
                         ledger '((cf8 1 (((cf9 ?x)) nil ((S ?x))))
                                  (cf9 1 (((cf8 ?x)) nil ((S ?x))))))))
            :caught-error)
    ;; -- sanity: legitimate groups (fresh names) still go through --
    (expect "Sanity: a legitimate mutual-recursion GROUP with fresh names still succeeds"
            (let ((l (define-inductive-predicates
                      ledger '((cok-even 1 (nil nil (zero)) (((cok-odd ?x)) nil ((S ?x))))
                               (cok-odd 1 (((cok-even ?x)) nil ((S ?x))))))))
              (judgement? 'wff? '(cok-even v0) l))
            t)
    (expect "Sanity: a legitimate n-ary GROUP with a fresh name still succeeds"
            (let ((l (define-inductive-predicates
                      ledger '((cok-sumr 3 (nil (?x) (?x zero ?x))
                                         (((cok-sumr ?x ?y ?z)) nil (?x (S ?y) (S ?z))))))))
              (judgement? 'wff? '(cok-sumr v0 v1 v2) l))
            t)
    ledger))

(defun run-inductive-definition-self-tests ()
  "Section 20: DEFINE-INDUCTIVE-PREDICATE(S) -- formation, introduction
(both AXIOM and IRULE clause shapes), a full induction proof via a
mechanically generated induction axiom, attack tests, and a second,
differently-shaped predicate confirming the generator isn't secretly
EVEN-specific; CHECK-INDUCTIVE-GROUP-WELL-FORMED's own consistency-check
attack tests (name collision, shape, groundedness); plus the two
general-case worked examples: mutual recursion (EVEN/ODD) and an n-ary
relation (SUMR, the graph of addition)."
  (let* ((ledger (bootstrap-kernel :arithmetic t))
         (ledger (test-inductive-even ledger))
         (ledger (test-inductive-generality ledger))
         (ledger (test-inductive-consistency-checks ledger)))
    (declare (ignorable ledger))
    ;; The two general-case (DEFINE-INDUCTIVE-PREDICATES, plural) worked
    ;; examples each get their OWN fresh ledger rather than threading the
    ;; one above: they reuse the predicate name EVEN (the mutual example)
    ;; and would otherwise now be REFUSED outright by
    ;; CHECK-INDUCTIVE-GROUP-WELL-FORMED's own name-collision check,
    ;; since the DIFFERENTLY-SHAPED, purely self-recursive EVEN already
    ;; minted by TEST-INDUCTIVE-EVEN is still on this same ledger (this
    ;; is precisely the bug TEST-INDUCTIVE-CONSISTENCY-CHECKS' first
    ;; attack test above provokes deliberately and confirms is now
    ;; caught, rather than silently accepted the way it was when this
    ;; mutual EVEN/ODD example was first written).
    (test-inductive-mutual-even-odd (bootstrap-kernel :arithmetic t))
    (test-inductive-nary-sumr (bootstrap-kernel :arithmetic t))
    (format t "~%Inductive-definition self-tests complete.~%")))

;;; ---------------------------------------------------------------------
;;; 21. EXISTS-ELIM: genuine existential elimination
;;; ---------------------------------------------------------------------
;;;
;;; III.3 could only ever INTRODUCE a .EXISTS-headed formula (from a
;;; concrete witness); there was no way to go the other direction and
;;; actually USE an already-proven (.exists ?x ?A) for anything besides
;;; citing it as IOTA's own existence premise. EXISTS-ELIM (Mendelson's
;;; Rule C) closes that gap: given (.exists ?x ?A) and a proof that SOME
;;; already-established formula Ac implies C, where Ac is verified (via
;;; the new @substitutes? meta-predicate) to equal A with x instantiated
;;; to a fresh witness variable w, concludes C outright.

(defun test-exists-elim (ledger)
  "The positive case (from exists v0(v0=v1), conclude v1=v1 by
instantiating the witness to a fresh v2 and immediately discarding it via
K/II.1 -- so, exactly like the EVEN-IND wiring test in Section 20, this
exercises the MECHANISM, not a deep fact), plus four attacks: the wrong-
Ac case (@substitutes? itself catches a citer's mismatched substitution
instance), and the three freshness violations (witness free in Gamma,
free in A, free in the conclusion C)."
  (expect "positive: from exists v0(v0=v1), conclude v1=v1 via witness v2"
          (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :hyp nil)
                            (1 (.eq v1 v1) :axiom (IV.1))
                            (2 (.to (.eq v1 v1) (.to (.eq v2 v1) (.eq v1 v1))) :axiom (II.1))
                            (3 (.to (.eq v2 v1) (.eq v1 v1)) :ir (MP 2 1))
                            (4 (.eq v1 v1) :ir (EXISTS-ELIM 0 3 v2)))
                          ledger)
          t)
  (expect "Attack: witness v2 free in an open hypothesis (Gamma) -- must reject"
          (check-k-proof '((0 (.eq v2 v3) :hyp nil)
                            (1 (.exists v0 (.eq v0 v1)) :hyp nil)
                            (2 (.eq v1 v1) :axiom (IV.1))
                            (3 (.to (.eq v1 v1) (.to (.eq v2 v1) (.eq v1 v1))) :axiom (II.1))
                            (4 (.to (.eq v2 v1) (.eq v1 v1)) :ir (MP 3 2))
                            (5 (.eq v1 v1) :ir (EXISTS-ELIM 1 4 v2)))
                          ledger)
          nil)
  (expect "Attack: witness v2 already free in A itself -- must reject"
          (check-k-proof '((0 (.exists v0 (.eq v0 v2)) :hyp nil)
                            (1 (.eq v1 v1) :axiom (IV.1))
                            (2 (.to (.eq v1 v1) (.to (.eq v2 v2) (.eq v1 v1))) :axiom (II.1))
                            (3 (.to (.eq v2 v2) (.eq v1 v1)) :ir (MP 2 1))
                            (4 (.eq v1 v1) :ir (EXISTS-ELIM 0 3 v2)))
                          ledger)
          nil)
  (expect "Attack: the cited antecedent does NOT actually equal A[w/x] -- must reject"
          (check-k-proof '((0 (.exists v0 (.eq v0 v1)) :hyp nil)
                            (1 (.eq v1 v1) :axiom (IV.1))
                            (2 (.to (.eq v1 v1) (.to (.eq v2 v3) (.eq v1 v1))) :axiom (II.1))
                            (3 (.to (.eq v2 v3) (.eq v1 v1)) :ir (MP 2 1))
                            (4 (.eq v1 v1) :ir (EXISTS-ELIM 0 3 v2)))
                          ledger)
          nil)
  (let ((selfimp-proof '((0 (.to (.to (.eq v2 v1) (.to (.to (.eq v2 v1) (.eq v2 v1)) (.eq v2 v1)))
                                 (.to (.to (.eq v2 v1) (.to (.eq v2 v1) (.eq v2 v1))) (.to (.eq v2 v1) (.eq v2 v1))))
                             :axiom (II.2))
                          (1 (.to (.eq v2 v1) (.to (.to (.eq v2 v1) (.eq v2 v1)) (.eq v2 v1))) :axiom (II.1))
                          (2 (.to (.to (.eq v2 v1) (.to (.eq v2 v1) (.eq v2 v1))) (.to (.eq v2 v1) (.eq v2 v1)))
                             :ir (MP 0 1))
                          (3 (.to (.eq v2 v1) (.to (.eq v2 v1) (.eq v2 v1))) :axiom (II.1))
                          (4 (.to (.eq v2 v1) (.eq v2 v1)) :ir (MP 2 3)))))
    (expect "Attack setup: the self-implication (v2=v1)->(v2=v1) itself checks (S/K derivation)"
            (check-k-proof selfimp-proof ledger) t)
    (expect "Attack: witness v2 leaks into the CONCLUSION C itself -- must reject"
            (check-k-proof (append '((0 (.exists v0 (.eq v0 v1)) :hyp nil)) selfimp-proof
                                    '((5 (.eq v2 v1) :ir (EXISTS-ELIM 0 4 v2))))
                            ledger)
            nil))
  ledger)

(defun run-exists-elim-self-tests ()
  "Section 21: EXISTS-ELIM -- the positive case plus four attacks."
  (let* ((ledger (bootstrap-kernel))
         (ledger (test-exists-elim ledger)))
    (declare (ignorable ledger))
    (format t "~%EXISTS-ELIM self-tests complete.~%")))

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

(defun test-define-function-by-description (ledger)
  "Worked example: DOUBLE(x) := the y such that y = x+x. Proves EXISTENCE
(trivially, y:=x+x itself witnesses it, via III.3) and UNIQUENESS
(symmetry/transitivity, the exact same multi-step deduction-theorem-direct
chaining pattern as Section 19's own uniq-full) as ordinary, independent
theorems first -- DEFINE-FUNCTION-BY-DESCRIPTION never sees a single
IOTA/EXISTS-ELIM step, only their FINAL closed conclusions -- then defines
DOUBLE and confirms the defining axiom makes it behave exactly as
specified, plus attack tests for both prerequisite-mismatch failure
modes."
  (let* ((exists-proof '((0 (.eq (+ v0 v0) (+ v0 v0)) :axiom (IV.1))
                          (1 (.to (.eq (+ v0 v0) (+ v0 v0)) (.exists v1 (.eq v1 (+ v0 v0)))) :axiom (III.3 v1 (.eq v1 (+ v0 v0)) (+ v0 v0)))
                          (2 (.exists v1 (.eq v1 (+ v0 v0))) :ir (MP 1 0))
                          (3 (.forall v0 (.exists v1 (.eq v1 (+ v0 v0)))) :ir (Gen 2 v0))))
         (ledger (check-and-extend ledger 'th 'th-double-exists exists-proof)))
    (expect "existence: forall v0 (exists v1 (v1=v0+v0)) is a real ledger theorem"
            (check-k-proof '((0 (.forall v0 (.exists v1 (.eq v1 (+ v0 v0)))) :th (th-double-exists))) ledger)
            t)
    (let* ((inner '((0 (.eq v1 (+ v0 v0)) :hyp nil)
                     (1 (.eq v2 (+ v0 v0)) :hyp nil)
                     (2 (.to (.eq v2 (+ v0 v0)) (.eq (+ v0 v0) v2)) :axiom (IV.3))
                     (3 (.eq (+ v0 v0) v2) :ir (MP 2 1))
                     (4 (.to (.eq v1 (+ v0 v0)) (.to (.eq (+ v0 v0) v2) (.eq v1 v2))) :axiom (IV.4))
                     (5 (.to (.eq (+ v0 v0) v2) (.eq v1 v2)) :ir (MP 4 0))
                     (6 (.eq v1 v2) :ir (MP 5 3))))
           (ledger (check-and-extend-by-deduction-direct ledger 'dbl-uniq-step1 '(.eq v2 (+ v0 v0)) inner))
           (step2 '((0 (.eq v1 (+ v0 v0)) :hyp nil)
                    (1 (.to (.eq v2 (+ v0 v0)) (.eq v1 v2)) :th-ded (dbl-uniq-step1 0))))
           (ledger (check-and-extend-by-deduction-direct ledger 'dbl-uniq-step2 '(.eq v1 (+ v0 v0)) step2))
           (ledger (check-and-extend ledger 'th 'dbl-uniq-gen-v2
                                      '((0 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2))) :th-ded (dbl-uniq-step2))
                                        (1 (.forall v2 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2)))) :ir (Gen 0 v2)))))
           (ledger (check-and-extend ledger 'th 'dbl-uniq-gen-v1
                                      '((0 (.forall v2 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2)))) :th (dbl-uniq-gen-v2))
                                        (1 (.forall v1 (.forall v2 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2))))) :ir (Gen 0 v1)))))
           (ledger (check-and-extend ledger 'th 'th-double-uniqueness
                                      '((0 (.forall v1 (.forall v2 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2))))) :th (dbl-uniq-gen-v1))
                                        (1 (.forall v0 (.forall v1 (.forall v2 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2)))))) :ir (Gen 0 v0))))))
      (expect "uniqueness: forall v0,v1,v2 (v1=v0+v0 -> (v2=v0+v0 -> v1=v2)) is a real ledger theorem"
              (check-k-proof '((0 (.forall v0 (.forall v1 (.forall v2 (.to (.eq v1 (+ v0 v0)) (.to (.eq v2 (+ v0 v0)) (.eq v1 v2))))))
                                  :th (th-double-uniqueness)))
                              ledger)
              t)
      (let ((defined-ledger (define-function-by-description
                              ledger 'double '(v0) 'v1 'v2 '(.eq v1 (+ v0 v0))
                              'th-double-exists 'th-double-uniqueness)))
        (expect "(double v0) is a term after DEFINE-FUNCTION-BY-DESCRIPTION"
                (judgement? 'term? '(double v0) defined-ledger) t)
        (expect "the defining axiom makes DOUBLE(v0) = v0+v0 usable directly, no IOTA in sight"
                (check-k-proof '((0 (.eq (double v0) (+ v0 v0)) :axiom (double-def))) defined-ledger)
                t)
        (expect "Attack: EXISTENCE-NAME argument swapped for UNIQUENESS-NAME -- must error, not silently define"
                (handler-case (progn (define-function-by-description
                                       ledger 'double2 '(v0) 'v1 'v2 '(.eq v1 (+ v0 v0))
                                       'th-double-uniqueness 'th-double-exists)
                                      :no-error)
                              (error () :caught-error))
                :caught-error)
        (expect "Attack: a WRONG defining formula (mismatched with the actual proven theorems) -- must error"
                (handler-case (progn (define-function-by-description
                                       ledger 'double3 '(v0) 'v1 'v2 '(.eq v1 (+ v0 zero))
                                       'th-double-exists 'th-double-uniqueness)
                                      :no-error)
                              (error () :caught-error))
                :caught-error)
        defined-ledger))))

(defun run-function-definition-self-tests ()
  "Section 22: DEFINE-FUNCTION-BY-DESCRIPTION -- the DOUBLE worked
example (existence, uniqueness, definition, and using the defined
function directly) plus two prerequisite-mismatch attack tests."
  (let* ((ledger (bootstrap-kernel :arithmetic t))
         (ledger (test-define-function-by-description ledger)))
    (declare (ignorable ledger))
    (format t "~%Function-definition self-tests complete.~%")))

(in-package :cl-user)
(ledger-kernel::run-self-tests)
(ledger-kernel::run-classical-logic-self-tests)
(ledger-kernel::run-tactics-self-tests)
(ledger-kernel::run-alpha-conversion-self-tests)
(ledger-kernel::run-derived-entry-memoization-self-tests)
(ledger-kernel::run-bootstrap-from-spec-self-tests)
(ledger-kernel::run-iota-self-tests)
(ledger-kernel::run-inductive-definition-self-tests)
(ledger-kernel::run-exists-elim-self-tests)
(ledger-kernel::run-function-definition-self-tests)
