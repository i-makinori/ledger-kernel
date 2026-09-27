;;;; persistence.lisp -- Section 10: persistence as a flat command stream
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

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
;;;   (:declare-predicate-schema-symbol SYM ARITY)
;;;   (:th   NAME RAW-PROOF)
;;;   (:ith  NAME RAW-PROOF)
;;;   (:def-abbrev NAME DEFINIENS RAW-PROOF)
;;;   (:th-ded NAME HYP-FORMULA RAW-PROOF)
;;;   (:define-function-by-description NAME ARG-VARS Y-VAR Y2-VAR A-FORMULA
;;;                                    EXISTENCE-NAME UNIQUENESS-NAME)
;;; The last one replays DEFINE-FUNCTION-BY-DESCRIPTION (Section 22),
;;; which re-checks its existence/uniqueness theorems before minting the
;;; new function symbol; see the :PRIMITIVE note just below.
;;; :PRIMITIVE entries are never part of the stream: nothing outside
;;; BOOTSTRAP-KERNEL's own lexical scope can create one (ADMIT-PRIMITIVE
;;; is closed, by design -- see section 2), and BOOTSTRAP-KERNEL is
;;; deterministic given the same :ATOMIC-SYMBOLS/:VARIABLES, so replaying
;;; a command stream always starts from a fresh (BOOTSTRAP-KERNEL) call,
;;; never from a saved copy of the primitive base itself. The one
;;; exception is a :PRIMITIVE entry minted by DEFINE-FUNCTION-BY-
;;; DESCRIPTION: its ORIGIN is (:PRIMITIVE :BY-DESCRIPTION COMMAND), and
;;; LEDGER-COMMANDS writes COMMAND (once, at the defining axiom) so that
;;; the definition is replayed -- and re-checked -- rather than lost.
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
  (loop for e in (treap-values-below (ledger-all ledger) (ledger-bound ledger))
        for origin = (entry-origin e)
        for cmd = (if (eq (car origin) :primitive)
                      ;; :PRIMITIVE entries are BOOTSTRAP-KERNEL's (or a
                      ;; .system file's) own doing -- the seed symbols plus
                      ;; TERM?/WFF?/IRULE/AXIOM rules -- reconstructed by
                      ;; bootstrapping again in LEDGER-FROM-COMMANDS, never
                      ;; by a DECLARE-* command, which would wrongly treat an
                      ;; already-seeded symbol as a fresh one and be refused.
                      ;; The one exception is a DEFINE-FUNCTION-BY-DESCRIPTION
                      ;; definition, written once, at its defining axiom.
                      (and (eq (second origin) :by-description)
                           (eq (entry-kind e) 'axiom)
                           (third origin))
                      (case (entry-kind e)
                        (atomic-wff-symbol (list :declare-atomic-wff-symbol (entry-payload e)))
                        (variable-symbol (list :declare-variable-symbol (entry-payload e)))
                        (predicate-schema-symbol
                         (list* :declare-predicate-schema-symbol (entry-payload e)))
                        ((th ith)
                         (destructuring-bind (name raw-proof) (entry-payload e)
                           (list (if (eq (entry-kind e) 'th) :th :ith) name raw-proof)))
                        (def-abbrev
                         (destructuring-bind (name raw-proof) (entry-payload e)
                           (list :def-abbrev name (proof-conclusion raw-proof) raw-proof)))
                        (th-ded
                         (destructuring-bind (name hyp-formula raw-proof) (entry-payload e)
                           (list :th-ded name hyp-formula raw-proof)))
                        (t nil)))
        when cmd collect cmd))

(defun ledger-from-commands (commands &key (log (silent-log))
                                            (ledger (error "LEDGER-FROM-COMMANDS: :LEDGER is required (e.g. one built by BOOTSTRAP-KERNEL-FROM-SPEC-FILE).")))
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
  (progn
    (dolist (cmd commands ledger)
      (destructuring-bind (op . args) cmd
        (setf ledger
              (case op
                (:declare-atomic-wff-symbol (declare-atomic-wff-symbol ledger (first args)))
                (:declare-variable-symbol (declare-variable-symbol ledger (first args)))
                (:declare-predicate-schema-symbol
                 (declare-predicate-schema-symbol ledger (first args) (second args)))
                ((:th :ith) (destructuring-bind (name raw-proof) args
                              (check-and-extend ledger (if (eq op :th) 'th 'ith) name raw-proof log)))
                (:def-abbrev (destructuring-bind (name definiens raw-proof) args
                               (check-and-extend-abbrev ledger name definiens raw-proof log)))
                (:th-ded (destructuring-bind (name hyp-formula raw-proof) args
                           (check-and-extend-by-deduction-direct ledger name hyp-formula raw-proof log)))
                (:define-function-by-description
                 (apply #'define-function-by-description ledger args))
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

(defun read-forms-from-file (path)
  "Every top-level S-expression in PATH, read as DATA ONLY: with the
standard readtable and *READ-EVAL* off, so #.(...) in a file signals a
reader error instead of running code, and no reader macro installed in the
current image can change how the file is read. Symbols are read in the
LEDGER-KERNEL package. This is what makes it true that loading a .ledger
or .system file cannot do anything but hand commands to the kernel's own
gates: a hostile file can fail to load, but it cannot execute."
  (with-open-file (in path :direction :input)
    (with-standard-io-syntax
      (let ((*read-eval* nil)
            (*package* (find-package :ledger-kernel)))
        (loop for form = (read in nil in)   ; the stream itself as EOF marker
              until (eq form in)
              collect form)))))

(defun read-ledger-from-file (path &key (log (silent-log))
                                         (ledger (error "READ-LEDGER-FROM-FILE: :LEDGER is required (e.g. one built by BOOTSTRAP-KERNEL-FROM-SPEC-FILE).")))
  "Read a command stream written by WRITE-LEDGER-TO-FILE back into a
genuine, freshly re-verified ledger (LEDGER-FROM-COMMANDS) -- reloading a
ledger costs exactly as much re-verification work as building it live
did, by design (see the section header above).

LEDGER, when supplied, is the starting point PATH's commands are replayed
onto (see LEDGER-FROM-COMMANDS) instead of a fresh BOOTSTRAP-KERNEL --
this is how several files chain into one growing ledger, module by
module: (READ-LEDGER-FROM-FILE \"b.ledger\" :LEDGER (READ-LEDGER-FROM-FILE
\"a.ledger\"))."
  (ledger-from-commands (read-forms-from-file path)
                        :log log
                        :ledger ledger))
