;;;; persistence.lisp -- saving and loading a ledger as a command stream
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; A saved ledger is not a dump of ENTRY structs or indices. It is the
;;; flat list of COMMANDS -- calls to the growth API -- that built it,
;;; replayed onto a starting ledger to rebuild it. A command is one of:
;;;   (:declare-atomic-wff-symbol SYM)
;;;   (:declare-variable-symbol SYM)
;;;   (:declare-predicate-schema-symbol SYM ARITY)
;;;   (:th     NAME RAW-PROOF)
;;;   (:th-ded NAME HYP-FORMULA RAW-PROOF)
;;;   (:define-function-by-description NAME ARG-VARS Y-VAR Y2-VAR A-FORMULA
;;;                                    EXISTENCE-NAME UNIQUENESS-NAME)
;;;
;;; :PRIMITIVE entries are not written: they come from .system files, so
;;; a stream must be replayed onto a ledger bootstrapped from the same
;;; .system files. The exception is a DEFINE-FUNCTION-BY-DESCRIPTION
;;; definition, written as its command so that it is replayed and
;;; re-checked.
;;;
;;; Loading is not privileged: every command is re-verified through the
;;; ordinary gates, so a corrupted or hand-edited file can fail to load
;;; but cannot smuggle in an unverified entry.

(defun entry-source-payload (e)
  "E's payload as it was written: for a TH / TH-DED entry the payload holds
the kernel (de Bruijn) form that citations use, and the ORIGIN keeps the
surface text, with its variable names, which is what is saved and shown.
Other entries are returned unchanged."
  (let ((origin (entry-origin e)) (p (entry-payload e)))
    (case (entry-kind e)
      (th (if (eq (car origin) :derived) (list (first p) (second origin)) p))
      (th-ded (if (eq (car origin) :derived-by-deduction)
                  (list (first p) (second origin) (third origin))
                  p))
      (t p))))

(defun ledger-commands (ledger &key canonical)
  "The command stream that rebuilds LEDGER's non-primitive entries, in
admission order (read from LEDGER's own ALL index, up to its BOUND).
Theorems are written as they were written (ENTRY-SOURCE-PAYLOAD), or,
with CANONICAL, in the canonical form that was checked and stored
(canonical.lisp): the verified facts, independent of how they were named.
Either stream replays to the same ledger."
  (loop for e in (treap-values-below (ledger-all ledger) (ledger-bound ledger))
        for origin = (entry-origin e)
        for cmd = (if (eq (car origin) :primitive)
                      ;; Primitive entries come back from the .system files,
                      ;; except a by-description definition, written once,
                      ;; at its defining axiom.
                      (and (eq (second origin) :by-description)
                           (eq (entry-kind e) 'axiom)
                           (third origin))
                      (case (entry-kind e)
                        (atomic-wff-symbol (list :declare-atomic-wff-symbol (entry-payload e)))
                        (variable-symbol (list :declare-variable-symbol (entry-payload e)))
                        (predicate-schema-symbol
                         (list* :declare-predicate-schema-symbol (entry-payload e)))
                        (th
                         (destructuring-bind (name raw-proof)
                             (if canonical (entry-payload e) (entry-source-payload e))
                           (list :th name raw-proof)))
                        (th-ded
                         (destructuring-bind (name hyp-formula raw-proof)
                             (if canonical (entry-payload e) (entry-source-payload e))
                           (list :th-ded name hyp-formula raw-proof)))
                        (t nil)))
        when cmd collect cmd))

(defun ledger-from-commands (commands &key (log (silent-log))
                                            (ledger (error "LEDGER-FROM-COMMANDS: :LEDGER is required (e.g. one built by BOOTSTRAP-KERNEL-FROM-SPEC-FILE).")))
  "Replay COMMANDS in order onto LEDGER through the ordinary growth API.
LEDGER must carry the same primitive base the commands were written
against; it may also be an already-grown ledger, so separate files can
be chained as modules."
  (dolist (cmd commands ledger)
    (destructuring-bind (op . args) cmd
      (setf ledger
            (case op
              (:declare-atomic-wff-symbol (declare-atomic-wff-symbol ledger (first args)))
              (:declare-variable-symbol (declare-variable-symbol ledger (first args)))
              (:declare-predicate-schema-symbol
               (declare-predicate-schema-symbol ledger (first args) (second args)))
              (:th (destructuring-bind (name raw-proof) args
                     (check-and-extend ledger 'th name raw-proof log)))
              (:th-ded (destructuring-bind (name hyp-formula raw-proof) args
                         (check-and-extend-by-deduction-direct ledger name hyp-formula raw-proof log)))
              (:define-function-by-description
               (apply #'define-function-by-description ledger args))
              (t (error "LEDGER-FROM-COMMANDS: unknown command ~S" cmd)))))))

(defun write-commands-to-file (commands path)
  "Write COMMANDS to PATH as plain S-expressions, one per line. *PACKAGE*
is bound to LEDGER-KERNEL so symbols read back as the same symbols."
  (with-open-file (out path :direction :output :if-exists :supersede :if-does-not-exist :create)
    (let ((*package* (find-package :ledger-kernel))
          (*print-case* :downcase))
      (dolist (cmd commands)
        (prin1 cmd out)
        (terpri out))))
  path)

(defun write-ledger-to-file (ledger path &key canonical)
  "Write LEDGER's command stream (LEDGER-COMMANDS) to PATH; with
CANONICAL, the canonical form of every theorem."
  (write-commands-to-file (ledger-commands ledger :canonical canonical) path))

(defun read-forms-from-file (path)
  "Every top-level form in PATH, read as data only: standard readtable,
*READ-EVAL* NIL (so #. cannot run code), symbols in LEDGER-KERNEL. A
hostile .ledger or .system file can fail to load but cannot execute."
  (with-open-file (in path :direction :input)
    (with-standard-io-syntax
      (let ((*read-eval* nil)
            (*package* (find-package :ledger-kernel)))
        (loop for form = (read in nil in)   ; the stream itself as EOF marker
              until (eq form in)
              collect form)))))

(defun read-ledger-from-file (path &key (log (silent-log))
                                         (ledger (error "READ-LEDGER-FROM-FILE: :LEDGER is required (e.g. one built by BOOTSTRAP-KERNEL-FROM-SPEC-FILE).")))
  "Replay the commands in PATH onto LEDGER, re-verifying each one (see
LEDGER-FROM-COMMANDS)."
  (ledger-from-commands (read-forms-from-file path)
                        :log log
                        :ledger ledger))
