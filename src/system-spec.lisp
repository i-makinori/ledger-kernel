;;;; system-spec.lisp -- defining a logic from a .system file
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; A .system file lists the primitive vocabulary, formation rules,
;;; axioms and inference rules of a logic. Its directives are:
;;;   (:atomic-wff-symbols SYM...)
;;;   (:variable-symbols SYM...)
;;;   (:term-formation NAME CONDITIONS RESULT-PATTERN)
;;;   (:wff-formation   NAME CONDITIONS RESULT-PATTERN)
;;;   (:axiom NAME CONDITIONS (EXTRA-PARAM-PATTERNS CONCLUSION-PATTERN))
;;;   (:irule NAME CONDITIONS (PREMISE-PATTERNS EXTRA-PARAM-PATTERNS
;;;                            :=> CONCLUSION-PATTERN))
;;; CONDITIONS and patterns may use only the kernel's fixed catalog of
;;; meta-predicates and meta-constructors; a new one needs new Lisp code.
;;;
;;; Trust: unlike .ledger theorems, .system entries are :PRIMITIVE,
;;; admitted by fiat with nothing to check them against. Loading one is
;;; an act of trust in its author (an inconsistent axiom set cannot be
;;; detected from inside). BOOTSTRAP-KERNEL-FROM-SPEC is the only code
;;; that creates :PRIMITIVE entries, and everything derived on top is
;;; still fully checked.

(defun bootstrap-kernel-from-spec (spec &key (atomic-symbols '(A B C D E F G H))
                                              (variables '(v0 v1 v2 v3 v4 v5))
                                              (ledger nil)
                                              (origin-note nil))
  "Admit SPEC's directives as :PRIMITIVE entries onto LEDGER, or, when
LEDGER is NIL, onto an empty ledger seeded with ATOMIC-SYMBOLS and
VARIABLES. Passing LEDGER chains .system files (e.g. base logic, then
arithmetic). ORIGIN-NOTE is stored as (:PRIMITIVE . ORIGIN-NOTE); only
LEDGER-COMMANDS reads it, to recognize function definitions."
  (labels ((admit (ledger kind payload)
             "The only way to create a :PRIMITIVE entry; private to this function."
             (ledger-append ledger kind payload (list* :primitive origin-note)))
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
  "The directives in PATH, read as data only (READ-FORMS-FROM-FILE)."
  (read-forms-from-file path))

(defun bootstrap-kernel-from-spec-file (path &key (atomic-symbols '(A B C D E F G H))
                                                   (variables '(v0 v1 v2 v3 v4 v5))
                                                   (ledger nil))
  "Read the .system file PATH and admit it with BOOTSTRAP-KERNEL-FROM-SPEC."
  (bootstrap-kernel-from-spec (read-system-spec-from-file path)
                               :atomic-symbols atomic-symbols :variables variables :ledger ledger))
