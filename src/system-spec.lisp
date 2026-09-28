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

;;; --- Bound pattern variables in canonical form ------------------------
;;;
;;; A rule's pattern variables are local to the rule, so renaming them
;;; changes nothing. Those that appear as the variable of a binder, e.g.
;;; ?X and ?U in
;;;   (.to (.exists1 ?x ?A) (.exists ?x (.and ?A (.forall ?u ...))))
;;; are renamed ?BV1, ?BV2, ... ("bound variable 1, 2, ...") in the order
;;; in which they first appear as a binder's variable, walking the rule's
;;; FORM and then its CONDITIONS. The renaming is per rule and applied to
;;; the whole rule at once (form, conditions, extra parameters), so a
;;; variable that is also used free, like Gen's ?x, is renamed everywhere.
;;; Other pattern variables (?A, ?t, ?w, ...) keep their names, as the
;;; free variables and atoms of a theorem do. The names as written are
;;; kept in the entry's ORIGIN under :SOURCE-NAMES.

(defun bound-pattern-variable-name-p (sym)
  "T iff SYM is a canonical bound pattern variable ?BVn."
  (and (pat-var-p sym)
       (let ((s (symbol-name sym)))
         (and (> (length s) 3) (string= (subseq s 0 3) "?BV")
              (every #'digit-char-p (subseq s 3))))))

(defun rule-binder-renaming (conditions form)
  "Alist ?x -> ?BVn for the pattern variables bound by a binder in FORM or
CONDITIONS, numbered in order of first appearance."
  (let ((map nil) (n 0))
    (labels ((walk (x)
               (when (consp x)
                 (when (and (named-binder-p x) (pat-var-p (second x))
                            (not (assoc (second x) map :test #'eq)))
                   (push (cons (second x)
                               (intern (format nil "?BV~D" (incf n)) :ledger-kernel))
                         map))
                 (walk (car x))
                 (walk (cdr x)))))
      (walk form)
      (walk conditions))
    (nreverse map)))

(defun canonicalize-rule-binders (name conditions form)
  "(VALUES conditions form map): CONDITIONS and FORM with their bound
pattern variables renamed ?BV1, ?BV2, ... (RULE-BINDER-RENAMING), all at
once. Signals an error if the rule already uses a ?BVn name for
something else, since the renaming would then merge two variables."
  (let ((map (rule-binder-renaming conditions form)))
    (labels ((clash (x)
               (cond ((consp x) (or (clash (car x)) (clash (cdr x))))
                     (t (and (bound-pattern-variable-name-p x)
                             (not (assoc x map :test #'eq))
                             (rassoc x map :test #'eq))))))
      (when (or (clash conditions) (clash form))
        (error "BOOTSTRAP-KERNEL-FROM-SPEC: rule ~S uses a ?BVn pattern ~
                variable of its own; rename it." name)))
    (values (sublis map conditions) (sublis map form) map)))

(defun bootstrap-kernel-from-spec (spec &key (atomic-symbols '(A B C D E F G H))
                                              (variables '(v0 v1 v2 v3 v4 v5))
                                              (ledger nil)
                                              (origin-note nil))
  "Admit SPEC's directives as :PRIMITIVE entries onto LEDGER, or, when
LEDGER is NIL, onto an empty ledger seeded with ATOMIC-SYMBOLS and
VARIABLES. Passing LEDGER chains .system files (e.g. base logic, then
arithmetic). ORIGIN-NOTE is stored as (:PRIMITIVE . ORIGIN-NOTE); only
LEDGER-COMMANDS reads it, to recognize function definitions."
  (labels ((admit (ledger kind payload &optional source-names)
             "The only way to create a :PRIMITIVE entry; private to this function."
             (ledger-append ledger kind payload
                            (list* :primitive
                                   (append origin-note
                                           (and source-names (list :source-names source-names))))))
           (admit-rule (ledger kind name conditions form)
             "Admit a rule with its bound pattern variables made canonical."
             (multiple-value-bind (c f map) (canonicalize-rule-binders name conditions form)
               (admit ledger kind (list name c f) map)))
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
                                    (admit-rule ledger 'term? name conditions result-pattern)))
                (:wff-formation (destructuring-bind (name conditions result-pattern) (cdr cmd)
                                   (admit-rule ledger 'wff? name conditions result-pattern)))
                (:axiom (destructuring-bind (name conditions form) (cdr cmd)
                          (admit-rule ledger 'axiom name conditions form)))
                (:irule (destructuring-bind (name conditions form) (cdr cmd)
                          (admit-rule ledger 'irule name conditions form)))
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
