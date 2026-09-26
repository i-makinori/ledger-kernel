;;;; generate-connectives-ledger.lisp
;;;;
;;;; Regenerates hilbert-library/06-connectives.ledger: the basic
;;;; propositional lemmas for .and/.or/.iff, each proved by PROVE-TAUTOLOGY.
;;;; The generated file is an ordinary .ledger command stream; loading it
;;;; re-verifies every proof from scratch, so this script is a convenience,
;;;; not part of the trusted base.
;;;;
;;;; Usage, from the repository root:
;;;;   sbcl --non-interactive --load tools/generate-connectives-ledger.lisp

(require :asdf)
(asdf:load-asd (merge-pathnames "ledger-kernel.asd"))
(asdf:load-system :ledger-kernel)

(in-package :ledger-kernel)

(defparameter *connective-lemmas*
  '((th-contrapositive   (.to (.to a b) (.to (.neg b) (.neg a))))
    ;; conjunction
    (th-and-intro        (.to a (.to b (.and a b))))
    (th-and-elim-l       (.to (.and a b) a))
    (th-and-elim-r       (.to (.and a b) b))
    (th-and-comm         (.to (.and a b) (.and b a)))
    ;; disjunction
    (th-or-intro-l       (.to a (.or a b)))
    (th-or-intro-r       (.to b (.or a b)))
    (th-or-elim          (.to (.to a c) (.to (.to b c) (.to (.or a b) c))))
    (th-or-comm          (.to (.or a b) (.or b a)))
    (th-excluded-middle  (.or a (.neg a)))
    ;; biconditional
    (th-iff-intro        (.to (.to a b) (.to (.to b a) (.iff a b))))
    (th-iff-mp           (.to (.iff a b) (.to a b)))
    (th-iff-mpr          (.to (.iff a b) (.to b a)))
    (th-iff-refl         (.iff a a))
    (th-iff-sym          (.to (.iff a b) (.iff b a)))
    (th-iff-trans        (.to (.iff a b) (.to (.iff b c) (.iff a c))))
    ;; De Morgan
    (th-not-and          (.iff (.neg (.and a b)) (.or (.neg a) (.neg b))))
    (th-not-or           (.iff (.neg (.or a b)) (.and (.neg a) (.neg b)))))
  "(NAME FORMULA) pairs, in the order they are admitted.")

(defun library-file (name)
  (asdf:system-relative-pathname :ledger-kernel (concatenate 'string "hilbert-library/" name)))

(defun connectives-base-ledger ()
  "00-classical-fol-equality.system + 00-connectives.system + the
01/02/03/05 .ledger modules that PROVE-TAUTOLOGY relies on."
  (reduce (lambda (l f) (read-ledger-from-file (library-file f) :ledger l))
          '("01-propositional-core.ledger" "02-predicate-core.ledger"
            "03-equality-core.ledger" "05-classical-logic.ledger")
          :initial-value (bootstrap-kernel-from-spec-file
                          (library-file "00-connectives.system")
                          :ledger (bootstrap-kernel-from-spec-file
                                   (library-file "00-classical-fol-equality.system")))))

(let* ((base (connectives-base-ledger))
       (ledger (reduce (lambda (l lemma) (prove-tautology l (second lemma) (first lemma)))
                       *connective-lemmas* :initial-value base))
       (new-commands (nthcdr (length (ledger-commands base)) (ledger-commands ledger)))
       (path (library-file "06-connectives.ledger")))
  (write-commands-to-file new-commands path)
  (format t "~&Wrote ~D commands (~D lemmas) to ~A~%"
          (length new-commands) (length *connective-lemmas*) path))
