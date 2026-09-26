;;;; predicate-schema-tests.lisp -- predicate schema symbols, :INST,
;;;; vocabulary visibility, and hilbert-library/07-quantifier-schemas.ledger
;;;; Part of the ledger-kernel/tests system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun test-predicate-schema-declarations (ledger)
  "Declaring P/1 and R/2; formation of their applications; freshness."
  (let* ((ledger (declare-predicate-schema-symbol ledger 'p 1))
         (ledger (declare-predicate-schema-symbol ledger 'r 2)))
    (expect "(p v0) is a wff" (judgement? 'wff? '(p v0) ledger) t)
    (expect "(p (.iota v1 (.eq v1 v2))) is a wff (any term as argument)"
            (judgement? 'wff? '(p (.iota v1 (.eq v1 v2))) ledger) t)
    (expect "(r v0 v1) is a wff" (judgement? 'wff? '(r v0 v1) ledger) t)
    (expect "Attack: (p v0 v1) -- wrong arity -- is not a wff" (judgement? 'wff? '(p v0 v1) ledger) nil)
    (expect "Attack: (p A) -- a wff, not a term, as argument -- is not a wff" (judgement? 'wff? '(p A) ledger) nil)
    (expect "Attack: (s v0) with S undeclared is not a wff" (judgement? 'wff? '(s v0) ledger) nil)
    (expect "v0 is free in (p v0)" (meta-not-free-in? ledger nil 'v0 '(p v0)) nil)
    (expect "v0 is not free in (.forall v0 (p v0))" (meta-not-free-in? ledger nil 'v0 '(.forall v0 (p v0))) t)
    (expect "Attack: declaring P a second time -- must error"
            (handler-case (progn (declare-predicate-schema-symbol ledger 'p 1) :declared)
              (error () :refused))
            :refused)
    (expect "Attack: declaring P as an atomic-wff symbol too -- must error"
            (handler-case (progn (declare-atomic-wff-symbol ledger 'p) :declared)
              (error () :refused))
            :refused)
    (expect "Attack: arity 0 -- must error"
            (handler-case (progn (declare-predicate-schema-symbol ledger 'z0 0) :declared)
              (error () :refused))
            :refused)
    ledger))

(defun test-predicate-schema-soundness (ledger)
  "A lemma whose correctness depends on a variable NOT occurring in P:
from P(v1) conclude forall v0. P(v1) (Gen, v0 not free in the
hypothesis). Instances that respect that are accepted; an instance that
puts v0 into P is rejected, however it is requested."
  (let ((ledger (check-and-extend-by-deduction-direct
                 ledger 'th-test-vacuous-gen '(p v1)
                 '((0 (p v1) :hyp nil)
                   (1 (.forall v0 (p v1)) :ir (gen 0 v0))))))
    (expect "vacuous Gen lemma at P(y) := y = y"
            (check-k-proof '((0 (.to (.eq v1 v1) (.forall v0 (.eq v1 v1))) :th-ded (th-test-vacuous-gen)))
                           ledger)
            t)
    (expect "Attack: vacuous Gen lemma at P(y) := v0 = y (v0 captured) -- must reject"
            (check-k-proof '((0 (.to (.eq v0 v1) (.forall v0 (.eq v0 v1))) :th-ded (th-test-vacuous-gen)))
                           ledger)
            nil)
    (expect "Attack: the same capture requested explicitly via :inst -- must reject"
            (check-k-proof '((0 (.to (.eq v0 v1) (.forall v0 (.eq v0 v1)))
                                :th-ded (th-test-vacuous-gen :inst ((p (v2) (.eq v0 v2))))))
                           ledger)
            nil)
    (expect "Attack: :inst replacing the Gen variable v0 by a non-variable -- must reject"
            (check-k-proof '((0 (.to (.eq v2 v1) (.forall (.iota v3 (.eq v3 v3)) (.eq v2 v1)))
                                :th-ded (th-test-vacuous-gen :inst ((v0 (.iota v3 (.eq v3 v3)))))))
                           ledger)
            nil)
    ledger))

(defun test-quantifier-schema-library (ledger)
  "hilbert-library/07-quantifier-schemas.ledger on top of ZF + the empty
set: automatic and explicit instantiation, later vocabulary, attacks."
  (let* ((ledger (read-ledger-from-file (library-path "07-quantifier-schemas.ledger") :ledger ledger))
         (ledger (read-ledger-from-file (zf-library-path "01-empty-set.ledger") :ledger ledger)))
    (expect "th-forall-elim, P found automatically: forall v0 (v0 in v3) -> v1 in v3"
            (check-k-proof '((0 (.to (.forall v0 (.in v0 v3)) (.in v1 v3)) :th (th-forall-elim))) ledger) t)
    (expect "th-forall-elim at the term (empty), via :inst ((v1 (empty)))"
            (check-k-proof '((0 (.to (.forall v0 (.in v0 v3)) (.in (empty) v3))
                                :th (th-forall-elim :inst ((v1 (empty))))))
                           ledger) t)
    (expect "Attack: th-forall-elim at (empty) WITHOUT :inst -- no such instance, must reject"
            (check-k-proof '((0 (.to (.forall v0 (.in v0 v3)) (.in (empty) v3)) :th (th-forall-elim))) ledger)
            nil)
    (expect "th-exists-intro instantiated with (empty), defined AFTER the lemma"
            (check-k-proof '((0 (.to (.eq v1 (empty)) (.exists v0 (.eq v0 (empty)))) :th (th-exists-intro)))
                           ledger) t)
    (expect "th-exists-mono with set-theoretic P and Q"
            (check-k-proof '((0 (.to (.forall v0 (.to (.in v0 v1) (.in v0 v2)))
                                     (.to (.exists v0 (.in v0 v1)) (.exists v0 (.in v0 v2))))
                                :th-ded (th-exists-mono)))
                           ledger) t)
    (expect "th-forall-mono with explicit P and Q"
            (check-k-proof '((0 (.to (.forall v0 (.to (.in v0 v1) (.in v0 v2)))
                                     (.to (.forall v0 (.in v0 v1)) (.forall v0 (.in v0 v2))))
                                :th-ded (th-forall-mono :inst ((p (v3) (.in v3 v1)) (q (v3) (.in v3 v2))))))
                           ledger) t)
    (expect "th-exists1-unique: two empty sets are equal, from E!y (y is empty)"
            (check-k-proof '((0 (.to (.exists1 v0 (.forall v3 (.neg (.in v3 v0))))
                                     (.to (.forall v3 (.neg (.in v3 v1)))
                                          (.to (.forall v3 (.neg (.in v3 v2))) (.eq v1 v2))))
                                :th-ded (th-exists1-unique)))
                           ledger) t)
    (expect "Attack: th-exists1-exists at P(y) := y = v4 (captures the lemma's witness v4) -- must reject"
            (check-k-proof '((0 (.to (.exists1 v0 (.eq v0 v4)) (.exists v0 (.eq v0 v4))) :th-ded (th-exists1-exists)))
                           ledger) nil)
    (expect "... and accepted once the witness is moved out of the way: :inst ((v4 v3))"
            (check-k-proof '((0 (.to (.exists1 v0 (.eq v0 v4)) (.exists v0 (.eq v0 v4)))
                                :th-ded (th-exists1-exists :inst ((v4 v3)))))
                           ledger) t)
    (expect "Attack: :inst P that does not produce the claimed formula -- must reject"
            (check-k-proof '((0 (.to (.forall v0 (.in v0 v3)) (.in v1 v2))
                                :th (th-forall-elim :inst ((p (v0) (.in v0 v3))))))
                           ledger) nil)
    (expect "Attack: :inst with a wrong arity for P -- must reject"
            (check-k-proof '((0 (.to (.forall v0 (.in v0 v3)) (.in v1 v3))
                                :th (th-forall-elim :inst ((p (v0 v2) (.in v0 v3))))))
                           ledger) nil)
    (expect "Attack: :inst naming an undeclared symbol -- must reject"
            (check-k-proof '((0 (.to (.forall v0 (.in v0 v3)) (.in v1 v3))
                                :th (th-forall-elim :inst ((zzz v1)))))
                           ledger) nil)
    (expect "Attack: :inst not followed by a list -- must reject"
            (check-k-proof '((0 (.to (.forall v0 (.in v0 v3)) (.in v1 v3)) :th (th-forall-elim :inst)))
                           ledger) nil)
    (let ((early (entries-upto (entry-k (first (entries-of-kind 'predicate-schema-symbol ledger))) ledger)))
      (expect "vocabulary: (empty), defined later, is still a term in an earlier ENTRIES-UPTO view"
              (judgement? 'term? '(empty) early) t)
      (expect "... but a later THEOREM is not citable from that earlier view"
              (check-k-proof '((0 (.neg (.in v0 (empty))) :th (th-zf-not-in-empty))) early) nil)
      (expect "... nor a later AXIOM"
              (check-k-proof '((0 (.forall v2 (.neg (.in v2 (empty)))) :axiom (empty-def))) early) nil))
    (let ((path "/tmp/ledger-kernel-self-test-predicate-schema.tmp"))
      (unwind-protect
           (expect "a ledger with predicate schema declarations round-trips through a file"
                   (progn (write-ledger-to-file ledger path)
                          (check-k-proof '((0 (.to (.forall v0 (.in v0 v3)) (.in (empty) v3))
                                              :th (th-forall-elim :inst ((v1 (empty))))))
                                         (read-ledger-from-file path :ledger (zf-ledger))))
                   t)
        (ignore-errors (delete-file path))))
    ledger))

(defun lax-schema-match (pat expr ledger &optional binds)
  "A deliberately BROKEN stand-in for MATCH-SCHEMA-ATOMS that never fails:
the first binding of a symbol wins and every later mismatch is ignored."
  (cond ((and (symbolp pat) (atomic-wff-symbol-p pat ledger))
         (if (lookup-binding pat binds) binds (cons (cons pat expr) binds)))
        ((and (consp pat) (predicate-schema-arity (car pat) ledger))
         (cond ((lookup-binding (car pat) binds) binds)
               ((distinct-variables-p (cdr pat) ledger)
                (cons (cons (car pat) (list :lambda (cdr pat) expr)) binds))
               (t binds)))
        ((and (consp pat) (consp expr))
         (lax-schema-match (cdr pat) (cdr expr) ledger (lax-schema-match (car pat) (car expr) ledger binds)))
        (t binds)))

(defun test-equality-checks-guard-matching (ledger)
  "Soundness of a citation must not depend on MATCH-SCHEMA-ATOMS being
right: with the matcher replaced by LAX-SCHEMA-MATCH, false citations are
still rejected by the explicit hypothesis/conclusion comparison plus
re-verification in TRY-DERIVED-ENTRY / TRY-DEDUCTION-ENTRY. (Removing
that comparison makes these citations succeed with the broken matcher.)"
  (let ((ledger (read-ledger-from-file (library-path "07-quantifier-schemas.ledger") :ledger ledger))
        (orig (symbol-function 'match-schema-atoms)))
    (unwind-protect
         (progn
           (setf (symbol-function 'match-schema-atoms) #'lax-schema-match)
           (expect "broken matcher: false 'forall v0 (v0 in v3) -> v1 in v2' still rejected"
                   (check-k-proof '((0 (.to (.forall v0 (.in v0 v3)) (.in v1 v2)) :th (th-forall-elim))) ledger)
                   nil)
           (expect "broken matcher: false 'v1 in v2 -> exists v0 (v0 in v3)' still rejected"
                   (check-k-proof '((0 (.to (.in v1 v2) (.exists v0 (.in v0 v3)))
                                       :th (th-exists-intro :inst ((p (v5) (.in v5 v3))))))
                                  ledger)
                   nil)
           (expect "broken matcher: false 'forall z not(z in y) -> y = y2' still rejected"
                   (check-k-proof '((0 (.to (.forall v3 (.neg (.in v3 v1))) (.eq v1 v2))
                                       :th-ded (th-exists1-unique)))
                                  ledger)
                   nil))
      (setf (symbol-function 'match-schema-atoms) orig))
    (expect "matcher restored: a genuine instance is accepted again"
            (check-k-proof '((0 (.to (.forall v0 (.in v0 v3)) (.in v1 v3)) :th (th-forall-elim))) ledger)
            t)
    ledger))

(defun run-predicate-schema-self-tests ()
  "Predicate schema symbols, :INST, vocabulary visibility, and
hilbert-library/07-quantifier-schemas.ledger."
  (let* ((ledger (connectives-ledger))
         (ledger (test-predicate-schema-declarations ledger)))
    (test-predicate-schema-soundness ledger))
  (test-quantifier-schema-library (zf-logic-ledger))
  (test-equality-checks-guard-matching (zf-logic-ledger))
  (format t "~%Predicate-schema self-tests complete.~%"))
