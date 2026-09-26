;;;; judgement.lisp -- Section 5: JUDGEMENT?, the core recursive checker
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

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
