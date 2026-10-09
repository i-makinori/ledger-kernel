;;;; judgement.lisp -- JUDGEMENT?, the core recursive checker

(in-package :ledger-kernel)

;;; (judgement? kind expr ledger) is T iff some entry of KIND in LEDGER
;;; matches EXPR under bindings satisfying that entry's side conditions,
;;; or (for WFF?/VAR?/TERM?) EXPR is justified by a declaration. This one
;;; function covers wff?, var?, term? and any other judgement kind.

(defun judgement-bind (kind args binds ledger &optional (seen nil) (open-hyps nil))
  "Prove (KIND . ARGS): first from declarations, else by the first KIND
entry whose FORM matches and whose side conditions hold, extending BINDS.
Returns (values new-binds ok-p).

SEEN is the cycle guard: the (KIND . ARGS) goals already in progress up
the call chain; a repeat fails. It is keyed on the concrete goal, not on
the rule, because one formation rule (e.g. WFF_TO?) is legitimately reused
at every nesting depth for different subgoals. OPEN-HYPS (Gamma) is passed
through unchanged to CHECK-CONDITIONS."
  (when (declared-symbol-judgement-p kind args ledger seen open-hyps)
    (return-from judgement-bind (values binds t)))
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
  "Match (KIND . ARGS) against ENTRY's FORM and check its side conditions.
Returns (values new-binds ok-p)."
  (destructuring-bind (name conditions form) (entry-payload entry)
    (declare (ignore name))
    ;; No SEED-FRESH: a formation rule's binder is the whole expression
    ;; being judged, so TAKE-FRESH's fallback (scan that expression)
    ;; already avoids everything in play.
    (let ((b0 (match-template form (cons kind args) binds)))
      (if (match-fail-p b0)
          (values binds nil)
          (check-conditions conditions b0 ledger seen open-hyps)))))

(defun %judgement? (kind expr ledger &optional (seen nil) (open-hyps nil))
  "T iff kernel-form EXPR holds as a KIND judgement in LEDGER. SEEN and
OPEN-HYPS are as in JUDGEMENT-BIND; top-level callers omit them."
  (nth-value 1 (judgement-bind kind (list expr) nil ledger seen open-hyps)))

(defun judgement? (kind expr ledger &optional (seen nil) (open-hyps nil))
  "As %JUDGEMENT?, for EXPR as written (bound variables by name; a raw
(:BV n) is refused, see CONTAINS-RAW-INDEX-P)."
  (and (not (contains-raw-index-p expr))
       (%judgement? kind (named->db expr ledger) ledger seen open-hyps)))

;;; Declared symbols are base cases read off Sigma, not formation rules:
;;; a generic rule such as (wff? ?A) would match any expression, including
;;; undeclared symbols.

(defun declared-symbol-judgement-p (kind args ledger seen open-hyps)
  "T when (KIND . ARGS) holds because of a declaration: a declared atomic
wff symbol is a wff, a declared variable is a var and a term, and a
declared predicate schema applied to the right number of terms is a wff."
  (and (= (length args) 1)
       (let ((x (car args)))
         (if (symbolp x)
             (case kind
               (wff? (atomic-wff-symbol-p x ledger))
               ((var? term?) (variable-p x ledger)))
             (and (eq kind 'wff?)
                  (predicate-schema-application-wff-p x ledger seen open-hyps))))))

(defun predicate-schema-application-wff-p (expr ledger seen open-hyps)
  "EXPR is (P t1 ... tn) with P a declared predicate schema of arity n and
every ti a term."
  (and (consp expr)
       (let ((arity (predicate-schema-arity (car expr) ledger)))
         (and arity
              (listp (cdr expr))
              (= (length (cdr expr)) arity)
              (every (lambda (arg) (%judgement? 'term? arg ledger seen open-hyps)) (cdr expr))))))
