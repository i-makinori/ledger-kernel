;;;; meta.lisp -- Section 4: meta predicates and constructors
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

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

(defun meta-predicates-table ()
  "The dispatch table CHECK-CONDITION/META-PREDICATE-P look up @-tagged
side conditions in."
  (list (cons '@not-free-in? #'meta-not-free-in?)
        (cons '@not-free-in-dependencies? #'meta-not-free-in-dependencies?)
        (cons '@subst-ok? #'meta-subst-ok?)
        (cons '@substitutes? #'meta-substitutes?)))

(defun meta-constructors-table ()
  "As META-PREDICATES-TABLE, but for meta-constructors (META-CONSTRUCTOR-P,
used by MATCH-TEMPLATE)."
  (list (cons '@subst (lambda (var term wff) (substitute-wff var term wff)))))
