;;;; tests.lisp -- ledger-kernel/web/tests: the renderer and the JSON API
;;;; (no HTTP involved). Run with (asdf:test-system :ledger-kernel/web).

(in-package :ledger-kernel)

(defun test-web-render ()
  (let ((l (world-ledger (find-world "zf"))))
    (flet ((r (f) (render-formula f l)))
      (expect "render: not-in and nested quantifiers"
              (string= (r '(.exists v1 (.forall v2 (.neg (.in v2 v1))))) "∃v₁ ∀v₂ v₂ ∉ v₁") t)
      (expect "render: a quantifier as an operand of → is parenthesised"
              (string= (r '(.to (.forall v2 (.neg (.in v2 v1))) (.eq v1 v3))) "(∀v₂ v₂ ∉ v₁) → v₁ = v₃") t)
      (expect "render: → is right-associative, and ∧ binds tighter than ↔"
              (string= (r '(.iff (.and a b) (.to a (.to b c)))) "A ∧ B ↔ A → B → C") t)
      (expect "render: a left-nested → keeps its parentheses"
              (string= (r '(.to (.to a b) c)) "(A → B) → C") t)
      (expect "render: ∅, ≠, predicate schemas, ∃!"
              (string= (r '(.exists1 v0 (.and (p v0) (.neg (.eq v0 (empty)))))) "∃!v₀(P(v₀) ∧ v₀ ≠ ∅)") t)
      (expect "render: arithmetic terms keep only the parentheses they need"
              (string= (r '(.eq (* (+ v0 v1) (s zero)) (s (+ v0 zero)))) "(v₀ + v₁) · S(0) = S(v₀ + 0)") t)
      (expect "render: substitution in schemas as A[t/x]"
              (string= (r '(.to (.forall ?x ?a) (@subst ?x ?t ?a))) "(∀?X ?A) → ?A[?T/?X]") t)
      (expect "render: malformed input falls back to the S-expression"
              (stringp (r '(.to a))) t))))

(defun test-web-api ()
  (let* ((entries (api-entries "zf"))
         (e (find "th-zf-empty-exists" entries :key (lambda (h) (gethash "name" h)) :test #'string=))
         (detail (api-entry "zf" (gethash "k" e)))
         (proof (gethash "proof" detail)))
    (expect "api-entries lists every entry of the world"
            (= (length entries) (ledger-count (world-ledger (find-world "zf")))) t)
    (expect "api-entry: th-zf-empty-exists has its 9-line proof" (= (length proof) 9) t)
    (expect "api-entry: line 2 is MP citing lines 1 and 0"
            (equalp (gethash "refs" (aref proof 2)) #("1" "0")) t)
    (expect "api-entry: an axiom citation links to the axiom's entry"
            (string= (gethash "kind" (gethash "cite" (aref proof 0))) "axiom") t))
  (let ((ok (api-check "zf" "((0 (.in v0 v1) :hyp nil)
                              (1 (.to (.in v0 v1) (.or (.in v0 v1) (.in v0 v2))) :th (th-or-intro-l))
                              (2 (.or (.in v0 v1) (.in v0 v2)) :ir (mp 1 0)))"))
        (bad (api-check "zf" "((0 (.in v0 v1) :hyp nil)
                               (1 (.to (.in v0 v1) (.in v0 v1)) :th (th-identity))
                               (2 (.in v0 v2) :ir (mp 1 0)))"))
        (evil (api-check "zf" "((0 #.(error \"boom\") :hyp nil))"))
        (junk (api-check "zf" "((0 (.in v0 v1)))")))
    (expect "api-check: a correct proof is accepted" (eq (gethash "ok" ok) 'yason:true) t)
    (expect "api-check: a wrong proof is rejected at line 2"
            (and (eq (gethash "ok" bad) 'yason:false) (equal (gethash "failedAt" bad) "2")) t)
    (expect "api-check: per-line status accepted / accepted / rejected"
            (equalp (map 'vector (lambda (l) (gethash "status" l)) (gethash "lines" bad))
                    #("accepted" "accepted" "rejected"))
            t)
    (expect "api-check: #. is never evaluated"
            (and (eq (gethash "ok" evil) 'yason:false) (search "READ-EVAL" (gethash "error" evil))) t)
    (expect "api-check: a malformed line is reported, not checked"
            (and (eq (gethash "ok" junk) 'yason:false) (search "Line 1" (gethash "error" junk))) t)))

(defun test-web-links ()
  (let* ((w (find-world "zf"))
         (e (find "th-zf-not-in-empty" (api-entries "zf") :key (lambda (h) (gethash "name" h)) :test #'string=))
         (detail (api-entry "zf" (gethash "k" e)))
         (segments (gethash "segments" (gethash "conclusion" detail)))
         (linked (remove-if-not (lambda (s) (gethash "k" s)) (coerce segments 'list))))
    (flet ((target (text) (let ((s (find text linked :key (lambda (s) (gethash "t" s)) :test #'string=)))
                            (and s (find-entry-by-k w (gethash "k" s))))))
      (expect "links: the plain text is unchanged by linking"
              (string= (gethash "text" (gethash "conclusion" detail)) "v₀ ∉ ∅") t)
      (expect "links: the segments spell out the same text"
              (string= (apply #'concatenate 'string (map 'list (lambda (s) (gethash "t" s)) segments))
                       "v₀ ∉ ∅")
              t)
      (expect "links: v₀ goes to the variable's declaration"
              (eq (entry-kind (target "v₀")) 'variable-symbol) t)
      (expect "links: ∉ goes to the formation rule of ∈"
              (eq (entry-kind (target "∉")) 'wff?) t)
      (expect "links: ∅ goes to its defining axiom EMPTY-DEF"
              (string= (symbol-name (car (entry-payload (target "∅")))) "EMPTY-DEF") t))
    (let* ((r (api-check "zf" "((0 (.forall v0 (.to (p v0) (q v0))) :hyp nil)
                                 (1 (.to (.exists v0 (p v0)) (.exists v0 (q v0))) :th-ded (th-exists-mono-s1 0)))"))
           (line (aref (gethash "lines" r) 1)))
      (expect "links: api-check reports what each line cites"
              (let* ((cite (gethash "cite" line))
                     (cited (and cite (find-entry-by-k (find-world "zf") (gethash "k" cite)))))
                (and cited (string= (symbol-name (car (entry-payload cited))) "TH-EXISTS-MONO-S1")))
              t)
      (expect "links: api-check formulas carry segments"
              (plusp (length (gethash "segments" (gethash "formula" line)))) t))
    (expect "links: entry summaries stay plain text (no markers)"
            (notany (lambda (h) (find (code-char 1) (gethash "text" h))) (api-entries "zf")) t)))

(defun test-web-deps ()
  (let ((w (find-world "zf")))
    (labels ((k-of (name)
               (gethash "k" (find name (api-entries "zf") :key (lambda (h) (gethash "name" h)) :test #'string=)))
             (names (refs) (map 'list (lambda (r) (gethash "name" r)) refs))
             (found (name) (gethash "foundations" (api-entry "zf" (k-of name)))))
      (let ((exists (found "th-zf-empty-exists"))
            (unique (found "th-zf-empty-unique"))
            (not-in (found "th-zf-not-in-empty")))
        (expect "deps: the empty set's existence rests on Separation, not Extensionality"
                (let ((a (names (gethash "axioms" exists))))
                  (and (member "zf-separation" a :test #'string=)
                       (not (member "zf-extensionality" a :test #'string=))))
                t)
        (expect "deps: its uniqueness rests on Extensionality, not Separation"
                (let ((a (names (gethash "axioms" unique))))
                  (and (member "zf-extensionality" a :test #'string=)
                       (not (member "zf-separation" a :test #'string=))))
                t)
        (expect "deps: not(x in (empty)) rests on the definition EMPTY-DEF ..."
                (and (member "empty-def" (names (gethash "definitions" not-in)) :test #'string=) t) t)
        (expect "... and, through it, on both Separation and Extensionality"
                (let ((a (names (gethash "axioms" not-in))))
                  (and (member "zf-separation" a :test #'string=)
                       (member "zf-extensionality" a :test #'string=) t))
                t)
        (expect "deps: MP is among the inference rules used"
                (and (member "mp" (names (gethash "rules" exists)) :test #'string=) t) t)
        (expect "deps: a TH-DED step on the way is reported"
                (eq (gethash "deductionMeta" exists) 'yason:true) t))
      (let ((used (names (gethash "usedBy" (api-entry "zf" (k-of "th-and-elim-r"))))))
        (expect "deps: th-and-elim-r is used by th-zf-empty-exists (through its step -s1)"
                (and (member "th-zf-empty-exists" used :test #'string=) t) t)
        (expect "deps: ... and the auxiliary step itself is not listed"
                (member "th-zf-empty-exists-s1" used :test #'string=) nil))
      (expect "deps: Separation is used, directly or not, by the empty-set theorems"
              (>= (gethash "dependents" (api-entry "zf" (k-of "zf-separation"))) 2) t)
      (expect "deps: axioms such as II.1 are not hidden as auxiliary entries"
              (eq (gethash "aux" (find "ii.1" (api-entries "zf") :key (lambda (h) (gethash "name" h)) :test #'string=))
                  'yason:false)
              t)
      (expect "deps: every citation in every stored proof resolves to an entry"
              (let ((d (world-deps w)))
                (every (lambda (e)
                         ;; (a definition's axiom also counts its existence and
                         ;; uniqueness theorems; only stored proofs are compared)
                         (or (null (entry-proof e))
                          (= (length (gethash (entry-k e) (deps-cites d)))
                            (length (remove-duplicates
                                     (loop for (nil nil role by) in (entry-proof e)
                                           unless (eq role :hyp) collect (car by)))))))
                       (world-entries w)))
              t))))

(defun run-web-self-tests ()
  (let ((*expect-results* (cons 0 0)))
    (unless *worlds* (load-worlds))
    (test-web-render)
    (test-web-api)
    (test-web-links)
    (test-web-deps)
    (destructuring-bind (passed . failed) *expect-results*
      (format t "~%~D/~D web self-tests passed.~%" passed (+ passed failed))
      (zerop failed))))
