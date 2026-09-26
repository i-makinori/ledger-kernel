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

(defun run-web-self-tests ()
  (let ((*expect-results* (cons 0 0)))
    (unless *worlds* (load-worlds))
    (test-web-render)
    (test-web-api)
    (destructuring-bind (passed . failed) *expect-results*
      (format t "~%~D/~D web self-tests passed.~%" passed (+ passed failed))
      (zerop failed))))
