;;;; render.lisp -- formulas as text in textbook notation
;;;;
;;;;   (.to A B)            A → B          (.forall x A)   ∀x A
;;;;   (.neg A)             ¬A             (.exists x A)   ∃x A
;;;;   (.and A B)           A ∧ B          (.exists1 x A)  ∃!x A
;;;;   (.or A B)            A ∨ B          (.iota x A)     ιx A
;;;;   (.iff A B)           A ↔ B          (.eq s t)       s = t
;;;;   (.in s t)            s ∈ t          (empty)         ∅
;;;;   (.neg (.in s t))     s ∉ t          (.neg (.eq s t)) s ≠ t
;;;;   (+ s t) / (* s t)    s + t / s · t  (S t) / zero    S(t) / 0
;;;;   (f t1 .. tn)         f(t1, .., tn)  v0, v12         v₀, v₁₂
;;;;
;;;; Precedence: ¬ and the quantifiers bind tightest, then ∧, ∨, →, ↔
;;;; (→ associates to the right). A quantified formula is still put in
;;;; parentheses when it is an operand of a binary connective, so the
;;;; scope of ∀x is never left for the reader to guess.
;;;;
;;;; The renderer never fails: anything it does not recognise is printed
;;;; as an S-expression, so half-typed input in the editor still displays.

(in-package :ledger-kernel)

(defparameter *binary-connectives*
  ;; head  symbol  precedence  left-min  right-min   (higher binds tighter)
  '((.iff "↔" 1 2 2)
    (.to  "→" 2 3 2)
    (.or  "∨" 3 3 4)
    (.and "∧" 4 4 5)))

(defparameter *quantifiers*
  '((.forall . "∀") (.exists . "∃") (.exists1 . "∃!") (.iota . "ι")))

(defparameter *infix-terms* '((+ . "+") (* . "·")))

;;; --- Links -------------------------------------------------------------------
;;; When *RENDER-LINK* is a function (SYMBOL -> entry K or NIL), every
;;; rendered symbol or operator that has an entry introducing it is wrapped
;;; in invisible markers  ^A K ^B TEXT ^C  (control characters that never
;;; occur in a formula). RENDER-SEGMENTS turns such a string into a list of
;;; (TEXT . K-or-NIL) pieces for the browser to show as links. With
;;; *RENDER-LINK* NIL (the default) rendering is plain text.

(defvar *render-link* nil)

(defun link (sym text)
  (let ((k (and *render-link* sym (funcall *render-link* sym))))
    (if k
        (format nil "~C~D~C~A~C" (code-char 1) k (code-char 2) text (code-char 3))
        text)))

(defun render-segments (marked)
  "Split a string produced with *RENDER-LINK* into (TEXT . K-or-NIL) pieces."
  (let ((pieces nil) (i 0) (n (length marked)))
    (loop while (< i n)
          do (let ((start (position (code-char 1) marked :start i)))
               (when (null start)
                 (push (cons (subseq marked i) nil) pieces)
                 (return))
               (when (> start i) (push (cons (subseq marked i start) nil) pieces))
               (let* ((mid (position (code-char 2) marked :start start))
                      (end (position (code-char 3) marked :start mid)))
                 (push (cons (subseq marked (1+ mid) end)
                             (parse-integer marked :start (1+ start) :end mid))
                       pieces)
                 (setf i (1+ end)))))
    (nreverse pieces)))

(defun subscript-digits (string)
  (map 'string (lambda (c)
                 (if (digit-char-p c)
                     (char "₀₁₂₃₄₅₆₇₈₉" (digit-char-p c))
                     c))
       string))

(defun render-symbol (sym ledger)
  (if (pat-var-p sym)
      (symbol-name sym)
      (link sym (render-symbol-text sym ledger))))

(defun render-symbol-text (sym ledger)
  (let ((name (symbol-name sym)))
    (cond
      ((pat-var-p sym) name)
      ((and ledger (variable-p sym ledger))
       ;; v0 -> v₀
       (let ((pos (position-if #'digit-char-p name)))
         (if pos
             (concatenate 'string (string-downcase (subseq name 0 pos))
                          (subscript-digits (subseq name pos)))
             (string-downcase name))))
      ((eq sym 'ledger-kernel::zero) "0")
      ((eq sym 'ledger-kernel::s) "S")
      ((and ledger (or (atomic-wff-symbol-p sym ledger) (predicate-schema-arity sym ledger))) name)
      (t (string-downcase name)))))

(defun proper-list-p (x)
  (and (listp x) (handler-case (list-length x) (error () nil))))

(defun render-sexp (x)
  (let ((*package* (find-package :ledger-kernel))
        (*print-case* :downcase)
        (*print-pretty* nil))
    (prin1-to-string x)))

(defun render-at (f min-prec ledger)
  "Render F; parenthesise it if it binds more loosely than MIN-PREC."
  (multiple-value-bind (text prec) (render-1 f ledger)
    (if (< prec min-prec) (concatenate 'string "(" text ")") text)))

(defun render-1 (f ledger)
  "Returns (VALUES TEXT PRECEDENCE)."
  (cond
    ((symbolp f) (values (render-symbol f ledger) 10))
    ((not (proper-list-p f)) (values (render-sexp f) 10))
    ((null f) (values "()" 10))
    (t
     (let* ((head (car f)) (args (cdr f))
            (bin (assoc head *binary-connectives*))
            (quant (assoc head *quantifiers*))
            (infix (assoc head *infix-terms*)))
       (cond
         ((and bin (= (length args) 2))
          (destructuring-bind (op prec lmin rmin) (cdr bin)
            (values (concatenate 'string (render-at (first args) lmin ledger)
                                 " " (link head op) " "
                                 (render-at (second args) rmin ledger))
                    prec)))
         ((and (eq head '.neg) (= (length args) 1)
               (consp (first args)) (member (car (first args)) '(.in .eq))
               (= (length (first args)) 3))
          ;; ¬(s ∈ t) as s ∉ t, ¬(s = t) as s ≠ t
          (let ((inner (first args)))
            (values (concatenate 'string (render-term (second inner) ledger)
                                 " " (link (car inner) (if (eq (car inner) '.in) "∉" "≠")) " "
                                 (render-term (third inner) ledger))
                    6)))
         ((and (eq head '.neg) (= (length args) 1))
          (let ((arg (first args)))
            (values (concatenate 'string (link '.neg "¬")
                                 (if (and (consp arg) (assoc (car arg) *quantifiers*))
                                     (render-at arg 0 ledger)
                                     (render-at arg 5 ledger)))
                    5)))
         ((and quant (= (length args) 2) (symbolp (first args)))
          ;; ∀x A for a tight body (atom, ¬, another quantifier),
          ;; ∀x(A → B) otherwise
          (let* ((body-form (second args))
                 (tight (not (and (consp body-form) (assoc (car body-form) *binary-connectives*))))
                 (body (if tight
                           (render-at body-form 0 ledger)
                           (concatenate 'string "(" (render-at body-form 0 ledger) ")"))))
            (values (concatenate 'string (link head (cdr quant)) (render-symbol (first args) ledger)
                                 (if tight " " "") body)
                    ;; parenthesised as an operand of a binary connective
                    ;; (every connective asks for at least 2), bare at top level
                    1.5)))
         ((and (eq head '.eq) (= (length args) 2))
          (values (concatenate 'string (render-term (first args) ledger) " " (link '.eq "=") " "
                               (render-term (second args) ledger))
                  6))
         ((and (eq head '.in) (= (length args) 2))
          (values (concatenate 'string (render-term (first args) ledger) " " (link '.in "∈") " "
                               (render-term (second args) ledger))
                  6))
         ((and infix (= (length args) 2))
          ;; operands keep their own parentheses: (a + b) · c
          (values (concatenate 'string "(" (values (render-1 (first args) ledger))
                               " " (link head (cdr infix)) " "
                               (values (render-1 (second args) ledger)) ")")
                  10))
         ((and (eq head 'ledger-kernel::empty) (null args)) (values (link head "∅") 10))
         ((symbolp head)
          ;; predicate schema, predicate or function application
          (values (format nil "~A(~{~A~^, ~})" (render-symbol head ledger)
                          (mapcar (lambda (a) (render-term a ledger)) args))
                  10))
         (t (values (render-sexp f) 10)))))))

(defun render-term (term ledger)
  "A term in a position that needs no parentheses of its own (a side of
= or ∈, a function argument): s + t rather than (s + t)."
  (if (and (proper-list-p term) (= (length term) 3) (assoc (car term) *infix-terms*))
      (let ((text (render-1 term ledger)))
        (subseq text 1 (1- (length text))))
      (values (render-1 term ledger))))

(defun render-formula (formula &optional ledger)
  "FORMULA as a string in textbook notation (see the file header). Plain
text unless *RENDER-LINK* is bound (see above)."
  (handler-case (values (render-1 formula ledger))
    (error () (render-sexp formula))))

(defun render-formula-segments (formula ledger)
  "FORMULA as (TEXT . K-or-NIL) pieces, linking each symbol and operator
to the entry that introduced it (requires *RENDER-LINK*)."
  (render-segments (render-formula formula ledger)))
