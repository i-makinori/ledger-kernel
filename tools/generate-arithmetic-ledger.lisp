;;;; generate-arithmetic-ledger.lisp
;;;;
;;;; Writes hilbert-library/08-arithmetic.ledger: the commutative-semiring
;;;; laws of + and * in Peano arithmetic, each proved by induction from
;;;; P1-P10. Proofs are assembled by the small builder below and every
;;;; theorem is admitted through CHECK-AND-EXTEND as it is built, so this
;;;; script is a convenience, not part of the trusted base: loading the
;;;; generated file re-verifies everything.
;;;;
;;;; Usage, from the repository root:
;;;;   sbcl --non-interactive --load tools/generate-arithmetic-ledger.lisp
;;;;
;;;; Conventions of the generated library
;;;; - General laws are stated CLOSED, over the bound-only variables
;;;;   x1 x2 x3 (declared at the top of the file and never used free), e.g.
;;;;     th-add-comm : (.forall x1 (.forall x2 (.eq (+ x1 x2) (+ x2 x1))))
;;;;   A proof uses one by citing it and eliminating the quantifiers with
;;;;   III.1 at the terms it needs. Since the terms never contain x1-x3,
;;;;   the substitution can never capture a variable.
;;;; - Working proofs use the free variables v0-v5. For each law NAME the
;;;;   file also holds its induction pieces NAME-base, NAME-step (a TH-DED
;;;;   entry: phi(v) -> phi(S v)) and NAME-ind (forall v phi).

(require :asdf)
(asdf:load-asd (merge-pathnames "ledger-kernel.asd"))
(asdf:load-system :ledger-kernel)
(in-package :ledger-kernel)

(defun library-file (name)
  (asdf:system-relative-pathname :ledger-kernel (concatenate 'string "hilbert-library/" name)))

(defparameter *base-systems*
  '("00-classical-fol-equality.system" "00-connectives.system"
    "00-peano-arithmetic.system" "00-peano-order.system"))
(defparameter *base-modules*
  '("01-propositional-core.ledger" "02-predicate-core.ledger"
    "03-equality-core.ledger" "04-peano-arithmetic.ledger"
    "05-classical-logic.ledger" "06-connectives.ledger"))

(defun peano-base-ledger ()
  (let ((l nil))
    (dolist (f *base-systems*)
      (setf l (bootstrap-kernel-from-spec-file (library-file f) :ledger l)))
    (dolist (f *base-modules* l)
      (setf l (read-ledger-from-file (library-file f) :ledger l)))))

;;; --- builder state ------------------------------------------------------

(defvar *L* nil "The ledger being grown.")
(defvar *commands* nil "Commands emitted so far, newest first.")
(defvar *closed* (make-hash-table) "Closed law name -> its formula.")

(defvar *lines*)
(defvar *count*)
(defvar *formulas*)

(defmacro with-proof (&body body)
  "Run BODY with a fresh proof under construction; return the raw proof."
  `(let ((*lines* nil) (*count* 0) (*formulas* (make-hash-table)))
     ,@body
     (reverse *lines*)))

(defun line (formula role by)
  (let ((n *count*))
    (incf *count*)
    (push (list n formula role by) *lines*)
    (setf (gethash n *formulas*) formula)
    n))

(defun fm (n) (or (gethash n *formulas*) (error "no line ~S" n)))

(defun admit-th (name proof)
  (setf *L* (check-and-extend *L* 'th name proof (make-log-config :errors t)))
  (push (list :th name proof) *commands*)
  name)

(defun admit-ded (name hyp proof)
  (setf *L* (check-and-extend-by-deduction-direct *L* name hyp proof (make-log-config :errors t)))
  (push (list :th-ded name hyp proof) *commands*)
  name)

(defun declare-var (v)
  (setf *L* (declare-variable-symbol *L* v))
  (push (list :declare-variable-symbol v) *commands*))

;;; --- proof steps ----------------------------------------------------------

(defun hyp (f) (line f :hyp nil))
(defun ax (f name &rest extra) (line f :axiom (cons name extra)))
(defun cite (name f &rest lines) (line f :th (cons name lines)))

(defun mp (imp ant)
  (let ((f (fm imp)))
    (unless (and (eq (car f) '.to) (equal (second f) (fm ant)))
      (error "MP mismatch: ~S / ~S" f (fm ant)))
    (line (third f) :ir (list 'mp imp ant))))

(defun gen (n v) (line `(.forall ,v ,(fm n)) :ir (list 'gen n v)))

(defun forall-elim (n term)
  "From line N, (.forall x A), derive A[term/x] by III.1."
  (destructuring-bind (q x a) (fm n)
    (assert (eq q '.forall))
    (mp (ax `(.to (.forall ,x ,a) ,(substitute-named x term a)) 'iii.1 term) n)))

(defun use (name &rest terms)
  "Cite closed law NAME and instantiate its leading quantifiers with TERMS."
  (let ((n (cite name (or (gethash name *closed*) (error "unknown law ~S" name)))))
    (dolist (tm terms n) (setf n (forall-elim n tm)))))

;;; equality
(defun lhs (n) (second (fm n)))
(defun rhs (n) (third (fm n)))
(defun refl (tm) (ax `(.eq ,tm ,tm) 'iv.1))
(defun sym (n) (mp (ax `(.to (.eq ,(lhs n) ,(rhs n)) (.eq ,(rhs n) ,(lhs n))) 'iv.3) n))
(defun trans (i j)
  (unless (equal (rhs i) (lhs j)) (error "TRANS mismatch: ~S / ~S" (fm i) (fm j)))
  (mp (mp (ax `(.to (.eq ,(lhs i) ,(rhs i)) (.to (.eq ,(lhs j) ,(rhs j)) (.eq ,(lhs i) ,(rhs j))))
              'iv.4)
          i)
      j))
(defun chain (&rest ns) (reduce #'trans ns))
(defun cong-s (n) (mp (ax `(.to ,(fm n) (.eq (s ,(lhs n)) (s ,(rhs n)))) 'p8) n))
(defun cong2 (op axiom i j)
  (mp (mp (ax `(.to ,(fm i) (.to ,(fm j) (.eq (,op ,(lhs i) ,(lhs j)) (,op ,(rhs i) ,(rhs j))))) axiom)
          i)
      j))
(defun cong+ (i j) (cong2 '+ 'p9 i j))
(defun cong* (i j) (cong2 '* 'p10 i j))
(defun rw+l (n tm) "From a=b get a+tm = b+tm." (cong+ n (refl tm)))
(defun rw+r (tm n) "From a=b get tm+a = tm+b." (cong+ (refl tm) n))
(defun rw*l (n tm) (cong* n (refl tm)))
(defun rw*r (tm n) (cong* (refl tm) n))

;;; Peano axiom instances
(defun p4 (x) (ax `(.eq (+ ,x zero) ,x) 'p4))
(defun p5 (x y) (ax `(.eq (+ ,x (s ,y)) (s (+ ,x ,y))) 'p5))
(defun p6 (x) (ax `(.eq (* ,x zero) zero) 'p6))
(defun p7 (x y) (ax `(.eq (* ,x (s ,y)) (+ (* ,x ,y) ,x)) 'p7))

;;; --- laws -------------------------------------------------------------------

(defparameter *bound-vars* '(x1 x2 x3))

(defun close-law (name open-proof-fn vars &optional (bound *bound-vars*))
  "Admit NAME: the universal closure over *BOUND-VARS* of the formula that
OPEN-PROOF-FN proves (in the working VARS). Each working variable a_i is
generalized, instantiated to x_i by III.1 and generalized again."
  (let ((proof
          (with-proof
            (let ((n (funcall open-proof-fn)))
              (loop for a in (reverse vars)
                    for x in (reverse (subseq bound 0 (length vars)))
                    do (setf n (gen (forall-elim (gen n a) x) x)))))))
    (admit-th name proof)
    (setf (gethash name *closed*) (proof-conclusion proof))
    name))

(defun induction-law (name var phi vars base step)
  "Prove PHI by induction on VAR and admit the closed law NAME.
BASE is a function building a proof of PHI[0/VAR]; it may return
(:ded HYP) to have the proof admitted by the Deduction Theorem instead.
STEP receives the line of the hypothesis PHI and builds PHI[S VAR/VAR]."
  (let* ((phi0 (substitute-named var 'zero phi))
         (phis (substitute-named var `(s ,var) phi))
         (base-name (intern (format nil "~A-BASE" name)))
         (step-name (intern (format nil "~A-STEP" name)))
         (ind-name (intern (format nil "~A-IND" name))))
    (let (ded-hyp)
      (let ((proof (with-proof (let ((r (funcall base)))
                                 (when (and (consp r) (eq (car r) :ded)) (setf ded-hyp (second r)))))))
        (if ded-hyp
            (admit-ded base-name ded-hyp proof)
            (admit-th base-name proof))))
    (admit-ded step-name phi (with-proof (funcall step (hyp phi))))
    (admit-th ind-name
              (with-proof
                (let* ((st (cite step-name `(.to ,phi ,phis)))
                       (g (gen st var))
                       (p3 (ax `(.to ,phi0 (.to ,(fm g) (.forall ,var ,phi))) 'p3 var phi))
                       (b (cite base-name phi0)))
                  (mp (mp p3 b) g))))
    (close-law name (lambda () (forall-elim (cite ind-name `(.forall ,var ,phi)) var)) vars)))

(defmacro with-vars ((&rest names) &body body)
  "Bind NAMES to the working variables v0, v1, ... in order."
  `(let ,(loop for n in names for i from 0 collect `(,n ',(intern (format nil "V~D" i))))
     ,@body))

(defun build-arithmetic ()
  (dolist (v *bound-vars*) (declare-var v))
  (with-vars (a b c)
    ;; 0 + a = a  (restating 04's th-zero-plus-identity in closed form)
    (close-law 'th-add-zero-l
               (lambda () (forall-elim (cite 'th-zero-plus-identity '(.forall v0 (.eq (+ zero v0) v0))) a))
               (list a))

    ;; S a + b = S (a + b)
    (induction-law 'th-add-succ-l b `(.eq (+ (s ,a) ,b) (s (+ ,a ,b))) (list a b)
      (lambda ()
        (trans (p4 `(s ,a)) (sym (cong-s (p4 a)))))
      (lambda (h)
        (chain (p5 `(s ,a) b) (cong-s h) (sym (cong-s (p5 a b))))))

    ;; a + b = b + a
    (induction-law 'th-add-comm b `(.eq (+ ,a ,b) (+ ,b ,a)) (list a b)
      (lambda () (trans (p4 a) (sym (use 'th-add-zero-l a))))
      (lambda (h) (chain (p5 a b) (cong-s h) (sym (use 'th-add-succ-l b a)))))

    ;; (a + b) + c = a + (b + c)
    (induction-law 'th-add-assoc c `(.eq (+ (+ ,a ,b) ,c) (+ ,a (+ ,b ,c))) (list a b c)
      (lambda () (trans (p4 `(+ ,a ,b)) (sym (rw+r a (p4 b)))))
      (lambda (h)
        (chain (p5 `(+ ,a ,b) c) (cong-s h)
               (sym (trans (rw+r a (p5 b c)) (p5 a `(+ ,b ,c)))))))

    ;; a + c = b + c -> a = b
    (let ((h-of (lambda (z) `(.to (.eq (+ ,a ,z) (+ ,b ,z)) (.eq ,a ,b)))))
      (induction-law 'th-add-cancel-r c (funcall h-of c) (list a b c)
        (lambda ()
          (let ((e (hyp `(.eq (+ ,a zero) (+ ,b zero)))))
            (chain (sym (p4 a)) e (p4 b))
            (list :ded (fm e))))
        (lambda (h)
          ;; inner: with h open, discharge a + Sc = b + Sc
          (let* ((inner-name 'th-add-cancel-r-step-inner)
                 (e-f `(.eq (+ ,a (s ,c)) (+ ,b (s ,c)))))
            (admit-ded inner-name e-f
                       (with-proof
                         (let* ((h1 (hyp (funcall h-of c)))
                                (e (hyp e-f))
                                (ss (chain (sym (p5 a c)) e (p5 b c)))
                                (p2 (ax `(.to ,(fm ss) (.eq (+ ,a ,c) (+ ,b ,c))) 'p2)))
                           (mp h1 (mp p2 ss)))))
            (cite inner-name `(.to ,e-f (.eq ,a ,b)) h)))))

    ;; 0 * a = 0
    (induction-law 'th-mul-zero-l a `(.eq (* zero ,a) zero) (list a)
      (lambda () (p6 'zero))
      (lambda (h) (chain (p7 'zero a) (p4 `(* zero ,a)) h)))

    ;; S a * b = a * b + b
    (induction-law 'th-mul-succ-l b `(.eq (* (s ,a) ,b) (+ (* ,a ,b) ,b)) (list a b)
      (lambda ()
        (trans (p6 `(s ,a)) (sym (trans (p4 `(* ,a zero)) (p6 a)))))
      (lambda (h)
        (let* ((ab `(* ,a ,b))
               ;; (ab + b) + a = (ab + a) + b
               (swap (chain (use 'th-add-assoc ab b a)
                            (rw+r ab (use 'th-add-comm b a))
                            (sym (use 'th-add-assoc ab a b)))))
          (chain (p7 `(s ,a) b)
                 (rw+l h `(s ,a))
                 (p5 `(+ ,ab ,b) a)
                 (cong-s swap)
                 (sym (p5 `(+ ,ab ,a) b))
                 (sym (rw+l (p7 a b) `(s ,b)))))))

    ;; a * b = b * a
    (induction-law 'th-mul-comm b `(.eq (* ,a ,b) (* ,b ,a)) (list a b)
      (lambda () (trans (p6 a) (sym (use 'th-mul-zero-l a))))
      (lambda (h) (chain (p7 a b) (rw+l h a) (sym (use 'th-mul-succ-l b a)))))

    ;; a * (b + c) = a * b + a * c
    (induction-law 'th-mul-distrib-l c `(.eq (* ,a (+ ,b ,c)) (+ (* ,a ,b) (* ,a ,c))) (list a b c)
      (lambda ()
        (trans (rw*r a (p4 b))
               (sym (trans (rw+r `(* ,a ,b) (p6 a)) (p4 `(* ,a ,b))))))
      (lambda (h)
        (chain (rw*r a (p5 b c))
               (p7 a `(+ ,b ,c))
               (rw+l h a)
               (use 'th-add-assoc `(* ,a ,b) `(* ,a ,c) a)
               (sym (rw+r `(* ,a ,b) (p7 a c))))))

    ;; (a * b) * c = a * (b * c)
    (induction-law 'th-mul-assoc c `(.eq (* (* ,a ,b) ,c) (* ,a (* ,b ,c))) (list a b c)
      (lambda ()
        (trans (p6 `(* ,a ,b)) (sym (trans (rw*r a (p6 b)) (p6 a)))))
      (lambda (h)
        (chain (p7 `(* ,a ,b) c)
               (rw+l h `(* ,a ,b))
               (sym (trans (rw*r a (p7 b c))
                           (use 'th-mul-distrib-l a `(* ,b ,c) b))))))

    ;; (a + b) * c = a * c + b * c
    (close-law 'th-mul-distrib-r
               (lambda ()
                 (chain (use 'th-mul-comm `(+ ,a ,b) c)
                        (use 'th-mul-distrib-l c a b)
                        (cong+ (use 'th-mul-comm c a) (use 'th-mul-comm c b))))
               (list a b c))

    ;; a + S 0 = S a,  a * S 0 = a
    (close-law 'th-add-one (lambda () (trans (p5 a 'zero) (cong-s (p4 a)))) (list a))
    (close-law 'th-mul-one
               (lambda () (chain (p7 a 'zero) (rw+l (p6 a) a) (use 'th-add-zero-l a)))
               (list a))

    ;; c + a = c + b -> a = b
    (close-law 'th-add-cancel-l
               (lambda ()
                 (let ((dname 'th-add-cancel-l-s1)
                       (e-f `(.eq (+ ,c ,a) (+ ,c ,b))))
                   (admit-ded dname e-f
                              (with-proof
                                (let* ((e (hyp e-f))
                                       (s (chain (use 'th-add-comm a c) e (use 'th-add-comm c b)))
                                       (cancel (use 'th-add-cancel-r a b c)))
                                  (mp cancel s))))
                   (cite dname `(.to ,e-f (.eq ,a ,b)))))
               (list a b c))))

(defparameter *header-08* ";;; 08-arithmetic.ledger -- generated by tools/generate-arithmetic-ledger.lisp
;;;
;;; The commutative-semiring laws of + and * in Peano arithmetic, proved by
;;; induction from P1-P10. Load after 00-peano-arithmetic.system and the
;;; 01-06 modules. General laws are closed over the bound-only variables
;;; x1 x2 x3; cite one and instantiate it with III.1:
;;;
;;;   th-add-zero-l     0 + x = x
;;;   th-add-succ-l     S x + y = S (x + y)
;;;   th-add-comm       x + y = y + x
;;;   th-add-assoc      (x + y) + z = x + (y + z)
;;;   th-add-cancel-r   x + z = y + z -> x = y
;;;   th-add-cancel-l   z + x = z + y -> x = y
;;;   th-add-one        x + S 0 = S x
;;;   th-mul-zero-l     0 * x = 0
;;;   th-mul-succ-l     S x * y = x * y + y
;;;   th-mul-comm       x * y = y * x
;;;   th-mul-distrib-l  x * (y + z) = x * y + x * z
;;;   th-mul-distrib-r  (x + y) * z = x * z + y * z
;;;   th-mul-assoc      (x * y) * z = x * (y * z)
;;;   th-mul-one        x * S 0 = x

")

;;; --- order (09) --------------------------------------------------------------

(defun schema (name alist)
  "The statement of propositional lemma NAME with atoms replaced per ALIST."
  (sublis alist (ecase name
                  (th-or-intro-l '(.to a (.or a b)))
                  (th-or-intro-r '(.to b (.or a b)))
                  (th-or-elim '(.to (.to a c) (.to (.to b c) (.to (.or a b) c))))
                  (th-ex-falso '(.to (.neg a) (.to a b)))
                  (th-raa '(.to (.to a b) (.to (.to a (.neg b)) (.neg a))))
                  (th-and-intro '(.to a (.to b (.and a b))))
                  (th-and-elim-l '(.to (.and a b) a))
                  (th-and-elim-r '(.to (.and a b) b)))))

(defun and-intro (i j)
  (mp (mp (prop 'th-and-intro `((a . ,(fm i)) (b . ,(fm j)))) i) j))
(defun and-l (n) (mp (prop 'th-and-elim-l `((a . ,(second (fm n))) (b . ,(third (fm n))))) n))
(defun and-r (n) (mp (prop 'th-and-elim-r `((a . ,(second (fm n))) (b . ,(third (fm n))))) n))
(defun ex-falso (n-neg n-pos goal)
  "From (.neg X) and X derive GOAL."
  (mp (mp (prop 'th-ex-falso `((a . ,(fm n-pos)) (b . ,goal))) n-neg) n-pos))

(defun prop (name alist &rest lines) (apply #'cite name (schema name alist) lines))

(defun or-intro-l (n other) (mp (prop 'th-or-intro-l `((a . ,(fm n)) (b . ,other))) n))
(defun or-intro-r (other n) (mp (prop 'th-or-intro-r `((a . ,other) (b . ,(fm n)))) n))
(defun or-elim (n-ac n-bc n-or)
  "From A -> C, B -> C and A v B, derive C."
  (destructuring-bind (op fa fb) (fm n-or)
    (assert (eq op '.or))
    (let ((fc (third (fm n-ac))))
      (mp (mp (mp (prop 'th-or-elim `((a . ,fa) (b . ,fb) (c . ,fc))) n-ac) n-bc) n-or))))

(defun exists-intro (n x body tm)
  "From line N, BODY[TM/X], derive (.exists X BODY) by III.3."
  (mp (ax `(.to ,(fm n) (.exists ,x ,body)) 'iii.3 x body tm) n))

(defun exists-elim (n-ex n-imp w)
  "From (.exists x A) and A[W/x] -> C, derive C (W must be fresh)."
  (line (third (fm n-imp)) :ir (list 'exists-elim n-ex n-imp w)))

(defparameter *le-var* 'x4 "The bound variable of every unfolded s <= t.")

(defun le-unfold (n)
  (destructuring-bind (op s tt) (fm n)
    (assert (eq op '.le))
    (mp (ax `(.to (.le ,s ,tt) (.exists ,*le-var* (.eq (+ ,s ,*le-var*) ,tt))) 'le-unfold) n)))

(defun le-intro (n)
  "From line N, s + d = t, derive s <= t."
  (destructuring-bind (op (plus s d) tt) (fm n)
    (assert (and (eq op '.eq) (eq plus '+)))
    (let* ((body `(.eq (+ ,s ,*le-var*) ,tt))
           (ex (exists-intro n *le-var* body d)))
      (mp (ax `(.to ,(fm ex) (.le ,s ,tt)) 'le-fold) ex))))

(defun ded (name opens dis fn)
  "Admit NAME by the Deduction Theorem: hypotheses OPENS stay open, DIS is
discharged. FN gets the hypothesis lines (OPENS..., DIS) and builds the
rest. Returns the discharged statement (.to DIS C)."
  (let ((proof (with-proof (apply fn (append (mapcar #'hyp opens) (list (hyp dis)))))))
    (admit-ded name dis proof)
    `(.to ,dis ,(proof-conclusion proof))))

(defun build-order ()
  (declare-var *le-var*)
  (with-vars (a b c d e)
    ;; a <= a,  0 <= a,  a <= S a,  a <= a + b
    (close-law 'th-le-refl (lambda () (le-intro (p4 a))) (list a))
    (close-law 'th-le-zero-l (lambda () (le-intro (use 'th-add-zero-l a))) (list a))
    (close-law 'th-le-succ (lambda () (le-intro (use 'th-add-one a))) (list a))
    (close-law 'th-le-add (lambda () (le-intro (refl `(+ ,a ,b)))) (list a b))

    ;; a <= b -> b <= c -> a <= c
    (let* ((h1 `(.le ,a ,b)) (h2 `(.le ,b ,c)) (goal `(.le ,a ,c))
           (e1 `(.eq (+ ,a ,d) ,b)) (e2 `(.eq (+ ,b ,e) ,c)))
      (ded 'th-le-trans-s1 (list e1) e2
           (lambda (n1 n2)
             (le-intro (chain (sym (use 'th-add-assoc a d e)) (rw+l n1 e) n2))))
      (ded 'th-le-trans-s2 (list h2) e1
           (lambda (m2 n1) (exists-elim (le-unfold m2) (cite 'th-le-trans-s1 `(.to ,e2 ,goal) n1) e)))
      (ded 'th-le-trans-s3 (list h1) h2
           (lambda (m1 m2) (exists-elim (le-unfold m1) (cite 'th-le-trans-s2 `(.to ,e1 ,goal) m2) d)))
      (let ((st (ded 'th-le-trans-s4 nil h1
                     (lambda (m1) (cite 'th-le-trans-s3 `(.to ,h2 ,goal) m1)))))
        (close-law 'th-le-trans (lambda () (cite 'th-le-trans-s4 st)) (list a b c))))

    ;; a = 0  v  exists x4. a = S x4
    (let ((ex-of (lambda (tm) `(.exists ,*le-var* (.eq ,tm (s ,*le-var*))))))
      (induction-law 'th-zero-or-succ a `(.or (.eq ,a zero) ,(funcall ex-of a)) (list a)
        (lambda () (or-intro-l (refl 'zero) (funcall ex-of 'zero)))
        (lambda (h)
          (declare (ignore h))
          (or-intro-r `(.eq (s ,a) zero)
                      (exists-intro (refl `(s ,a)) *le-var* `(.eq (s ,a) (s ,*le-var*)) a)))))

    ;; a + b = 0 -> b = 0
    (let* ((goal `(.to (.eq (+ ,a ,b) zero) (.eq ,b zero)))
           (eb `(.eq ,b (s ,d)))
           (ex `(.exists ,*le-var* (.eq ,b (s ,*le-var*)))))
      (ded 'th-add-eq-zero-r-s1 (list eb) `(.eq (+ ,a ,b) zero)
           (lambda (neb nf)
             (let* ((sum (chain (sym (trans (rw+r a neb) (p5 a d))) nf)) ; S(a+d) = 0
                    (p1 (ax `(.neg ,(fm sum)) 'p1)))
               (mp (mp (prop 'th-ex-falso `((a . ,(fm sum)) (b . (.eq ,b zero)))) p1) sum))))
      (ded 'th-add-eq-zero-r-s2 nil eb
           (lambda (neb) (cite 'th-add-eq-zero-r-s1 goal neb)))
      (ded 'th-add-eq-zero-r-s3 nil ex
           (lambda (nex) (exists-elim nex (cite 'th-add-eq-zero-r-s2 `(.to ,eb ,goal)) d)))
      (close-law 'th-add-eq-zero-r
                 (lambda ()
                   (or-elim (ax `(.to (.eq ,b zero) ,goal) 'ii.1)
                            (cite 'th-add-eq-zero-r-s3 `(.to ,ex ,goal))
                            (use 'th-zero-or-succ b)))
                 (list a b)))

    ;; a <= b -> b <= a -> a = b
    (let* ((h1 `(.le ,a ,b)) (h2 `(.le ,b ,a)) (goal `(.eq ,a ,b))
           (e1 `(.eq (+ ,a ,d) ,b)) (e2 `(.eq (+ ,b ,e) ,a)))
      (ded 'th-le-antisym-s1 (list e1) e2
           (lambda (n1 n2)
             (let* ((de0 (mp (use 'th-add-cancel-l `(+ ,d ,e) 'zero a)
                             (chain (sym (use 'th-add-assoc a d e)) (rw+l n1 e) n2 (sym (p4 a)))))
                    (d0 (mp (use 'th-add-eq-zero-r e d) (trans (use 'th-add-comm e d) de0))))
               (sym (chain (sym n1) (rw+r a d0) (p4 a))))))
      (ded 'th-le-antisym-s2 (list h2) e1
           (lambda (m2 n1) (exists-elim (le-unfold m2) (cite 'th-le-antisym-s1 `(.to ,e2 ,goal) n1) e)))
      (ded 'th-le-antisym-s3 (list h1) h2
           (lambda (m1 m2) (exists-elim (le-unfold m1) (cite 'th-le-antisym-s2 `(.to ,e1 ,goal) m2) d)))
      (let ((st (ded 'th-le-antisym-s4 nil h1
                     (lambda (m1) (cite 'th-le-antisym-s3 `(.to ,h2 ,goal) m1)))))
        (close-law 'th-le-antisym (lambda () (cite 'th-le-antisym-s4 st)) (list a b))))

    ;; a <= b -> S a <= S b
    (let* ((h `(.le ,a ,b)) (goal `(.le (s ,a) (s ,b))) (e1 `(.eq (+ ,a ,d) ,b)))
      (ded 'th-le-succ-mono-s1 nil e1
           (lambda (n1) (le-intro (chain (use 'th-add-succ-l a d) (cong-s n1)))))
      (let ((st (ded 'th-le-succ-mono-s2 nil h
                     (lambda (m) (exists-elim (le-unfold m) (cite 'th-le-succ-mono-s1 `(.to ,e1 ,goal)) d)))))
        (close-law 'th-le-succ-mono (lambda () (cite 'th-le-succ-mono-s2 st)) (list a b))))

    ;; a <= b  v  b <= a   (induction on a)
    (let ((phi-of (lambda (x) `(.or (.le ,x ,b) (.le ,b ,x)))))
      (induction-law 'th-le-total a (funcall phi-of a) (list a b)
        (lambda () (or-intro-l (use 'th-le-zero-l b) `(.le ,b zero)))
        (lambda (h)
          (let* ((goal (funcall phi-of `(s ,a)))
                 (e1 `(.eq (+ ,a ,d) ,b))
                 (d0 `(.eq ,d zero))
                 (ds `(.eq ,d (s ,e)))
                 (exd `(.exists ,*le-var* (.eq ,d (s ,*le-var*)))))
            ;; d = 0: b = a, so b + S0 = S a
            (ded 'th-le-total-s1 (list e1) d0
                 (lambda (n1 nd)
                   (let ((ba (chain (sym n1) (rw+r a nd) (p4 a))))
                     (or-intro-r `(.le (s ,a) ,b)
                                 (le-intro (trans (rw+l ba '(s zero)) (use 'th-add-one a)))))))
            ;; d = S e: S a + e = b
            (ded 'th-le-total-s2 (list e1) ds
                 (lambda (n1 nd)
                   (or-intro-l (le-intro (chain (use 'th-add-succ-l a e) (sym (p5 a e))
                                                (rw+r a (sym nd)) n1))
                               `(.le ,b (s ,a)))))
            (ded 'th-le-total-s3 (list e1) exd
                 (lambda (n1 nx) (exists-elim nx (cite 'th-le-total-s2 `(.to ,ds ,goal) n1) e)))
            (ded 'th-le-total-s4 nil e1
                 (lambda (n1)
                   (or-elim (cite 'th-le-total-s1 `(.to ,d0 ,goal) n1)
                            (cite 'th-le-total-s3 `(.to ,exd ,goal) n1)
                            (use 'th-zero-or-succ d))))
            (ded 'th-le-total-s5 nil `(.le ,a ,b)
                 (lambda (m) (exists-elim (le-unfold m) (cite 'th-le-total-s4 `(.to ,e1 ,goal)) d)))
            (ded 'th-le-total-s6 nil `(.le ,b ,a)
                 (lambda (m)
                   (or-intro-r `(.le (s ,a) ,b)
                               (mp (mp (use 'th-le-trans b a `(s ,a)) m) (use 'th-le-succ a)))))
            (or-elim (cite 'th-le-total-s5 `(.to (.le ,a ,b) ,goal))
                     (cite 'th-le-total-s6 `(.to (.le ,b ,a) ,goal))
                     h)))))))

;;; --- division by a successor (10) ---------------------------------------------
;;;
;;; a = q * S b + r with r <= b: division by S b, which is never zero, so the
;;; quotient and remainder are total functions of (a, b).

(defun define-fn (name arg-vars y-var y2-var a-formula ex-name un-name)
  (setf *L* (define-function-by-description *L* name arg-vars y-var y2-var a-formula ex-name un-name))
  (push (list :define-function-by-description name arg-vars y-var y2-var a-formula ex-name un-name)
        *commands*))

(defun build-division ()
  (dolist (v '(x5 x6 v6 v7)) (declare-var v))
  (with-vars (a b q r q2 r2 k j)
    (let* ((sb `(s ,b))
           (falsum '(.eq (s zero) zero)))

      ;; not (S b <= b)
      (let ((e `(.eq (+ (s ,b) ,r) ,b)))
        (ded 'th-not-succ-le-s1 nil e
             (lambda (ne)
               (let* ((sr0 (mp (use 'th-add-cancel-l `(s ,r) 'zero b)
                               (chain (p5 b r) (sym (use 'th-add-succ-l b r)) ne (sym (p4 b)))))
                      (np1 (ax `(.neg ,(fm sr0)) 'p1)))
                 (ex-falso np1 sr0 falsum))))
        (ded 'th-not-succ-le-s2 nil `(.le (s ,b) ,b)
             (lambda (m) (exists-elim (le-unfold m) (cite 'th-not-succ-le-s1 `(.to ,e ,falsum)) r)))
        (close-law 'th-not-succ-le
                   (lambda ()
                     (let* ((le `(.le (s ,b) ,b))
                            (raa (prop 'th-raa `((a . ,le) (b . ,falsum))))
                            (np1 (ax `(.neg ,falsum) 'p1))
                            (k2 (mp (ax `(.to (.neg ,falsum) (.to ,le (.neg ,falsum))) 'ii.1) np1)))
                       (mp (mp raa (cite 'th-not-succ-le-s2 `(.to ,le ,falsum))) k2)))
                   (list b)))

      ;; r <= b -> r = b  v  S r <= b
      (let* ((goal `(.or (.eq ,r ,b) (.le (s ,r) ,b)))
             (e1 `(.eq (+ ,r ,q) ,b)) (d0 `(.eq ,q zero)) (ds `(.eq ,q (s ,k)))
             (exd `(.exists x4 (.eq ,q (s x4)))))
        (ded 'th-le-cases-s1 (list e1) d0
             (lambda (n1 nd)
               (or-intro-l (chain (sym (p4 r)) (rw+r r (sym nd)) n1) `(.le (s ,r) ,b))))
        (ded 'th-le-cases-s2 (list e1) ds
             (lambda (n1 nd)
               (or-intro-r `(.eq ,r ,b)
                           (le-intro (chain (use 'th-add-succ-l r k) (sym (p5 r k))
                                            (rw+r r (sym nd)) n1)))))
        (ded 'th-le-cases-s3 (list e1) exd
             (lambda (n1 nx) (exists-elim nx (cite 'th-le-cases-s2 `(.to ,ds ,goal) n1) k)))
        (ded 'th-le-cases-s4 nil e1
             (lambda (n1)
               (or-elim (cite 'th-le-cases-s1 `(.to ,d0 ,goal) n1)
                        (cite 'th-le-cases-s3 `(.to ,exd ,goal) n1)
                        (use 'th-zero-or-succ q))))
        (let ((st (ded 'th-le-cases-s5 nil `(.le ,r ,b)
                       (lambda (m) (exists-elim (le-unfold m) (cite 'th-le-cases-s4 `(.to ,e1 ,goal)) q)))))
          (close-law 'th-le-cases (lambda () (cite 'th-le-cases-s5 st)) (list r b))))

      ;; existence: forall a b. exists x3 x5. a = x5 * S b + x3  and  x3 <= b
      (flet ((body (tm qq rr) `(.and (.eq ,tm (+ (* ,qq ,sb) ,rr)) (.le ,rr ,b))))
        (let ((phi-of (lambda (tm) `(.exists x3 (.exists x5 ,(body tm 'x5 'x3))))))
          (flet ((pack (n-eq n-le)
                   ;; n-eq: T = Q * S b + R,  n-le: R <= b  ==>  phi(T)
                   (destructuring-bind (eq tm (plus (times qq sbb) rr)) (fm n-eq)
                     (declare (ignore eq plus times sbb))
                     (let* ((c (and-intro n-eq n-le))
                            (e5 (exists-intro c 'x5 (body tm 'x5 rr) qq)))
                       (exists-intro e5 'x3 `(.exists x5 ,(body tm 'x5 'x3)) rr)))))
            (induction-law 'th-divmod-exists a (funcall phi-of a) (list a b)
              (lambda ()
                (pack (sym (trans (p4 `(* zero ,sb)) (use 'th-mul-zero-l sb)))
                      (use 'th-le-zero-l b)))
              (lambda (h)
                (let* ((goal (funcall phi-of `(s ,a)))
                       (eq `(.eq ,a (+ (* ,q ,sb) ,r)))
                       (le `(.le ,r ,b)) (rb `(.eq ,r ,b)) (rs `(.le (s ,r) ,b))
                       (and-f (body a q r))
                       (ex5 `(.exists x5 ,(body a 'x5 r))))
                  (flet ((sa (neq) ; S a = q * S b + S r
                           (trans (cong-s neq) (sym (p5 `(* ,q ,sb) r)))))
                    (ded 'th-divmod-exists-k1 (list eq) rb
                         (lambda (neq nrb)
                           (pack (chain (sa neq) (rw+r `(* ,q ,sb) (cong-s nrb))
                                        (sym (use 'th-mul-succ-l q sb)) (sym (p4 `(* (s ,q) ,sb))))
                                 (use 'th-le-zero-l b))))
                    (ded 'th-divmod-exists-k2 (list eq) rs
                         (lambda (neq nrs) (pack (sa neq) nrs))))
                  (ded 'th-divmod-exists-k3 (list eq) le
                       (lambda (neq nle)
                         (or-elim (cite 'th-divmod-exists-k1 `(.to ,rb ,goal) neq)
                                  (cite 'th-divmod-exists-k2 `(.to ,rs ,goal) neq)
                                  (mp (use 'th-le-cases r b) nle))))
                  (ded 'th-divmod-exists-k4 nil and-f
                       (lambda (nc) (mp (cite 'th-divmod-exists-k3 `(.to ,le ,goal) (and-l nc)) (and-r nc))))
                  (ded 'th-divmod-exists-k5 nil ex5
                       (lambda (nx) (exists-elim nx (cite 'th-divmod-exists-k4 `(.to ,and-f ,goal)) q)))
                  (exists-elim h (cite 'th-divmod-exists-k5 `(.to ,ex5 ,goal)) r)))))))

      ;; core of uniqueness:
      ;; q S b + r = q2 S b + r2 -> r <= b -> q <= q2 -> q = q2 and r = r2
      (let* ((qsb `(* ,q ,sb)) (q2sb `(* ,q2 ,sb)) (ksb `(* ,k ,sb))
             (he `(.eq (+ ,qsb ,r) (+ ,q2sb ,r2)))
             (hr `(.le ,r ,b))
             (goal `(.and (.eq ,q ,q2) (.eq ,r ,r2)))
             (ek `(.eq (+ ,q ,k) ,q2))
             (er `(.eq ,r (+ ,ksb ,r2)))
             (kz `(.eq ,k zero)) (ks `(.eq ,k (s ,j)))
             (exk `(.exists x4 (.eq ,k (s x4)))))
        (ded 'th-divmod-unique-u1 (list ek er) kz
             (lambda (nek ner nkz)
               (and-intro (chain (sym (p4 q)) (rw+r q (sym nkz)) nek)
                          (chain ner (rw+l (trans (rw*l nkz sb) (use 'th-mul-zero-l sb)) r2)
                                 (use 'th-add-zero-l r2)))))
        (ded 'th-divmod-unique-u2 (list er hr) ks
             (lambda (ner nhr nks)
               (let* ((jsb `(* ,j ,sb))
                      (r-big (chain ner
                                    (rw+l (chain (rw*l nks sb) (use 'th-mul-succ-l j sb)
                                                 (use 'th-add-comm jsb sb))
                                          r2)
                                    (use 'th-add-assoc sb jsb r2)))
                      (sb-le-r (le-intro (sym r-big)))
                      (sb-le-b (mp (mp (use 'th-le-trans sb r b) sb-le-r) nhr)))
                 (ex-falso (use 'th-not-succ-le b) sb-le-b goal))))
        (ded 'th-divmod-unique-u3 (list er hr) exk
             (lambda (ner nhr nx) (exists-elim nx (cite 'th-divmod-unique-u2 `(.to ,ks ,goal) ner nhr) j)))
        (ded 'th-divmod-unique-u4 (list ek hr) er
             (lambda (nek nhr ner)
               (or-elim (cite 'th-divmod-unique-u1 `(.to ,kz ,goal) nek ner)
                        (cite 'th-divmod-unique-u3 `(.to ,exk ,goal) ner nhr)
                        (use 'th-zero-or-succ k))))
        (ded 'th-divmod-unique-u5 (list he hr) ek
             (lambda (nhe nhr nek)
               (let* ((q2sb= (trans (rw*l (sym nek) sb) (use 'th-mul-distrib-r q k sb)))
                      (e2 (chain nhe (rw+l q2sb= r2) (use 'th-add-assoc qsb ksb r2)))
                      (nr (mp (use 'th-add-cancel-l r `(+ ,ksb ,r2) qsb) e2)))
                 (mp (cite 'th-divmod-unique-u4 `(.to ,er ,goal) nek nhr) nr))))
        (ded 'th-divmod-unique-u6 (list he hr) `(.le ,q ,q2)
             (lambda (nhe nhr nq)
               (exists-elim (le-unfold nq) (cite 'th-divmod-unique-u5 `(.to ,ek ,goal) nhe nhr) k)))
        (ded 'th-divmod-unique-u7 (list he) hr
             (lambda (nhe nhr) (cite 'th-divmod-unique-u6 `(.to (.le ,q ,q2) ,goal) nhe nhr)))
        (let ((st (ded 'th-divmod-unique-u8 nil he
                       (lambda (nhe) (cite 'th-divmod-unique-u7 `(.to ,hr (.to (.le ,q ,q2) ,goal)) nhe)))))
          (close-law 'th-divmod-unique-core (lambda () (cite 'th-divmod-unique-u8 st))
                     (list b q r q2 r2) '(x1 x2 x3 x5 x6))))

      ;; both quotient and remainder agree
      (let* ((qsb `(* ,q ,sb)) (q2sb `(* ,q2 ,sb))
             (he `(.eq (+ ,qsb ,r) (+ ,q2sb ,r2)))
             (hr `(.le ,r ,b)) (hr2 `(.le ,r2 ,b))
             (goal `(.and (.eq ,q ,q2) (.eq ,r ,r2)))
             (goal2 `(.and (.eq ,q2 ,q) (.eq ,r2 ,r))))
        (ded 'th-divmod-unique-p1 nil goal2
             (lambda (n) (and-intro (sym (and-l n)) (sym (and-r n)))))
        (ded 'th-divmod-unique-p2 (list he hr2) `(.le ,q2 ,q)
             (lambda (nhe nhr2 nq)
               (mp (cite 'th-divmod-unique-p1 `(.to ,goal2 ,goal))
                   (mp (mp (mp (use 'th-divmod-unique-core b q2 r2 q r) (sym nhe)) nhr2) nq))))
        (ded 'th-divmod-unique-p3 (list he hr) hr2
             (lambda (nhe nhr nhr2)
               (or-elim (mp (mp (use 'th-divmod-unique-core b q r q2 r2) nhe) nhr)
                        (cite 'th-divmod-unique-p2 `(.to (.le ,q2 ,q) ,goal) nhe nhr2)
                        (use 'th-le-total q q2)))))

      (close-law 'th-divmod-unique
                 (lambda ()
                   (let* ((qsb `(* ,q ,sb)) (q2sb `(* ,q2 ,sb))
                          (he `(.eq (+ ,qsb ,r) (+ ,q2sb ,r2)))
                          (hr `(.le ,r ,b)) (hr2 `(.le ,r2 ,b))
                          (goal `(.and (.eq ,q ,q2) (.eq ,r ,r2))))
                     (ded 'th-divmod-unique-p4 (list he) hr
                          (lambda (nhe nhr) (cite 'th-divmod-unique-p3 `(.to ,hr2 ,goal) nhe nhr)))
                     (let ((st (ded 'th-divmod-unique-p5 nil he
                                    (lambda (nhe) (cite 'th-divmod-unique-p4
                                                        `(.to ,hr (.to ,hr2 ,goal)) nhe)))))
                       (cite 'th-divmod-unique-p5 st))))
                 (list b q r q2 r2) '(x1 x2 x3 x5 x6))

      ;; The defining formulas below contain no binders (<= and < are atomic),
      ;; so no instance of the defining axioms can capture a variable.

      ;; x <= y -> x * z <= y * z
      (let* ((h `(.le ,q ,q2)) (goal `(.le (* ,q ,k) (* ,q2 ,k))) (e1 `(.eq (+ ,q ,j) ,q2)))
        (ded 'th-le-mul-mono-s1 nil e1
             (lambda (n1) (le-intro (trans (sym (use 'th-mul-distrib-r q j k)) (rw*l n1 k)))))
        (let ((st (ded 'th-le-mul-mono-s2 nil h
                       (lambda (m) (exists-elim (le-unfold m) (cite 'th-le-mul-mono-s1 `(.to ,e1 ,goal)) j)))))
          (close-law 'th-le-mul-mono (lambda () (cite 'th-le-mul-mono-s2 st)) (list q q2 k))))

      ;; the quotient: q * S b <= a < S q * S b
      (let* ((aq (lambda (qq) `(.and (.le (* ,qq ,sb) ,a) (.lt ,a (* (s ,qq) ,sb)))))
             (h1 `(.le ,q ,q2)) (h2 `(.le (* ,q2 ,sb) ,a)) (h3 `(.lt ,a (* (s ,q) ,sb)))
             (g `(.eq ,q ,q2)))
        ;; q <= q2 -> q2 S b <= a -> a < S q S b -> q = q2
        (ded 'th-div-s-unique-d1 (list h2 h3) `(.le (s ,q) ,q2)
             (lambda (n2 n3 nsq)
               (let* ((m (mp (use 'th-le-mul-mono `(s ,q) q2 sb) nsq))
                      (t1 (mp (mp (use 'th-le-trans `(* (s ,q) ,sb) `(* ,q2 ,sb) a) m) n2))
                      (lt (mp (ax `(.to ,h3 (.le (s ,a) (* (s ,q) ,sb))) 'lt-unfold) n3))
                      (t2 (mp (mp (use 'th-le-trans `(s ,a) `(* (s ,q) ,sb) a) lt) t1)))
                 (ex-falso (use 'th-not-succ-le a) t2 g))))
        (ded 'th-div-s-unique-d2 (list h2 h3) h1
             (lambda (n2 n3 n1)
               (or-elim (cite 'th-identity `(.to ,g ,g))
                        (cite 'th-div-s-unique-d1 `(.to (.le (s ,q) ,q2) ,g) n2 n3)
                        (mp (use 'th-le-cases q q2) n1))))
        (ded 'th-div-s-unique-d3 (list h2) h3
             (lambda (n2 n3) (cite 'th-div-s-unique-d2 `(.to ,h1 ,g) n2 n3)))
        (let ((st (ded 'th-div-s-unique-d4 nil h2
                       (lambda (n2) (cite 'th-div-s-unique-d3 `(.to ,h3 (.to ,h1 ,g)) n2)))))
          (close-law 'th-div-s-unique-core (lambda () (cite 'th-div-s-unique-d4 st))
                     (list b q q2 a) '(x1 x2 x3 x5)))
        ;; A(q) -> A(q2) -> q = q2
        (let ((c1 (funcall aq q)) (c2 (funcall aq q2)))
          (ded 'th-div-s-unique-v0 (list c1 c2) `(.le ,q2 ,q)
               (lambda (n1 n2 nle)
                 (sym (mp (mp (mp (use 'th-div-s-unique-core b q2 q a) (and-l n1)) (and-r n2)) nle))))
          (ded 'th-div-s-unique-v1 (list c1) c2
               (lambda (n1 n2)
                 (or-elim (mp (mp (use 'th-div-s-unique-core b q q2 a) (and-l n2)) (and-r n1))
                          (cite 'th-div-s-unique-v0 `(.to (.le ,q2 ,q) ,g) n1 n2)
                          (use 'th-le-total q q2))))
          (let ((st (ded 'th-div-s-unique-v2 nil c1
                         (lambda (n1) (cite 'th-div-s-unique-v1 `(.to ,c2 ,g) n1)))))
            (close-law 'th-div-s-unique (lambda () (cite 'th-div-s-unique-v2 st))
                       (list a b q q2) '(x1 x2 x3 x6))))
        ;; a = q S b + r -> r <= b -> A(q)
        (let* ((ceq `(.eq ,a (+ (* ,q ,sb) ,r)))
               (er `(.eq (+ ,r ,k) ,b))
               (c (funcall aq q))
               (body `(.and (.eq ,a (+ (* ,q ,sb) ,r)) (.le ,r ,b)))
               (ex5 `(.exists x5 (.and (.eq ,a (+ (* x5 ,sb) ,r)) (.le ,r ,b))))
               (goal `(.exists x3 ,(funcall aq 'x3))))
          (ded 'th-div-s-exists-x1 (list ceq) er
               (lambda (nc ne)
                 (let* ((qsb `(* ,q ,sb))
                        (le1 (le-intro (sym nc)))
                        (sum (chain (rw+l (trans (cong-s nc) (sym (p5 qsb r))) k)
                                    (use 'th-add-assoc qsb `(s ,r) k)
                                    (rw+r qsb (trans (use 'th-add-succ-l r k) (cong-s ne)))
                                    (sym (use 'th-mul-succ-l q sb))))
                        (lt (mp (ax `(.to (.le (s ,a) (* (s ,q) ,sb)) (.lt ,a (* (s ,q) ,sb))) 'lt-fold)
                                (le-intro sum))))
                   (and-intro le1 lt))))
          (ded 'th-div-s-exists-x2 (list ceq) `(.le ,r ,b)
               (lambda (nc nle) (exists-elim (le-unfold nle) (cite 'th-div-s-exists-x1 `(.to ,er ,c) nc) k)))
          (ded 'th-div-s-exists-x3 nil body
               (lambda (nb)
                 (exists-intro (mp (cite 'th-div-s-exists-x2 `(.to (.le ,r ,b) ,c) (and-l nb)) (and-r nb))
                               'x3 (funcall aq 'x3) q)))
          (ded 'th-div-s-exists-x4 nil ex5
               (lambda (nx) (exists-elim nx (cite 'th-div-s-exists-x3 `(.to ,body ,goal)) q)))
          (close-law 'th-div-s-exists
                     (lambda ()
                       (exists-elim (use 'th-divmod-exists a b) (cite 'th-div-s-exists-x4 `(.to ,ex5 ,goal)) r))
                     (list a b))
          (define-fn 'div-s '(x1 x2) 'x3 'x6
                     '(.and (.le (* x3 (s x2)) x1) (.lt x1 (* (s x3) (s x2))))
                     'th-div-s-exists 'th-div-s-unique)

          ;; the remainder: a = div-s(a, b) * S b + r
          (let* ((dd `(div-s ,a ,b)) (dsb `(* ,dd ,sb))
                 (ar (lambda (rr) `(.eq ,a (+ ,dsb ,rr))))
                 (def (lambda () (ax `(.and (.le ,dsb ,a) (.lt ,a (* (s ,dd) ,sb))) 'div-s-def))))
            (ded 'th-mod-s-exists-y1 nil `(.eq (+ ,dsb ,r) ,a)
                 (lambda (n) (exists-intro (sym n) 'x3 (funcall ar 'x3) r)))
            (close-law 'th-mod-s-exists
                       (lambda ()
                         (exists-elim (le-unfold (and-l (funcall def)))
                                      (cite 'th-mod-s-exists-y1 `(.to (.eq (+ ,dsb ,r) ,a) (.exists x3 ,(funcall ar 'x3))))
                                      r))
                       (list a b))
            (let ((st (ded 'th-mod-s-unique-z1 (list (funcall ar r)) (funcall ar r2)
                           (lambda (n1 n2)
                             (mp (use 'th-add-cancel-l r r2 dsb) (trans (sym n1) n2))))))
              (ded 'th-mod-s-unique-z2 nil (funcall ar r)
                   (lambda (n1) (cite 'th-mod-s-unique-z1 st n1)))
              (close-law 'th-mod-s-unique
                         (lambda () (cite 'th-mod-s-unique-z2 `(.to ,(funcall ar r) ,st)))
                         (list a b r r2) '(x1 x2 x3 x6)))
            (define-fn 'mod-s '(x1 x2) 'x3 'x6
                       '(.eq x1 (+ (* (div-s x1 x2) (s x2)) x3))
                       'th-mod-s-exists 'th-mod-s-unique)

            ;; mod-s(a, b) <= b
            (let* ((md `(mod-s ,a ,b)) (goal `(.le ,md ,b)))
              (ded 'th-mod-s-le-m1 (list ceq) `(.le ,r ,b)
                   (lambda (nc nle)
                     (let* ((dq (mp (mp (use 'th-div-s-unique a b dd q) (funcall def))
                                    (mp (cite 'th-div-s-exists-x2 `(.to (.le ,r ,b) ,c) nc) nle)))
                            (a-dr (trans nc (rw+l (rw*l (sym dq) sb) r)))
                            (mdef (ax `(.eq ,a (+ ,dsb ,md)) 'mod-s-def))
                            (mr (mp (mp (use 'th-mod-s-unique a b md r) mdef) a-dr))
                            (m-le-r (le-intro (trans (p4 md) mr))))
                       (mp (mp (use 'th-le-trans md r b) m-le-r) nle))))
              (ded 'th-mod-s-le-m2 nil body
                   (lambda (nb) (mp (cite 'th-mod-s-le-m1 `(.to (.le ,r ,b) ,goal) (and-l nb)) (and-r nb))))
              (ded 'th-mod-s-le-m3 nil ex5
                   (lambda (nx) (exists-elim nx (cite 'th-mod-s-le-m2 `(.to ,body ,goal)) q)))
              (close-law 'th-mod-s-le
                         (lambda ()
                           (exists-elim (use 'th-divmod-exists a b) (cite 'th-mod-s-le-m3 `(.to ,ex5 ,goal)) r))
                         (list a b))))))

      ;; Goedel's beta function: beta(c, d, i) = c mod (1 + (i + 1) d)
      ;;                                        = mod-s(c, S i * d)
      (with-vars (c d i y y2)
        (let ((tm `(mod-s ,c (* (s ,i) ,d))))
          (close-law 'th-beta-exists
                     (lambda () (exists-intro (refl tm) 'x5 `(.eq x5 ,tm) tm))
                     (list c d i))
          (let ((st (ded 'th-beta-unique-s1 (list `(.eq ,y ,tm)) `(.eq ,y2 ,tm)
                         (lambda (n1 n2) (trans n1 (sym n2))))))
            (ded 'th-beta-unique-s2 nil `(.eq ,y ,tm)
                 (lambda (n1) (cite 'th-beta-unique-s1 st n1)))
            (close-law 'th-beta-unique
                       (lambda () (cite 'th-beta-unique-s2 `(.to (.eq ,y ,tm) ,st)))
                       (list c d i y y2) '(x1 x2 x3 x5 x6))))
        (define-fn 'beta '(x1 x2 x3) 'x5 'x6 '(.eq x5 (mod-s x1 (* (s x3) x2)))
                   'th-beta-exists 'th-beta-unique)))))

(defparameter *header-09* ";;; 09-order.ledger -- generated by tools/generate-arithmetic-ledger.lisp
;;;
;;; The order of the natural numbers (00-peano-order.system: s <= t is
;;; exists x4. s + x4 = t). Load after 08-arithmetic.ledger. Laws are closed
;;; over the bound-only variables x1 x2 x3, as in 08:
;;;
;;;   th-le-refl        x <= x
;;;   th-le-zero-l      0 <= x
;;;   th-le-succ        x <= S x
;;;   th-le-add         x <= x + y
;;;   th-le-trans       x <= y -> y <= z -> x <= z
;;;   th-le-antisym     x <= y -> y <= x -> x = y
;;;   th-le-succ-mono   x <= y -> S x <= S y
;;;   th-le-total       x <= y  v  y <= x
;;;   th-zero-or-succ   x = 0  v  exists x4. x = S x4
;;;   th-add-eq-zero-r  x + y = 0 -> y = 0

")

(defun write-library (path header commands)
  (with-open-file (out path :direction :output :if-exists :supersede :if-does-not-exist :create)
    (write-string header out)
    (let ((*package* (find-package :ledger-kernel))
          (*print-case* :downcase)
          (*print-right-margin* 100))
      (dolist (cmd commands)
        (pprint cmd out)
        (terpri out)))))

(defparameter *header-10* ";;; 10-division.ledger -- generated by tools/generate-arithmetic-ledger.lisp
;;;
;;; Division by a successor, S b (never zero), and the functions it defines.
;;; Load after 09-order.ledger.
;;;
;;;   th-not-succ-le          not (S x <= x)
;;;   th-le-cases             x <= y -> x = y  v  S x <= y
;;;   th-divmod-exists        forall a b. exists r q. a = q * S b + r  and  r <= b
;;;   th-divmod-unique-core   q S b + r = q' S b + r' -> r <= b -> q <= q' -> q = q' and r = r'
;;;   th-divmod-unique        q S b + r = q' S b + r' -> r <= b -> r' <= b -> q = q' and r = r'
;;;   th-le-mul-mono          x <= y -> x * z <= y * z
;;;   th-div-s-unique, th-div-s-exists, th-mod-s-unique, th-mod-s-exists
;;;   th-mod-s-le             mod-s(a, b) <= b
;;;
;;;   div-s(a, b)   the quotient of a divided by S b:
;;;                 div-s(a,b) * S b <= a < S div-s(a,b) * S b      (DIV-S-DEF)
;;;   mod-s(a, b)   the remainder: a = div-s(a,b) * S b + mod-s(a,b)  (MOD-S-DEF)
;;;   beta(c, d, i) Goedel's beta function, mod-s(c, S i * d), i.e. the
;;;                 remainder of c divided by 1 + (i + 1) d   (BETA-DEF)
;;;
;;; All three are admitted by DEFINE-FUNCTION-BY-DESCRIPTION, which re-checks
;;; the existence and uniqueness theorems above before adding the symbol.
;;; Their defining formulas contain no binders (<= and < are atomic), so no
;;; instance of a defining axiom can capture a variable.

")

(enable-derived-entry-memoization)
(setf *L* (peano-base-ledger))
(build-arithmetic)
(let ((arith (reverse *commands*)) order)
  (setf *commands* nil)
  (build-order)
  (setf order (reverse *commands*) *commands* nil)
  (build-division)
  (write-library (library-file "08-arithmetic.ledger") *header-08* arith)
  (write-library (library-file "09-order.ledger") *header-09* order)
  (write-library (library-file "10-division.ledger") *header-10* (reverse *commands*))
  (format t "~&Wrote ~D + ~D + ~D commands to 08-arithmetic, 09-order, 10-division~%"
          (length arith) (length order) (length *commands*)))
