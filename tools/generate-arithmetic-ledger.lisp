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
    (mp (ax `(.to (.forall ,x ,a) ,(substitute-wff x term a)) 'iii.1 term) n)))

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

(defun close-law (name open-proof-fn vars)
  "Admit NAME: the universal closure over *BOUND-VARS* of the formula that
OPEN-PROOF-FN proves (in the working VARS). Each working variable a_i is
generalized, instantiated to x_i by III.1 and generalized again."
  (let ((proof
          (with-proof
            (let ((n (funcall open-proof-fn)))
              (loop for a in (reverse vars)
                    for x in (reverse (subseq *bound-vars* 0 (length vars)))
                    do (setf n (gen (forall-elim (gen n a) x) x)))))))
    (admit-th name proof)
    (setf (gethash name *closed*) (proof-conclusion proof))
    name))

(defun induction-law (name var phi vars base step)
  "Prove PHI by induction on VAR and admit the closed law NAME.
BASE is a function building a proof of PHI[0/VAR]; it may return
(:ded HYP) to have the proof admitted by the Deduction Theorem instead.
STEP receives the line of the hypothesis PHI and builds PHI[S VAR/VAR]."
  (let* ((phi0 (substitute-wff var 'zero phi))
         (phis (substitute-wff var `(s ,var) phi))
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
                  (th-ex-falso '(.to (.neg a) (.to a b))))))

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

(enable-derived-entry-memoization)
(setf *L* (peano-base-ledger))
(build-arithmetic)
(let ((arith (reverse *commands*)))
  (setf *commands* nil)
  (build-order)
  (write-library (library-file "08-arithmetic.ledger") *header-08* arith)
  (write-library (library-file "09-order.ledger") *header-09* (reverse *commands*))
  (format t "~&Wrote ~D + ~D commands to 08-arithmetic.ledger and 09-order.ledger~%"
          (length arith) (length *commands*)))
