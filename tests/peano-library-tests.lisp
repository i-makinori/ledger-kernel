;;;; peano-library-tests.lisp -- 00-peano-order.system and the generated
;;;; 08-arithmetic, 09-order, 10-division ledgers
;;;; (tools/generate-arithmetic-ledger.lisp)

(in-package :ledger-kernel)

(defun peano-library-ledger ()
  "FOL + connectives + Peano arithmetic + order, and the modules 01-06, 08-10."
  (let ((l nil))
    (dolist (f '("00-classical-fol-equality.system" "00-connectives.system"
                 "00-peano-arithmetic.system" "00-peano-order.system"))
      (setf l (bootstrap-kernel-from-spec-file (library-path f) :ledger l)))
    (dolist (f '("01-propositional-core.ledger" "02-predicate-core.ledger"
                 "03-equality-core.ledger" "04-peano-arithmetic.ledger"
                 "05-classical-logic.ledger" "06-connectives.ledger"
                 "08-arithmetic.ledger" "09-order.ledger" "10-division.ledger")
               l)
      (setf l (read-ledger-from-file (library-path f) :ledger l)))))

(defparameter *peano-laws*
  '((th-add-comm (.forall x1 (.forall x2 (.eq (+ x1 x2) (+ x2 x1)))))
    (th-add-assoc (.forall x1 (.forall x2 (.forall x3 (.eq (+ (+ x1 x2) x3) (+ x1 (+ x2 x3)))))))
    (th-add-cancel-r (.forall x1 (.forall x2 (.forall x3 (.to (.eq (+ x1 x3) (+ x2 x3)) (.eq x1 x2))))))
    (th-mul-comm (.forall x1 (.forall x2 (.eq (* x1 x2) (* x2 x1)))))
    (th-mul-assoc (.forall x1 (.forall x2 (.forall x3 (.eq (* (* x1 x2) x3) (* x1 (* x2 x3)))))))
    (th-mul-distrib-l (.forall x1 (.forall x2 (.forall x3 (.eq (* x1 (+ x2 x3)) (+ (* x1 x2) (* x1 x3)))))))
    (th-le-trans (.forall x1 (.forall x2 (.forall x3 (.to (.le x1 x2) (.to (.le x2 x3) (.le x1 x3)))))))
    (th-le-antisym (.forall x1 (.forall x2 (.to (.le x1 x2) (.to (.le x2 x1) (.eq x1 x2))))))
    (th-le-total (.forall x1 (.forall x2 (.or (.le x1 x2) (.le x2 x1)))))
    (th-zero-or-succ (.forall x1 (.or (.eq x1 zero) (.exists x4 (.eq x1 (s x4))))))
    (th-divmod-exists (.forall x1 (.forall x2 (.exists x3 (.exists x5 (.and (.eq x1 (+ (* x5 (s x2)) x3))
                                                                           (.le x3 x2)))))))
    (th-mod-s-le (.forall x1 (.forall x2 (.le (mod-s x1 x2) x2)))))
  "Some of the closed laws of 08-10, as they must be stated.")

(defun count-binders (form)
  "Number of binder occurrences (.forall, .exists, ...) in FORM."
  (cond ((atom form) 0)
        ((member (car form) (binder-heads)) (1+ (count-binders (cddr form))))
        (t (+ (count-binders (car form)) (count-binders (cdr form))))))

(defun test-peano-laws (ledger)
  (dolist (law *peano-laws*)
    (expect (format nil "~(~A~) is a theorem, stated as documented" (first law))
            (check-k-proof `((0 ,(second law) :th (,(first law)))) ledger) t))
  (let ((comm (second (assoc 'th-add-comm *peano-laws*))))
    (expect "using a law: 1 + 2 = 2 + 1 by instantiating th-add-comm with III.1"
            (check-k-proof
             `((0 ,comm :th (th-add-comm))
               (1 (.to ,comm (.forall x2 (.eq (+ (s zero) x2) (+ x2 (s zero))))) :axiom (iii.1 (s zero)))
               (2 (.forall x2 (.eq (+ (s zero) x2) (+ x2 (s zero)))) :ir (mp 1 0))
               (3 (.to (.forall x2 (.eq (+ (s zero) x2) (+ x2 (s zero))))
                       (.eq (+ (s zero) (s (s zero))) (+ (s (s zero)) (s zero))))
                  :axiom (iii.1 (s (s zero))))
               (4 (.eq (+ (s zero) (s (s zero))) (+ (s (s zero)) (s zero))) :ir (mp 3 2)))
             ledger)
            t))
  (expect "Attack: citing th-le-antisym as if x <= y alone gave x = y -- must reject"
          (check-k-proof '((0 (.forall x1 (.forall x2 (.to (.le x1 x2) (.eq x1 x2))))
                            :th (th-le-antisym)))
                         ledger)
          nil)
  (expect "Attack: capturing instantiation of a closed law (x2 into forall x2) -- must reject"
          (check-k-proof '((0 (.forall x1 (.forall x2 (.eq (+ x1 x2) (+ x2 x1)))) :th (th-add-comm))
                           (1 (.to (.forall x1 (.forall x2 (.eq (+ x1 x2) (+ x2 x1))))
                                   (.forall x2 (.eq (+ x2 x2) (+ x2 x2))))
                            :axiom (iii.1 x2)))
                         ledger)
          nil)
  (expect "division: 7 = div-s(7, 2) * 3 + mod-s(7, 2) is an instance of MOD-S-DEF"
          (let ((seven '(s (s (s (s (s (s (s zero)))))))) (two '(s (s zero))))
            (check-k-proof `((0 (.eq ,seven (+ (* (div-s ,seven ,two) (s ,two)) (mod-s ,seven ,two)))
                              :th (mod-s-def :inst ((x1 ,seven) (x2 ,two)))))
                           ledger))
          t)
  (expect "the three defined functions (div-s, mod-s, beta) are iota abbreviations with binder-free formulas"
          (let ((defs (remove-if-not (lambda (e) (eq (second (entry-origin e)) :by-description))
                                     (entries-of-kind 'abbreviation ledger))))
            (and (= (length defs) 3)
                 (every (lambda (e)
                          ;; As written: the iota term over a formula with no binder of its own.
                          (let ((body (second (or (getf (cdr (entry-origin e)) :written) (entry-payload e)))))
                            (and (eq (first body) '.iota) (= 0 (count-binders (third body))))))
                        defs)))
          t)
  (expect "s <= t is exists z (s + z = t), whatever z is called"
          (same-formula-p ledger '(.le v0 v1) '(.exists v2 (.eq (+ v0 v2) v1))) t)
  (expect "Attack: an expansion whose bound variable is free in the terms is a different formula"
          (same-formula-p ledger '(.le v0 v1) '(.exists v0 (.eq (+ v0 v0) v1))) nil)
  ledger)

(defun run-peano-library-self-tests ()
  "The generated arithmetic and order libraries load (every proof
re-verified) and their laws can be cited."
  (let ((ledger (peano-library-ledger)))
    (test-peano-laws ledger)
    (expect "every TH-DED of the arithmetic libraries is expanded into a real, checked proof"
            (every #'deduction-entry-expanded-p (entries-of-kind 'th-ded ledger)) t))
  (format t "~%Peano library self-tests complete.~%"))
