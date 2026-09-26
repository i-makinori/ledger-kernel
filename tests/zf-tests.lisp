;;;; zf-tests.lisp -- zf-library/00-zf.system: ZF set theory axioms
;;;; Part of the ledger-kernel/tests system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; The expected instances below are built with small helpers written
;;; independently of the .system file, directly from the textbook
;;; statement of each axiom, so a transcription error in the file shows up
;;; as a rejected positive instance rather than being checked against
;;; itself.

(defun zf-and (a b) (list '.neg (list '.to a (list '.neg b))))
(defun zf-or (a b) (list '.to (list '.neg a) b))
(defun zf-iff (a b) (zf-and (list '.to a b) (list '.to b a)))
(defun zf-in (a b) (list '.in a b))
(defun zf-eq (a b) (list '.eq a b))
(defun zf-all (x a) (list '.forall x a))
(defun zf-ex (x a) (list '.exists x a))
(defun zf-imp (a b) (list '.to a b))
(defun zf-not (a) (list '.neg a))

(defun zf-extensionality (x y z)
  (zf-all x (zf-all y (zf-imp (zf-all z (zf-iff (zf-in z x) (zf-in z y)))
                              (zf-eq x y)))))

(defun zf-pairing (x y z w)
  (zf-all x (zf-all y (zf-ex z (zf-all w (zf-iff (zf-in w z)
                                                 (zf-or (zf-eq w x) (zf-eq w y))))))))

(defun zf-union (x y z w)
  (zf-all x (zf-ex y (zf-all z (zf-iff (zf-in z y)
                                       (zf-ex w (zf-and (zf-in w x) (zf-in z w))))))))

(defun zf-power-set (x y z w)
  (zf-all x (zf-ex y (zf-all z (zf-iff (zf-in z y)
                                       (zf-all w (zf-imp (zf-in w z) (zf-in w x))))))))

(defun zf-infinity (x y z w)
  (zf-ex x (zf-and (zf-ex y (zf-and (zf-in y x) (zf-all z (zf-not (zf-in z y)))))
                   (zf-all y (zf-imp (zf-in y x)
                                     (zf-ex z (zf-and (zf-in z x)
                                                      (zf-all w (zf-iff (zf-in w z)
                                                                        (zf-or (zf-in w y) (zf-eq w y)))))))))))

(defun zf-foundation (x y z)
  (zf-all x (zf-imp (zf-ex y (zf-in y x))
                    (zf-ex y (zf-and (zf-in y x)
                                     (zf-not (zf-ex z (zf-and (zf-in z y) (zf-in z x)))))))))

(defun zf-separation (x y z phi)
  (zf-all x (zf-ex y (zf-all z (zf-iff (zf-in z y) (zf-and (zf-in z x) phi))))))

(defun zf-replacement (a b x y u phi phi-u)
  "PHI-U is PHI with U substituted for Y, written out by the caller."
  (zf-all a (zf-imp (zf-all x (zf-imp (zf-in x a)
                                      (zf-ex y (zf-and phi (zf-all u (zf-imp phi-u (zf-eq u y)))))))
                    (zf-ex b (zf-all x (zf-imp (zf-in x a)
                                               (zf-ex y (zf-and (zf-in y b) phi))))))))

(defun zf-ledger ()
  (bootstrap-kernel-from-spec-file
   (asdf:system-relative-pathname :ledger-kernel "zf-library/00-zf.system")
   :ledger (bootstrap-kernel-from-spec-file (library-path "00-classical-fol-equality.system"))))

(defun zf-axiom-ok-p (ledger formula axiom-name)
  (check-k-proof (list (list 0 formula :axiom (list axiom-name))) ledger))

(defun test-zf-axioms (ledger)
  "Every ZF axiom accepts a textbook instance; instances violating a
distinct-variable or freshness side condition are rejected."
  (expect "(.in v0 v1) is a wff" (judgement? 'wff? '(.in v0 v1) ledger) t)
  (expect "(.in v0 (.iota v1 (.eq v1 v2))) is a wff (terms, not only variables)"
          (judgement? 'wff? '(.in v0 (.iota v1 (.eq v1 v2))) ledger) t)
  (expect "ZF-EXTENSIONALITY at x,y,z = v0,v1,v2"
          (zf-axiom-ok-p ledger (zf-extensionality 'v0 'v1 'v2) 'zf-extensionality) t)
  (expect "ZF-EXTENSIONALITY at other variable names x,y,z = v3,v5,v4"
          (zf-axiom-ok-p ledger (zf-extensionality 'v3 'v5 'v4) 'zf-extensionality) t)
  (expect "ZF-PAIRING" (zf-axiom-ok-p ledger (zf-pairing 'v0 'v1 'v2 'v3) 'zf-pairing) t)
  (expect "ZF-UNION" (zf-axiom-ok-p ledger (zf-union 'v0 'v1 'v2 'v3) 'zf-union) t)
  (expect "ZF-POWER-SET" (zf-axiom-ok-p ledger (zf-power-set 'v0 'v1 'v2 'v3) 'zf-power-set) t)
  (expect "ZF-INFINITY" (zf-axiom-ok-p ledger (zf-infinity 'v0 'v1 'v2 'v3) 'zf-infinity) t)
  (expect "ZF-FOUNDATION" (zf-axiom-ok-p ledger (zf-foundation 'v0 'v1 'v2) 'zf-foundation) t)
  (expect "ZF-SEPARATION with phi = not(z = z) (the empty-set instance)"
          (zf-axiom-ok-p ledger (zf-separation 'v0 'v1 'v2 '(.neg (.eq v2 v2))) 'zf-separation) t)
  (expect "ZF-SEPARATION with a parameter v3 free in phi"
          (zf-axiom-ok-p ledger (zf-separation 'v0 'v1 'v2 '(.in v2 v3)) 'zf-separation) t)
  (expect "ZF-REPLACEMENT with phi = (y = x)"
          (zf-axiom-ok-p ledger (zf-replacement 'v0 'v1 'v2 'v3 'v4 '(.eq v3 v2) '(.eq v4 v2))
                         'zf-replacement) t)
  ;; --- side conditions ------------------------------------------------
  (expect "Attack: ZF-EXTENSIONALITY with z := x (captures x) -- must reject"
          (zf-axiom-ok-p ledger (zf-extensionality 'v0 'v1 'v0) 'zf-extensionality) nil)
  (expect "Attack: ZF-EXTENSIONALITY with x := y -- must reject"
          (zf-axiom-ok-p ledger (zf-extensionality 'v0 'v0 'v2) 'zf-extensionality) nil)
  (expect "Attack: ZF-PAIRING with w := z -- must reject"
          (zf-axiom-ok-p ledger (zf-pairing 'v0 'v1 'v2 'v2) 'zf-pairing) nil)
  (expect "Attack: ZF-SEPARATION with y free in phi (Russell-style self-reference) -- must reject"
          (zf-axiom-ok-p ledger (zf-separation 'v0 'v1 'v2 '(.neg (.in v2 v1))) 'zf-separation) nil)
  (expect "Attack: ZF-SEPARATION with z := x -- must reject"
          (zf-axiom-ok-p ledger (zf-separation 'v0 'v1 'v0 '(.eq v0 v0)) 'zf-separation) nil)
  (expect "Attack: ZF-REPLACEMENT with b free in phi -- must reject"
          (zf-axiom-ok-p ledger (zf-replacement 'v0 'v1 'v2 'v3 'v4 '(.in v3 v1) '(.in v4 v1))
                         'zf-replacement) nil)
  (expect "Attack: ZF-REPLACEMENT with u free in phi -- must reject"
          (zf-axiom-ok-p ledger (zf-replacement 'v0 'v1 'v2 'v3 'v4 '(.eq v3 v4) '(.eq v4 v4))
                         'zf-replacement) nil)
  (expect "Attack: ZF-REPLACEMENT whose uniqueness clause is not phi[u/y] -- must reject"
          (zf-axiom-ok-p ledger (zf-replacement 'v0 'v1 'v2 'v3 'v4 '(.eq v3 v2) '(.eq v2 v2))
                         'zf-replacement) nil)
  (expect "Attack: 'there is an empty set' is not itself an axiom -- must reject"
          (zf-axiom-ok-p ledger (zf-ex 'v0 (zf-all 'v1 (zf-not (zf-in 'v1 'v0)))) 'zf-infinity) nil)
  ledger)

(defun test-zf-derivation (ledger)
  "A small derivation using a ZF axiom together with the base logic:
strip both outer quantifiers from Extensionality with III.1 and MP."
  (let* ((ext (zf-extensionality 'v0 'v1 'v2))
         (inner (third ext))                                ; forall v1 (...)
         (open-form (third inner))                          ; (forall v2 ...) -> v0 = v1
         (ledger (check-and-extend
                  ledger 'th 'th-zf-ext-open
                  `((0 ,ext :axiom (zf-extensionality))
                    (1 (.to ,ext ,inner) :axiom (III.1 v0))
                    (2 ,inner :ir (MP 1 0))
                    (3 (.to ,inner ,open-form) :axiom (III.1 v1))
                    (4 ,open-form :ir (MP 3 2))))))
    (expect "Extensionality without its outer quantifiers is a ZF theorem"
            (check-k-proof `((0 ,open-form :th (th-zf-ext-open))) ledger) t)
    (expect "the propositional core library still loads on top of ZF"
            (let ((l (read-ledger-from-file (library-path "01-propositional-core.ledger")
                                            :ledger ledger)))
              (check-k-proof `((0 (.to (.in v0 v1) (.in v0 v1)) :th (th-identity))) l))
            t)
    ledger))

(defun run-zf-self-tests ()
  "zf-library/00-zf.system: formation of .IN, one positive instance per
axiom, side-condition attacks, and a small derivation."
  (let* ((ledger (zf-ledger))
         (ledger (test-zf-axioms ledger))
         (ledger (test-zf-derivation ledger)))
    (declare (ignorable ledger))
    (format t "~%ZF self-tests complete.~%")))
