;;;; canonical-tests.lisp -- the canonical form of entries (canonical.lisp)
;;;; Part of the ledger-kernel/tests system (see ledger-kernel.asd).

(in-package :ledger-kernel)

(defun test-canonical-names (ledger)
  "The families FVk, BVk, LFk, PSk/n and how the ledger sees them."
  (expect "FV3 is a free-variable name, BV2 a bound one, LF1 an atom, PS2/3 a schema of arity 3"
          (equal (list (canonical-name-parts 'fv3) (canonical-name-parts 'bv2)
                       (canonical-name-parts 'lf1) (canonical-schema-arity '|PS2/3|))
                 '(:fv :bv :lf 3))
          t)
  (expect "FV0, FV01, FVX, PS1 are not canonical names"
          (some #'canonical-name-p '(fv0 fv01 fvx ps1))
          nil)
  (expect "FV3 is a variable, LF1 an atomic wff, PS2/1 a predicate schema, in every ledger"
          (and (variable-p 'fv3 ledger) (atomic-wff-symbol-p 'lf1 ledger)
               (eql (predicate-schema-arity '|PS2/1| ledger) 1))
          t)
  (expect "(ps1/2 fv1 fv2) is a wff; (ps1/2 fv1) is not"
          (and (judgement? 'wff? '(|PS1/2| fv1 fv2) ledger)
               (not (judgement? 'wff? '(|PS1/2| fv1) ledger)))
          t)
  (expect "Attack: declaring FV1 as a variable -- must error (reserved)"
          (handler-case (progn (declare-variable-symbol ledger 'fv1) :declared)
            (error () :refused))
          :refused)
  (expect "Attack: declaring LF1 as an atomic symbol -- must error (reserved)"
          (handler-case (progn (declare-atomic-wff-symbol ledger 'lf1) :declared)
            (error () :refused))
          :refused)
  ledger)

(defun test-canonical-form (ledger)
  "CANONICALIZE-PROOF on small proofs."
  (let ((ledger (declare-predicate-schema-symbol ledger 'p 1)))
    (expect "bound variables per formula, free ones per entry, in order of appearance"
            (equal (canonicalize-proof '((0 (.forall v3 (.eq v3 v1)) :hyp nil)
                                         (1 (.exists v2 (.eq v0 v2)) :hyp nil))
                                       ledger)
                   '((0 (.forall bv1 (.eq bv1 fv1)) :hyp nil)
                     (1 (.exists bv1 (.eq fv2 bv1)) :hyp nil)))
            t)
    (expect "binders are numbered in order of appearance within a formula"
            (equal (canonicalize-proof '((0 (.to (.forall v0 (.exists v1 (.eq v0 v1)))
                                                 (.forall v2 (.eq v2 v2)))
                                            :hyp nil))
                                       ledger)
                   '((0 (.to (.forall bv1 (.exists bv2 (.eq bv1 bv2))) (.forall bv3 (.eq bv3 bv3)))
                      :hyp nil)))
            t)
    (expect "atoms and predicate schemas get LFk and PSk/n"
            (equal (canonicalize-proof '((0 (.to b (p v4)) :hyp nil) (1 (.to a b) :hyp nil)) ledger)
                   '((0 (.to lf1 (|PS1/1| fv1)) :hyp nil) (1 (.to lf2 lf1) :hyp nil)))
            t)
    (expect "names in justifications are renamed with the same map: (gen 0 v1), (iii.1 v1)"
            (equal (canonicalize-proof '((0 (.eq v2 v2) :axiom (iv.1))
                                         (1 (.forall v1 (.eq v1 v1)) :ir (gen 0 v2)))
                                       ledger)
                   '((0 (.eq fv1 fv1) :axiom (iv.1)) (1 (.forall bv1 (.eq bv1 bv1)) :ir (gen 0 fv1))))
            t)
    (expect "line numbers that look like atoms (A) are not renamed"
            (equal (canonicalize-proof '((a b :hyp nil) (x b :ir (mp a a))) ledger)
                   '((a lf1 :hyp nil) (x lf1 :ir (mp a a))))
            t)
    (let ((c (canonicalize-proof '((0 (.forall v3 (.eq v3 v1)) :hyp nil) (1 (.to a (p v1)) :hyp nil))
                                 ledger)))
      (expect "canonicalizing a canonical proof changes nothing"
              (equal (canonicalize-proof c ledger) c) t))
    (expect "a free BV1 written in the input is a free variable, renamed to FV1, never captured"
            (equal (canonicalize-proof '((0 (.forall v0 (.eq v0 bv1)) :hyp nil)) ledger)
                   '((0 (.forall bv1 (.eq bv1 fv1)) :hyp nil)))
            t)
    (let* ((l1 (check-and-extend ledger 'th 'th-canon-a '((0 (.to a (.forall v0 (.eq v0 v1))) :hyp nil))))
           (l2 (check-and-extend l1 'th 'th-canon-b '((0 (.to c (.forall v5 (.eq v5 v3))) :hyp nil)))))
      (expect "two theorems that differ only in naming have the same canonical payload"
              (equal (second (entry-payload (find-derived-entry 'th-canon-a l2)))
                     (second (entry-payload (find-derived-entry 'th-canon-b l2))))
              t)
      (expect "... and each keeps its text as written and its renaming map"
              (and (equal (second (entry-source-payload (find-derived-entry 'th-canon-b l2)))
                          '((0 (.to c (.forall v5 (.eq v5 v3))) :hyp nil)))
                   (equal (entry-canonical-map (find-derived-entry 'th-canon-b l2))
                          '((c . lf1) (v3 . fv1))))
              t)
      (expect "the theorem is cited with the citing proof's own names"
              (check-k-proof '((0 (.to d (.forall v2 (.eq v2 v4))) :hyp nil)
                               (1 (.to d (.forall v2 (.eq v2 v4))) :th (th-canon-b 0)))
                             l2)
              t)))
  ledger)

(defun test-canonical-citation (ledger)
  "Standardizing apart, and :INST keys written with the cited entry's names."
  (let* ((ledger (check-and-extend ledger 'th 'th-canon-refl
                                   '((0 (.eq v1 v1) :axiom (iv.1))
                                     (1 (.forall v0 (.eq v0 v0)) :ir (gen 0 v1))
                                     (2 (.to (.forall v0 (.eq v0 v0)) (.eq v2 v2)) :axiom (iii.1 v2))
                                     (3 (.eq v2 v2) :ir (mp 2 1))))))
    (expect "the lemma's internal variable v1 does not clash with the citer's v1"
            (check-k-proof '((0 (.eq v1 v1) :th (th-canon-refl))) ledger) t)
    (expect "its free variable v2 is found by matching"
            (check-k-proof '((0 (.eq v3 v3) :th (th-canon-refl))) ledger) t)
    (expect ":inst with the lemma's own name v2 still works"
            (check-k-proof '((0 (.eq v4 v4) :th (th-canon-refl :inst ((v2 v4))))) ledger) t)
    (expect ":inst with the lemma's canonical name works too"
            (check-k-proof '((0 (.eq v4 v4) :th (th-canon-refl :inst ((fv2 v4))))) ledger) t)
    (expect "Attack: an instance that is not one -- must reject"
            (check-k-proof '((0 (.eq v4 v3) :th (th-canon-refl))) ledger) nil))
  ledger)

(defun test-canonical-round-trip (ledger)
  "A ledger saved in canonical form reloads, re-verifies, and saves the
same canonical form again."
  (let* ((base ledger)
         (l1 (reduce (lambda (l f) (read-ledger-from-file (library-path f) :ledger l))
                     '("01-propositional-core.ledger" "02-predicate-core.ledger" "03-equality-core.ledger"
                       "05-classical-logic.ledger" "06-connectives.ledger" "07-quantifier-schemas.ledger")
                     :initial-value base))
         (path (merge-pathnames "canonical-round-trip.ledger" (uiop:temporary-directory))))
    (write-ledger-to-file l1 path :canonical t)
    (let ((l2 (handler-case (read-ledger-from-file path :ledger base)
                (error () nil))))
      (expect "the canonical file of the logic library reloads (every proof re-verified)"
              (and l2 (= (ledger-count l1) (ledger-count l2))) t)
      (expect "... and saves to the same canonical form"
              (and l2 (equal (ledger-commands l1 :canonical t) (ledger-commands l2 :canonical t)))
              t))
    (ignore-errors (delete-file path)))
  ledger)

(defun run-canonical-self-tests ()
  (format t "~&--- canonical form ---~%")
  (let ((ledger (fol-kernel)))
    (test-canonical-names ledger)
    (test-canonical-form ledger)
    (test-canonical-citation ledger))
  (test-canonical-round-trip
   (bootstrap-kernel-from-spec-file (library-path "00-connectives.system") :ledger (fol-kernel)))
  t)
