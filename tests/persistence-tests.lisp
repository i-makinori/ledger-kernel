;;;; persistence-tests.lisp -- Section 12: persistence regression tests
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 12. Regression tests for Section 10 (file I/O / persistence)
;;; ---------------------------------------------------------------------
;;;
;;; LEDGER-COMMANDS/LEDGER-FROM-COMMANDS/WRITE-LEDGER-TO-FILE/READ-LEDGER-
;;; FROM-FILE (Section 10) were exercised only by hand, in scratch scripts,
;;; when they were first written -- never wired into RUN-SELF-TESTS
;;; itself, so nothing would have caught a later regression there. This
;;; section closes that gap: a genuine round trip through the filesystem
;;; (not just in-memory COMMANDS/FROM-COMMANDS), checked three ways --
;;; byte-for-byte command-stream fidelity, a real re-citation of a THEOREM
;;; that itself came from @DEDUCTION, and a tamper-resistance check
;;; showing a corrupted file can only ever fail to load, never smuggle in
;;; an unsound entry.

(defun tree-subst (old new tree)
  "Blind structural substitution (no notion of binders/capture, unlike
SUBSTITUTE-WFF in Section 4) -- used here only to build a deliberately
corrupted test fixture, never inside the kernel's own trusted logic."
  (cond
    ((eq tree old) new)
    ((consp tree) (cons (tree-subst old new (car tree)) (tree-subst old new (cdr tree))))
    (t tree)))

(defun tree-contains-p (x tree)
  (or (eq x tree) (and (consp tree) (or (tree-contains-p x (car tree)) (tree-contains-p x (cdr tree))))))

(defun test-persistence-round-trip (ledger)
  "WRITE-LEDGER-TO-FILE / READ-LEDGER-FROM-FILE, genuinely through the
filesystem (not just LEDGER-COMMANDS/LEDGER-FROM-COMMANDS in memory).
Does not grow the ledger (writes/reads a temp file as a side effect, then
removes it)."
  (let ((path "/tmp/ledger-kernel-self-test-persistence.tmp")
        (bad-path "/tmp/ledger-kernel-self-test-persistence-tampered.tmp"))
    (unwind-protect
         (progn
           (write-ledger-to-file ledger path)
           (let ((reloaded (read-ledger-from-file path :ledger (fol-kernel))))
             (expect "Reload preserves the entry count exactly"
                     (= (ledger-count reloaded) (ledger-count ledger)) t)
             (expect "Reload's own command stream is identical to the original's"
                     (equal (ledger-commands reloaded) (ledger-commands ledger)) t)
             (expect "A plain axiom-instance judgement still holds after reload"
                     (judgement? 'wff? '(.to A B) reloaded) t)
             (expect "TH-GEN-VACUOUS (a TH entry) is still citable after reload"
                     (check-k-proof '((X C :hyp nil)
                                      (Y (.forall v0 C) :th (th-gen-vacuous X)))
                                    reloaded)
                     t)
             (expect "TH-DIRECT-MP-DEMO (a TH-DED entry, built via CHECK-AND-EXTEND-BY-DEDUCTION-DIRECT) is still citable after reload"
                     (check-k-proof '((0 F :hyp nil)
                                       (1 (.to (.to F G) G) :th-ded (th-direct-mp-demo 0)))
                                     reloaded)
                     t))
           ;; Tamper-resistance: corrupt one grown entry's proof (blindly
           ;; swap A for the undeclared Z inside the last :TH command
           ;; that mentions A) and confirm loading it can only fail,
           ;; never quietly succeed.
           (let* ((commands (ledger-commands ledger))
                  (victim (find-if (lambda (c) (and (eq (car c) :th) (tree-contains-p 'A c)))
                                   commands :from-end t)))
             (expect "Sanity: the ledger has a :TH command to tamper with" victim t)
             (when victim
               (let* ((tampered (tree-subst victim (tree-subst 'A 'Z victim) commands)))
                 (write-commands-to-file tampered bad-path)
                 (expect "A tampered command stream is refused outright, not silently accepted"
                         (handler-case (progn (read-ledger-from-file bad-path :ledger (fol-kernel)) nil)
                           (error () t))
                         t))))
           ledger)
      (ignore-errors (delete-file path))
      (ignore-errors (delete-file bad-path)))))

(defun test-chained-module-loading (ledger)
  "READ-LEDGER-FROM-FILE's :LEDGER argument: splitting one ledger's own
command stream into two files and loading them back CHAINED (the second
file's commands replayed onto the first file's already-reloaded result,
rather than each starting over from a fresh BOOTSTRAP-KERNEL) reconstructs
the SAME ledger a single-file reload would -- confirming several \"module\"
files can stand in for one, exactly as the next step (an actual
multi-file Hilbert-system source library) needs. Does not grow the
ledger (writes/reads two temp files as a side effect, then removes them)."
  (let ((path-a "/tmp/ledger-kernel-self-test-module-a.tmp")
        (path-b "/tmp/ledger-kernel-self-test-module-b.tmp"))
    (unwind-protect
         (let* ((commands (ledger-commands ledger))
                (half (floor (length commands) 2))
                (commands-a (subseq commands 0 half))
                (commands-b (subseq commands half)))
           (write-commands-to-file commands-a path-a)
           (write-commands-to-file commands-b path-b)
           (let* ((ledger-a (read-ledger-from-file path-a :ledger (fol-kernel)))
                  (chained (read-ledger-from-file path-b :ledger ledger-a)))
             (expect "Chained two-file load reaches the same entry count as the original"
                     (= (ledger-count chained) (ledger-count ledger)) t)
             (expect "...and the identical command stream"
                     (equal (ledger-commands chained) commands) t)
             (expect "TH-GEN-VACUOUS is still citable in the two-file chained result"
                     (check-k-proof '((X C :hyp nil) (Y (.forall v0 C) :th (th-gen-vacuous X))) chained)
                     t)))
      (ignore-errors (delete-file path-a))
      (ignore-errors (delete-file path-b)))
    ledger))

(defvar *reader-attack-ran* nil
  "Set by the #.(...) payload in TEST-FILE-READER-SAFETY if it ever runs.")

(defun test-hostile-file-shapes (ledger)
  "A file whose data is circular, shared or absurdly deep must fail to
load with an ordinary error, never exhaust the stack or hang."
  (let ((path "/tmp/ledger-kernel-self-test-hostile-shape.ledger"))
    (flet ((load-text (text)
             (with-open-file (out path :direction :output :if-exists :supersede)
               (write-string text out))
             (handler-case (progn (read-ledger-from-file path :ledger ledger) :loaded)
               (error () :refused))))
      (unwind-protect
           (progn
             (expect "Attack: a circular proof (#1=(... . #1#)) in a .ledger file -- must be refused"
                     (load-text "(:th th-loop #1=((0 (.to A (.to B A)) :axiom (II.1)) . #1#))")
                     :refused)
             (expect "Attack: shared structure (#1= / #1#) in a .ledger file -- must be refused"
                     (load-text "(:th th-shared ((0 #1=(.to A (.to B A)) :axiom (II.1)) (1 #1# :axiom (II.1))))")
                     :refused)
             (expect "Attack: nesting 100000 deep in a .ledger file -- must be refused, not crash"
                     (load-text (concatenate 'string
                                             (make-string 100000 :initial-element #\()
                                             (make-string 100000 :initial-element #\))))
                     :refused)
             (expect "an ordinary .ledger file still loads"
                     (load-text "(:th th-shape-ok ((0 (.to A (.to B A)) :axiom (II.1))))")
                     :loaded))
        (ignore-errors (delete-file path))))
    ledger))

(defun test-review-regressions (ledger)
  "Raw indices in written input, reserved symbols, and payloads that are
not re-converted when cited."
  (expect "Attack: a raw (:bv 0) captured by a written binder -- CHECK-K-PROOF must reject"
          (check-k-proof '((0 (.eq v0 v0) :axiom (IV.1))
                           (1 (.forall v0 (.eq v0 (:bv 0))) :ir (Gen 0 v0)))
                         ledger)
          nil)
  (expect "... and CHECK-AND-EXTEND must refuse to admit it"
          (handler-case (progn (check-and-extend ledger 'th 'th-raw-bv
                                                 '((0 (.eq v0 v0) :axiom (IV.1))
                                                   (1 (.forall v0 (.eq v0 (:bv 0))) :ir (Gen 0 v0))))
                               :admitted)
            (error () :refused))
          :refused)
  (expect "... and JUDGEMENT? says it is not a wff"
          (judgement? 'wff? '(.forall v0 (.eq v0 (:bv 0))) ledger) nil)
  (expect "the same proof with the bound variable named is accepted"
          (check-k-proof '((0 (.eq v0 v0) :axiom (IV.1))
                           (1 (.forall v0 (.eq v0 v0)) :ir (Gen 0 v0)))
                         ledger)
          t)
  (expect "Attack: declaring T as a variable -- must error"
          (handler-case (progn (declare-variable-symbol ledger t) :declared)
            (error () :refused))
          :refused)
  (expect "Attack: declaring the matcher's +FAIL+ as an atomic wff -- must error"
          (handler-case (progn (declare-atomic-wff-symbol ledger '+fail+) :declared)
            (error () :refused))
          :refused)
  ;; A hand-built TH entry (never through the gates) whose binder is over
  ;; KK, not a variable when it was appended, so the binder stays
  ;; unconverted. Declaring KK later must not change what the stored
  ;; proof says when it is cited: it is not converted again.
  (let* ((l (ledger-append ledger 'th
                           (list 'th-kk-later
                                 '((0 (.to (.forall kk A) (.to B (.forall kk A))) :axiom (II.1))))
                           (list :primitive)))
         (l (declare-variable-symbol l 'kk)))
    (expect "a stored payload is not re-converted against later vocabulary when cited"
            (check-k-proof '((0 (.to (.forall kk A) (.to B (.forall kk A))) :th (th-kk-later))) l)
            nil))
  ledger)

(defun test-file-reader-safety (ledger)
  "A .ledger or .system file is read as data only: #.(...) in it must not
run code while loading (it is a reader error instead), and the load must
fail rather than admit anything."
  (let ((ledger-path "/tmp/ledger-kernel-self-test-read-eval.ledger")
        (system-path "/tmp/ledger-kernel-self-test-read-eval.system")
        (payload "#.(progn (setf ledger-kernel::*reader-attack-ran* t) nil)"))
    (unwind-protect
         (progn
           (with-open-file (out ledger-path :direction :output :if-exists :supersede)
             (format out "(:th th-read-eval-probe ((0 (.to A (.to B A)) :axiom (II.1))))~%~A~%" payload))
           (with-open-file (out system-path :direction :output :if-exists :supersede)
             (format out "(:atomic-wff-symbols Z9)~%~A~%" payload))
           (setf *reader-attack-ran* nil)
           (expect "Attack: #.(...) in a .ledger file -- loading must fail"
                   (handler-case (progn (read-ledger-from-file ledger-path :ledger ledger) :loaded)
                     (error () :refused))
                   :refused)
           (expect "... and the #.(...) code must never have run"
                   *reader-attack-ran* nil)
           (expect "Attack: #.(...) in a .system file -- loading must fail"
                   (handler-case (progn (bootstrap-kernel-from-spec-file system-path :ledger ledger) :loaded)
                     (error () :refused))
                   :refused)
           (expect "... and the #.(...) code must never have run"
                   *reader-attack-ran* nil)
           (expect "a reader macro installed in the image does not change how files are read"
                   (let ((*readtable* (copy-readtable nil)))
                     ;; make ( read as the symbol HIJACKED; files must ignore this
                     (set-macro-character #\( (lambda (s c) (declare (ignore s c)) 'hijacked))
                     (with-open-file (out ledger-path :direction :output :if-exists :supersede)
                       (format out "(:th th-readtable-probe ((0 (.to A (.to B A)) :axiom (II.1))))~%"))
                     (handler-case
                         (check-k-proof '((0 (.to A (.to B A)) :th (th-readtable-probe)))
                                        (read-ledger-from-file ledger-path :ledger ledger))
                       (error () nil)))
                   t))
      (ignore-errors (delete-file ledger-path))
      (ignore-errors (delete-file system-path)))
    ledger))
