;;;; safe-read.lisp -- reading untrusted proof text without the Lisp reader
;;;;
;;;; The editor's text comes from anyone who can reach the server. CL:READ
;;;; would intern every unknown symbol it meets (a request full of made-up
;;;; names grows the package forever) and can recurse as deep as the input
;;;; nests. This reader accepts only the S-expressions a proof consists of:
;;;;   ( )            lists, nested at most *SAFE-READ-MAX-DEPTH* deep
;;;;   123            non-negative integers (line numbers)
;;;;   :hyp           keywords that already exist
;;;;   .to v0 th-foo  symbols that already exist in LEDGER-KERNEL
;;;;   ; ...          comments to the end of the line
;;;; Symbols are looked up with FIND-SYMBOL and never created: an unknown
;;;; name is an error. Every symbol a correct proof can use (connectives,
;;;; variables, rule and theorem names) already exists once the worlds are
;;;; loaded, so nothing a proof needs is lost. Strings, quote, backquote,
;;;; #-syntax, |...| and backslash escapes are refused.

(in-package :ledger-kernel)

(defparameter *safe-read-max-depth* 200
  "Deepest list nesting accepted by SAFE-READ-FORMS.")

(define-condition safe-read-error (error)
  ((message :initarg :message :reader safe-read-error-message))
  (:report (lambda (c s) (write-string (safe-read-error-message c) s))))

(defun safe-read-fail (fmt &rest args)
  (error 'safe-read-error :message (apply #'format nil fmt args)))

(defun safe-read-delimiter-p (ch)
  (or (member ch '(#\( #\) #\;)) (member ch '(#\Space #\Tab #\Newline #\Return #\Page))))

(defun safe-read-token-value (token)
  "The integer, keyword or existing symbol TOKEN names."
  (cond
    ((every #'digit-char-p token) (parse-integer token))
    ((string= token ".") (safe-read-fail "A lone \".\" (dotted pair) is not allowed."))
    ((char= (char token 0) #\:)
     (multiple-value-bind (sym status) (find-symbol (string-upcase (subseq token 1)) :keyword)
       (if status sym (safe-read-fail "Unknown keyword ~A." token))))
    (t
     (multiple-value-bind (sym status) (find-symbol (string-upcase token) :ledger-kernel)
       (if status sym (safe-read-fail "Unknown symbol ~A (not declared in any loaded system)." token))))))

(defun safe-read-forms (text)
  "The forms in TEXT, read as described above. Signals SAFE-READ-ERROR."
  (let ((pos 0) (len (length text)))
    (labels ((peek () (and (< pos len) (char text pos)))
             (skip-space ()
               (loop
                 (let ((ch (peek)))
                   (cond ((null ch) (return))
                         ((char= ch #\;) (loop until (or (null (peek)) (char= (peek) #\Newline))
                                               do (incf pos)))
                         ((member ch '(#\Space #\Tab #\Newline #\Return #\Page)) (incf pos))
                         (t (return))))))
             (read-form (depth)
               (skip-space)
               (let ((ch (peek)))
                 (cond
                   ((null ch) (safe-read-fail "Unexpected end of text: a list is not closed."))
                   ((char= ch #\))
                    (safe-read-fail "Unexpected \")\" at position ~D." pos))
                   ((char= ch #\()
                    (when (>= depth *safe-read-max-depth*)
                      (safe-read-fail "Lists are nested more than ~D deep." *safe-read-max-depth*))
                    (incf pos)
                    (loop with items = nil
                          do (skip-space)
                             (cond ((null (peek))
                                    (safe-read-fail "Unexpected end of text: a list is not closed."))
                                   ((char= (peek) #\))
                                    (incf pos)
                                    (return (nreverse items)))
                                   (t (push (read-form (1+ depth)) items)))))
                   ((find ch "\"'`,#|\\")
                    (safe-read-fail "The character ~S is not allowed in a proof." ch))
                   (t
                    (let ((start pos))
                      (loop while (and (peek) (not (safe-read-delimiter-p (peek))))
                            do (when (find (peek) "\"'`,#|\\")
                                 (safe-read-fail "The character ~S is not allowed in a proof." (peek)))
                               (incf pos))
                      (safe-read-token-value (subseq text start pos))))))))
      (loop with forms = nil
            do (skip-space)
               (if (peek)
                   (push (read-form 0) forms)
                   (return (nreverse forms)))))))
