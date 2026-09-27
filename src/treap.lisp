;;;; treap.lisp -- persistent treap used to index the ledger

(in-package :ledger-kernel)

;;; A treap is a BST on KEY that is also a heap on a random PRIORITY,
;;; which keeps it balanced in expectation, giving O(log n) insert and
;;; bounded lookup instead of the O(n) scan a plain list forces on every
;;; ledger read. Rebalancing is just "rotate if the new child outranks
;;; me", so a purely functional version stays short. No operation mutates
;;; a node: old ledger values remain valid and share structure.

(defstruct (treap-node (:constructor %make-treap-node (key value priority left right)))
  key value priority left right)

(defun treap-rotate-right (node)
  "Rotate NODE's left child up to the root (it outranks NODE)."
  (let ((l (treap-node-left node)))
    (%make-treap-node (treap-node-key l) (treap-node-value l) (treap-node-priority l)
                       (treap-node-left l)
                       (%make-treap-node (treap-node-key node) (treap-node-value node) (treap-node-priority node)
                                         (treap-node-right l) (treap-node-right node)))))

(defun treap-rotate-left (node)
  "Rotate NODE's right child up to the root (it outranks NODE)."
  (let ((r (treap-node-right node)))
    (%make-treap-node (treap-node-key r) (treap-node-value r) (treap-node-priority r)
                       (%make-treap-node (treap-node-key node) (treap-node-value node) (treap-node-priority node)
                                         (treap-node-left node) (treap-node-left r))
                       (treap-node-right r))))

(defun treap-insert (node key value)
  "Return a new treap with KEY -> VALUE added to NODE (NIL = empty),
replacing any existing value for KEY. Expected O(log n)."
  (cond
    ((null node) (%make-treap-node key value (random most-positive-fixnum) nil nil))
    ((< key (treap-node-key node))
     (let* ((new-left (treap-insert (treap-node-left node) key value))
            (grown (%make-treap-node (treap-node-key node) (treap-node-value node) (treap-node-priority node)
                                      new-left (treap-node-right node))))
       (if (> (treap-node-priority new-left) (treap-node-priority grown))
           (treap-rotate-right grown)
           grown)))
    ((> key (treap-node-key node))
     (let* ((new-right (treap-insert (treap-node-right node) key value))
            (grown (%make-treap-node (treap-node-key node) (treap-node-value node) (treap-node-priority node)
                                      (treap-node-left node) new-right)))
       (if (> (treap-node-priority new-right) (treap-node-priority grown))
           (treap-rotate-left grown)
           grown)))
    (t
     ;; KEY already present: replace the value, keep the priority.
     (%make-treap-node key value (treap-node-priority node) (treap-node-left node) (treap-node-right node)))))

(defun treap-values-below (node bound)
  "Values of the treap at NODE with key < BOUND (all if BOUND is NIL), in
ascending key order. Subtrees entirely >= BOUND are never visited, so the
cost is O(log n + result size); this is what makes ENTRIES-UPTO cheap."
  (labels ((walk (n tail)
             (cond
               ((null n) tail)
               ((and bound (>= (treap-node-key n) bound))
                (walk (treap-node-left n) tail))
               (t (walk (treap-node-left n) (cons (treap-node-value n) (walk (treap-node-right n) tail)))))))
    (walk node nil)))

;;; Persistent alist-as-map for the ledger's BY-KIND and BY-DERIVED-NAME
;;; indexes. Their keys (entry kinds, theorem names) are few relative to
;;; the ledger, so a linear alist at this outer level is fine; each lookup
;;; then narrows to a single bucket's treap.

(defun alist-put (alist key value)
  "New alist with KEY (compared with EQ) mapped to VALUE."
  (acons key value (remove key alist :key #'car :test #'eq)))

(defun alist-get (alist key)
  "Value of KEY (compared with EQ) in ALIST, or NIL."
  (cdr (assoc key alist :test #'eq)))
