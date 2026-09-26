;;;; treap.lisp -- Section 1.5: persistent treap used to index the ledger
;;;; Part of the ledger-kernel system (see ledger-kernel.asd).

(in-package :ledger-kernel)

;;; ---------------------------------------------------------------------
;;; 1.5. A persistent ordered map (treap), used to index the ledger
;;; ---------------------------------------------------------------------
;;;
;;; A plain list, scanned linearly, makes every ledger lookup (every
;;; entry of a given kind, every entry sharing a citation name) O(n) in
;;; the TOTAL number of entries the ledger has ever accumulated, however
;;; few of them are actually relevant. A TREAP is a binary search tree
;;; whose shape is kept balanced (in expectation) by tagging every node
;;; with a random priority and maintaining heap order on priority as well
;;; as BST order on key; unlike AVL/red-black trees it needs no rotation
;;; bookkeeping beyond "does my new child now outrank me", which keeps a
;;; purely functional (structure-sharing, non-mutating) implementation
;;; short. Every operation below returns a NEW treap and never mutates an
;;; existing node, so old ledger values, however deeply nested in a
;;; caller's LET*, remain exactly as they were.

(defstruct (treap-node (:constructor %make-treap-node (key value priority left right)))
  key value priority left right)

(defun treap-rotate-right (node)
  "NODE's left child outranks NODE: bring it up, giving it NODE (holding
the left child's old right subtree) as its new right child."
  (let ((l (treap-node-left node)))
    (%make-treap-node (treap-node-key l) (treap-node-value l) (treap-node-priority l)
                       (treap-node-left l)
                       (%make-treap-node (treap-node-key node) (treap-node-value node) (treap-node-priority node)
                                         (treap-node-right l) (treap-node-right node)))))

(defun treap-rotate-left (node)
  "Mirror image of TREAP-ROTATE-RIGHT, for when NODE's right child outranks it."
  (let ((r (treap-node-right node)))
    (%make-treap-node (treap-node-key r) (treap-node-value r) (treap-node-priority r)
                       (%make-treap-node (treap-node-key node) (treap-node-value node) (treap-node-priority node)
                                         (treap-node-left node) (treap-node-left r))
                       (treap-node-right r))))

(defun treap-insert (node key value)
  "Functional insert of KEY -> VALUE into the treap rooted at NODE (NIL
for an empty treap), giving KEY a fresh random priority. Every ledger
key used in this file (an ENTRY-K) is in fact always strictly greater
than every key already present -- entries are only ever appended -- but
this function makes no such assumption; it is an ordinary persistent
treap insert, expected O(log n) for a treap of N nodes regardless of
insertion order. Returns a NEW treap; NODE itself is untouched."
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
     ;; KEY already present (never happens for ENTRY-K, which is always
     ;; fresh, but this keeps TREAP-INSERT correct as a general map).
     (%make-treap-node key value (treap-node-priority node) (treap-node-left node) (treap-node-right node)))))

(defun treap-values-below (node bound)
  "Ascending-by-key list of the values stored in the treap rooted at
NODE, restricted to keys strictly less than BOUND (or every value, in
ascending key order, if BOUND is NIL). Because NODE's key order is a
genuine BST order, a node whose OWN key is already >= BOUND guarantees
its entire right subtree (all keys strictly greater still) is excluded
too, so that subtree is never even visited -- only the left spine down
to the boundary is walked eagerly; everything actually returned is
visited exactly once. This is what makes ENTRIES-UPTO's restriction
cheap: it costs nothing until something is actually read out of the
restricted view, and even then only in proportion to what is read,
O(log n + result size) rather than O(n)."
  (labels ((walk (n tail)
             (cond
               ((null n) tail)
               ((and bound (>= (treap-node-key n) bound))
                (walk (treap-node-left n) tail))
               (t (walk (treap-node-left n) (cons (treap-node-value n) (walk (treap-node-right n) tail)))))))
    (walk node nil)))

;;; A small persistent alist-as-map, used for LEDGER's BY-KIND and
;;; BY-DERIVED-NAME indices below. The number of distinct KEYs here (rule
;;; kinds, or distinct ITH/TH/DEF-ABBREV citation names) is what is
;;; small, not the ledger itself, so a linear ALIST lookup/update at this
;;; outer level is not the O(ledger-size) cost this section exists to
;;; eliminate -- the real saving is that each lookup narrows down to one
;;; single bucket's treap before doing any per-entry work.

(defun alist-put (alist key value)
  "Functional update: a NEW alist with KEY mapped to VALUE, replacing any
existing entry for KEY (compared with EQ -- kinds and names are always
symbols here)."
  (acons key value (remove key alist :key #'car :test #'eq)))

(defun alist-get (alist key)
  (cdr (assoc key alist :test #'eq)))
