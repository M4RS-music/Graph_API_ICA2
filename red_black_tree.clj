(defrecord Red-Black-Tree [root])
(defrecord Red-Black-Node [label value color left right parent child])

(def ^:const Black 0)
(def ^:const Red 1)
(def ^:const Left 2)
(def ^:const Right 3)
(def ^:const nil-leaf (Red-Black-Node. nil nil Black nil nil 0 nil))

(defn make-red-black-tree! [] (Red-Black-Tree. (ref nil-leaf)))

(def Tree (make-red-black-tree!))

(defn red-black-tree-empty? [tree] (= @(:root tree) nil-leaf))

(defn red-black-tree? [tree] (= (class tree) Red-Black-Tree))

(defn node-empty? [node]
  (= @node nil-leaf))

(defn node-root? [node]
  (nil? @(:parent @node)))

(defn make-node! [label value color parent child]
  (Red-Black-Node. label (ref value) (ref color) (ref nil-leaf) (ref nil-leaf) (ref parent) (ref child)))

(defn get-sibling [node]
  (if (= @(:child @node) Left)
    (:right @(:parent @node))
    (:left @(:parent @node))))

(defn get-uncle [node]
  (let [parent (:parent @node)]
    (get-sibling parent)

(defn color-of-uncle [node]
  @(:color (get-uncle node))

(defn color-of-parent [node]
  @(:color @(:parent @node)))

(defn red-parent-red-uncle-fix! [node]
  (let [uncle (get-uncle node)
        parent  (:parent @node)
        grandparent (:parent @(:parent @node))]
    (dosync
      (ref-set (:color parent) Black)
      (ref-set (:color uncle) Black)
      (when (not (node-root? grandparent))
        (ref-set (:color grandparent) Red)))
    (when (not (node-root? grandparent))
      (red-black-rules-checker! grandparent))))

(defn left-rotate! [node] nil)

(defn right-rotate! [node] nil)

(defn left-left-case! [grandparent]
  (right-rotate! grandparent)
  (dosync
    (ref-set (:color @grandparent) Red)
    (ref-set (:color @(:parent @grandparent)) Black)))

(defn left-right-case! [parent]
  (left-rotate! parent)
  (left-left-case! (:parent @(:parent @parent))))

(defn right-right-case! [grandparent]
  (left-rotate! grandparent)
  (dosync
    (ref-set (:color @grandparent) Red)
    (ref-set (:color @(:parent @grandparent)) Black)))

(defn right-left-case! [parent]
  (right-rotate! parent)
  (right-right-case! (:parent @(:parent @parent))))

(defn red-parent-black-uncle-checker! [node]
  (let [parent  @(:parent @node)
        node-child @(:child @node)
        parent-child @(:child parent)
        grandparent (:parent @(:parent @node))]
  (cond
    (and (= parent-child Left) (= node-child Left)) (left-left-case! grandparent)
    (and (= parent-child Left) (= node-child Right)) (left-right-case! parent)
    (and (= parent-child Right) (= node-child Left)) (right-left-case! parent)
    (and (= parent-child Right) (= node-child Right)) (right-right-case! grandparent))))

;;The color of parent does not work. parent reference is broken **...

(defn red-black-rules-checker! [node]
  (when (= @(:color @(:parent @node)) Red)
    (if (= (color-of-uncle node) Red)
      (red-parent-red-uncle-fix! node)
      (red-parent-black-uncle-checker! node))))

(defn node-insert-helper! [node parent label value child]
  (if (node-empty? node)
    (do
      (dosync
        (ref-set node
          (make-node! label value Red parent child)))
      (red-black-rules-checker! node))
    (cond
      (< value @(:value @node))
        (node-insert-helper! (:left @node) node label value Left)
      (> value @(:value @node))
        (node-insert-helper! (:right @node) node label value Right)
      (= value @(:value @node))
        (node-insert-helper! (:right @node) node label value Right))))

(defn node-insert! [tree label value]
  (if (red-black-tree-empty? tree)
    (dosync
      (ref-set (:root tree)
        (make-node! label value Black nil nil)))
    (cond
      (< value @(:value @(:root tree)))
        (node-insert-helper! (:left @(:root tree)) (:root tree) label value Left)
      (> value @(:value @(:root tree)))
        (node-insert-helper! (:right @(:root tree)) (:root tree) label value Right)
      (= value @(:value @(:root tree)))
        (node-insert-helper! (:right @(:root tree)) (:root tree) label value Right))))

(defn print-tree [node]
  (when (not (node-empty? node))
    (println "Label: " (:label @node))
    (println "Value: " @(:value @node))
    (if (= @(:color @node) 0)
      (println "Color: Black")
      (println "Color: Red"))
    (if (= @(:child @node) 2)
      (println "Child: Left")
      (if (nil? @(:child @node))
        (println "Child: Root")
        (println "Child: Right")))
    (println "=======================")
    (print-tree (:left @node))
    (print-tree (:right @node))))

;;start with root node of tree

(defn pick-least-node [node]
  (if (not (node-empty? (:left @node)))
    (pick-least-node (:left @node))
    (:label @node)))

;;** This proves parent reference does not work.

(defn pop-least-node! [node]
  (if (not (node-empty? (:left @node)))
    (pick-least-node (:left @node))
    (dosync
      (:label @node)
      (ref-set
        (:left @(:parent @node))
        nil-leaf))))
