;;Uses hash on labels to allow node lookup via label;;

(defrecord Red-Black-Tree-Map [root])
(defrecord Red-Black-Map-Node [hashl vertex color left right parent child])
(def ^:const Black 0)
(def ^:const Red 1)
(def ^:const Left 2)
(def ^:const Right 3)
(def ^:const nil-leaf (Red-Black-Node. nil nil Black nil nil 0 nil))

(defrecord Graph [vertices edges])
(defrecord Edge [from to weight label])
(defrecord Vertex [label neighbors latitude longitude status distance component])
(def ^:const unseen 4)
(def ^:const in-queue 5)
(def ^:const current 6)
(def ^:const visited 7)

(defn hash-label [label] (.hashCode label))
(defn make-red-black-tree-map! [] (Red-Black-Tree-Map. (ref nil-leaf)))

(defn make-graph [] (Graph. (def v-tree (make-red-black-tree-map!))
                            (def e-tree (make-red-black-tree-map!))))

(defn red-black-tree-map-empty? [tree] (= @(:root tree) nil-leaf))

(defn red-black-tree-map? [tree] (= (class tree) Red-Black-Tree))

(defn node-empty? [node]
  (= @node nil-leaf))

(defn node-root? [node]
  (nil? @(:parent @node)))

(defn make-map-node! [hashed-label vertex color parent child]
  (Red-Black-Map-Node. hashed-label (ref vertex) (ref color) (ref nil-leaf) (ref nil-leaf) (ref parent) (ref child)))

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

(defn map-node-insert-helper! [node parent hashed-label vertex child]
  (if (node-empty? node)
    (do
      (dosync
        (ref-set node
          (make-node! hashed-label vertex Red parent child)))
      (red-black-rules-checker! node))
    (cond
      (< hashed-label @(:hashl @node))
        (node-insert-helper! (:left @node) node hashed-label vertex Left)
      (> hashed-label @(:hashl @node))
        (node-insert-helper! (:right @node) node hashed-label vertex Right)
      (= hashed-label @(:hashl @node))
        (node-insert-helper! (:right @node) node hashed-label vertex Right))))

(defn red-black-hashmap-contains? [hashed-label node]
  (if (node-empty? node)
    false
    (if (= hashed-label (:hashl @node))
      true
      (if (< hashed-label (:hashl @node))
        (red-black-hashmap-contains? hashed-label (:left @node))
        (red-black-hashmap-contains? hashed-label (:right @node))))))

(defn graph-add-vertex! [graph label latitude longitude]
  (let [hashed-label (hash-label label)]
    (when (not (red-black-hashmap-contains? hashed-label (:root @(:vertices graph))))
      (map-node-insert-helper!
        (:root @(:vertices graph))
        nil
        hashed-label
        (Vertex. label (ref nil) latitude longitude (ref unseen) (ref ##Inf) (ref nil))
        child))))

;;start with root node of tree;;

(defn print-hash-tree [node]
  (when (not (node-empty? node))
    (println "Hash Value: " (:hashl @node))
    (println "Label: " (:label @(:vertex @node)))
    (println "Latitude: " (:latitude @(:vertex @node)))
    (println "Longitude: " (:longitude @(:vertex @node)))
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
