;;Uses hash on labels to allow node lookup via label;;

(defrecord Red-Black-Tree-Map [root])
(defrecord Red-Black-Map-Node [hashl grecord color left right parent child])
(def ^:const Black 0)
(def ^:const Red 1)
(def ^:const Left 2)
(def ^:const Right 3)
(def ^:const Root 8)
(defn make-nil-node [child] (Red-Black-Map-Node. (ref nil) (ref nil) (ref Black) (ref nil) (ref nil) (ref nil) (ref child)))

(defrecord Graph [vertices edges])
(defrecord Edge [from to weight label])
(defrecord Vertex [label neighbors latitude longitude status distance component])
(def ^:const unseen 4)
(def ^:const in-queue 5)
(def ^:const current 6)
(def ^:const visited 7)

(defn hash-label [label] (.hashCode label))
(defn make-red-black-tree-map! [] (Red-Black-Tree-Map. (ref (make-nil-node Root))))
(def v-tree (ref (make-red-black-tree-map!)))
(def e-tree (ref (make-red-black-tree-map!)))

(defn make-graph [] (Graph. v-tree e-tree))
(def g (make-graph))

(defn node-root? [node] (= @(:child node) Root))

(defn red-black-tree-map? [tree] (= (class tree) Red-Black-Tree))

(defn node-empty? [node] (nil? @(:hashl @node)))

(defn make-map-node! [hashed-label grecord color parent child]
  (Red-Black-Map-Node. (ref hashed-label) (ref grecord) (ref color) (ref (make-nil-node Left)) (ref (make-nil-node Right)) (ref parent) (ref child)))

(defn get-sibling [node]
  (if (= @(:child @node) Left)
    (:right @(:parent @node))
    (:left @(:parent @node))))

(defn get-uncle [node]
  (let [parent (:parent @node)]
    (get-sibling parent)))

(defn color-of-uncle [node]
  @(:color (get-uncle node)))

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
  (when (not (= @(:child @node) Root))
    (when (= @(:color @(:parent @node)) Red)
      (if (= (color-of-uncle node) Red)
        (red-parent-red-uncle-fix! node)
        (red-parent-black-uncle-checker! node)))))

(defn get-node [hashed-label node]
  (cond
    (< hashed-label @(:hashl @node))
      (get-node hashed-label (:left @node))
    (> hashed-label @(:hashl @node))
      (get-node hashed-label (:right @node))
    (= hashed-label @(:hashl @node))
      node
    (node-empty? node)
      false))

(defn neighbor-set! [to from]
  (let [to-neighbors @(:neighbors @(get-node (hash-label to (:root @(:vertices g)))))
        from-neighbors @(:neighbors @(get-node (hash-label from (:root @(:vertices g)))))]
    (dosync
      (ref-set (get-node (hash-label to (:root @(:vertices g))))
        (conj to-neighbors from))
      (ref-set (get-node (hash-label from (:root @(:vertices g))))
        (conj from-neighbors to)))))

(defn map-node-insert-helper! [node parent hashed-label grecord child is-edge?]
  (if (node-empty? node)
    (do
      (dosync
        (if (= child Root)
          (ref-set node
            (make-map-node! hashed-label grecord Black parent child))
          (ref-set node
            (make-map-node! hashed-label grecord Red parent child))))
      (red-black-rules-checker! node)
      (when is-edge?
        (neighbor-set! @(:to @(:grecord @node)) @(:from @(:grecord @node)))))
    (cond
      (< hashed-label @(:hashl @node))
        (map-node-insert-helper! (:left @node) node hashed-label grecord Left is-edge?)
      (> hashed-label @(:hashl @node))
        (map-node-insert-helper! (:right @node) node hashed-label grecord Right is-edge?)
      (= hashed-label @(:hashl @node))
        (map-node-insert-helper! (:right @node) node hashed-label grecord Right is-edge?))))

(defn red-black-hashmap-contains? [hashed-label node]
  (cond
    (node-empty? node)
      false
    (= hashed-label @(:hashl @node))
        true
    (< hashed-label @(:hashl @node))
      (red-black-hashmap-contains? hashed-label (:left @node))
    (> hashed-label @(:hashl @node))
      (red-black-hashmap-contains? hashed-label (:right @node))))

(defn graph-add-vertex! [graph label latitude longitude]
  (let [hashed-label (hash-label label)]
    (when (not (red-black-hashmap-contains? hashed-label (:root @(:vertices graph))))
      (map-node-insert-helper!
        (:root @(:vertices graph))
        nil
        hashed-label
        (Vertex. label (ref '()) latitude longitude (ref unseen) (ref ##Inf) (ref nil))
        Root
        false))))

(defn edge-key [to from] (sort (list to from)))

(defn graph-add-edge! [graph from to label weight]
  (let [hashed-edge-key (hash-label (edge-key from to))]
    (when (not (red-black-hashmap-contains? hashed-edge-key (:root @(:edges graph)))))
      (map-node-insert-helper!
        (:root @(:edges graph))
        nil
        hashed-edge-key
        (Edge. from to weight label)
        Root
        true)))

(defn print-hash-tree-vertex [node]
  (println "Hash Value: " @(:hashl @node))
  (println "Label: " (:label @(:grecord @node)))
  (println "Latitude: " (:latitude @(:grecord @node)))
  (println "Longitude: " (:longitude @(:grecord @node)))
  (println "Neighbors: " (:neighbors @(:grecord @node)))
  (if (= @(:color @node) 0)
    (println "Color: Black")
    (println "Color: Red"))
  (if (= @(:child @node) 2)
    (println "Child: Left")
    (if (nil? @(:child @node))
      (println "Child: Root")
      (println "Child: Right")))
  (println "======================="))

(defn print-hash-tree-edge [node]
  (println "Hash Value: " @(:hashl @node))
  (println "Label: " (:label @(:grecord @node)))
  (println "From: " (:from @(:grecord @node)))
  (println "To: " (:to @(:grecord @node)))
  (println "Wight: " (:weight @(:grecord @node)))
  (if (= @(:color @node) 0)
    (println "Color: Black")
    (println "Color: Red"))
  (if (= @(:child @node) 2)
    (println "Child: Left")
    (if (nil? @(:child @node))
      (println "Child: Root")
      (println "Child: Right")))
  (println "======================="))
