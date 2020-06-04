;;Uses hash on labels to allow node lookup via label.

;;;;;;;;;;;;; Record Structures and Constants for Red Black Queue ;;;;;;;;;;;;;;

;;This is for the open queue in bfs.
(defrecord Red-Black-Tree [root])
(defrecord Red-Black-Node [label value color left right parent child])
(def ^:const Black 0)
(def ^:const Red 1)
(def ^:const Left 2)
(def ^:const Right 3)
(def ^:const Root 8)
(defn make-nil-node [child] (Red-Black-Node. nil (ref nil) (ref Black) (ref nil) (ref nil) (ref nil) (ref child)))

;;;;;;;;;;;;;;;; Record Structures for Vertices and Edges Tree's ;;;;;;;;;;;;;;;

;;Each node keeps track of its hash value, graph record structure, color, children, parent
;;and of which child it is to its parent.
(defrecord Red-Black-Tree-Map [root])
(defrecord Red-Black-Map-Node [hashl grecord color left right parent child])
(defn make-nil-map-node [child] (Red-Black-Map-Node. (ref nil) (ref nil) (ref Black) (ref nil) (ref nil) (ref nil) (ref child)))

;;;;;;;;;;;;;;;; Record Structures and Constants for Graph ;;;;;;;;;;;;;;;;;;;;;

(defrecord Graph [vertices edges])
(defrecord Edge [from to weight label])
(defrecord Vertex [label neighbors latitude longitude status distance component])
;;Edge or Vertex are stored in grecord of Red-Black-Map-Node.
(def ^:const unseen 4)
(def ^:const in-queue 5)
(def ^:const current 6)
(def ^:const visited 7)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Creation Functions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn hash-label [label] (.hashCode label))
(defn make-red-black-tree-map! [] (Red-Black-Tree-Map. (ref (make-nil-map-node Root))))
(defn make-red-black-tree! [] (Red-Black-Tree. (ref (make-nil-node Root))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Creating Graph ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Creating rb tree maps for the Graph.
(def v-tree (ref (make-red-black-tree-map!)))
(def e-tree (ref (make-red-black-tree-map!)))
(defn make-graph [] (Graph. v-tree e-tree))
(def g (make-graph))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Creating Queue ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def rb-queue (make-red-black-tree!))

;;;;;;;;;;;; Helper Functions For Insertions and Checking Rules ;;;;;;;;;;;;;;;;

(defn node-root? [node] (= @(:child node) Root))

(defn node-empty? [node] (nil? @(:hashl @node)))

(defn tree-node-empty? [node] (nil? (:label @node)))

(defn red-black-tree-empty? [tree] (tree-node-empty? (:root tree)))

(defn red-black-map-empty? [tree] (node-empty? (:root tree)))

(defn make-map-node! [hashed-label grecord color parent child]
  (Red-Black-Map-Node. (ref hashed-label) (ref grecord) (ref color) (ref (make-nil-map-node Left)) (ref (make-nil-map-node Right)) (ref parent) (ref child)))

(defn make-node! [label value color parent child]
  (Red-Black-Node. label (ref value) (ref color) (ref (make-nil-node Left)) (ref (make-nil-node Right)) (ref parent) (ref child)))

(defn get-sibling [node]
  (if (= @(:child @node) Left)
    (:right @(:parent @node))
    (:left @(:parent @node))))

(defn get-uncle [node]
  (let [parent (:parent @node)]
    (get-sibling parent)))

(defn color-of-uncle [node]
  @(:color @(get-uncle node)))

(defn color-of-parent [node]
  @(:color @(:parent @node)))

;;;;;;;;;;;;;;;;; Functions For Checking and Fixing Color Rules ;;;;;;;;;;;;;;;;

(declare red-black-rules-checker!)

(defn red-parent-red-uncle-fix! [node]
  (let [uncle (get-uncle node)
        parent  (:parent @node)
        grandparent (:parent @(:parent @node))]
    (dosync
      (ref-set (:color @parent) Black)
      (ref-set (:color @uncle) Black)
      (when (not (node-root? @grandparent))
        (ref-set (:color @grandparent) Red)))
      (red-black-rules-checker! grandparent)))

(defn rb-rotate-left [a LEFT RIGHT]
  (println "rb-rotate-left")
  (let [b @(RIGHT a)
        p @(:parent a)
        child @(:child a)]
    (dosync
      (ref-set (RIGHT a) @(LEFT b))
      (ref-set (LEFT b) a)
      (ref-set (:parent a) b)
      (ref-set (:child a) Left)
      (ref-set (:child b) child)
      (when (not (nil? @(RIGHT a)))
        (ref-set (:parent @(RIGHT a)) a)
        (ref-set (:child @(RIGHT a)) Right))
      (when (not (nil? p))
        (if (= a @(LEFT p))
          (ref-set (LEFT p) b)
          (if (= a @(RIGHT p))
            (ref-set (RIGHT p) b))))
      (ref-set (:parent b) p))))

(defn rb-rotate-right [a LEFT RIGHT]
  (println "rb-rotate-right")
  (let [b @(RIGHT a)
        p @(:parent a)
        child @(:child a)]
    (dosync
      (ref-set (RIGHT a) @(LEFT b))
      (ref-set (LEFT b) a)
      (ref-set (:parent a) b)
      (ref-set (:child a) Right)
      (ref-set (:child b) child)
      (when (not (nil? @(RIGHT a)))
        (ref-set (:parent @(RIGHT a)) a)
        (ref-set (:child @(RIGHT a)) Left))
      (when (not (nil? p))
        (if (= a @(LEFT p))
          (ref-set (LEFT p) b)
          (if (= a @(RIGHT p))
            (ref-set (RIGHT p) b))))
      (ref-set (:parent b) p))))

(defn left-rotate! [a]
  (println "left-rotate!")
  (rb-rotate-left @a :left :right))

(defn right-rotate! [a]
  (println "right-rotate")
  (rb-rotate-right @a :right :left))

(defn left-left-case! [grandparent]
  (right-rotate! grandparent)
  (dosync
    (ref-set (:color @grandparent) Red)
    (ref-set (:color @(:parent @grandparent)) Black)))

(defn left-right-case! [parent]
  (left-rotate! parent)
  (left-left-case! (:parent @(:parent parent))))

(defn right-right-case! [grandparent]
  (left-rotate! grandparent)
  (dosync
    (ref-set (:color @grandparent) Red)
    (ref-set (:color @(:parent @grandparent)) Black)))

(defn right-left-case! [parent]
  (right-rotate! parent)
  (right-right-case! (:parent @(:parent parent))))

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

(defn red-black-rules-checker! [node]
  (when (not (= @(:child @node) Root))
    (when (= (color-of-parent node) Red)
      (if (= (color-of-uncle node) Red)
        (red-parent-red-uncle-fix! node)
        (red-parent-black-uncle-checker! node)))))

;;;;;;;;;;;;;;;;;; Graph Related Node Insertion Helpers ;;;;;;;;;;;;;;;;;;;;;;;;

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
  (let [to-neighbors @(:neighbors @(:grecord @(get-node (hash-label to) (:root @(:vertices g)))))
        from-neighbors @(:neighbors @(:grecord @(get-node (hash-label from) (:root @(:vertices g)))))]
    (dosync
      (ref-set (:neighbors @(:grecord @(get-node (hash-label to) (:root @(:vertices g)))))
        (conj to-neighbors from))
      (ref-set (:neighbors @(:grecord @(get-node (hash-label from) (:root @(:vertices g)))))
        (conj from-neighbors to)))))

(defn map-node-insert-helper! [node parent hashed-label grecord child is-edge?]
  (if (node-empty? node)
    (do
      (dosync
        (ref-set node
          (make-map-node! hashed-label grecord Red @parent child)))
      (when is-edge?
        (neighbor-set! (:to @(:grecord @node)) (:from @(:grecord @node))))
      (red-black-rules-checker! node))
    (cond
      (< hashed-label @(:hashl @node))
        (map-node-insert-helper! (:left @node) node hashed-label grecord Left is-edge?)
      (> hashed-label @(:hashl @node))
        (map-node-insert-helper! (:right @node) node hashed-label grecord Right is-edge?))))

(defn map-node-insert-helper-2! [node parent hashed-label grecord is-edge?]
  (if (node-empty? node)
    (do
      (dosync
        (ref-set node
          (make-map-node! hashed-label grecord Black parent Root)))
      (when is-edge?
        (neighbor-set! (:to @(:grecord @node)) (:from @(:grecord @node)))))
    (cond
      (< hashed-label @(:hashl @node))
        (map-node-insert-helper! (:left @node) node hashed-label grecord Left is-edge?)
      (> hashed-label @(:hashl @node))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Graph Insertion ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn graph-add-vertex! [graph label latitude longitude]
  (let [hashed-label (hash-label label)]
    (when (not (red-black-hashmap-contains? hashed-label (:root @(:vertices graph))))
      (map-node-insert-helper-2!
        (:root @(:vertices graph))
        nil
        hashed-label
        (Vertex. label (ref '()) latitude longitude (ref unseen) (ref ##Inf) (ref nil))
        false))))

(defn edge-key [to from] (sort (list to from)))

(defn graph-add-edge! [graph from to label weight]
  (let [hashed-edge-key (hash-label (edge-key from to))]
    (when (not (red-black-hashmap-contains? hashed-edge-key (:root @(:edges graph)))))
      (map-node-insert-helper-2!
        (:root @(:edges graph))
        nil
        hashed-edge-key
        (Edge. from to weight label)
        true)))

;;;;;;;;;;;;;;;;;;;;;;;; Queue Related Insertion ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn node-insert-helper! [node parent label value child]
  (if (tree-node-empty? node)
    (do
      (dosync
        (ref-set node
          (make-node! label value Red @parent child)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Queue Operations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn pick-least-node [node]
  (if (not (tree-node-empty? (:left @node)))
    (pick-least-node (:left @node))
    @node))

(defn remove-least-node! [node]
  (if (not (tree-node-empty? (:left @node)))
    (remove-least-node! (:left @node))
    (dosync
      (if (node-root? @node)
        (if (tree-node-empty? (:right @node))
          (ref-set
            (:root rb-queue)
            (make-nil-node Root))
          (do
            (ref-set
              (:root rb-queue)
              @(:right @node))
            (ref-set
              (:child @(:root rb-queue))
              Right)
            (ref-set
              (:parent @(:root rb-queue))
              nil)))
          (ref-set
            (:left @(:parent @node))
            (make-nil-node Left))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;; Breadth First Search ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;Reseting the distance and status of every vertex;;;
(defn graph-reset-helper! [node]
  (when (not (node-empty? node))
  (println "Reset one node")
    (dosync
      (ref-set (:status @(:grecord @node)) unseen)
      (ref-set (:distance @(:grecord @node)) ##Inf))
  (graph-reset-helper! (:left @node))
  (graph-reset-helper! (:right @node))))

(defn graph-reset! [graph]
  (graph-reset-helper! (:root @(:vertices graph))))
;;;;Reseting the distance and status of every vertex;;;

;;;;Status of vertex;;;;
(defn vertex-unseen? [node]
  (= @(:status @(:grecord @node)) unseen))

(defn vertex-current? [node]
  (= @(:status @(:grecord @node)) current))

(defn vertex-in-queue? [node]
  (= @(:status @(:grecord @node)) in-queue))

(defn vertex-visited? [node]
  (= @(:status @(:grecord @node)) visited))
;;;;Status of vertex;;;;

;;;;Get;;;;
(defn get-vertex [graph label]
  (:grecord @(get-node (hash-label label) (:root @(:vertices graph)))))

(defn get-edge [graph from to]
  (:grecord @(get-node (hash-label (edge-key from to)) (:root @(:edges graph)))))

(defn get-vertex-unseen? [graph label]
  (= @(:status @(get-vertex graph label)) unseen))
;;;;Get;;;;

;;;;BFS D;;;;
(defn breadth-first-search-dijkstra [graph start finish]
  (node-insert! rb-queue finish 0)
  (loop []
    (when (not (red-black-tree-empty? rb-queue))
    (let [current (pick-least-node (:root rb-queue))]
      (remove-least-node! (:root rb-queue))
      (dosync
        (ref-set (:distance @(get-vertex graph (:label current)))
                  @(:value current)))
      (when (not (= (:label current) start))
        (loop [neighbors
              @(:neighbors @(get-vertex graph (:label current)))]
          (let [current-neighbor (first neighbors)]
            (when (get-vertex-unseen? graph current-neighbor)
              (node-insert! rb-queue current-neighbor (inc @(:value @current)))))
          (recur (rest neighbors)))))
    (recur))))
;;;;BFS D;;;;

;;;;Dijksta Without Edge Weights;;;;
(defn dijkstra-trace-back-pick-best [vertex]
  (loop [neighbors @(:neighbors @(get-vertex graph (:label current)))
         best-distance ##Inf
         best-label nil]
    (if (= (count neighbors) 1)
      (if (< @(:distance @(get-vertex graph (first neighbors))) best-distance)
        (first neighbors)
        best-label)
      (if (< @(:distance @(get-vertex graph (first neighbors))) best-distance)
        (recur (rest neighbors)
               @(:distance @(get-vertex graph (first neighbors)))
               (first neighbors))
        (recur (rest neighbors)
                best-distance
                best-label)))))


(defn dijkstra-trace-back [graph start finish]
  (loop [current start]
    (println current)
    (when (not (= current finish))
      (recur (dijkstra-trace-back-pick-best current)))))

(defn dijkstra! [graph start finish]
  (graph-reset! graph)
  (if (= @(:component @(get-vertex graph start))
         @(:component @(get-vertex graph finish)))
    (do
      (breadth-first-search-dijkstra graph start finish)
      (dijkstra-trace-back graph start finish))
    (println "No path exists!")))
;;;;Dijksta Without Edge Weights;;;;

;;;;;;;;;;;;;;;;;;;;;;; Debugging Queue and Graph ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn print-vertex [node]
  (println "Hash Value: " @(:hashl @node))
  (println "Label: " (:label @(:grecord @node)))
  (println "Latitude: " (:latitude @(:grecord @node)))
  (println "Longitude: " (:longitude @(:grecord @node)))
  (println "Neighbors: " @(:neighbors @(:grecord @node)))
  (if (= @(:color @node) 0)
    (println "Color: Black")
    (println "Color: Red"))
  (if (= @(:child @node) 2)
    (println "Child: Left")
    (if (= @(:child @node) 8)
      (println "Child: Root")
      (println "Child: Right")))
  (println "======================="))

(defn print-edge [node]
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
    (if (= @(:child @node) 8)
      (println "Child: Root")
      (println "Child: Right")))
  (println "======================="))

(defn print-vertex-tree [node]
  (when (not (node-empty? node))
    (println "Hash Value: " @(:hashl @node))
    (println "Label: " (:label @(:grecord @node)))
    (println "Latitude: " (:latitude @(:grecord @node)))
    (println "Longitude: " (:longitude @(:grecord @node)))
    (println "Neighbors: " @(:neighbors @(:grecord @node)))
    (if (= @(:color @node) 0)
      (println "Color: Black")
      (println "Color: Red"))
    (if (= @(:child @node) 2)
      (println "Child: Left")
      (if (= @(:child @node) 8)
        (println "Child: Root")
        (println "Child: Right")))
    (println "=======================")
    (print-vertex-tree (:left @node))
    (print-vertex-tree (:right @node))))

(defn print-edge-tree [node]
  (when (not (node-empty? node))
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
      (if (= @(:child @node) 8)
        (println "Child: Root")
        (println "Child: Right")))
    (println "=======================")
    (print-edge-tree (:left @node))
    (print-edge-tree (:right @node))))

(defn print-tree [node]
  (when (not (tree-node-empty? node))
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

(defn print-vertices [] (print-vertex-tree (:root @(:vertices g))))
(defn print-edges [] (print-edge-tree (:root @(:edges g))))
(defn print-queue [] (print-tree (:root rb-queue)))
