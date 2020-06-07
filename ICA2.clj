;;;;;;;;;;;;;;;;;;;;;;;;;; Basics for Red Black Queue ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord Red-Black-Tree [root])
(defrecord Red-Black-Node [label value value2 color left right parent child])

(def ^:const Black 4)
(def ^:const Red 5)
(def ^:const Left 6)
(def ^:const Right 7)
(def ^:const Root 8)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Helper Functions;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defn make-nil-node [child] (Red-Black-Node. nil (ref nil) (ref nil) (ref Black)
                                            (ref nil) (ref nil) (ref nil)
                                            (ref child)))

(defn make-red-black-tree! [] (Red-Black-Tree. (ref (make-nil-node Root))))
(def rb-queue (make-red-black-tree!))

(defn node-root? [node] (= @(:child node) Root))
(defn tree-node-empty? [node] (nil? (:label @node)))
(defn red-black-tree-empty? [tree] (tree-node-empty? (:root tree)))

(defn make-node! [label value value2 color parent child]
  (Red-Black-Node. label (ref value) (ref value2) (ref color)
                  (ref (make-nil-node Left)) (ref (make-nil-node Right))
                  (ref parent) (ref child)))

(defn get-sibling [node]
  (if (= @(:child @node) Left)
    (:right @(:parent @node))
    (:left @(:parent @node))))

(defn get-uncle [node]
  (let [parent (:parent @node)]
    (get-sibling parent)))

(defn color-of-uncle [node]
  @(:color @(get-uncle node)))

(defn get-parent [node]
  @(:parent node))

(defn color-of-parent [node]
  @(:color @(:parent @node)))
;;;;;;;;;;;;;;;;;;;;;;;;;; Basics for Graph ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord Graph [vertices edges])
(defrecord Edge [from to weight label])
(defrecord Vertex [label neighbors latitude longitude status distance component])

(def ^:const unseen 0)
(def ^:const in-queue 1)
(def ^:const current 2)
(def ^:const visited 3)

(defn make-graph [] (Graph. (ref {}) (ref {})))

(def g (make-graph))

(defn has-vertex? [label graph]
  (contains? @(:vertices graph) label))

(defn graph-add-vertex! [graph label latitude longitude]
  (when (not (has-vertex? label graph))
    (let [vertices @(:vertices graph)]
      (dosync
        (ref-set
          (:vertices graph)
          (assoc vertices
            label
            (Vertex. label (ref nil) latitude longitude (ref unseen) (ref ##Inf) (ref nil)))))))
  nil)

(defn edge-key [to from] (sort (list to from)))

(defn has-edge? [graph to from] (contains? @(:edges graph) (edge-key to from)))

(defn graph-add-edge! [graph from to label weight]
  (when (not (has-edge? graph to from))
    (dosync
      (ref-set
        (:edges graph)
        (assoc @(:edges graph)
          (edge-key to from)
          (Edge. from to weight label)))
      (ref-set (:neighbors (get @(:vertices graph) from))
        (conj @(:neighbors (get @(:vertices graph) from)) to))
      (ref-set (:neighbors (get @(:vertices graph) to))
        (conj @(:neighbors (get @(:vertices graph) from)) from))))
  nil)

(defn get-edge [g t f]
  (get @(:edges g) (edge-key t f)))

(defn get-vertex [g l]
  (get @(:vertices g) l))

;;;;;;;;;Functions For Checking and Fixing Color Rules of Queue;;;;;;;;;;;;;;;;;

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
;;;;;;;;;;;;;;;;;;;;;;; Queue Related Insertion ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn node-insert-helper! [node parent label value value2 child]
  (if (tree-node-empty? node)
    (do
      (dosync
        (ref-set node
          (make-node! label value value2 Red @parent child)))
      (red-black-rules-checker! node))
    (cond
      (< value @(:value @node))
        (node-insert-helper! (:left @node) node label value value2 Left)
      (> value @(:value @node))
        (node-insert-helper! (:right @node) node label value value2 Right)
      (= value @(:value @node))
        (node-insert-helper! (:right @node) node label value value2 Right))))

(defn node-insert! [tree label value value2]
  (if (red-black-tree-empty? tree)
    (dosync
      (ref-set (:root tree)
        (make-node! label value value2 Black nil Root)))
    (cond
      (< value @(:value @(:root tree)))
        (node-insert-helper! (:left @(:root tree)) (:root tree) label value value2 Left)
      (> value @(:value @(:root tree)))
        (node-insert-helper! (:right @(:root tree)) (:root tree) label value value2 Right)
      (= value @(:value @(:root tree)))
        (node-insert-helper! (:right @(:root tree)) (:root tree) label value value2 Right))))

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
              Root)
            (ref-set
              (:parent @(:root rb-queue))
              nil)))
          (ref-set
            (:left @(:parent @node))
            (make-nil-node Left))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;Dijkstra Breadth First Search ;;;;;;;;;;;;;;;;;;;;;;;

;;;;Reseting the distance and status of every vertex;;;

(defn graph-reset! [graph]
  (doseq [v (vals @(:vertices graph))]
    (dosync
      (ref-set (:status v) unseen)
      (ref-set (:distance v) ##Inf))))
;;;;Reseting the distance and status of every vertex;;;

;;;;Status of vertex;;;;
(defn vertex-unseen? [graph label]
  (= @(:status (get @(:vertices graph) label)) unseen))

(defn vertex-current? [graph label]
  (= @(:status (get @(:vertices graph) label)) current))

(defn vertex-in-queue? [graph label]
  (= @(:status (get @(:vertices graph) label)) in-queue))

(defn vertex-visited? [graph label]
  (= @(:status (get @(:vertices graph) label)) visited))
;;;;Status of vertex;;;;

;;;;BFS Dijkstra;;;;
(defn breadth-first-search-dijkstra! [graph start finish]
  (node-insert! rb-queue finish 0 nil)
  (loop []
    (when (not (red-black-tree-empty? rb-queue))
    (let [current (pick-least-node (:root rb-queue))]
      (remove-least-node! (:root rb-queue))
      (dosync
        (ref-set (:distance (get-vertex graph (:label current)))
                  @(:value current)))
      (when (not (= (:label current) start))
        (loop [neighbors
              @(:neighbors (get-vertex graph (:label current)))]
          (let [current-neighbor (first neighbors)]
            (when (vertex-unseen? graph current-neighbor)
              (node-insert! rb-queue current-neighbor (inc @(:value current)) nil)))
          (recur (rest neighbors)))))
      (dosync
        (ref-set (:status (get-vertex graph (:label current))) visited))
    (recur))))
;;;;BFS Dijkstra;;;;

;;;;Dijksta Without Edge Weights;;;;
(defn dijkstra-trace-back-pick-best [graph vertex]
  (loop [neighbors @(:neighbors @(get-vertex graph vertex))
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
  (def rb-queue (make-red-black-tree!))
  (if (= @(:component @(get-vertex graph start))
         @(:component @(get-vertex graph finish)))
    (do
      (breadth-first-search-dijkstra! graph start finish)
      (dijkstra-trace-back graph start finish))
    (println "No path exists!")))
;;;;Dijksta Without Edge Weights;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;Dijkstra Breadth First Search ;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;A* Algorithm ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defn great-circle-distance [graph label1 label2]
  (let [vertex1 (get-vertex graph label1)
        vertex2 (get-vertex graph label2)
        lat1 (:latitude vertex1)
        lon1 (:longitude vertex1)
        lat2 (:latitude vertex2)
        lon2 (:longitude vertex2)
        dl (Math/abs (- lon2 lon1)) ; lambda - longitude
        dp (Math/abs (- lat2 lat1)) ; phi - latitude
        dlr (/ (* Math/PI dl) 180)
        dpr (/ (* Math/PI dp) 180)
        l1 (/ (* Math/PI lon1) 180)
        p1 (/ (* Math/PI lat1) 180)
        l2 (/ (* Math/PI lon2) 180)
        p2 (/ (* Math/PI lat2) 180)
        ds (Math/acos (+ (* (Math/sin p1) (Math/sin p2))
                         (* (Math/cos p1) (Math/cos p2) (Math/cos dlr))))]
    (* 6378 ds)))

;;;;;;;;;;;;;;;;;;;Weights Pick Best Neigbor::::::::::::::::::::::::::::::::::::
(defn weighted-trace-back-pick-best [graph vertex]
  (loop [neighbors @(:neighbors @(get-vertex graph vertex))
         best-distance ##Inf
         best-label nil]
    (if (= (count neighbors) 1)
      (if (and
            (< @(:distance @(get-vertex graph (first neighbors))) best-distance)
            (= (- @(:distance @(get-vertex graph vertex))
                  @(:distance @(get-vertex graph (first neighbors))))
              (:weight @(get-edge graph (first neighbors) vertex))))
        (first neighbors)
        best-label)
      (if (and
            (< @(:distance @(get-vertex graph (first neighbors))) best-distance)
            (= (- @(:distance @(get-vertex graph vertex))
                  @(:distance @(get-vertex graph (first neighbors))))
              (:weight @(get-edge graph (first neighbors) vertex))))
        (recur (rest neighbors)
               @(:distance @(get-vertex graph (first neighbors)))
               (first neighbors))
        (recur (rest neighbors)
                best-distance
                best-label)))))

(defn weighted-trace-back [graph start finish]
  (loop [current start]
    (println current)
    (when (not (= current finish))
      (recur (weighted-trace-back-pick-best current)))))
;;;;;;;;;;;;;;;;;;;Weights Pick Best Neigbor::::::::::::::::::::::::::::::::::::

;;;;;;;BFS A*;;;;;;;
(defn breadth-first-search-a*! [graph start finish]
  (node-insert! rb-queue finish (great-circle-distance graph finish start) 0)
  (loop []
    (when (not (red-black-tree-empty? rb-queue))
    (let [current (pick-least-node (:root rb-queue) start)]
      (remove-least-node! (:root rb-queue))
      (dosync
        (ref-set (:distance (get-vertex graph (:label current)))
                 @(:value2 current)))
      (when (not (= (:label current) start))
        (loop [neighbors
              @(:neighbors (get-vertex graph (:label current)))]
          (let [current-neighbor (first neighbors)
                edge-distance (:distance (get-edge graph
                                                   current-neighbor
                                                   (:label current)))
                great-circle (great-circle-distance graph
                                                    current-neighbor
                                                    start)]
            (when (vertex-unseen? graph current-neighbor)
              (node-insert! rb-queue current-neighbor
                            great-circle
                            (+ @(:value current) edge-distance))))
          (recur (rest neighbors)))))
    (recur))))
;;;;;;;BFS A*;;;;;;;

;;;;;;;;A*;;;;;;;;;;;
(defn a*! [graph start finish]
  (graph-reset! graph)
  (def rb-queue (make-red-black-tree!))
  (if (= @(:component @(get-vertex graph start))
         @(:component @(get-vertex graph finish)))
    (do
      (breadth-first-search-a*! graph start finish)
      (weighted-trace-back graph start finish))
    (println "No path exists!")))
;;;;;;;;A*;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;A* Algorithm ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Count Components;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defn breadth-first-search-connected-components! [graph start index]
  (node-insert! rb-queue start index nil)
  (loop []
    (when (not (red-black-tree-empty? rb-queue))
    (let [current (pick-least-node (:root rb-queue))]
      (remove-least-node! (:root rb-queue))
      (dosync
        (ref-set (:component (get-vertex graph (:label current)))
                  @(:value current)))
      (loop [neighbors
            @(:neighbors (get-vertex graph (:label current)))]
        (let [current-neighbor (first neighbors)]
          (when (vertex-unseen? graph current-neighbor)
            (node-insert! rb-queue current-neighbor index nil)))
        (recur (rest neighbors))))
      (dosync
        (ref-set (:status (get-vertex graph (:label current))) visited))
    (recur))))

(defn remaining-unseen [graph]
  (loop [v (vals @(:vertices graph))]
    (let [current (first v)]
      (if (= @(:status current) unseen)
        (:label current)
        (recur (rest v))))))

(defn index-components! [graph]
  (graph-reset! graph)
  (loop [index 0]
    (breadth-first-search-connected-components! graph
                                                (remaining-unseen graph)
                                                index)
    (recur (inc index))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Count Components;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Debugigng;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defn print-tree [node]
  (when (not (tree-node-empty? node))
    (println "Label: " (:label @node))
    (println "Value: " @(:value @node))
    (if (= @(:color @node) Black)
      (println "Color: Black")
      (println "Color: Red"))
    (if (= @(:child @node) Left)
      (println "Child: Left")
      (if (= @(:child @node) Root)
        (println "Child: Root")
        (println "Child: Right")))
    (println "=======================")
    (print-tree (:left @node))
    (print-tree (:right @node))))

(defn print-queue [] (print-tree (:root rb-queue)))

(defn rb-node->str-single [l n]
  (if (nil? n)
    (str l ":-")
    (str
     "\u001b["
     (if (= @(:color n) Black)
       "0;100"
       "0;41")
     "m" l ":"
     (:label n)
     "\u001b[0m")))

(defn rb-node->str [n]
  (str "["
       (rb-node->str-single "k" n)
       "|"
       (rb-node->str-single "p" @(:parent n))
       ","
       (rb-node->str-single "l" @(:left n))
       ","
       (rb-node->str-single "r" @(:right n))
       "]"))


(defn rb-node-print-tree [node prefix firstprefix]
  (when (not (nil? @node))
    ;;(println (str firstprefix @(:key @node) " => " ))
    (println (str firstprefix (rb-node->str @node)))
    (rb-node-print-tree (:left @node)
                          (if (not (nil? @(:right @node)))
                            (str prefix "│   ")
                            (str prefix "    "))
                          (str prefix
                               (if (not (nil? @(:right @node)))
                                 "├"
                                 "└")
                               "─ [L] "))
    (rb-node-print-tree (:right @node)
                          (str prefix "    ")
                          (str prefix "└─ [R] "))))


(defn rb-print-tree [tree]
  (if (nil? @(:root tree))
    (println "Empty tree!")
    (rb-node-print-tree (:root tree) " " "[/] ")))
