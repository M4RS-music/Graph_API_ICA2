(defrecord Graph [vertices edges])
(defrecord Edge [from to weight label spanning])
(defrecord Vertex [label neighbors latitude longitude status distance])

(def ^:const vertex-status-unseen 0)
(def ^:const vertex-status-in-queue 1)
(def ^:const vertex-status-current 2)
(def ^:const vertex-status-visited 3)

(defn make-graph [] (Graph. (ref {}) (ref {})))

(defn graph-has-vertex? [graph label]
  (contains? @(:vertices graph) label))

(defn graph-add-vertex! [graph label lat lon]
  (when (not (graph-has-vertex? graph label))
    (dosync
     (ref-set (:vertices graph)
              (assoc @(:vertices graph)
                     label
                     (Vertex. label (ref '()) lat lon
                              (ref vertex-status-unseen)
                              (ref ##Inf))))))
  nil)

(defn graph-edge-key [from to] (sort (list from to)))

(defn graph-has-edge? [graph from to]
  (contains? @(:edges graph) (graph-edge-key from to)))

(defn graph-add-edge! [graph from to label weight]
  (when (not (graph-has-edge? graph from to))
    (dosync
     (ref-set (:edges graph)
              (assoc @(:edges graph)
                     (graph-edge-key from to)
                     (Edge. from to weight label (ref false))))
     (let [neighbors (:neighbors (get @(:vertices graph) from))]
       (ref-set neighbors (cons to @neighbors)))
     (let [neighbors (:neighbors (get @(:vertices graph) to))]
       (ref-set neighbors (cons from @neighbors)))))
  nil)

(defn vertex-reset-status! [vertex]
  (dosync
   (ref-set (:status vertex) vertex-status-unseen)))

(defn graph-reset!
  ([graph]
   (graph-reset! graph vertex-reset-status!))
  ([graph reset-function]
   (doseq [vertex (vals @(:vertices graph))]
     (reset-function vertex))))

(defn vertex-reset-dijkstra! [vertex]
  (dosync
   (ref-set (:status vertex) vertex-status-unseen)
   (ref-set (:distance vertex) ##Inf)))

(defn graph-reset-dijkstra! [graph]
  (graph-reset! graph vertex-reset-dijkstra!))

(defn graph-vertex-status? [graph label status]
  (= @(:status (get @(:vertices graph) label))
     status))

(defn graph-vertex-visited? [graph label]
  (graph-vertex-status? graph label vertex-status-visited))

(defn graph-vertex-unseen? [graph label]
  (graph-vertex-status? graph label vertex-status-unseen))

(defn graph-vertex-unseen-or-in-queue? [graph label]
  (or (graph-vertex-status? graph label vertex-status-unseen)
      (graph-vertex-status? graph label vertex-status-in-queue)))

(defn graph-get-vertex [graph label]
  (get @(:vertices graph) label))

(defn graph-get-edge [graph from to]
  (get @(:edges graph) (graph-edge-key from to)))

(defn graph-get-edge-weight
  ([e]
   (:weight e))
  ([graph from to]
   (graph-get-edge-weight (graph-get-edge graph from to))))

(defn graph-dijkstra-weights-pick-best [graph queue]
  (with-local-vars [best-distance ##Inf
                    best-label "unknown"]
    (doseq [label queue]
      (let [vertex (graph-get-vertex graph label)]
        (if (< @(:distance vertex) @best-distance)
          (do
            (var-set best-distance @(:distance vertex))
            (var-set best-label (:label vertex))))))
    @best-label))

(defn graph-bfs-remove-from-queue [queue label]
  (filter (fn [x]
            (not (= x label)))
          queue))

(defn graph-bfs!
  ([graph]
   (graph-bfs! graph (first (keys @(:vertices graph)))))
  ([graph start]
   (graph-bfs! graph start (fn [x] true)))
  ([graph start func]
   (graph-bfs! graph start func (fn [graph queue] (first queue))))
  ([graph start func pick-best]
   (loop [queue (list start)]
     (when (not (empty? queue))
       (let [current-label (pick-best graph queue)
             current-vertex (get @(:vertices graph) current-label)
             current-neighbors @(:neighbors current-vertex)
             unseen-neighbors (filter (fn [label]
                                        (graph-vertex-unseen? graph label))
                                      current-neighbors)]
         (dosync (ref-set (:status current-vertex) vertex-status-current))
         (let [continue? (func current-vertex)]
           (dosync (ref-set (:status current-vertex) vertex-status-visited))
           (dosync
            (doseq [neighbor unseen-neighbors]
              (ref-set (:status (get @(:vertices graph) neighbor))
                       vertex-status-in-queue)))
           (if continue?
             (recur (concat (graph-bfs-remove-from-queue queue current-label)
                            unseen-neighbors)))))))))

(defn vertex-get-best-neighbor [graph vertex]
  (with-local-vars [best-distance ##Inf
                    best-label "unknown"]
    (doseq [neighbor-label @(:neighbors vertex)]
      (let [neighbor (graph-get-vertex graph neighbor-label)]
        (if (and (= @(:status neighbor) vertex-status-visited)
                 (< @(:distance neighbor) @best-distance))
          (do
            (var-set best-distance @(:distance neighbor))
            (var-set best-label (:label neighbor))))))
    @best-label))

(defn vertex-get-best-neighbor-with-weights [graph vertex]
  (with-local-vars [best-distance ##Inf
                    best-label "unknown"]
    (doseq [neighbor-label @(:neighbors vertex)]
      (let [neighbor (graph-get-vertex graph neighbor-label)]
        (when (and (= @(:status neighbor) vertex-status-visited)
                   (< @(:distance neighbor) @best-distance)
                   (= (- @(:distance vertex) @(:distance neighbor))
                      (graph-get-edge-weight graph
                                             (:label vertex)
                                             (:label neighbor))))
            (var-set best-distance @(:distance neighbor))
            (var-set best-label (:label neighbor)))))
    @best-label))

(defn graph-dijkstra-trace-back [graph start finish best-neighbor-func]
  (let [start-vertex (graph-get-vertex graph start)]
    (if (= @(:status start-vertex) vertex-status-visited)
      (loop [current-label start
             path '()]
        (let [path+current (conj path current-label)]
          (if (not (= current-label finish))
            (let [current-vertex (graph-get-vertex graph current-label)]
              (println ">>" current-label "::" @(:distance current-vertex))
              ;;(vertex-print current-vertex)
              (recur (best-neighbor-func graph current-vertex)
                     path+current))
            (let [current-vertex (graph-get-vertex graph current-label)]
              (println "**" current-label)
              ;;(vertex-print current-vertex)
              (println "Arrived at finish!")
              (reverse path+current)
              ))))
      (do
        (newline)
        (println "Path does not exist!")
        '()))))

(defn graph-dijkstra! [graph start finish]
  (graph-reset-dijkstra! graph)
  (dosync
   (ref-set (:distance (graph-get-vertex graph finish)) 0))
  (graph-bfs! graph
              finish
              (fn [vertex]
                ;;(println "----")
                ;;(vertex-print vertex)
                (print ".")
                (if (= start (:label vertex))
                  (do
                    (newline)
                    (println "We're home!")
                    false)
                  (do
                    (doseq [neighbor-label
                            (filter (fn [label]
                                      (graph-vertex-unseen? graph label))
                                    @(:neighbors vertex))]
                      (let [neighbor (graph-get-vertex graph neighbor-label)]
                        (dosync
                         (ref-set (:distance neighbor)
                                  (inc @(:distance vertex))))))
                    true))))
  (graph-dijkstra-trace-back graph start finish vertex-get-best-neighbor))

(defn graph-dijkstra-with-weight! [graph start finish]
  (graph-reset-dijkstra! graph)
  (dosync
   (ref-set (:distance (graph-get-vertex graph finish)) 0))
  (graph-bfs! graph
              finish
              (fn [vertex]
                ;;(println "----")
                ;;(vertex-print vertex)
                (print ".")
                (if (= start (:label vertex))
                  (do
                    (newline)
                    (println "We're home!")
                    false)
                  (do
                    (doseq [neighbor-label
                            (filter
                             (fn [label]
                               (graph-vertex-unseen-or-in-queue? graph label))
                             @(:neighbors vertex))]
                      (let [neighbor (graph-get-vertex graph neighbor-label)
                            weight (graph-get-edge-weight graph
                                                          (:label vertex)
                                                          neighbor-label)
                            distance (+ @(:distance vertex)
                                        weight)]
                        (when (or (= @(:distance neighbor) -1)
                                  (< distance @(:distance neighbor)))
                          (dosync
                           (ref-set (:distance neighbor)
                                    distance)))))
                    true)))
              graph-dijkstra-weights-pick-best)
  (graph-dijkstra-trace-back graph start finish
                             vertex-get-best-neighbor-with-weights))

(defn graph-straight-line-distance [graph label1 label2]
  (let [vertex1 (graph-get-vertex graph label1)
        vertex2 (graph-get-vertex graph label2)
        lat1 (:latitude vertex1)
        lon1 (:longitude vertex1)
        lat2 (:latitude vertex2)
        lon2 (:longitude vertex2)
        dlat (- lat2 lat1)
        dlon (- lon2 lon1)]
    (* 6378
       (Math/sin
        (/ (* Math/PI (Math/sqrt (+ (* dlat dlat) (* dlon dlon)))) 180)))))

(defn graph-great-circle-distance [graph label1 label2]
  (let [vertex1 (graph-get-vertex graph label1)
        vertex2 (graph-get-vertex graph label2)
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

(defn graph-a-star-pick-best [graph queue finish]
  (let [best-distance (ref ##Inf)
        best-label (ref "")]
    (doseq [label queue]
      (let [vertex (graph-get-vertex graph label)
            distance-to-finish (graph-great-circle-distance graph
                                                            label
                                                            finish)
            cost-estimation (+ @(:distance vertex) distance-to-finish)]
        (if (< cost-estimation @best-distance)
          (dosync
           (ref-set best-distance cost-estimation)
           (ref-set best-label (:label vertex))))))
    @best-label))

(defn graph-a*! [graph start finish]
  (graph-reset-dijkstra! graph)
  (dosync
   (ref-set (:distance (graph-get-vertex graph start)) 0))
  (graph-bfs! graph
              start
              (fn [vertex]
                ;;(println "----")
                ;;(vertex-print vertex)
                (print ".")
                (if (= finish (:label vertex))
                  (do
                    (newline)
                    (println "We're home!")
                    false)
                  (do
                    (doseq [neighbor-label
                            (filter
                             (fn [label]
                               (graph-vertex-unseen-or-in-queue? graph label))
                             @(:neighbors vertex))]
                      (let [neighbor (graph-get-vertex graph neighbor-label)
                            weight (graph-get-edge-weight graph
                                                          (:label vertex)
                                                          neighbor-label)
                            distance (+ @(:distance vertex)
                                        weight)]
                        (when (or (= @(:distance neighbor) -1)
                                  (< distance @(:distance neighbor)))
                          (dosync
                           (ref-set (:distance neighbor)
                                    distance)))))
                    true)))
              (fn [graph queue]
                (graph-a-star-pick-best graph queue finish)))
  (graph-dijkstra-trace-back graph finish start
                             vertex-get-best-neighbor-with-weights))

(defn graph-print-visited-counts [graph]
  (let [total (count @(:vertices graph))
        visited (count (filter (fn [vertex] (= @(:status vertex) vertex-status-visited))
                               (vals @(:vertices graph))))
        unvisited (- total visited)]
    (println (str "Visited " visited "/" total " (" unvisited " remaining)"))))

(defn vertex-print [v]
  (println "Vertex:" (:label v))
  (println "Neighbors:")
  (doseq [n @(:neighbors v)]
    (println "  " n))
  (println "GPS:" (:latitude v) (:longitude v))
  (println "Status:" @(:status v))
  (println "Distance to finish:" @(:distance v))
  nil)

(defn edge-print
  ([e]
   (println "Edge" (:label e) "::"
            (:from e) "--" (:to e)
            "(" (:weight e) "km )"))
  ([graph from to]
   (edge-print
    (get @(:edges graph)
         (graph-edge-key from to)))))

(defn graph-vertices-connected? [g start stop]
  (graph-reset! g)
  (graph-bfs! g start)
  (= @(:status (graph-get-vertex g stop)) vertex-status-visited))

(defn graph-is-connected? [g]
  (graph-reset! g)
  (graph-bfs! g)
  (let [total (count @(:vertices g))
        visited (count (filter (fn [vertex] (= @(:status vertex)
                                               vertex-status-visited))
                               (vals @(:vertices g))))
        unvisited (- total visited)]
    (= unvisited 0)))

(defn graph-unvisited-vertices [g]
  (filter (fn [vertex] (= @(:status vertex) vertex-status-unseen))
          (vals @(:vertices g))))

(defn graph-count-components [g]
  (graph-reset! g)
  (loop [cnt 0]
    (let [unvisited (graph-unvisited-vertices g)]
      (if (empty? unvisited)
        cnt
        (do
          (graph-bfs! g (:label (first unvisited)))
          (recur (inc cnt)))))))

(defn graph-prim-get-vertex-distance [graph label]
  (let [vertex (graph-get-vertex graph label)]
    (with-local-vars [best-distance ##Inf
                      best-visited-label nil]
      (doseq [neighbor-label @(:neighbors vertex)]
        (let [edge (graph-get-edge graph label neighbor-label)]
          (when (and (< (:weight edge) @best-distance)
                     (graph-vertex-visited? graph neighbor-label))
            (var-set best-distance (:weight edge))
            (var-set best-visited-label neighbor-label))))
      (list @best-distance @best-visited-label))))

(defn graph-prim!
  ([g]
   (graph-prim! g (first (keys @(:vertices g)))))
  ([g start]
   (graph-reset! g)
   (graph-bfs! g
              start
              (fn [x] true)
              (fn [g queue]
                (with-local-vars [best-distance ##Inf
                                  best-open-label nil
                                  best-visited-label nil]
                  (doseq [open-label queue]
                    (println open-label)
                    (let [open-vertex-info (graph-prim-get-vertex-distance g open-label)
                          open-vertex-distance (first open-vertex-info)
                          open-vertex-visited-neighbor (second open-vertex-info)]
                      (println open-vertex-info)
                      (when (<= open-vertex-distance @best-distance)
                        (var-set best-distance open-vertex-distance)
                        (var-set best-open-label open-label)
                        (var-set best-visited-label open-vertex-visited-neighbor))))
                  (when (< @best-distance ##Inf)
                    (let [edge (graph-get-edge g @best-open-label @best-visited-label)]
                      (dosync
                       (ref-set (:spanning edge) true))))
                  @best-open-label)))
   nil))

(defn graph-prim-print [g]
  (doseq [ep @(:edges g)] (let [e (second ep)] (when @(:spanning e) (edge-print e)))))
