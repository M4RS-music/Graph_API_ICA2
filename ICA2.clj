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
            (Vertex. label (ref nil) latitude longitude (ref unseen) (ref ##Inf) (ref nil))))))))

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
        (conj @(:neighbors (get @(:vertices graph) from)) from)))))

(defn get-edge [g t f]
  (get @(:edges g) (edge-key t f)))
