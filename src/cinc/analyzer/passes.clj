(ns cinc.analyzer.passes)

(defn cycling [& fns]
  (fn [ast]
    (let [new-ast (reduce #(%2 %) ast fns)]
      (if (= new-ast ast)
        ast
        (recur new-ast)))))

(defn children [{:keys [children] :as ast}]
  (when children
    (mapv ast children)))

(defn update-children
  ([ast f] (update-children ast f identity))
  ([ast f fix]
     (if-let [c (children ast)]
       (reduce (fn [ast [k v]]
                 (assoc ast k (if (vector? v)
                                (fix (mapv f (fix v)))
                                (f v))))
               ast (map list (fix (:children ast)) (fix c)))
       ast)))

(defn walk
  ([ast pre post]
     (walk ast pre post false))
  ([ast pre post reversed?]
     (let [ast (pre ast)
           fix (if reversed? (comp vec rseq) identity)
           w #(walk % pre post reversed?)
           ast (update-children ast w fix)]
       (post ast))))

(defn prewalk [ast f]
  (walk ast f identity))

(defn postwalk
  ([ast f]
     (walk ast identity f false))
  ([ast f reversed?]
     (walk ast identity f reversed?)))
