(ns cinc.analyzer.passes.cleanup)

(defn cleanup1 [ast]
  (let [ast (-> ast
              (update-in [:env] dissoc :locals)
              (update-in [:env] dissoc :loop-locals))]
    (if (= :local (:op ast))
      (dissoc (assoc ast :children (vec (remove #{:init} (:children ast)))) :init)
      ast)))


(defn cleanup2 [ast]
  (let [ast (-> ast
              (update-in [:env] dissoc :loop-locals-casts)
              (dissoc :atom))]
    ast))
