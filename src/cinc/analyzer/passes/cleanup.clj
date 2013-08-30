(ns cinc.analyzer.passes.cleanup)

(defn cleanup [ast]
  (let [ast (-> ast
              (update-in [:env] dissoc :locals)
              (update-in [:env] dissoc :loop-locals))]
    (if (= :local (:op ast))
      (dissoc ast :init)
      ast)))
