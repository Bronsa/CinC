(ns cinc.analyzer.passes.elide-meta
  (:require [cinc.analyzer :refer [analyze]]
            [cinc.analyzer.utils :refer [ctx prewalk]]))

(def elides [:foo])

(defmulti -elide-meta :op)

(defmethod -elide-meta :with-meta
  [{:keys [meta expr env] :as ast}]
  (let [new-meta (apply dissoc (:form meta) elides)]
    (if (not (empty? new-meta))
     (if (= new-meta meta)
       ast
       (assoc ast :meta (analyze new-meta (ctx env :expr))))
     (assoc-in expr [:env :context] (:context env)))))

(defmethod -elide-meta :def
  [{:keys [meta env] :as ast}]
  (if-let [new-meta (apply dissoc (:form meta) elides)]
    (if (= new-meta meta)
      ast
      (assoc ast :meta (analyze new-meta (ctx env :expr))))
    (assoc ast :meta nil)))

(defmethod -elide-meta :default [ast] ast)

(defn elide-meta [ast]
  (if elides
    (prewalk ast -elide-meta)
    ast))
