(ns cinc.analyzer.passes.elide-meta
  (:require [cinc.analyzer :refer [analyze]]))

(def elides (set (:elide-meta *compiler-options*)))

(defn dissoc-meta [{:keys [op form keys vals env] :as meta}]
  (let [form (apply dissoc form elides)]
    (if (= :const op)
      (analyze (list 'quote form) env)
      (let [new-meta (mapcat (fn [{:keys [form] :as k} v]
                               (when-not (elides form)
                                 [k v]))
                             keys vals)]
        (assoc meta
          :form form
          :keys (mapv first new-meta)
          :vals (mapv second new-meta))))))

(defmulti -elide-meta :op)

(defmethod -elide-meta :with-meta
  [{:keys [meta expr env] :as ast}]
  (let [new-meta (apply dissoc (:form meta) elides)]
    (if (not (empty? new-meta))
      (if (= new-meta (:form meta))
        ast
        (let [new-meta (dissoc-meta meta)]
          (assoc ast :meta new-meta)))
      (assoc-in expr [:env :context] (:context env)))))

(defmethod -elide-meta :def
  [{:keys [meta env] :as ast}]
  (let [new-meta (apply dissoc (:form meta) elides)]
    (if (not (empty? new-meta))
      (if (= new-meta (:form meta))
        ast
        (let [new-meta (dissoc-meta meta)]
          (assoc ast :meta new-meta)))
      (dissoc ast :meta))))

(defmethod -elide-meta :default [ast] ast)

(defn elide-meta [ast]
  (if (seq elides)
    (-elide-meta ast)
    ast))
