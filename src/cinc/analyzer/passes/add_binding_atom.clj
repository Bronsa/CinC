(ns cinc.analyzer.passes.add-binding-atom
  (:require [cinc.analyzer.passes :refer [prewalk]]
            [cinc.analyzer.utils :refer [update!]]))

(def ^:dynamic *bindings* {})

(defmulti -add-binding-atom :op)

(defmethod -add-binding-atom :binding
  [{:keys [name] :as ast}]
  (let [a (atom {})]
    (update! *bindings* assoc name a)
    (assoc ast :atom a)))

(defmethod -add-binding-atom :local
  [{:keys [name] :as ast}]
  (assoc ast :atom (*bindings* name)))

(defn add-binding-atom
  [ast]
  (binding [*bindings* *bindings*]
    (prewalk ast -add-binding-atom)))
