(ns cinc.analyzer.passes.jvm.collect-constants
  (:require [cinc.analyzer.utils :refer [postwalk]]))

(def ^:private ^:dynamic *constants*)

(defn -collect-constants
  [{:keys [op form] :as ast}]
  (if (= op :const)
    (let [id (if (contains? (:set *constants*) form)
               ((:map *constants*) form)
               (let [id (count (:set *constants*))]
                 (set! *constants*
                       (-> (assoc-in *constants* [:map form] id)
                         (update-in [:set] conj form)))
                 id))]
      (assoc ast :id id))
    ast))

(defn collect-constants
  [{:keys [op] :as ast}]
  (if (#{:fn :deftype* :reify*} op)
    (binding [*constants* {:map {} :set #{}}]
      (assoc (postwalk ast -collect-constants)
        :constants (:map *constants*)))
    ast))
