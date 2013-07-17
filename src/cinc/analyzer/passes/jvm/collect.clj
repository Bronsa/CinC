(ns cinc.analyzer.passes.jvm.collect
  (:require [cinc.analyzer.utils :refer [postwalk]]))

(def ^:private ^:dynamic *collects*
  {:constants {}
   :keywords  {}
   :vars      {}})

(defn -collect-constants
  [{:keys [op form] :as ast}]
  (if (= op :const)
    (let [id (if (contains? (:constants *collects*) form)
               ((:constants *collects*) form)
               (let [id (count (:set *collects*))]
                 (set! *collects* (assoc-in *collects* [:constants form] id))
                 id))]
      (assoc ast :id id))
    ast))

(defn collect-fns [what]
  (case what
    :constants -collect-constants
    nil))

(defn collect [& what]
  (fn [{:keys [op] :as ast}]
    (if (#{:fn :deftype* :reify*} op)
      (binding [*collects* *collects*]
        (let [f (apply comp (filter identity (mapv collect-fns what)))]
          (into (postwalk ast f)
                *collects*)))
      ast)))
