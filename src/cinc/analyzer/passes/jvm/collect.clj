(ns cinc.analyzer.passes.jvm.collect
  (:require [cinc.analyzer.utils :refer [postwalk]]))

(def ^:private ^:dynamic *collects*
  {:constants {}
   :keywords  {}
   :vars      {}})

(defn ^:private -register-constant
  [form]
  (or ((:constants *collects*) form)
      (let [id (count (:constants *collects*))]
        (set! *collects* (assoc-in *collects* [:constants form] id))
        id)))

(defn ^:private -collect-constants
  [{:keys [op form] :as ast}]
  (if (= op :const)
    (assoc ast :id (-register-constant form))
    ast))

(defn ^:private -collect-keywords
  [{:keys [op form type] :as ast}]
  (if (and (= op :const)
           (= type :keyword))
    (let [id (or ((:keywords *collects*) form)
                 (let [id (-register-constant form)]
                   (set! *collects* (assoc-in *collects* [:keywords form] id))
                   id))]
      (assoc ast :id id))
    ast))

(defn collect-fns [what]
  (case what
    :constants -collect-constants
    :keywords  -collect-keywords
    nil))

(defn collect [& what]
  (fn [{:keys [op] :as ast}]
    (if (#{:fn :deftype* :reify*} op)
      (binding [*collects* *collects*]
        (let [f (apply comp (filter identity (mapv collect-fns what)))]
          (into (postwalk ast f)
                *collects*)))
      ast)))
