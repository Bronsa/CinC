(ns cinc.analyzer.passes.jvm.collect
  (:require [cinc.analyzer.utils :refer [postwalk protocol-node?]]))

(def ^:private ^:dynamic *collects*
  {:constants           {}
   :vars                {}
   :referenced-locals  #{}
   :protocol-callsites #{}
   :keyword-callsites  #{}})

(defn -register-constant
  [form]
  (or ((:constants *collects*) form)
      (let [id (count (:constants *collects*))]
        (set! *collects* (assoc-in *collects* [:constants form] id))
        id)))

(defn -collect-constants
  [{:keys [op form type] :as ast}]
  (if (and (= op :const)
           (not= type :nil)
           (not= type :boolean))
    (let [id (-register-constant form)]
      (assoc ast :id id))
    ast))

(defn -collect-vars
  [{:keys [op var] :as ast}]
  (if (#{:def :var :the-var} op)
    (let [id (or ((:vars *collects*) var)
                 (let [id (-register-constant var)]
                   (set! *collects* (assoc-in *collects* [:vars var] id))
                   id))]
      (assoc ast :id id))
    ast))

(defn -collect-callsites
  [{:keys [op] :as ast}]
  (when (#{:keyword-invoke :invoke} op)
    (let [f (:fn ast)]
      (cond
       (and (= :var (:op f))
            (protocol-node? (:var f)))
       (set! *collects* (update-in *collects* [:protocol-callsites] conj (:name f)))

       (= :keyword-invoke op)
       (set! *collects* (update-in *collects* [:keyword-callsites] conj (:form f))))))
  ast)

(defn -collect-referenced-locals
  [{:keys [op name] :as ast}]
  (when (and (= :local op)
             (not ((:referenced-locals *collects*) name)))
    (set! *collects* (update-in *collects* [:referenced-locals] conj name)))
  ast)

(defn collect-fns [what]
  (case what
    :constants         -collect-constants
    :vars              -collect-vars
    :referenced-locals -collect-referenced-locals
    :callsites         -collect-callsites
    nil))

(defn collect [& what]
  (fn [{:keys [op] :as ast}]
    (if (#{:fn :deftype* :reify*} op)
      (binding [*collects* *collects*]
        (let [f (apply comp (filter identity (mapv collect-fns what)))]
          (into (postwalk ast f)
                *collects*)))
      ast)))
