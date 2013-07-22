(ns cinc.analyzer.passes.collect
  (:require [cinc.analyzer.utils :refer [postwalk protocol-node?]]))

(defmacro update! [target f & args]
  (list 'set! target (list* f args)))

(def ^:private ^:dynamic *collects*
  {:constants           {}
   :vars                {}
   :closed-overs       #{}
   :protocol-callsites #{}
   :keyword-callsites  #{}})

(defn -register-constant
  [form]
  (or ((:constants *collects*) form)
      (let [id (count (:constants *collects*))]
        (update! *collects* assoc-in [:constants form] id)
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
                   (update! *collects* assoc-in [:vars var] id)
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
       (update! *collects* update-in [:protocol-callsites] conj (:name f))

       (= :keyword-invoke op)
       (update! *collects* update-in [:keyword-callsites] conj (:form f)))))
  ast)

(defmulti -collect-closed-overs :op)
(defmethod -collect-closed-overs :default [ast] ast)

(defmethod -collect-closed-overs :local
  [{:keys [op name] :as ast}]
  (update! *collects* update-in [:closed-overs] conj name)
  ast)

(defmethod -collect-closed-overs :binding
  [{:keys [init name] :as ast}]
  (update! *collects* update-in [:closed-overs] disj name)
  (when init
    (-collect-closed-overs init)) ;; since we're in a postwalk, a bit of trickery is necessary
  ast)

(defmethod -collect-closed-overs :deftype
  [{:keys [fields] :as ast}]
  (update! *collects* assoc :closed-overs (set fields))
  ast)

(defmethod -collect-closed-overs :fn-method
  [{:keys [params] :as ast}]
  (update! *collects* update-in [:closed-overs]
           #(apply disj % (mapv :name params)))
  ast)

(defmethod -collect-closed-overs :fn
  [{:keys [name] :as ast}]
  (update! *collects* update-in [:closed-overs] disj name)
  ast)

(defn collect-fns [what]
  (case what
    :constants    -collect-constants
    :vars         -collect-vars
    :closed-overs -collect-closed-overs
    :callsites    -collect-callsites
    nil))

(defn collect [& what]
  (fn [{:keys [op env] :as ast}]
    (if (#{:fn :deftype :reify} op)
      (binding [*collects* *collects*]
        (let [f (apply comp (filter identity (mapv collect-fns what)))]
          (into (postwalk ast f)
                *collects*)))
      ast)))
