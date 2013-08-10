(ns cinc.analyzer.passes.jvm.clear-locals
  (:require [cinc.analyzer.utils :refer [update! walk]]))

(defmulti annotate-branch :op)

(defmethod annotate-branch :if
  [ast]
  (-> ast
    (assoc :branch? true)
    (assoc-in [:test :should-not-clear] true)
    (assoc-in [:then :path?] true)
    (assoc-in [:else :path?] true)))

(defmethod annotate-branch :local
  [{:keys [local] :as ast}]
  (if (= :letfn local)
    (assoc ast :should-not-clear true)
    ast))

(defmethod annotate-branch :fn-method
  [ast]
  (assoc ast :path? true))

(defmethod annotate-branch :method
  [ast]
  (assoc ast :path? true))

(defmethod annotate-branch :case
  [{:keys [thens] :as ast}]
  (-> ast
    (assoc :branch? true)
    (assoc-in [:test :should-not-clear] true)
    (assoc-in [:default :path?] true)))

(defmethod annotate-branch :case-then
  [ast]
  (assoc ast :path? true))

(defmethod annotate-branch :default [ast] ast)

(def ^:dynamic *clears* {:branch-clears #{}
                         :clears        #{}
                         :closes        #{}})

(defn -clear-locals
  [{:keys [op name local path? should-not-clear env] :as ast}]
  (if (and (= :local op)
           (#{:let :loop :letfn :arg} local)
           (or (not ((:closes *clears*) name))
               (:once env))
           (not ((:clears *clears*) name))
           (not should-not-clear))
    (do
      (update! *clears* update-in [:branch-clears] conj name)
      (update! *clears* update-in [:clears] conj name)
      (assoc ast :to-clear? true))
    ast))

(defn clear-locals-around
  [{:keys [path? branch?] :as ast}]
  (let [ast (-clear-locals ast)]
    (if path?
      (doseq [c (:clears *clears*)]
        (when ((:branch-clears *clears*) c)
          (update! *clears* update-in [:clears] disj c)))
      (when branch?
        (update! *clears* update-in [:clears] into (:branch-clears *clears*))
        (update! *clears* assoc :branch-clears #{})))
    ast))

(defn -propagate-closed-overs
  [{:keys [op closed-overs] :as ast}]
  (when (#{:reify :fn :deftype} op)
    (update! *clears* assoc-in [:closes] (or closed-overs #{})))
  ast)

(defn clear-locals [ast]
  (binding [*clears* *clears*]
    (walk ast -propagate-closed-overs clear-locals-around :reversed)))
