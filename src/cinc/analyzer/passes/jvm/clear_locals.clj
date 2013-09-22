(ns cinc.analyzer.passes.jvm.clear-locals
  (:require [cinc.analyzer.passes :refer [walk]]
            [cinc.analyzer.utils :refer [update!]]))

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
