(ns cinc.analyzer.passes.jvm.clear-locals
  (:require [cinc.analyzer.utils :refer [update! postwalk prewalk]]))

(defmulti annotate-branch :op)

(defmethod annotate-branch :if
  [ast]
  (-> ast
    (assoc :branch? true)
    (assoc-in [:test :should-not-clear] true)
    (assoc-in [:then :path?] true)
    (assoc-in [:else :path?] true)))

(defmethod annotate-branch :default [ast] ast)

(def ^:dynamic *clears* {:branch-clears #{}
                         :clears        #{}})

(defmulti -clear-locals :op)

(defmethod -clear-locals :local
  [{:keys [name path? should-not-clear] :as ast}]
  (if (and (not ((:clears *clears*) name))
           (not should-not-clear))
    (do
      (update! *clears* update-in [:branch-clears] conj name)
      (update! *clears* update-in [:clears] conj name)
      (assoc ast :to-clear? true))
    ast))

(defmethod -clear-locals :default [ast] ast)

(defn clear-locals-around
  [{:keys [path? branch? op] :as ast}]
  (let [ast (-clear-locals ast)]
    (if path?
      (doseq [c (:clears *clears*)]
        (when ((:branch-clears *clears*) c)
          (update! *clears* update-in [:clears] disj c)))
      (when branch?
        (update! *clears* update-in [:clears] into (:branch-clears *clears*))
        (update! *clears* assoc :branch-clears #{})))
    ast))

(defn clear-locals [ast]
  (binding [*clears* *clears*]
    (postwalk ast clear-locals-around :reversed)))
