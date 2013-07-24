(ns cinc.analyzer.passes.jvm.clear-locals
  (:require [cinc.analyzer.utils :refer [update! postwalk prewalk]]))

(def ^:dynamic *branch* 0)

(defmulti -annotate-branch :op)

(defmethod -annotate-branch :if
  [ast]
  (let [branch (update! *branch* inc)]
    (-> ast
      (assoc-in [:test :should-not-clear] true)
      (assoc-in [:then :path?] branch)
      (assoc-in [:else :path?] branch))))

(defmethod -annotate-branch :default [ast] ast)

(defn annotate-branch [ast]
  (binding [*branch* *branch*]
    (prewalk ast -annotate-branch)))

(def ^:dynamic *clears* {})

(defmulti -clear-locals :op)

(defmethod -clear-locals :local
  [{:keys [name path? should-not-clear] :as ast}]
  (if (and (not (*clears* name))
           (not should-not-clear))
    (do (update! *clears* assoc name 0)
        (assoc ast :to-clear? true))
    (assoc ast :to-clear? false)))

(defmethod -clear-locals :default
  [{:keys [path?] :as ast}]
  (when path?
    (doseq [[k v] *clears*]
      (when (= nil v)
        (update! *clears* assoc k path?))
      (when (= path? v)
       (update! *clears* dissoc k))))
  ast)

(defn clear-locals [ast]
  (binding [*clears* *clears*]
    (postwalk ast -clear-locals :reversed)))
