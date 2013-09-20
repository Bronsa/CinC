(ns cinc.analyzer.passes.jvm.annotate-branch)

(defmulti annotate-branch :op)

(defmethod annotate-branch :if
  [ast]
  (-> ast
    (assoc :branch? true)
    (assoc-in [:test :should-not-clear] true)
    (assoc-in [:then :path?] true)
    (update-in [:else] #(when % (assoc % :path? true)))))

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
