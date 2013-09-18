(ns cinc.analyzer.passes.jvm.validate-loop-locals
  (:require [cinc.analyzer.passes.jvm.emit-form :refer [emit-form]]
            [cinc.analyzer.passes :refer [prewalk]]
            [cinc.analyzer.utils :refer [update!]]))

(def ^:dynamic ^:private validating? false)
(def ^:dynamic ^:private mismatch? #{})

(defn find-mismatch [{:keys [op exprs] :as ast} tags]
  (when (and (= op :recur)
             (not= (mapv :tag exprs) tags))
    (update! mismatch? conj (mapv :tag exprs)))
  ast)

(defmulti -validate-loop-locals (fn [_ {:keys [op]}] op))

(defmethod -validate-loop-locals :loop
  [analyze {:keys [bindings body env] :as ast}]
  (if validating?
    ast
    (binding [mismatch? #{}]
      (let [bind-tags (mapv :tag bindings)]
        (prewalk body (fn [ast] (find-mismatch ast bind-tags)))
        (if mismatch?
          (let [bindings (apply mapcat (fn [{:keys [name tag init]} & mismatches]
                                         (if (every? #{tag} mismatches)
                                           [name (emit-form init)]
                                           [(with-meta name {:tag Object})
                                            (emit-form init)]))
                                bindings mismatch?)]
            (binding [validating? true]

              (analyze `(loop* [~@bindings] ~(emit-form body))
                       (assoc env :loop-locals-casts
                              (let [binds (mapv first (partition 2 bindings))]
                                (zipmap binds (mapv (comp :tag meta) binds)))))))
          ast)))))

(defmethod -validate-loop-locals :local
  [_ {:keys [form local env] :as ast}]
  (if validating?
    (if-let [cast ((:loop-locals-casts env) form)]
      (assoc ast :tag cast)
      ast)
    ast))

(defmethod -validate-loop-locals :recur
  [_ {:keys [exprs env] :as ast}]
  (if validating?
    (let [casts (:loop-locals-casts env)]
      (assoc ast
        :exprs (mapv (fn [e c]
                       (if c (assoc e :cast c) c))
                     exprs (vals casts))))
    ast))

(defmethod -validate-loop-locals :default
  [_ ast]
  ast)

(defn validate-loop-locals [analyze]
  (fn [ast] (-validate-loop-locals analyze ast)))
