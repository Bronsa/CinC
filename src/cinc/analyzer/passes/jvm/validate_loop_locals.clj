(ns cinc.analyzer.passes.jvm.validate-loop-locals
  (:require [cinc.analyzer.passes :refer [prewalk postwalk]]
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
        (if (seq mismatch?)
          (let [bindings (apply mapv (fn [{:keys [form tag]} & mismatches]
                                       (if (every? #{tag} mismatches)
                                         form
                                         (with-meta form {:tag Object})))
                                bindings mismatch?)
                binds (zipmap bindings (mapv (comp :tag meta) bindings))]
            (binding [validating? true]
              (postwalk (prewalk (assoc ast :bindings
                                        (mapv (fn [bind f]
                                                (assoc bind :form f))
                                              (:bindings ast) bindings))
                                 (fn [ast]
                                         (assoc-in (dissoc ast :tag)
                                                   [:env :loop-locals-casts] binds)))
                        analyze)))
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
                       (if c (assoc e :tag c) c))
                     exprs (vals casts))))
    ast))

(defmethod -validate-loop-locals :default
  [_ ast]
  ast)

(defn validate-loop-locals [analyze]
  (fn [ast] (-validate-loop-locals analyze ast)))
