(ns cinc.analyzer.passes.infer-tag
  (:require [cinc.analyzer.utils :refer [postwalk arglist-for-arity]])
  (:import (clojure.lang IPersistentVector IPersistentMap
                         IPersistentSet ISeq Keyword Var
                         Symbol)
           java.util.regex.Pattern))

(defmulti -infer-tag :op)

(defmethod -infer-tag :vector
  [ast]
  (assoc ast :tag IPersistentVector))

(defmethod -infer-tag :map
  [ast]
  (assoc ast :tag IPersistentMap))

(defmethod -infer-tag :set
  [ast]
  (assoc ast :tag IPersistentMap))

(defmethod -infer-tag :seq
  [ast]
  (assoc ast :tag ISeq))

(defmethod -infer-tag :class
  [ast]
  (assoc ast :tag Class))

(defmethod -infer-tag :keyword
  [ast]
  (assoc ast :tag Keyword))

(defmethod -infer-tag :symbol
  [ast]
  (assoc ast :tag Symbol))

(defmethod -infer-tag :string
  [ast]
  (assoc ast :tag String))

;; need to specialize
(defmethod -infer-tag :number
  [ast]
  (assoc ast :tag Number))

(defmethod -infer-tag :type
  [{:keys [form] :as ast}]
  (assoc ast :tag (class form)))

(defmethod -infer-tag :record
  [{:keys [form] :as ast}]
  (assoc ast :tag (class form)))

(defmethod -infer-tag :char
  [ast]
  (assoc ast :tag Character))

(defmethod -infer-tag :regex
  [ast]
  (assoc ast :tag Pattern))

(defmethod -infer-tag :the-var
  [ast]
  (assoc ast :tag Var))

(defmethod -infer-tag :binding
  [{:keys [init] :as ast}]
  (if init
    (merge ast
           (when-let [tag (:tag init)]
             {:tag tag})
           (when-let [arglists (:arg-lists init)]
             {:arg-lists arglists}))
    ast))

(defmethod -infer-tag :local
  [{:keys [init] :as ast}]
  (if init
        (merge ast
           (when-let [tag (:tag init)]
             {:tag tag})
           (when-let [arglists (:arg-lists init)]
             {:arg-lists arglists}))
        ast))

(defmethod -infer-tag :var
  [{:keys [var] :as ast}]
  (let [{:keys [dynamic tag arg-lists]} (meta var)]
    (if (not dynamic)
      (merge ast
             (when tag {:tag tag})
             (when arg-lists {:arg-lists arg-lists}))
      ast)))

(defmethod -infer-tag :def
  [{:keys [init var] :as ast}]
  (let [ast (assoc ast :tag Var)]
    (if-let [arglists (:arg-lists init)]
      (assoc ast :arg-lists arglists)
      ast)))

(defmethod -infer-tag :const
  [{:keys [op type form] :as ast}]
  (if (not= :unknown type)
    (assoc (-infer-tag (assoc ast :op type))
      :op op)
    (assoc ast :tag (class form))))

(defmethod -infer-tag :if
  [{:keys [then else] :as ast}]
  (let [[then-tag else-tag] (mapv :tag [then else])]
    (if (and then-tag
             (or (not else)
             (= then-tag else-tag)))
      (assoc ast :tag then-tag)
      ast)))

(defmethod -infer-tag :new
  [{:keys [maybe-class] :as ast}]
  (assoc ast :tag maybe-class))

(defmethod -infer-tag :do
  [{:keys [ret] :as ast}]
  (if-let [tag (:tag ret)]
    (assoc ast :tag tag)
    ast))

(defmethod -infer-tag :let
  [{:keys [body] :as ast}]
  (if-let [tag (:tag body)]
    (assoc ast :tag tag)
    ast))

(defmethod -infer-tag :letfn
  [{:keys [body] :as ast}]
  (if-let [tag (:tag body)]
    (assoc ast :tag tag)
    ast))

(defmethod -infer-tag :loop
  [{:keys [body] :as ast}]
  (if-let [tag (:tag body)]
    (assoc ast :tag tag)
    ast))

(defmethod -infer-tag :fn-method
  [{:keys [form body params] :as ast}]
  (let [tag (or (:tag (meta (first form)))
                (:tag body))
        ast (if tag
              (assoc ast :tag tag)
              ast)]
    (assoc ast
      :arglist (with-meta (mapv :name params)
                 {:tag tag}))))

(defmethod -infer-tag :fn
  [{:keys [methods] :as ast}]
  (assoc ast :arg-lists (mapv :arglist methods)))

(defmethod -infer-tag :try
  [{:keys [body catches] :as ast}]
  (if-let [body-tag (:tag body)]
    (if-let [catches-tags (seq (filter identity (map (comp :tag :body) catches)))]
      (if (every? = (conj catches-tags body-tag))
        (assoc ast :tag body-tag)
        ast)
      (assoc ast :tag body-tag)) ;; or should it infer nothing? we need to differenciate between nil and not there
    ast))

(defmethod -infer-tag :invoke
  [{:keys [fn args] :as ast}]
  (if (#{:var :local :fn} (:op fn))
    (let [argc (count args)
          arglist (arglist-for-arity fn argc)]
      (if-let [tag (or (:tag (meta arglist)) ;; ideally we would select the fn-method
                       (:tag fn))]
        (assoc ast :tag tag)
        ast))
    ast))

(defmethod -infer-tag :default [ast] ast)

(defn infer-shortest-path
  [{:keys [tag form name] :as ast}]
  (if tag
    ast
    (if-let [tag (:tag (meta name))]
      (assoc ast :tag tag)
      (if-let [form-tag (:tag (meta form))]
        (assoc ast :tag form-tag)
        (-infer-tag ast)))))

(defn infer-tag [ast]
  (postwalk ast infer-shortest-path))
