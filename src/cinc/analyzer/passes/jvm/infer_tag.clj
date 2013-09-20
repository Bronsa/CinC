(ns cinc.analyzer.passes.jvm.infer-tag
  (:require [cinc.analyzer.utils :refer [arglist-for-arity]]
            [cinc.analyzer.jvm.utils :refer [convertible?]])
  (:import (clojure.lang PersistentVector IPersistentMap
                         IPersistentSet ISeq Keyword Var
                         Symbol AFunction)
           java.util.regex.Pattern))

(defmulti infer-constant-tag :op)
(defmulti -infer-tag :op)

(defmethod infer-constant-tag :vector
  [ast]
  (assoc ast :tag PersistentVector))

(defmethod infer-constant-tag :map
  [ast]
  (assoc ast :tag IPersistentMap))

(defmethod infer-constant-tag :set
  [ast]
  (assoc ast :tag IPersistentSet))

(defmethod infer-constant-tag :seq
  [ast]
  (assoc ast :tag ISeq))

(defmethod infer-constant-tag :class
  [ast]
  (assoc ast :tag Class))

(defmethod infer-constant-tag :keyword
  [ast]
  (assoc ast :tag Keyword))

(defmethod infer-constant-tag :symbol
  [ast]
  (assoc ast :tag Symbol))

(defmethod infer-constant-tag :string
  [ast]
  (assoc ast :tag String))

(defmethod infer-constant-tag :number
  [{:keys [form] :as ast}]
  (assoc ast :tag (class form)))

(defmethod infer-constant-tag :type
  [{:keys [form] :as ast}]
  (assoc ast :tag (class form)))

(defmethod infer-constant-tag :record
  [{:keys [form] :as ast}]
  (assoc ast :tag (class form)))

(defmethod infer-constant-tag :char
  [ast]
  (assoc ast :tag Character))

(defmethod infer-constant-tag :regex
  [ast]
  (assoc ast :tag Pattern))

(defmethod infer-constant-tag :the-var
  [ast]
  (assoc ast :tag Var))

(defmethod infer-constant-tag :bool
  [ast]
  (assoc ast :tag Boolean))

(defmethod infer-constant-tag :const
  [{:keys [op type form] :as ast}]
  (if (not= :unknown type)
    (assoc (infer-constant-tag (assoc ast :op type))
      :op op)
    (assoc ast :tag (class form))))

(defmethod infer-constant-tag :quote
  [{:keys [expr] :as ast}]
  (let [{:keys [tag] :as expr} (infer-constant-tag expr)]
    (assoc ast
      :expr expr
      :tag  tag)))

(defmethod -infer-tag :binding
  [{:keys [init local] :as ast}]
  (if init
    (merge ast
           (when-let [tag (:tag init)]
             {:tag tag})
           (when-let [return-tag (:return-tag init)]
             {:return-tag return-tag})
           (when-let [arglists (:arglists init)]
             {:arglists arglists}))
    ast))

(defmethod -infer-tag :local
  [{:keys [init local env form] :as ast}]
  (if init
    (merge ast
           (when-let [tag (:tag init)]
             {:tag tag})
           (when-let [return-tag (:return-tag init)]
             {:return-tag return-tag})
           (when-let [arglists (:arglists init)]
             {:arglists arglists}))
    (if (= :fn local)
      (assoc ast :tag clojure.lang.AFunction)
      (if (= :arg local)
        (let [{:keys [form variadic?]} ((:locals env) form)
              tag (or (:tag (meta form))
                      (and variadic? clojure.lang.ArraySeq)
                      Object)]
          (assoc ast :tag tag))
        ast))))

(defmethod -infer-tag :var
  [{:keys [var] :as ast}]
  (let [{:keys [dynamic tag arg-lists]} (meta var)]
    (if (not dynamic)
      (merge ast
             (when tag
               (if (fn? @var)
                 {:tag AFunction :return-tag tag}
                 {:tag tag}))
             (when arg-lists {:arglists arg-lists}))
      ast)))

(defmethod -infer-tag :def
  [{:keys [init var] :as ast}]
  (let [ast (assoc ast :tag Var)]
    (if-let [arglists (:arglists init)]
      (assoc ast :arglists arglists)
      ast)))

(defmethod -infer-tag :if
  [{:keys [then else] :as ast}]
  (let [[then-tag else-tag] (mapv :tag [then else])]
    (cond
     (and then-tag
          (or (:loop-tag else)
              (= then-tag else-tag)))
     (assoc ast :tag then-tag)

     (and else-tag (:loop-tag then))
     (assoc ast :tag else-tag)

     :else
     ast)))

(defmethod -infer-tag :case
  [{:keys [thens] :as ast}]
  (let [thens (mapv :then thens)
        tag (first (keep :tag thens))]
    (if (and tag
             (every? (fn [x] (or (= (:tag x) tag)
                           (:loop-tag x))) thens))
      (assoc ast :tag tag)
      ast)))

(defmethod -infer-tag :new
  [{:keys [maybe-class class] :as ast}]
  (assoc ast :tag (or class maybe-class)))

(defmethod -infer-tag :recur
  [ast]
  (assoc ast :loop-tag true))

(defmethod -infer-tag :with-meta
  [{:keys [expr] :as ast}]
  (if-let [tag (:tag expr)]
    (assoc ast :tag tag)
    ast))

(defmethod -infer-tag :do
  [{:keys [ret] :as ast}]
  (if-let [tag (:tag ret)]
    (assoc ast :tag tag)
    (if (:loop-tag ret)
      (assoc ast :loop-tag true)
      ast)))

(defmethod -infer-tag :let
  [{:keys [body] :as ast}]
  (if-let [tag (:tag body)]
    (assoc ast :tag tag)
    (if (:loop-tag body)
      (assoc ast :loop-tag true)
      ast)))

(defmethod -infer-tag :letfn
  [{:keys [body] :as ast}]
  (if-let [tag (:tag body)]
    (assoc ast :tag tag)
    (if (:loop-tag body)
      (assoc ast :loop-tag true)
      ast)))

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
  (assoc ast
    :arglists (mapv :arglist methods)
    :tag AFunction))

(defmethod -infer-tag :try
  [{:keys [body catches] :as ast}]
  (if-let [body-tag (:tag body)]
    (if (every? = (conj (filter identity (map (comp :tag :body) catches)) body-tag))
      (assoc ast :tag body-tag)
      ast)
    (if (:loop-tag body)
      (assoc ast :loop-tag true)
      ast)))

(defmethod -infer-tag :invoke
  [{:keys [fn args] :as ast}]
  (if (#{:var :local :fn} (:op fn))
    (let [argc (count args)
          arglist (arglist-for-arity fn argc)]
      (if-let [tag (or (:tag (meta arglist)) ;; ideally we would select the fn-method
                       (:return-tag fn))]
        (assoc ast
          :tag  tag
          :cast tag) ;; ensure we check-cast the return value
        ast))
    ast))

(defmethod -infer-tag :method
  [{:keys [form body params] :as ast}]
  (let [tag (or (:tag (meta (first form)))
                (:tag body))]
    (if tag
      (assoc ast :tag tag)
      ast)))

(defmethod -infer-tag :deftype
  [ast]
  (assoc ast :tag Class))

(defmethod -infer-tag :reify
  [{:keys [class-name] :as ast}]
  (assoc ast :tag class-name))

(defmethod infer-constant-tag :default [ast] ast)
(defmethod -infer-tag :default [ast] ast)

(defn infer-tag
  [{:keys [tag form name] :as ast}]
  (if tag
    ast
    (if-let [tag (:tag (meta name))]
      (assoc ast :tag tag)
      (if-let [form-tag (:tag (meta form))]
        (assoc ast :tag form-tag)
        (-infer-tag ast)))))
