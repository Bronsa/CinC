(ns clojure.analyzer
  (:refer-clojure :exclude [macroexpand-1 *ns*])
  (:require [clojure.java.io :as io]
            [clojure.string :as s])
  (:import (clojure.lang LazySeq IRecord IType)))

(defn record? [x]
  (instance? IRecord x))
(defn type? [x]
  (instance? IType x))

(defmulti -analyze (fn [op form env & _]))

(defn analyze [form env]
  "Given an environment, a map containing
   -  :locals (mapping of names to lexical bindings),
   -  :context (one of :statement, :expr, :return, :eval),
   -  :ns (a symbol naming the compilation ns)
 and form, returns an expression object (a map containing at least :form, :op and :env keys)."
  (let [form (if (instance? LazySeq form)
               (or (seq form) ())  ; we need to force evaluation in order to analyze
               form)]
    (case form

      nil                 (-analyze :const form env :nil)
      (true false)             (-analyze :const form env :bool)

      (cond

       (symbol? form)   (-analyze :symbol     form env) ;; TODO
       (keyword? form)  (-analyze :keyword    form env) ;; need to register
       (string? form)   (-analyze :string     (.intern ^String form) env)
       (number? form)   (-analyze :number     form env)

       ;; don't move those, we need to skip the empty check for records
       (type? form)     (-analyze :type       form env)
       (record? form)   (-analyze :record     form env)

       (and (coll? form)
            (empty? form))
                        (-analyze :empty-coll form env)

       (seq? form)      (-analyze :seq        form env) ;; TODO
       (vector? form)   (-analyze :vector     form env)
       (map? form)      (-analyze :map        form env)
       (set? form)      (-analyze :set        form env)

       :else            (-analyze :const      form env :unknown)))))

(defmethod -analyze :keyword
  [_ form env]
  {:op       :keyword
   :env      env
   :literal? true
   :form     form})

(defmethod -analyze :string
  [_ form env]
  {:op       :string
   :env      env
   :literal? true
   :form     (.intern ^String form)})

(defmethod -analyze :const ;; char, regexes, classes, quoted stuff
  [_ form env type]
  {:op       :const
   :env      env
   :type     type
   :literal? true
   :form     form})

(defn coll-type [coll]
  (cond
   (seq? coll)    :list
   (vector? coll) :vector
   (map? coll)    :map
   (set? coll)    :set))

(defn ^:private or-eval [{:keys [context] :as env} ctx]
  (if (= :eval context)
    env
    (assoc env :context ctx)))

(defn wrapping-meta [{:keys [form env] :as expr}]
  (if (meta form)
    {:op   :meta
     :env  env
     :form form
     :meta (-analyze :map (meta form) (or-eval env :expr))
     :expr (update-in expr [:env] or-eval :expr)}
    expr))

(defmethod -analyze :type
  [_ form env]
  (if-not (meta form)
    (-analyze :const form env :type)
    (wrapping-meta
     {:op       :type
      :env      env
      :literal? true
      :form     form})))

(defmethod -analyze :record
  [_ form env]
  (if-not (meta form)
    (-analyze :const form env :record)
    (wrapping-meta
     {:op       :record
      :env      env
      :literal? true
      :form     form})))

(defmethod -analyze :empty-coll
  [_ form env]
  (wrapping-meta
   {:op   :empty-coll
    :env  env
    :type (coll-type form)
    :form form}))

(defmethod -analyze :vector
  [_ form env]
  (let [items-env (or-eval env :expr)
        items (mapv (analyze-in-env items-env) form)
        const? (and (every? :literal? items)
                    (not (meta form)))]
    (if const?
      (-analyze :const form env :vector)
      (wrapping-meta
       {:op    :vector
        :env   env
        :items items
        :form  form}))))

(defmethod -analyze :map
  [_ form env]
  (let [kv-env (or-eval env :expr)
        keys (keys form)
        vals (vals form)
        [ks vs] (map (partial mapv (analyze-in-env kv-env)) [keys vals])
        const? (and (every? :literal? ks)
                    (every? :literal? vs)
                    (not (meta form)))]
    (if const?
      (-analyze :const form env :map)
      (wrapping-meta
       {:op   :map
        :env  env
        :keys ks
        :vals vs
        :form form}))))

(defmethod -analyze :set
  [_ form env]
  (let [items-env (or-eval env :expr)
        items (mapv (analyze-in-env items-env) form)
        const? (and (every? :literal? items)
                    (not (meta form)))]
    (if const?
      (-analyze :const form env :set)
      (wrapping-meta
       {:op    :set
        :env   env
        :items items
        :form  form}))))

(defn resolve-var [sym env]
  )

(defmethod -analyze :symbol
  [_ sym env]
  (let [ret {:env  env
             :form sym}]
    (into ret
          (if-let [local-binding (-> env :locals)]
            {:op   :local-binding
             :info  local-binding}
            {:op   :var
             :info (resolve-var sym env)}))))
