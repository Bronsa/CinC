(set! *warn-on-reflection* true)

(ns cinc.analyzer
  (:refer-clojure :exclude [macroexpand-1])
  (:require [clojure.java.io :as io]
            [clojure.string :as s]
            [cinc.host-utils :refer :all])
  (:import (clojure.lang LazySeq IRecord IType ILookup Var RT)))

(defn record? [x]
  (instance? IRecord x))
(defn type? [x]
  (instance? IType x))

(defmulti -analyze (fn [op form env & _] op))
(defmulti parse (fn [op & rest] op))

(defn analyze [form env]
  "Given an environment, a map containing
   -  :locals (mapping of names to lexical bindings),
   -  :context (one of :statement, :expr, :return, :eval),
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
       (string? form)   (-analyze :string     form env)
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
   :form     form})

(defmethod -analyze :const ;; char, regexes, classes, quoted stuff
  [_ form env type]
  {:op       :const
   :env      env
   :type     type
   :literal? true
   :form     form})

(defmethod -analyze :number
  [_ form env]
  {:op       :number
   :env      env
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

(defn ^:private analyze-in-env [env]
  (fn [form] (analyze form env)))

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

;; constans will be detected in a second pass
;; will move constant colls detection to that pass too
(defmethod -analyze :symbol
  [_ sym env]
  (let [ret (if-let [local-binding (-> env :locals sym)]
              (assoc local-binding
                :op :local-binding)
              (if-let [^Var var (resolve-var sym)]
                {:op   :var
                 :name (.sym var)
                 :ns   (-> var .ns .name)
                 :var  var}
                (or (maybe-host-expr sym)
                    (throw (ex-info (str "could not resolve var: " sym) {:var sym})))))]
    (into {:env  env
           :form sym}
          ret)))

(def specials
  '#{def loop* recur if let* letfn* do fn*
     quote var . set! case* import* try catch
     deftype* reify* throw finally new &})

(defn macroexpand-1 [form env]
  (if (seq? form)
    (let [op (first form)]
      (if (specials op)
        form
        (let [v (try (resolve-var op true)
                     (catch Exception _))]
          (if (and (not (-> env :locals op)) ;; locals cannot be macros
                   (:macro (meta v)))
            (apply @v env form (rest form)) ; (m &env &form & args)
            (if (symbol? op)
              (let [opname (name op)]
                (cond

                 (= (first opname) \.) ; (.foo bar ..)
                 (let [[target & args] (next form)
                       target (if (maybe-class target)
                                (with-meta (list 'clojure.core/identity target) {:tag Class})
                                target)]
                   (with-meta (list* '. target (symbol (subs opname 1)) args)
                     (meta form)))

                 (and (namespace op)
                      (maybe-class (namespace op))) ; (class/field ..)
                 (let [target (maybe-class (namespace op))]
                   (with-meta (list* '. target opname (next form))
                     (meta form)))

                 (= (last opname) \.) ;; (class. ..)
                 (list* 'new (symbol (subs opname 0 (dec (count opname)))) (next form))

                 :else form))
              (if-let [c (maybe-class op)]
                (throw (ex-info (str "expecting var but" form "is mapped to " c) {:form form}))
                form))))))
    form))

(defmethod -analyze :seq
  [_ form env]
  (let [env (assoc env :line
                   (or (-> form meta :line)
                       (:line env)))]
    (let [op (first form)]
      (if (nil? op)
        (ex-info "Can't call nil" {:form form}))
      (let [mform (macroexpand-1 form env)]
        (if (identical? form mform)
          (if (specials op)
            (parse op form env)
            (parse :invoke form env))
          (analyze env mform name))))))
