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
(defmulti parse (fn [[op & form] & rest] op))

;; once we have all set working, need to figure out a way to stop depending on :eval
;; see: https://groups.google.com/forum/?fromgroups#!topic/clojure-dev/KI9fvw9fEMg
(defn analyze
  "Given an environment, a map containing
   -  :locals (mapping of names to lexical bindings),
   -  :context (one of :statement, :expr, :return, :eval),
 and form, returns an expression object (a map containing at least :form, :op and :env keys)."
  [form env]
  (let [form (if (instance? LazySeq form)
               (or (seq form) ())  ; we need to force evaluation in order to analyze
               form)]
    (case form

      nil                 (-analyze :const form env :nil)
      (true false)             (-analyze :const form env :bool)

      (cond

       (symbol? form)   (-analyze :symbol     form env)
       (keyword? form)  (-analyze :keyword    form env) ;; need to register
       (string? form)   (-analyze :string     form env)
       (number? form)   (-analyze :number     form env)

       ;; don't move those, we need to skip the empty check for records
       (type? form)     (-analyze :type       form env)
       (record? form)   (-analyze :record     form env)

       (and (coll? form)
            (empty? form))
                        (-analyze :empty-coll form env)

       (seq? form)      (-analyze :seq        form env)
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
                :op         :local-binding
                :assignable? true)
              (if-let [^Var var (resolve-var sym)]
                {:op         :var
                 :name       (.sym var)
                 :ns         (-> var .ns .name)
                 :assignabe? true
                 :var        var}
                (or (maybe-host-expr sym)
                    (throw (ex-info (str "could not resolve var: " sym) {:var sym})))))]
    (into {:env  env
           :form sym}
          ret)))

(def specials
  '#{def loop* recur if let* letfn* do fn*
     quote var . set! case* import* try catch
     deftype* reify* throw finally new &})

(defn desugar-dot [[op & expr :as form]]
  (if (symbol? op)
    (let [opname (name op)]
      (cond

       (= (first opname) \.)  ; (.foo bar ..)
       (let [[target & args] expr
             target (if (maybe-class target)
                      (with-meta (list 'clojure.core/identity target) {:tag Class})
                      target)]
         (with-meta (list* '. target (symbol (subs opname 1)) args)
           (meta form)))

       (and (namespace op)
                      (maybe-class (namespace op))) ; (class/field ..)
       (let [target (maybe-class (namespace op))]
         (with-meta (list* '. target opname expr)
           (meta form)))

       (= (last opname) \.) ;; (class. ..)
       (list* 'new (symbol (subs opname 0 (dec (count opname)))) expr)

       :else form))
    (if-let [c (maybe-class op)]
      (throw (ex-info (str "expecting var but" form "is mapped to " c) {:form form}))
      form)))

(defn macroexpand-1 [form env]
  (if (seq? form)
    (let [op (first form)]
      (if (specials op)
        form
        (let [v (maybe-var op)]
          (if (and (not (-> env :locals (get op))) ;; locals cannot be macros
                   (:macro (meta v)))
            (apply @v env form (rest form)) ; (m &env &form & args)
            (desugar-dot form)))))
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
          (parse form env) ;; invoke == :default
          (analyze mform env))))))

(defn analyze-block
  "returns {:statements .. :ret ..}"
  [exprs env]
  (let [statements-env (or-eval env :statement)
        statements (mapv (analyze-in-env statements-env)
                         (butlast exprs))
        ret (analyze (last exprs) env)]
    {:statements statements
     :ret        ret}))

(defmethod parse 'do
  [[_ & exprs :as form] env]
  (into {:op   :do
         :env  env
         :form form}
        (analyze-block exprs env)))

(defmethod parse 'if
  [[_ test then [& else] :as form] env]
  {:pre [(or (= 3 (count form))
             (= 4 (count form)))]}
  (let [test (analyze test (or-eval env :expr))
        then (analyze then env)
        else (analyze else env)]
    {:op   :if
     :form form
     :env  env
     :test test
     :then then
     :else else}))

(defmethod parse 'new
  [[_ class & args :as form] env]
  {:pre [(>= (count form) 2)]}
  (if-let [class (maybe-class class)]
    (let [args-env (or-eval env :expr)
          args (mapv (analyze-in-env args-env) args)]
      {:op    :new
       :env   env
       :form  form
       :class class
       :args  args})
    (throw (ex-info (str "class not found: " class) {:class class}))))

(defmethod parse 'var
  [[_ var :as form] env]
  (if-let [var (maybe-var var)]
    {:op   :var
     :env  env
     :form form
     :var  var}
    (throw (ex-info (str "var not found: " var) {:var var}))))

;; clojure parses for empty-colls/numbers/strings
(defmethod parse 'quote
  [[_ expr :as form] env]
  {:op   :constant
   :env  env
   :form form})

(defmethod parse 'set!
  [[_ target val :as form] env]
  {:pre [(= (count form) 3)]}
  (let [target (analyze target (assoc env :context :expr))]
    (if (:assignable? target) ;; + instance fields
      {:op     :set!
       :env    env
       :form   form
       :target target
       :val    val})))

(defmethod parse 'try
  [[_ & body :as form] {:keys [context] :as env}]
  (if-not (= :return context)
    (analyze `((^:once fn* [] ~form)) env) ;; non-return try blocks need to be wrapped in a fn
    (let [catch? (every-pred seq? #(= (first %) 'catch))
          finally? (every-pred seq? #(= (first %) 'finally))
          [body tail] (split-with (complement (some-fn catch? finally?)) body)
          [cblocks tail] (split-with catch? tail)
          [[fblock & fbs :as fblocks] tail] (split-with finally? tail)]
      (when-not (empty? tail)
        (throw (ex-info "only catch or finally clause can follow catch in try expression"
                        {:expr tail})))
      (when-not (empty? fbs)
        (throw (ex-info "only one finally clause allowed in try expression"
                        {:expr fblocks})))
      (let [body (when-not (empty? body)
                   (parse (cons 'do body) (assoc env :in-try true))) ;; avoid recur
            cenv (assoc env :context :expr)
            cblocks (mapv #(parse % cenv) cblocks)
            fblock (parse (cons 'do (rest fblock)) (assoc env :context :statement))]
        {:op      :try
         :env     env
         :form    form
         :body    body
         :catches cblocks
         :finally fblock}))))

(defmethod parse 'catch
  [[_ etype ename & body :as form] env]
  (if-let [ec (maybe-class etype)]
    (if (and (symbol? ename)
             (not (namespace ename)))
      (into (analyze-block body (update-in env [:locals] assoc ename {:name ename}))
            {:op    :catch
             :class ec
             :local ename
             :env   env
             :form  form})
      (throw (ex-info (str "invalid binding form: " ename) {:sym ename})))
    (throw (ex-info (str "unable to resolve classname: " etype) {:class etype}))))
