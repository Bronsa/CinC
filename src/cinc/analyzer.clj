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

(defn analyze
  "Given an environment, a map containing
   -  :locals (mapping of names to lexical bindings),
   -  :context (one of :statement, :expr, :return),
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

(defn wrapping-meta [{:keys [form env] :as expr}]
  (if (meta form)
    {:op   :meta
     :env  env
     :form form
     :meta (-analyze :map (meta form) (assoc env :context :expr))
     :expr (assoc-in expr [:env :context] :expr)}
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
  (let [items-env (assoc env :context :expr)
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
  (let [kv-env (assoc env :context :expr)
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
  (let [items-env (assoc env :context :expr)
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
                :op         :local)
;;              :assignable? true ;; only ^:*-mutable
              (if-let [^Var var (resolve-var sym)]
                {:op          :var
                 :name        (.sym var)
                 :ns          (-> var .ns .name)
                 :assignable? true
                 :var         var}
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
  (let [statements-env (assoc env :context :statement)
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
  (let [test (analyze test (assoc env :context :expr))
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
    (let [args-env (assoc env :context :expr)
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
    (if (:assignable? target) ;; + fields
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
      {:op    :catch
       :class ec
       :local ename
       :env   env
       :form  form
       :body  (parse (cons 'do body) (assoc-in env [:locals ename] {:name ename
                                                                    :tag  etype}))}
      (throw (ex-info (str "invalid binding form: " ename) {:sym ename})))
    (throw (ex-info (str "unable to resolve class: " etype) {:class etype}))))

(defmethod parse 'throw
  [[_ throw :as form] env]
  {:op    :throw
   :env   env
   :form  form
   :throw (analyze throw (assoc env :context :expr))})

(defmethod parse 'import*
  [[_ class :as form] env]
  (when-let [class (maybe-class class)]
    {:op    :import
     :env   env
     :form  form
     :class class}
    (ex-info (str "class not found: " class) {:class class})))

(defmethod parse 'letfn*
  [[_ bindings & body :as form] {:keys [context] :as env}]
  {:pre [(vector? bindings)
         (even? (count bindings))]}
  (let [bindings (apply hash-map bindings)
        fns (keys bindings)]
    (when-not (every? #(and (symbol? %)
                       (not (namespace %)))
                 fns)
      (throw (ex-info (str "bad binding form: " (first (remove symbol? fns)))
                      {:form form})))
    (let [binds (zipmap fns (map (fn [name]
                                   {:name name
                                    :local true})
                                 fns))
          e (update-in env [:locals] (fnil into {}) binds)
          binds (mapv (fn [{:keys [name] :as b}]
                        (assoc b
                          :init (analyze (bindings name) (assoc e :context :expr))))
                      (vals binds))
          body (parse (cons 'do body) e)]
      {:op       :letfn
       :env      env
       :form     form
       :bindings binds
       :body     body})))

(defn analyze-let
  [[op bindings & body :as form] {:keys [context] :as env}]
  {:pre [(vector? bindings)
         (even? (count bindings))]}
  (let [loop? (= 'loop* op)]
    (if (and loop?
             (= :expr context))
      (analyze `((^:once fn [] ~form)) env)
      (loop [bindings (seq (partition 2 bindings))
             env (assoc env :context :expr)
             binds []]
        (if-let [[name init] (first bindings)]
          (do
            (when (or (namespace name)
                      (.contains (str name) "."))
              (throw (ex-info (str "invalid binding form: " name)
                              {:sym name})))
            (let [init-expr (analyze init env)
                  bind-expr {:name  name
                             :init  init-expr
                             :local true}]
              (recur (next bindings)
                     (assoc-in env [:locals name] bind-expr)
                     (conj binds bind-expr))))
          (let [body-env (assoc env
                           :context (if (= :expr context)
                                      :return context))
                body (parse (cons 'do body)
                            (if loop?
                              (assoc body-env
                                :loop-locals binds)
                              body-env))]
            {:body     body
             :bindings binds}))))))

(defmethod parse 'let*
  [form env]
  (into {:op   :let
         :form form
         :env  env}
        (analyze-let form env)))

(defmethod parse 'loop*
  [form env]
  (into {:op   :loop
         :form form
         :env  env}
        (analyze-let form env)))

(defmethod parse 'recur
  [[_ & exprs :as form] {:keys [context loop-locals in-try]
                         :as env}]
  {:pre [(= :return context)
         loop-locals
         (not in-try)
         (= (count exprs) (count loop-locals))]}
  (let [exprs (mapv (analyze-in-env (assoc env :context :expr))
                    exprs)]
    {:op    :recur
     :env   env
     :form  form
     :exprs exprs}))

(defn analyze-fn-method [[params & body :as form] {:keys [locals] :as env}]
  {:pre [(every? symbol? params)
         (not-any? namespace params)]}
  (let [variadic? (boolean (some '#{&} params))
        params-names (vec (remove '#{&} params))
        params-expr (mapv (fn [name]
                            {:name name})
                          params-names)
        arity (count params-names)
        fixed-arity (if variadic?
                      (dec arity)
                      arity)
        body-env (assoc (update-in env [:locals] (fnil into {})
                                   (zipmap params-names params-expr))
                   :context :return)
        body (parse (cons 'do body) body-env)]
    (when variadic?
      (let [x (drop-while #(not= % '&) params)]
        (when (not= 2 (count x))
          (throw (ex-info (str "unexpected parameter: " (first (drop 2 x)))
                          {:params params})))))
    {:op          :fn-method
     :form        form
     :env         env
     :variadic?   variadic?
     :params      params-expr
     :fixed-arity fixed-arity
     :body        body}))

(defmethod parse 'fn*
  [[_ & args :as form] {:keys [name] :as env}]
  (let [[name meths] (if (symbol? (first args))
                       [(first args) (next args)]
                       [name (seq args)])
        e (if name (assoc-in env [:locals name] {:name name}) env)
        meths (if (vector? (first meths)) (list meths) meths) ;;turn (fn [] ...) into (fn ([]...))
        menv (if (> (count meths) 1) (assoc env :context :expr) e)
        methods-exprs (mapv #(analyze-fn-method % menv) meths)
        variadic (seq (filter :variadic? methods-exprs))
        variadic? (boolean variadic)
        fixed-arities (map :fixed-arity (remove :variadic? methods-exprs))
        max-fixed-arity (apply max fixed-arities)]
    (when (>= (count variadic) 2)
      (throw (ex-info "can't have more than 1 variadic overload"
                      {:variadics (mapv :form variadic)})))
    (when (not= (distinct fixed-arities) fixed-arities)
      (throw (ex-info "can't have 2 overloads with the same arity"
                      {:form form})))
    (when (and variadic?
               (not-every? #(<= (:fixed-arity %)
                          (:fixed-arity (first variadic)))
                      (remove :variadic? methods-exprs)))
      (throw (ex-info "Can't have fixed arity function with more params than variadic function"
                      {:form form})))
    {:op              :fn
     :env             env
     :form            form
     :name            name
     :variadic?       variadic?
     :max-fixed-arity max-fixed-arity
     :methods         methods-exprs}))
