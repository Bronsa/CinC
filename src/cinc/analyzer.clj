(ns cinc.analyzer
  "Utilities for host-agnostic analysis of clojure forms"
  (:refer-clojure :exclude [macroexpand-1 macroexpand])
  (:require [cinc.analyzer.utils :refer :all]
            [clojure.java.io :as io]
            [clojure.tools.reader :as r]
            [clojure.tools.reader.reader-types :as rt])
  (:import (clojure.lang LazySeq Var)))

(defmulti -analyze (fn [op form env & _] op))
(defmulti parse (fn [[op & form] & rest] op))

(defn analyze
  "Given an environment, a map containing
   -  :locals (mapping of names to lexical bindings),
   -  :context (one of :statement, :expr or :return
 and form, returns an expression object (a map containing at least :form, :op and :env keys)."
  [form {:keys [context] :as env}]
  (let [form (if (instance? LazySeq form)
               (or (seq form) ())      ; we need to force evaluation in order to analyze
               form)]
    (case form

      nil              (-analyze :const form env :nil)
      (true false)     (-analyze :const form env :bool)

      (cond

       (symbol? form)   (-analyze :symbol form env)

       (type? form)     (-analyze :const  form env :type)
       (record? form)   (-analyze :const  form env :record)

       (seq? form)      (-analyze :seq    form env)
       (vector? form)   (-analyze :vector form env)
       (map? form)      (-analyze :map    form env)
       (set? form)      (-analyze :set    form env)

       :else            (-analyze :const  form env)))))

(defn analyze-file
  ([file] (analyze-file file analyze))
  ([file analyze]
     (let [res (or (io/resource file) (io/as-url (io/as-file file)))]
       (assert res (str "Can't find " file " in classpath"))
       (binding [*file* (.getPath res)]
         (with-open [r (io/input-stream res)]
           (let [env {:context :statement :locals {}}
                 pbr (rt/indexing-push-back-reader
                      (rt/input-stream-push-back-reader r))]
             (loop [r (r/read pbr false ::eof false) ret []]
               (if-not (identical? ::eof r)
                 (recur (r/read pbr false ::eof false) (conj ret (analyze r env)))
                 ret))))))))

(defn analyze-in-env
  "Given an env returns a function that when called with an argument
   analyzes that argument in the specified env"
  [env]
  (fn [form] (analyze form env)))

(defn wrapping-meta [{:keys [form env] :as expr}]
  (let [meta (dissoc (meta form) :line :column :file)
        quoted? (::quoted meta)
        quoted-meta (if quoted? (list 'quote (dissoc meta ::quoted)) meta)]
    (if (and (seq meta)
             (obj? form))
      {:op   :with-meta
       :env  env
       :form form
       :meta (analyze quoted-meta (ctx env :expr))
       :expr (assoc-in expr [:env :context] :expr)}
     expr)))

(defmethod -analyze :const
  [_ form env & [type]]
  (let [type (or type (classify form))]
   (wrapping-meta
    {:op       :const
     :env      env
     :type     type
     :literal? true
     :form     form})))

(defmethod -analyze :vector
  [_ form env]
  (let [items-env (ctx env :expr)
        items (mapv (analyze-in-env items-env) form)]
    (wrapping-meta
     {:op    :vector
      :env   env
      :items items
      :form  form})))

(defmethod -analyze :map
  [_ form env]
  (let [kv-env (ctx env :expr)
        keys (keys form)
        vals (vals form)
        [ks vs] (map (partial mapv (analyze-in-env kv-env)) [keys vals])]
    (wrapping-meta
     {:op   :map
      :env  env
      :keys ks
      :vals vs
      :form form})))

(defmethod -analyze :set
  [_ form env]
  (let [items-env (ctx env :expr)
        items (mapv (analyze-in-env items-env) form)]
    (wrapping-meta
     {:op    :set
      :env   env
      :items items
      :form  form})))

(def specials
  '#{do if new var quote set! try
     catch throw finally
     let* letfn* loop* recur fn* case*
     & def . deftype* reify*})

(defn desugar-host-expr [[op & expr :as form]]
  (if (symbol? op)
    (let [opname (name op)]
      (cond

       (= (first opname) \.)         ; (.foo bar ..)
       (let [[target & args] expr
             args (list* (symbol (subs opname 1)) args)]
         (with-meta (list '. target (if (= 1 (count args)) ;; we don't know if (.foo bar) ia
                                      (first args) args))  ;; a method call or a field access
           (meta form)))

       (= (last opname) \.) ;; (class. ..)
       (with-meta (list* 'new (symbol (subs opname 0 (dec (count opname)))) expr)
         (meta form))

       :else form))
    form))

;; we only know about namespaces and vars, no class information available
;; true macroexpansion will be host-dependent
(defn ^:dynamic macroexpand-1 [form env]
  (if (seq? form)
    (let [op (first form)]
      (if (specials op) ;; how do we handle host-specific specials? (e.g clojurescript ns)
        form
        (let [v (maybe-var op)]
          (if (and (not (-> env :locals (get op))) ;; locals cannot be macros
                   (:macro (meta v)))
            (apply @v env form (rest form)) ; (m &env &form & args)
            (desugar-host-expr form)))))
    form))

(defn macroexpand
  [form env]
  (let [ex (macroexpand-1 form env)]
    (if (identical? ex form)
      form
      (macroexpand ex env))))

;; preserve meta
;; ^:const vars will be detected in a second pass
;; will eventually move out constant colls detection to that pass too
(defmethod -analyze :symbol
  [_ sym env]
  (let [mform (macroexpand-1 sym env)]
    (if (symbol? mform)
      (merge (if-let [local-binding (-> env :locals sym)]
               (assoc local-binding
                 :op          :local
                 :assignable? (boolean (:mutable local-binding)))
               (if-let [^Var var (resolve-var sym)]
                 {:op          :var
                  :name        (.sym var)
                  :ns          (-> var .ns .name)
                  :assignable? (thread-bound? var)
                  :var         var}
                 (if-let [maybe-class (namespace sym)] ;; e.g. js/foo.bar or Long/MAX_VALUE
                   (let [maybe-class (symbol maybe-class)]
                     (if-not (find-ns maybe-class)
                       {:op          :maybe-host-form
                        :maybe-class maybe-class
                        :maybe-field (symbol (name sym))}
                       (throw (ex-info (str "could not resolve var: " sym)
                                       {:var sym}))))
                   {:op          :maybe-class ;; e.g. java.lang.Integer or Long
                    :maybe-class sym})))
             {:env  env
              :form sym})
      (analyze mform env))))

(defmethod -analyze :seq
  [_ form env]
  (let [env (into env (source-info form env))]
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
  (let [statements-env (ctx env :statement)
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
  [[_ test then & [else] :as form] env]
  {:pre [(or (= 3 (count form))
             (= 4 (count form)))]}
  (let [test-expr (analyze test (ctx env :expr))
        then-expr (analyze then env)
        else-expr (analyze else env)]
    (merge {:op   :if
            :form form
            :env  env
            :test test-expr
            :then then-expr}
           (when else
             {:else else-expr}))))

(defmethod parse 'new
  [[_ class & args :as form] env]
  {:pre [(>= (count form) 2)]}
  (let [args-env (ctx env :expr)
        args (mapv (analyze-in-env args-env) args)]
    {:op          :new
     :env         env
     :form        form
     :maybe-class class
     :args        args}))

(defmethod parse 'var
  [[_ var :as form] env]
  (if-let [var (maybe-var var)]
    {:op   :the-var
     :env  env
     :form form
     :var  var}
    (throw (ex-info (str "var not found: " var) {:var var}))))

(defmethod parse 'quote
  [[_ expr :as form] env]
  (let [expr (if-let [m (meta expr)]
               (with-meta expr (assoc m ::quoted true))
               expr)]
    (-analyze :const expr env)))

(defmethod parse 'set!
  [[_ target val :as form] env]
  {:pre [(= (count form) 3)]}
  (let [target (analyze target (ctx env :expr))
        val (analyze val (ctx env :expr))]
    (if (:assignable? target) ;; + fields
      {:op     :set!
       :env    env
       :form   form
       :target target
       :val    val}
      (throw (ex-info "cannot set! non-assignable target" {:target target})))))

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
            cenv (ctx env :expr)
            cblocks (mapv #(parse % cenv) cblocks)
            fblock (parse (cons 'do (rest fblock)) (ctx env :statement))]
        {:op      :try
         :env     env
         :form    form
         :body    body
         :catches cblocks
         :finally fblock}))))

(defmethod parse 'catch
  [[_ etype ename & body :as form] env]
  (if (and (symbol? ename)
           (not (namespace ename)))
    {:op          :catch
     :maybe-class etype
     :local       ename
     :env         env
     :form        form
     :body        (parse (cons 'do body) (assoc-in env [:locals ename]
                                                   (merge {:env (source-info ename env)}
                                                          {:op   :binding
                                                           :name ename
                                                           :tag  etype})))}
    (throw (ex-info (str "invalid binding form: " ename) {:sym ename}))))

(defmethod parse 'throw
  [[_ throw :as form] env]
  {:op        :throw
   :env       env
   :form      form
   :exception (analyze throw (ctx env :expr))})

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
                                   (merge {:env (source-info name env)}
                                    {:op    :binding
                                     :name  name
                                     :form  name
                                     :local true}))
                                 fns))
          e (update-in env [:locals] merge binds)
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
      (analyze `((^:once fn* [] ~form)) env)
      (loop [bindings (seq (partition 2 bindings))
             env (ctx env :expr)
             binds []]
        (if-let [[name init] (first bindings)]
          (do
            (when (or (namespace name)
                      (.contains (str name) "."))
              (throw (ex-info (str "invalid binding form: " name)
                              {:sym name})))
            (let [init-expr (analyze init env)
                  bind-expr (merge {:env (source-info name env)}
                                   {:op    :binding
                                    :name  name
                                    :init  init-expr
                                    :form  name
                                    :local true})]
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
  (let [exprs (mapv (analyze-in-env (ctx env :expr))
                    exprs)]
    {:op    :recur
     :env   env
     :form  form
     :exprs exprs}))

;; second pass with info to check arity?
(defn analyze-fn-method [[params & body :as form] {:keys [locals] :as env}]
  {:pre [(every? symbol? params)
         (not-any? namespace params)]}
  (let [variadic? (boolean (some '#{&} params))
        params-names (vec (remove '#{&} params))
        params-expr (mapv (fn [name]
                            {:env  (source-info name env)
                             :form name
                             :name name
                             :op   :binding
                             :arg  true})
                          params-names)
        arity (count params-names)
        fixed-arity (if variadic?
                      (dec arity)
                      arity)
        body-env (into (update-in env [:locals]
                                  merge (zipmap params-names params-expr))
                       {:context     :return
                        :loop-locals params-expr})
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

;; TODO name generation
(defmethod parse 'fn*
  [[_ & args :as form] {:keys [name] :as env}]
  (let [[name meths] (if (symbol? (first args))
                       [(first args) (next args)]
                       [name (seq args)])
        e (if name (assoc-in env [:locals name] {:name name}) env)
        meths (if (vector? (first meths)) (list meths) meths) ;;turn (fn [] ...) into (fn ([]...))
        menv (if (> (count meths) 1) (ctx env :expr) e)
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

(defmethod parse 'case*
  [[_ expr shift mask default case-map switch-type test-type & [skip-check?] :as form] env]
  (let [[low high] ((juxt first last) (keys case-map))
        test-expr (analyze expr (ctx env :expr))
        [tests thens] (reduce (fn [[te th] [min-hash [test then]]]
                                (let [test-expr (analyze (list 'quote test) env)
                                      then-expr (analyze then env)]
                                  [(conj te test-expr) (conj th then-expr)]))
                              [(sorted-map) {}] case-map)
        default-expr (analyze default env)]
    {:op          :case
     :form        form
     :env         env
     :test        test-expr
     :default     default-expr
     :tests       tests
     :thens       thens
     :shift       shift
     :mask        mask
     :low         low
     :high        high
     :switch-type switch-type
     :test-type   test-type
     :skip-check? skip-check?}))

(defmethod parse 'def
  [[_ sym & expr :as form] env]
  {:pre [(symbol? sym)
         (or (not (namespace sym))
             (= *ns* (the-ns (namespace sym))))]}
  (let [pfn (fn
              ([])
              ([init]
                 {:init init})
              ([doc init]
                 {:pre [(string? doc)]}
                 {:init init :doc doc}))
        args (apply pfn expr)
        doc (or (:doc args) (-> sym meta :doc))
        meta ((fnil merge {}) (meta sym) (when doc {:doc doc}))
        meta-expr (analyze meta (ctx env :expr))
        var (doto (intern *ns* sym)
              (reset-meta! meta))
        args (when-let [[_ init] (find args :init)]
               {:init (analyze init (ctx env :expr))})]
    (merge {:op   :def
            :env  env
            :form form
            :name sym
            :var  var
            :meta meta-expr}
           args)))

(defmethod parse '.
  [[_ target & [m-or-f] :as form] env]
  {:pre [(>= (count form) 3)
         (not (namespace (if (symbol? m-or-f) m-or-f (first m-or-f))))]}
  (let [target-expr (analyze target (ctx env :expr))
        call? (seq? m-or-f)
        expr (if call?
               {:op          :host-call
                :target-expr target-expr
                :method      (first m-or-f)
                :args        (mapv (analyze-in-env (ctx env :expr)) (next m-or-f))}
               {:op          :host-interop ;; either field access or single method call
                :target-expr target-expr
                :m-or-f      m-or-f})]
    (merge {:form form
            :env  env}
           expr)))

;; primitives
;; keyword callsites
;; runtime instanceof for constant exprs
;; invoke
(defmethod parse :default
  [[f & args :as form] env]
  (let [e (ctx env :expr)
        fn-expr (analyze f e)
        args-expr (mapv (analyze-in-env e) args)]
    {:op   :invoke
     :form form
     :env  env
     :meta (analyze (meta form) (ctx env :expr))
     :fn   fn-expr
     :args args-expr}))
