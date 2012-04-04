(ns clojure.analyzer
  (:refer-clojure :exclude [macroexpand-1 *ns*])
  (:require [clojure.java.io :as io]
            [clojure.string :as string])
  (:use [clojure pprint]))

;; TODO: This is for my convenience when developing, will need to replace this with a real boostrap
(when-not (resolve 'clojure.core/namespaces)
  (in-ns 'clojure.core) 
  (load "core1") 
  (in-ns 'clojure.analyzer) 
  (def ^:dynamic *ns* 'user)
  (refer 'clojure.core :only '[namespaces *warn-on-undeclared*])) 

(def specials '#{quote def fn* if do let* loop* throw try recur new . reify})

(def ^:dynamic *recur-frames* nil)

(defmacro disallowing-recur [& body]
  `(binding [*recur-frames* (cons nil *recur-frames*)] ~@body))

(defmulti parse (fn [op & rest] op))

(declare analyze-symbol analyze-seq analyze-map analyze-vector analyze-set)

(defn analyze
  "Given an environment, a map containing {:locals (mapping of names to bindings), :context
(one of :statement, :expr, :return), :ns (a symbol naming the
compilation ns)}, and form, returns an expression object (a map
containing at least :form, :op and :env keys)."
  ([form] (analyze {:ns (@namespaces *ns*) :context :statement :locals {}} form nil))
  ([env form] (analyze env form nil))
  ([env form name]
   (let [form
         (if (instance? clojure.lang.LazySeq form)
           (or (seq form) ())
           form)]
     (cond
       (symbol? form) (analyze-symbol env form)
       (and (seq? form) (seq form)) (analyze-seq env form name)
       (map? form) (analyze-map env form name)
       (vector? form) (analyze-vector env form name)
       (set? form) (analyze-set env form name)
       :else {:op :constant :env env :form form}))))

(defn analyze-block
  "returns {:statements .. :ret ..}"
  [env exprs]
  (let [statements (disallowing-recur
    (seq (map #(analyze (assoc env :context :statement ) %) (butlast exprs))))
        ret (if (<= (count exprs) 1)
      (analyze env (first exprs))
      (analyze (assoc env :context (if (= :statement (:context env)) :statement :return )) (last exprs)))]
    {:statements statements :ret ret}))

;; TODO: This could be children-keys that just returns the keys of the children, then walk would probably
;             be simple to implement in terms of that
(defmulti children :op)
(defmulti walk (fn [form f] (:op form)))

(defn- walk-coll [f]
  (fn [coll]
    (into (empty coll) (map f coll))))

(defn analyze-file
  [f]
  (let [res (or (io/resource f) (io/as-url (io/as-file f)))]
    (assert res (str "Can't find " f " in classpath"))
    (binding [*file* (.getPath res)]
      (with-open [r (io/reader res)]
        (let [env {:ns (@namespaces *ns*) :context :statement :locals {}}
              pbr (clojure.lang.LineNumberingPushbackReader. r)
              eof (Object.)]
          (loop [r (read pbr false eof false) ret []]
            (let [env (assoc env :ns (@namespaces *ns*))]
              (if-not (identical? eof r)
                (recur (read pbr false eof false) (conj ret (analyze env r)))
                ret))))))))

(defmacro ^:private debug-prn
  [& args]
  `(.println System/err (str ~@args)))

(defn confirm-var-exists [env prefix suffix]
  (when *warn-on-undeclared*
    (let [crnt-ns (-> env :ns :name )]
      (when (= prefix crnt-ns)
        (when-not (-> @namespaces crnt-ns :defs suffix)
          (debug-prn
            "WARNING: Use of undeclared Var " prefix " / " suffix
            (when (:line env)
              (str " at line " (:line env)))))))))

(defn resolve-ns-alias [env name]
  (let [sym (symbol name)]
    (get (:requires (:ns env)) sym sym)))

(defn core-name?
  "Is sym visible from core in the current compilation namespace?"
  [env sym]
  (and (get (:defs (@namespaces 'clojure.core)) sym)
    (not (contains? (-> env :ns :excludes ) sym))))

(defn make-symbol [ns sym]
  (symbol (str ns) (str sym)))

(defn resolve-var
  ([env sym] (resolve-var env sym (fn [env ns sym] (make-symbol ns sym))))
  ([env sym var-fn]
  (let [s (str sym)
        lb (-> env :locals sym)
        nm
        (cond
          lb (:name lb)

          (namespace sym)
          (let [ns (namespace sym)
                full-ns (resolve-ns-alias env ns)]
            (var-fn env full-ns (name sym)))

          (.contains s ".")
          (let [idx (.indexOf s ".")
                prefix (symbol (subs s 0 idx))
                suffix (subs s idx)
                lb (-> env :locals prefix)]
            (if lb
              (symbol (str (:name lb) suffix))
              (do
                (var-fn env prefix (symbol suffix))
                sym)))

          (get-in @namespaces [(-> env :ns :name ) :uses sym])
          (var-fn env (get-in @namespaces [(-> env :ns :name) :uses sym]) (name sym))

          :else
          (let [full-ns (if (core-name? env sym) 'clojure.core (-> env :ns :name))]
            (var-fn env full-ns sym)))]
    {:name nm})))

(defn resolve-existing-var [env sym]
  (resolve-var env sym
    (fn [env ns sym]
      (confirm-var-exists env ns sym)
      (make-symbol ns sym))))

(defn parse-invoke
  [env [f & args]]
  (disallowing-recur
    (let [enve (assoc env :context :expr )
          fexpr (analyze enve f)
          argexprs (vec (map #(analyze enve %) args))]
      {:env env :op :invoke :f fexpr :args argexprs})))

(defmethod children :invoke
  [{:keys [f args]}]
  (conj args f))

(defmethod walk :invoke
  [form f]
  (-> form
    (update-in [:f] f)
    (update-in [:args] (walk-coll f))))

(defn analyze-symbol
  "Finds the var associated with sym"
  [env sym]
  (let [ret {:env env :form sym}
        lb (-> env :locals sym)]
    (if lb
      (assoc ret :op :var :info lb)
      (assoc ret :op :var :info (resolve-existing-var env sym)))))

(defmethod children :var
  [form]
  nil)

(defmethod walk :var [form f] form)

(defn get-expander [sym env]
  (let [mvar
        (when-not (or (-> env :locals sym) ;locals hide macros
                      (-> env :ns :excludes sym))
          (if-let [nstr (namespace sym)]
            (when-let [ns (find-ns (symbol nstr))]
              (.findInternedVar ^clojure.lang.Namespace ns (symbol (name sym))))
            (if-let [nsym (-> env :ns :defs sym)]
              (.findInternedVar ^clojure.lang.Namespace (find-ns nsym) sym)
              (.findInternedVar ^clojure.lang.Namespace (find-ns 'clojure.core) sym))))]
    (when (and mvar (.isMacro ^clojure.lang.Var mvar))
      @mvar)))

(defn macroexpand-1 [env form]
  (let [op (first form)]
    (if (specials op)
      form
      (if-let [mac (and (symbol? op) (get-expander op env))]
        (apply mac form env (rest form))
        (if (symbol? op)
          (let [opname (str op)]
            (cond
              (= (first opname) \.) (let [[target & args] (next form)]
                                      (list* '. target (symbol (subs opname 1)) args))
              (= (last opname) \.) (list* 'new (symbol (subs opname 0 (dec (count opname)))) (next form))
              :else form))
          form)))))

(defn analyze-seq
  [env form name]
  (let [env (assoc env :line (or (-> form meta :line )
                                 (:line env)))]
    (let [op (first form)]
      (assert (not (nil? op)) "Can't call nil")
      (let [mform (macroexpand-1 env form)]
        (if (identical? form mform)
          (if (specials op)
            (parse op env form name)
            (parse-invoke env form))
          (analyze env mform name))))))

(declare analyze-wrap-meta)

(defn analyze-map
  [env form name]
  (let [expr-env (assoc env :context :expr )
        simple-keys? (every? #(or (string? %) (keyword? %)) (keys form))
        ks (disallowing-recur (vec (map #(analyze expr-env % name) (keys form))))
        vs (disallowing-recur (vec (map #(analyze expr-env % name) (vals form))))]
    (analyze-wrap-meta {:op :map :env env :form form
                        :keys ks :vals vs :simple-keys? simple-keys?}
      name)))

(defmethod children :map
  [{:keys [keys vals]}]
  (concat keys vals))

(defmethod walk :map
  [form f]
  (-> form
    (update-in [:keys] (walk-coll f))
    (update-in [:vals] (walk-coll f))))

(defn analyze-vector
  [env form name]
  (let [expr-env (assoc env :context :expr )
        items (disallowing-recur (vec (map #(analyze expr-env % name) form)))]
    (analyze-wrap-meta {:op :vector :env env :form form :children items} name)))

(defmethod children :vector
  [form]
  (:children form))

(defmethod walk :vector
  [form f]
  (update-in form [:children] (walk-coll f)))

(defn analyze-wrap-meta [expr name]
  (let [form (:form expr)]
    (if (meta form)
      (let [env (:env expr) ; take on expr's context ourselves
            expr (assoc-in expr [:env :context ] :expr ) ; change expr to :expr
            meta-expr (analyze-map (:env expr) (meta form) name)]
        {:op :meta :env env :form form
         :meta meta-expr :expr expr})
      expr)))

(defmethod children :meta
  [{:keys [meta-expr expr]}]
  [meta-expr expr])

(defmethod walk :meta
  [form f]
  (-> form
    (update-in [:meta-expr] f)
    (update-in [:meta] f)))

(defmethod parse 'if
  [op env [_ test then else :as form] name]
  (let [test-expr (disallowing-recur (analyze (assoc env :context :expr) test))
        then-expr (analyze env then)
        else-expr (analyze env else)]
    {:env env :op :if :form form :test test-expr :then then-expr :else else-expr}))

(defmethod children :if
  [{:keys [test then else]}]
  [test then else])

(defmethod walk :if
  [form f]
  (-> form
    (update-in [:test] f)
    (update-in [:then] f)
    (update-in [:else] f)))

(defmethod parse 'throw
  [op env [_ throw :as form] name]
  (let [throw-expr (disallowing-recur (analyze (assoc env :context :expr) throw))]
    {:env env :op :throw :form form
     :throw throw-expr}))

(defmethod children :throw
  [{:keys [throw]}]
  [throw])

(defmethod walk :throw
  [form f]
  (update-in form [:throw] f))

(defmethod parse 'try
  [op env [_ & body :as form] name]
  (let [catch? #(and (list? %) (= (first %) 'catch))
        finally? #(and (list? %) (= (first %) 'finally))
        [body tail] (split-with (complement #(or (catch? %) (finally? %))) body)
        [cblocks [fblock]] (split-with catch? tail)
        catchenv (update-in env [:context] #(if (= :expr %) :return %))
        try (when body
              (assoc (analyze-block (if (or cblocks fblock) catchenv env) body) :op :do))
        catches (into [] 
                  (map 
                    (fn [[ _ type name & cb]] 
                      (let [locals (:locals catchenv)
                            locals (if name
                                     (assoc locals name {:name name})
                                     locals)]
                      (assoc (analyze-block (assoc catchenv :locals locals) cb) :op :do :catch-type type :catch-local name)))
                   cblocks))
        finally (when (seq fblock)  
                  (assoc (analyze-block (assoc env :context :statement) (rest fblock)) :op :do))]
    (when name (assert (not (namespace name)) "Can't qualify symbol in catch"))
    {:env env :op :try :form form
     :try try
     :finally finally
     :name name
     :catches catches}))

(defmethod children :try
  [{:keys [try catches finally]}]
  (let [ret (conj catches try)]
    (if finally
      (cons finally ret)
      ret)))

(defmethod walk :try
  [form f]
  (let [form (-> form
               (update-in [:try] f)  
               (update-in [:catches] (walk-coll f)))]
    (if-let [finally (:finally form)]
      (assoc form :finally (f finally))
      form)))

(defmethod parse 'def
  [op env form name]
  (let [pfn (fn
              ([_ sym] {:sym sym})
              ([_ sym init] {:sym sym :init init})
              ([_ sym doc init] {:sym sym :doc doc :init init}))
        args (apply pfn form)
        sym (:sym args)]
    (assert (not (namespace sym)) "Can't def ns-qualified name")
    (let [name (:name (resolve-var (dissoc env :locals ) sym))
          init-expr (when (contains? args :init ) (disallowing-recur
                                                    (analyze (assoc env :context :expr ) (:init args) sym)))
          export-as (when-let [export-val (-> sym meta :export )]
        (if (= true export-val) name export-val))
          doc (or (:doc args) (-> sym meta :doc ))]
      (swap! namespaces update-in [(-> env :ns :name ) :defs sym]
                        (fn [m]
                          (let [m (assoc (or m {}) :name name)]
                            (if-let [line (:line env)]
                              (-> m
                                (assoc :file *file*)
                                (assoc :line line))
                              m))))
      (merge {:env env :op :def :form form
              :name name :doc doc :init init-expr}
        (when export-as {:export export-as})))))

(defmethod children :def
  [{:keys [init]}]
  (when init [init]))

(defmethod walk :def
  [form f]
  (if-let [init (:init form)]
    (assoc form :init (f init))
    form))

(defn- analyze-fn-method [env locals meth]
  (letfn [(uniqify [[p & r]]
            (when p
              (cons (if (some #{p} r) (gensym (str p)) p)
                (uniqify r))))]
    (let [params (first meth)
          fields (-> params meta ::fields )
          variadic (boolean (some '#{&} params))
          params (uniqify (remove '#{&} params))
          fixed-arity (count (if variadic (butlast params) params))
          body (next meth)
          locals (reduce (fn [m name] (assoc m name {:name name})) locals params)
          recur-frame {:names (vec params) :flag (atom nil)}
          block (binding [*recur-frames* (cons recur-frame *recur-frames*)]
                  (analyze-block (assoc env :context :return :locals locals) body))]

      (merge {:env env :op :method :variadic variadic :params params
              :max-fixed-arity fixed-arity :recurs @(:flag recur-frame)} block))))

(defmethod children :method
  [{:keys [statements ret]}]
  (cons ret statements))

(defmethod walk :method
  [form f]
  (-> form
    (update-in [:statements] (walk-coll f))
    (update-in [:ret] f)))

(defmethod parse 'fn*
  [op env [_ & args] name]
  (let [[name meths] (if (symbol? (first args))
                       [(first args) (next args)]
                       [name (seq args)])
        ;;turn (fn [] ...) into (fn ([]...))
        meths (if (vector? (first meths)) (list meths) meths)
        locals (:locals env)
        locals (if name (assoc locals name {:name name :this true}) locals)
        env (assoc env :locals locals)
        menv (if (> (count meths) 1) (assoc env :context :expr ) env)
        methods (map #(analyze-fn-method menv locals %) meths)
        max-fixed-arity (apply max (map :max-fixed-arity methods))
        variadic (boolean (some :variadic methods))]
    ;;todo - validate unique arities, at most one variadic, variadic takes max required args
    {:env env :op :fn :name name :methods methods :variadic variadic :recur-frames *recur-frames*
     :max-fixed-arity max-fixed-arity}))

(defmethod children :fn
  [{:keys [methods]}]
  methods)

(defmethod walk :fn
  [form f]
  (update-in form [:methods] (walk-coll f)))

(defmethod parse 'do
  [op env [_ & exprs] _]
  (merge {:env env :op :do} (analyze-block env exprs)))

(defmethod children :do
  [{:keys [statements ret]}]
  (cons ret statements))

(defmethod walk :do
  [form f]
  (-> form
    (update-in [:statements] (walk-coll f))
    (update-in [:ret] f)))

(defn analyze-let
  [encl-env [_ bindings & exprs :as form] is-loop]
  (assert (and (vector? bindings) (even? (count bindings))) "bindings must be vector of even number of elements")
  (let [context (:context encl-env)
        [bes env]
        (disallowing-recur
          (loop [bes []
                 env (assoc encl-env :context :expr)
                 bindings (seq (partition 2 bindings))]
            (if-let [[name init] (first bindings)]
              (do
                (assert (not (or (namespace name) (.contains (str name) "."))) (str "Invalid local name: " name))
                (let [init-expr (analyze env init)
                      be {:name name :op :binding :init init-expr}]
                  (recur (conj bes be)
                    (assoc-in env [:locals name] be)
                    (next bindings))))
              [bes env])))
        recur-frame (when is-loop {:names (vec (map :name bes)) :flag (atom nil)})
        {:keys [statements ret]}
        (binding [*recur-frames* (if recur-frame (cons recur-frame *recur-frames*) *recur-frames*)]
          (analyze-block (assoc env :context (if (= :expr context) :return context)) exprs))]
    {:env encl-env :op :let :loop is-loop
     :bindings bes :statements statements :ret ret :form form}))

(defmethod children :binding
  [{:keys [init]}]
  [init])

(defmethod walk :binding
  [form f]
  (update-in form [:init] f))

(defmethod children :let
  [{:keys [bindings statements ret]}]
  (-> ret (cons statements) (concat bindings)))

(defmethod walk :let
  [form f]
  (-> form
    (update-in [:bindings] (walk-coll f))
    (update-in [:statements] (walk-coll f))
    (update-in [:ret] f)))

(defmethod parse 'let*
  [op encl-env form _]
  (analyze-let encl-env form false))

(defmethod parse 'loop*
  [op encl-env form _]
  (analyze-let encl-env form true))

(defmethod parse 'recur
  [op env [_ & exprs] _]
  (let [context (:context env)
        frame (first *recur-frames*)]
    (assert frame "Can't recur here")
    (assert (= (count exprs) (count (:names frame))) "recur argument count mismatch")
    (reset! (:flag frame) true)
    (assoc {:env env :op :recur}
      :frame frame
      :exprs (disallowing-recur (vec (map #(analyze (assoc env :context :expr) %) exprs))))))

(defmethod children :recur
  [{:keys [exprs]}]
  exprs)

(defmethod walk :recur
  [form f]
  (update-in form [:exprs] (walk-coll f)))

(defmethod parse 'quote
  [_ env [_ x] _]
  {:op :constant :env env :form x})

(defmethod children :constant
  [form]
  nil)

(defmethod walk :constant
  [form f]
  form)

(defmethod parse 'new
  [_ env [_ ctor & args] _]
  (disallowing-recur
    (let [enve (assoc env :context :expr)
          ctorexpr (analyze enve ctor)
          argexprs (vec (map #(analyze enve %) args))]
      {:env env :op :new :ctor ctorexpr :args argexprs})))

(defmethod children :new
  [{:keys [args ctor]}]
  (conj args ctor))

(defmethod walk :new
  [form f]
  (-> form
    (update-in [:args] (walk-coll f))
    (update-in [:ctor] f)))

(defmethod parse 'ns
  [_ env [_ name & args] _]
  (let [excludes
        (reduce (fn [s [k exclude xs]]
                  (if (= k :refer-clojure)
                    (do
                      (assert (= exclude :exclude) "Only [:refer-clojure :exclude [names]] form supported")
                      (into s xs))
                    s))
                #{} args)
        {uses :use requires :require :as params}
        (reduce (fn [m [k & libs]]
                  (assert (#{:use :require} k)
                          "Only :refer-clojure, :require, :use libspecs supported")
                  (assoc m k 
                    (into {}
                          (mapcat
                            (fn [[lib kw expr]]
                                (case k
                                  (:require)
                                  (do (assert (and expr (= :as kw))
                                              "Only (:require [lib.ns :as alias]*) form of :require is supported")
                                    [[expr lib]])
                                  (:use)
                                  (do (assert (and expr (= :only kw))
                                              "Only (:use [lib.ns :only [names]]*) form of :use is supported")
                                    (map vector expr (repeat lib)))))
                            libs))))
                {} (remove (fn [[r]] (= r :refer-clojure)) args))]
    (set! *ns* name)
    (require 'clojure.core)
    (swap! namespaces #(-> %
                           (assoc-in [name :name] name)
                           (assoc-in [name :excludes] excludes)
                           (assoc-in [name :uses] uses)
                           (assoc-in [name :requires] requires)))
    {:env env :op :ns :name name :uses uses :requires requires :excludes excludes}))

(defmethod children :ns
  [form]
  nil)

(defmethod walk :ns
  [form f]
  form)

;; dot accessor code

(def ^:private property-symbol? #(boolean (and (symbol? %) (re-matches #"^-.*" (name %)))))

(defn- clean-symbol
  [sym]
  (if (property-symbol? sym)
    (-> sym name (.substring 1) symbol)
    sym))

(defn- classify-dot-form
  [[target member args]]
  [(cond (nil? target) ::error
                       :default      ::expr)
   (cond (property-symbol? member) ::property
                                   (symbol? member)          ::symbol
                                   (seq? member)             ::list
                                   :default                  ::error)
   (cond (nil? args) ()
                     :default    ::expr)])

(defmulti build-dot-form #(classify-dot-form %))

;; (. o -p)
;; (. (...) -p)
(defmethod build-dot-form [::expr ::property ()]
  [[target prop _]]
  {:dot-action ::access :target target :field (clean-symbol prop)})

;; (. o -p <args>)
(defmethod build-dot-form [::expr ::property ::list]
  [[target prop args]]
  (throw (Error. (str "Cannot provide arguments " args " on property access " prop))))

(defn- build-method-call
  "Builds the intermediate method call map used to reason about the parsed form during
  compilation."
  [target meth args]
  (if (symbol? meth)
    {:dot-action ::call :target target :method (munge meth) :args args}
    {:dot-action ::call :target target :method (munge (first meth)) :args args}))

;; (. o m 1 2)
(defmethod build-dot-form [::expr ::symbol ::expr]
  [[target meth args]]
  (build-method-call target meth args))

;; (. o m)
(defmethod build-dot-form [::expr ::symbol ()]
  [[target meth args]]
; TODO: I think this warning was only for clojurescript
;  (debug-prn "WARNING: The form " (list '. target meth)
;                                  " is no longer a property access. Maybe you meant "
;                                  (list '. target (symbol (str '- meth))) " instead?")
  (build-method-call target meth args))

;; (. o (m))
;; (. o (m 1 2))
(defmethod build-dot-form [::expr ::list ()]
  [[target meth-expr _]]
  (build-method-call target (first meth-expr) (rest meth-expr)))

(defmethod build-dot-form :default
  [dot-form]
  (throw (Error. (str "Unknown dot form of " (list* '. dot-form) " with classification " (classify-dot-form dot-form)))))

(defmethod parse '.
  [_ env [_ target & [field & member+]] _]
  (disallowing-recur
    (let [{:keys [dot-action target method field args]} (build-dot-form [target field member+])
          enve        (assoc env :context :expr)
          targetexpr  (analyze enve target)]
      (case dot-action
        ::access {:env env :op :dot
                  :target targetexpr
                  :field field}
        ::call   (let [argexprs (map #(analyze enve %) args)]
        {:env env :op :dot
         :target targetexpr
         :method method
         :args argexprs})))))

(defmethod children :dot
  [{:keys [target args]}]
  (cons target args))

(defmethod walk :dot
  [form f]
  (-> form
    (update-in [:target] f)
    (update-in [:args] (walk-coll f))))

(defn analyze-method-impls
  [env meth]
  (let [name (or (first meth) (throw (Error. "Must specify a method to implement")))
        params (fnext meth)
        this (or (first params) (throw (Error. (str "Must supply at least one argument for 'this' in: " name))))
        params (next params)
        meth (cons params (nnext meth))
        locals (assoc (:locals env) this {:name this :this true})
        env (assoc env :locals locals)
        method (analyze-fn-method env locals meth)]
    (assoc method :name name)))

(defmethod parse 'reify
  [op env [_ & args] _]
  (let [aargs (map #(if (symbol? %) % (analyze-method-impls env %)) args)
        m (apply hash-map (partition-by symbol? aargs))
        ancestors (map first (keys m))
        methods (reduce into []
                   (for [[[class] meths] m]
                     (for [meth meths]
                       (assoc meth :class class))))]
    {:env env :op :reify :opts {} :methods methods :ancestors ancestors}))

(defmethod children :reify
  [{:keys [methods]}]
  methods)

(defmethod walk :reify
  [form f]
  (update-in form [:methods] (walk-coll f)))
