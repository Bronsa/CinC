(ns clojure.analyzer
  (:refer-clojure :exclude [*ns* *file* macroexpand-1])
  (:require [clojure.java.io :as io]
   [clojure.string :as string])
  (:use [clojure pprint]))

(let [mappings (.getMappings (clojure.lang.Namespace/find 'clojure.core))]
  (defonce namespaces (atom {'clojure.core {:name 'clojure.core :defs mappings}
                             'user {:name 'user}}))
  )

(def ^:dynamic *ns* 'user)
(def ^:dynamic *file* nil)
(def ^:dynamic *warn-on-undeclared* false)

(def specials '#{if def fn* let* loop* recur . reify})

(def ^:dynamic *recur-frames* nil)

(defmacro disallowing-recur [& body]
  `(binding [*recur-frames* (cons nil *recur-frames*)] ~@body))

(defmulti parse (fn [op & rest] op))

(declare analyze-symbol analyze-seq analyze-map analyze-vector analyze-set)

(defn analyze
  "Given an environment, a map containing {:locals (mapping of names to bindings), :context
(one of :statement, :expr, :return), :ns (a symbol naming the
compilation ns)}, and form, returns an expression object (a map
containing at least :form, :op and :env keys). If expr has any (immediately)
nested exprs, must have :children [exprs...] entry. This will
facilitate code walking without knowing the details of the op set."
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
          (var-fn env (get-in @namespaces [(-> env :ns :name ) :uses sym]) (name sym))

          :else
          (let [full-ns (if (core-name? env sym) 'clojure.core (-> env :ns :name ))]
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
      {:env env :op :invoke :f fexpr :args argexprs :children (conj argexprs fexpr)})))

(defn analyze-symbol
  "Finds the var associated with sym"
  [env sym]
  (let [ret {:env env :form sym}
        lb (-> env :locals sym)]
    (if lb
      (assoc ret :op :var :info lb)
      (assoc ret :op :var :info (resolve-existing-var env sym)))))


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
        simple-keys? (every? #(or (string? %) (keyword? %))
      (keys form))
        ks (disallowing-recur (vec (map #(analyze expr-env % name) (keys form))))
        vs (disallowing-recur (vec (map #(analyze expr-env % name) (vals form))))]
    (analyze-wrap-meta {:op :map :env env :form form :children (vec (concat ks vs))
                        :keys ks :vals vs :simple-keys? simple-keys?}
      name)))

(defn analyze-vector
  [env form name]
  (let [expr-env (assoc env :context :expr )
        items (disallowing-recur (vec (map #(analyze expr-env % name) form)))]
    (analyze-wrap-meta {:op :vector :env env :form form :children items} name)))

(defn analyze-wrap-meta [expr name]
  (let [form (:form expr)]
    (if (meta form)
      (let [env (:env expr) ; take on expr's context ourselves
            expr (assoc-in expr [:env :context ] :expr ) ; change expr to :expr
            meta-expr (analyze-map (:env expr) (meta form) name)]
        {:op :meta :env env :form form :children [meta-expr expr]
         :meta meta-expr :expr expr})
      expr)))

(defmethod parse 'if
  [op env [_ test then else :as form] name]
  (let [test-expr (disallowing-recur (analyze (assoc env :context :expr) test))
        then-expr (analyze env then)
        else-expr (analyze env else)]
    {:env env :op :if :form form
     :test test-expr :then then-expr :else else-expr
     :children [test-expr then-expr else-expr]}))

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
        (when init-expr {:children [init-expr]})
        (when export-as {:export export-as})))))

(defn analyze-block
  "returns {:statements .. :ret .. :children ..}"
  [env exprs]
  (let [statements (disallowing-recur
    (seq (map #(analyze (assoc env :context :statement ) %) (butlast exprs))))
        ret (if (<= (count exprs) 1)
      (analyze env (first exprs))
      (analyze (assoc env :context (if (= :statement (:context env)) :statement :return )) (last exprs)))]
    {:statements statements :ret ret :children (vec (cons ret statements))}))

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
                      be {:name name :init init-expr}]
                  (recur (conj bes be)
                    (assoc-in env [:locals name] be)
                    (next bindings))))
              [bes env])))
        recur-frame (when is-loop {:names (vec (map :name bes)) :flag (atom nil)})
        {:keys [statements ret children]}
        (binding [*recur-frames* (if recur-frame (cons recur-frame *recur-frames*) *recur-frames*)]
          (analyze-block (assoc env :context (if (= :expr context) :return context)) exprs))]
    {:env encl-env :op :let :loop is-loop
     :bindings bes :statements statements :ret ret :form form :children (into [children] (map :init bes))}))

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
          targetexpr  (analyze enve target)
          children    [enve]]
      (case dot-action
        ::access {:env env :op :dot :children children
                  :target targetexpr
                  :field field}
        ::call   (let [argexprs (map #(analyze enve %) args)]
        {:env env :op :dot :children (into children argexprs)
         :target targetexpr
         :method method
         :args argexprs})))))

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
