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

(def specials '#{def fn*})

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

(defn confirm-var-exists [env prefix suffix]
  (when *warn-on-undeclared*
    (let [crnt-ns (-> env :ns :name )]
      (when (= prefix crnt-ns)
        (when-not (-> @namespaces crnt-ns :defs suffix)
          (binding [*out* *err*]
            (println
              (str " WARNING: Use of undeclared Var " prefix " / " suffix
                (when (:line env)
                  (str " at line " (:line env)))))))))))

(defn resolve-ns-alias [env name]
  (let [sym (symbol name)]
    (get (:requires (:ns env)) sym sym)))

(defn core-name?
  "Is sym visible from core in the current compilation namespace?"
  [env sym]
  (and (get (:defs (@namespaces 'clojure.core)) sym)
    (not (contains? (-> env :ns :excludes ) sym))))

(defn resolve-var [env sym]
  (let [s (str sym)
        lb (-> env :locals sym)
        nm
        (cond
          lb (:name lb)

          (namespace sym)
          (let [ns (namespace sym)]
            (symbol (str (resolve-ns-alias env ns)) (name sym)))

          (.contains s ".")
          (let [idx (.indexOf s ".")
                prefix (symbol (subs s 0 idx))
                suffix (subs s idx)
                lb (-> env :locals prefix)]
            (if lb
              (symbol (str (:name lb) suffix))
              sym))

          :else (let [full-ns (if (core-name? env sym) 'clojure.core (-> env :ns :name ))]
                  (symbol (str full-ns) (name sym))))]
    {:name nm}))

(defn resolve-existing-var [env sym]
  (let [s (str sym)
        lb (-> env :locals sym)
        nm
        (cond
          lb (:name lb)

          (namespace sym)
          (let [ns (namespace sym)
                full-ns (resolve-ns-alias env ns)]
            (confirm-var-exists env full-ns (symbol (name sym)))
            (symbol (str full-ns) (name sym)))

          (.contains s ".")
          (let [idx (.indexOf s ".")
                prefix (symbol (subs s 0 idx))
                suffix (subs s idx)
                lb (-> env :locals prefix)]
            (if lb
              (symbol (str (:name lb) suffix))
              (do
                (confirm-var-exists env prefix (symbol suffix))
                sym)))

          (get-in @namespaces [(-> env :ns :name ) :uses sym])
          (symbol (str (get-in @namespaces [(-> env :ns :name ) :uses sym])) (name sym))

          :else (let [full-ns (if (core-name? env sym) 'clojure.core (-> env :ns :name ))]
                  (confirm-var-exists env full-ns sym)
                  (symbol (str full-ns) (name sym))))]
    {:name nm}))

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

(defmethod parse 'def
  [op env form name]
  (let [pfn (fn ([_ sym] {:sym sym})
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

      (merge {:env env :variadic variadic :params params
              :max-fixed-arity fixed-arity :recurs @(:flag recur-frame)} block))))

(defmethod parse 'fn*
  [op env [_ & args] name]
  (let [[name meths] (if (symbol? (first args))
    [(first args) (next args)]
    [name (seq args)])
        ;;turn (fn [] ...) into (fn ([]...))
        meths (if (vector? (first meths)) (list meths) meths)
        locals (:locals env)
        locals (if name (assoc locals name {:name name}) locals)
        menv (if (> (count meths) 1) (assoc env :context :expr ) env)
        methods (map #(analyze-fn-method menv locals %) meths)
        max-fixed-arity (apply max (map :max-fixed-arity methods))
        variadic (boolean (some :variadic methods))]
    ;;todo - validate unique arities, at most one variadic, variadic takes max required args
    {:env env :op :fn :name name :methods methods :variadic variadic :recur-frames *recur-frames*
     :max-fixed-arity max-fixed-arity}))