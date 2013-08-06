(ns cinc.analyzer.jvm
  (:refer-clojure :exclude [macroexpand-1 macroexpand])
  (:require [cinc.analyzer
             :as ana
             :refer [analyze parse analyze-in-env wrapping-meta analyze-fn-method]
             :rename {analyze -analyze}]
            [cinc.analyzer.utils :refer [ctx maybe-var walk prewalk cycling]]
            [cinc.analyzer.jvm.utils :refer :all :exclude [box]]
            [cinc.analyzer.passes.source-info :refer [source-info]]
            [cinc.analyzer.passes.elide-meta :refer [elide-meta]]
            [cinc.analyzer.passes.constant-lifter :refer [constant-lift]]
            [cinc.analyzer.passes.warn-earmuff :refer [warn-earmuff]]
            [cinc.analyzer.passes.collect :refer [collect]]
            [cinc.analyzer.passes.jvm.box :refer [box]]
            [cinc.analyzer.passes.uniquify :refer [uniquify-locals]]
            [cinc.analyzer.passes.jvm.clear-locals :refer [annotate-branch clear-locals]]
            [cinc.analyzer.passes.jvm.validate :refer [validate]]
            [cinc.analyzer.passes.jvm.infer-tag :refer [infer-tag infer-constant-tag]]
            [cinc.analyzer.passes.jvm.analyze-host-expr :refer [analyze-host-expr]]))

(def jvm-specials
  (into ana/specials
        '#{monitor-enter monitor-exit clojure.core/import* reify* deftype* case*}))

(defn desugar-host-expr [form]
  (cond
   (symbol? form)
   (let [target (maybe-class (namespace form))
         field (symbol (name form))]
     (if (and (namespace form) target)
       (with-meta (list '. target field)
         (merge (meta form)
                {:field true}))
       form))

   (seq? form)
   (let [[op & expr] form]
     (if (symbol? op)
       (let [opname (name op)]
         (cond

          (= (first opname) \.) ; (.foo bar ..)
          (let [[target & args] expr
                target (if-let [target (maybe-class target)]
                         (with-meta (list 'clojure.core/identity target) {:tag Class})
                         target)
                args (list* (symbol (subs opname 1)) args)]
            (with-meta (list '. target (if (= 1 (count args)) ;; we don't know if (.foo bar) ia
                                         (first args) args)) ;; a method call or a field access
              (meta form)))

          (and (namespace op)
               (maybe-class (namespace op))) ; (class/field ..)
          (let [target (maybe-class (namespace op))]
            (with-meta (list '. target (list* (symbol opname) expr)) ;; static access in call position however are always method calls
              (meta form)))

          (= (last opname) \.) ;; (class. ..)
          (with-meta (list* 'new (symbol (subs opname 0 (dec (count opname)))) expr)
            (meta form))

          :else form))
       form))

   :else form))

(defn macroexpand-1 [form env]
  (if (seq? form)
    (let [op (first form)]
      (if (jvm-specials op)
        form
        (let [v (maybe-var op)]
          (if (and (not (-> env :locals (get op))) ;; locals cannot be macros
                   (:macro (meta v)))
            (apply @v env form (rest form)) ; (m &env &form & args)
            (desugar-host-expr form)))))
        (desugar-host-expr form)))

(defmethod parse 'monitor-enter
  [[_ target :as form] env]
  {:op          :monitor-enter
   :env         env
   :form        form
   :target-expr (-analyze target (ctx env :expr))})

(defmethod parse 'monitor-exit
  [[_ target :as form] env]
  {:op          :monitor-exit
   :env         env
   :form        form
   :target-expr (-analyze target (ctx env :expr))})

(defmethod parse 'clojure.core/import*
  [[_ class :as form] env]
  {:op          :import
   :env         env
   :form        form
   :maybe-class class})

(defn analyze-method-impls
  [[name [this & params :as args] & body :as form] env]
  {:pre [(symbol? name)
         (vector? args)
         this]}
  (let [meth (cons params body)
        this-expr {:name  this
                   :env   env
                   :form  this
                   :op    :binding
                   :tag   (:this env)
                   :local :this}
        env (assoc-in (dissoc env :this) [:locals this] this-expr)
        method (analyze-fn-method meth env)]
    (assoc (dissoc method :variadic?)
      :op   :method
      :form form
      :this this-expr
      :name name)))

(defn -deftype [name class-name args interfaces]
  (let [interfaces (mapv #(symbol (.getName ^Class %)) interfaces)]
    (eval (list 'do (list 'deftype* name class-name args :implements interfaces)
                (list 'import class-name)))))

(defmethod parse 'reify*
  [[_ interfaces & methods :as form] env]
  (let [interfaces (conj (disj (set (mapv maybe-class interfaces)) Object)
                         clojure.lang.IObj)
        name (gensym "reify__")
        class-name (symbol (str (namespace-munge *ns*) "." name))
        menv (assoc env :this class-name)
        methods (mapv #(assoc (analyze-method-impls % menv)
                         :interfaces interfaces) methods)]

    (-deftype name class-name [] interfaces)

    (wrapping-meta
     {:op         :reify
      :env        env
      :form       form
      :class-name class-name
      :methods    methods
      :interfaces interfaces})))

(defmethod parse 'deftype*
  [[_ name class-name fields _ interfaces & methods :as form] env]
  (let [interfaces (disj (set (mapv maybe-class interfaces)) Object)
        fields-expr (mapv (fn [name]
                            {:env     env
                             :form    name
                             :name    name
                             :mutable (let [m (meta name)]
                                        (or (:unsynchronized-mutable m)
                                            (:volatile-mutable m)))
                             :local   :field
                             :op      :binding})
                          fields)
        menv (assoc env
               :locals (zipmap fields fields-expr)
               :this class-name)
        methods (mapv #(assoc (analyze-method-impls % menv)
                         :interfaces interfaces) methods)]

    (-deftype name class-name fields interfaces)

    {:op         :deftype
     :env        env
     :form       form
     :name       name
     :class-name class-name
     :fields     fields-expr
     :methods    methods
     :interfaces interfaces}))

(defmethod parse 'case*
  [[_ expr shift mask default case-map switch-type test-type & [skip-check?] :as form] env]
  (let [[low high] ((juxt first last) (keys case-map))
        test-expr (-analyze expr (ctx env :expr))
        [tests thens] (reduce (fn [[te th] [min-hash [test then]]]
                                (let [test-expr (-analyze (list 'quote test) env)
                                      then-expr (-analyze then env)]
                                  [(conj te {:op   :case-test
                                             :hash min-hash
                                             :test test-expr})
                                   (conj th {:op   :case-then
                                             :hash min-hash
                                             :then then-expr})]))
                              [[] []] case-map) ;; transform back in a sorted-map + hash-map when emitting
        default-expr (-analyze default env)]
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

(defn cleanup [ast]
  (-> ast
    (update-in [:env] dissoc :locals)
    (update-in [:env] dissoc :loop-locals)))

(defn analyze
  "Given an environment, a map containing
   -  :locals (mapping of names to lexical bindings),
   -  :context (one of :statement, :expr or :return
 and form, returns an expression object (a map containing at least :form, :op and :env keys)."
  [form env]
  (binding [ana/macroexpand-1 macroexpand-1]
    (-> (-analyze form env)
      uniquify-locals
      (walk (fn [ast]
              (-> ast
                cleanup
                warn-earmuff
                annotate-branch
                source-info
                elide-meta))
            (comp (cycling infer-tag analyze-host-expr validate box)
               infer-constant-tag
               constant-lift))
      (prewalk (collect :constants
                        :callsites
                        :closed-overs
                        :vars))
      clear-locals)))

(defn analyze-file
  [file]
  (ana/analyze-file file analyze))
