(ns cinc.analyzer.jvm
  (:refer-clojure :exclude [macroexpand-1 macroexpand])
  (:require [cinc.analyzer
             :as ana
             :refer [analyze parse analyze-in-env analyze-method-impls wrapping-meta]
             :rename {analyze -analyze}]
            [cinc.analyzer.utils :refer [ctx maybe-var walk prewalk]]
            [cinc.analyzer.jvm.utils :refer :all :exclude [box]]
            [cinc.analyzer.passes.source-info :refer [source-info]]
            [cinc.analyzer.passes.elide-meta :refer [elide-meta]]
            [cinc.analyzer.passes.constant-lifter :refer [constant-lift]]
            [cinc.analyzer.passes.warn-earmuff :refer [warn-earmuff]]
            [cinc.analyzer.passes.collect :refer [collect]]
            [cinc.analyzer.passes.jvm.box :refer [box]]
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
                target (if (maybe-class target)
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

(defmethod parse 'reify*
  [[_ interfaces & methods :as form] env]
  (let [interfaces (conj (set interfaces)
                         clojure.lang.IObj)
        methods (mapv #(assoc (analyze-method-impls % env)
                         :interfaces interfaces) methods)]
    (wrapping-meta
     {:op         :reify
      :env        env
      :form       form
      :methods    methods
      :interfaces interfaces})))

(defmethod parse 'deftype*
  [[_ name class-name fields _ interfaces & methods :as form] env]
  (let [interfaces (set interfaces)
        fields-expr (mapv (fn [name]
                            {:env  env
                             :form name
                             :name name
                             :op   :binding})
                          fields)
        menv (assoc env :locals (zipmap fields fields-expr))
        methods (mapv #(assoc (analyze-method-impls % menv)
                         :interfaces interfaces) methods)]
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
                                  [(conj te test-expr) (conj th then-expr)]))
                              [(sorted-map) {}] case-map)
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

(defn cycling [& fns]
  (fn [ast]
    (let [new-ast (reduce #(%2 %) ast fns)]
      (if (= new-ast ast)
        ast
        (recur new-ast)))))

(defn analyze
  "Given an environment, a map containing
   -  :locals (mapping of names to lexical bindings),
   -  :context (one of :statement, :expr or :return
 and form, returns an expression object (a map containing at least :form, :op and :env keys)."
  [form env]
  (binding [ana/macroexpand-1 macroexpand-1]
    (-> (-analyze form env)
      (walk (fn [ast]
              (-> ast
                warn-earmuff
                annotate-branch
                infer-constant-tag
                elide-meta
                source-info))
            (comp constant-lift
               (cycling infer-tag analyze-host-expr validate box)))
      (prewalk (collect :constants
                        :callsites
                        :closed-overs
                        :vars))
      clear-locals)))

(defn analyze-file
  [file]
  (ana/analyze-file file analyze))
