(ns cinc.analyzer.jvm
  (:refer-clojure :exclude [macroexpand-1 macroexpand])
  (:require [cinc.analyzer :as ana :refer [parse analyze-in-env]]
            [cinc.analyzer.utils :refer [ctx maybe-var]]
            [cinc.analyzer.jvm.utils :refer :all]
            [cinc.analyzer.passes.infer-tag :refer [infer-tag]]
            [cinc.analyzer.passes.source-info :refer [source-info]]
            [cinc.analyzer.passes.elide-meta :refer [elide-meta]]
            [cinc.analyzer.passes.constant-lifter :refer [constant-lift]]
            [cinc.analyzer.passes.jvm.validate :refer [validate]]
            [cinc.analyzer.passes.jvm.analyze-host-expr :refer [analyze-host-expr]]))

(def jvm-specials
  (into ana/specials
        '#{monitor-enter monitor-exit clojure.core/import*}))

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
       (let [opname (name op)
             c (maybe-class op)]
         (cond

          c
          (throw (ex-info (str "expecting var but" form "is mapped to " c) {:form form}))


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
   :target-expr (ana/analyze target (ctx env :expr))})

(defmethod parse 'monitor-exit
  [[_ target :as form] env]
  {:op          :monitor-exit
   :env         env
   :form        form
   :target-expr (ana/analyze target (ctx env :expr))})

(defmethod parse 'clojure.core/import*
  [[_ class :as form] env]
  (if-let [class (maybe-class class)]
    {:op    :import
     :env   env
     :form  form
     :class class}
    (ex-info (str "class not found: " class) {:class class})))

(def passes
  [constant-lift
   (fn [ast]
     (let [new-ast (-> ast
                     infer-tag
                     analyze-host-expr
                     validate)]
       (if (= new-ast ast)
         new-ast
         (recur new-ast))))
   source-info
   elide-meta])

(defn analyze
  "Given an environment, a map containing
   -  :locals (mapping of names to lexical bindings),
   -  :context (one of :statement, :expr or :return
 and form, returns an expression object (a map containing at least :form, :op and :env keys)."
  [form env]
  (binding [ana/macroexpand-1 macroexpand-1]
    ((apply comp (rseq passes))
     (ana/analyze form env))))

(defn analyze-file
  [file]
  (ana/analyze-file file analyze))
