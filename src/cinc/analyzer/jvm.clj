(ns cinc.analyzer.jvm
  (:refer-clojure :exclude [macroexpand-1 macroexpand])
  (:require [cinc.analyzer :as ana :refer [parse analyze-in-env]]
            [cinc.analyzer.utils :refer [ctx maybe-var]]
            [cinc.analyzer.jvm.utils :refer :all]
            [cinc.analyzer.passes.jvm.validate :refer [validate]]
            [cinc.analyzer.passes.constant-lifter :refer [constant-lift]]))

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
          (list* 'new (symbol (subs opname 0 (dec (count opname)))) expr)

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

;; TODO: passes for:
;; locals clearing
;; closing overs

;; make assignable
;; TODO: reflect to validate calls/require runtime-reflection
(defn analyze-host-call
  [target-type [method & args] target-expr class? env]
  (let [op (case target-type
             :static   :static-call
             :instance :instance-call)]
    (merge
     {:op     op
      :method method
      :args   (mapv (ana/analyze-in-env (ctx env :expr)) args)}
     (case target-type
       :static   {:class (:form target-expr)}
       :instance {:instance target-expr}))))

(defn maybe-static-field [[_ class sym]]
  (when-let [{:keys [flags]} (static-field class sym)]
    {:op          :static-field
     :assignable? (not (:final flags))
     :class       class
     :field       sym}))

(defn maybe-static-method [[_ class sym]]
  (when-let [_ (static-method class sym)]
    {:op     :static-call
     :class  class
     :method sym}))

(defn maybe-instance-method [target-expr class sym]
  (when-let [_ (instance-method class sym)]
    {:op       :instance-call
     :instance target-expr
     :method   sym}))

(defn maybe-instance-field [target-expr class sym]
  (when-let [{:keys [flags]} (instance-field class sym)]
    {:op          :instance-field
     :assignable? (not (:final flags))
     :instance    target-expr
     :field       sym}))

(defn analyze-host-expr
  [target-type m-or-f target-expr class env]
  (if class
    (if-let [field (maybe-static-field (list '. class m-or-f))]
      field
      (if-let [method (maybe-static-method (list '. class m-or-f))]
        method
        (throw (ex-info (str "cannot find field or no-arg method call "
                             m-or-f " for class " class)
                        {:class  class
                         :m-or-f m-or-f}))))
    (if-let [class (maybe-class (-> target-expr :meta :tag))]
      ;; it's tagged: we know the target class at compile time
      (if-let [field (maybe-instance-field target-expr class m-or-f)]
        field
        (if-let [method (maybe-instance-method target-expr class m-or-f)]
          method
          (throw (ex-info (str "cannot find field or no-arg method call "
                               m-or-f " for class " class)
                          {:instance target-expr
                           :m-or-f   m-or-f}))))
      {:op     :unknown-host-form
       :target target-expr
       :m-or-f m-or-f})))

(defmethod parse '.
  [[_ target & [m-or-f] :as form] env]
  {:pre [(>= (count form) 3)
         (not (namespace (if (symbol? m-or-f) m-or-f (first m-or-f))))]}
  (let [target-expr (ana/analyze target (ctx env :expr))
        class? (maybe-class target)
        call? (seq? m-or-f)
        target-type (if class? :static :instance)
        expr ((if call?
                analyze-host-call
                analyze-host-expr)
              target-type m-or-f target-expr class? env)]
    (merge {:form form
            :env env}
           expr)))

(defn analyze
  "Given an environment, a map containing
   -  :locals (mapping of names to lexical bindings),
   -  :context (one of :statement, :expr or :return
 and form, returns an expression object (a map containing at least :form, :op and :env keys)."
  [form env]
  (binding [ana/macroexpand-1 macroexpand-1]
    (-> (ana/analyze form env)
      validate
      constant-lift)))
