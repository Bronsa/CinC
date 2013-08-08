(ns cinc.analyzer.passes.jvm.analyze-host-expr
  (:require [cinc.analyzer :as ana]
            [cinc.analyzer.utils :refer [ctx]]
            [cinc.analyzer.jvm.utils :refer :all]))

(defn maybe-static-field [[_ class sym]]
  (when-let [{:keys [flags type]} (static-field class sym)]
    {:op          :static-field
     :assignable? (not (:final flags))
     :class       class
     :field       sym
     :tag         type}))

(defn maybe-static-method [[_ class sym]]
  (when-let [{:keys [return-type]} (static-method class sym)]
    {:op     :static-call
     :tag    return-type
     :class  class
     :method sym}))

(defn maybe-instance-method [target-expr class sym]
  (when-let [{:keys [return-type]} (instance-method class sym)]
      {:op       :instance-call
       :tag      return-type
       :instance target-expr
       :class    class
       :method   sym}))

(defn maybe-instance-field [target-expr class sym]
  (when-let [{:keys [flags type]} (instance-field class sym)]
    {:op          :instance-field
     :assignable? (not (:final flags))
     :class       class
     :instance    target-expr
     :field       sym
     :tag         type}))

(defn analyze-host-call
  [target-type method args target-expr class env]
  (let [op (case target-type
             :static   :static-call
             :instance :instance-call)]
    (merge
     {:op     op
      :method method
      :args   args}
     (case target-type
       :static   {:class    class}
       :instance {:instance target-expr
                  :class    (:tag target-expr)}))))

(defn analyze-host-field
  [target-type field target-expr class env]
  (if class
    (case target-type
      :static (or (maybe-static-field (list '. class field))
                  (throw (ex-info (str "cannot find field "
                                       field " for class " class)
                                  {:class class
                                   :field field})))
      :instance (or (maybe-instance-field target-expr class field)
                    (throw (ex-info (str "cannot find field "
                                         field " for class " class)
                                    {:instance target-expr
                                     :field    field}))))
    {:op     :host-interop
     :target target-expr
     :m-or-f field}))

(defn -analyze-host-expr
  [target-type m-or-f target-expr class env]
  (if class
    (or (maybe-static-field (list '. class m-or-f))
        (maybe-static-method (list '. class m-or-f))
        (throw (ex-info (str "cannot find field or no-arg method call "
                             m-or-f " for class " class)
                        {:class  class
                         :m-or-f m-or-f})))
    (if-let [class (maybe-class (-> target-expr :tag))]
      (or (maybe-instance-field target-expr class m-or-f)
          (maybe-instance-method target-expr class m-or-f)
          (throw (ex-info (str "cannot find field or no-arg method call "
                               m-or-f " for class " class)
                          {:instance target-expr
                           :m-or-f   m-or-f})))
      {:op     :host-interop
       :target target-expr
       :m-or-f m-or-f})))

(defn analyze-host-expr
  [{:keys [op form env] :as ast}]
  (if (#{:host-interop :host-call :host-field} op)
    (let [target (:target ast)
          class? (maybe-class (:form target))
          target-type (if class? :static :instance)]
      (merge {:form form
              :env  env}
             (case op

               :host-call
               (analyze-host-call target-type (:method ast)
                                  (:args ast) target class? env)

               :host-field
               (analyze-host-field target-type (:field ast)
                                   target (or class?
                                              (:tag target)) env)

               (-analyze-host-expr target-type (:m-or-f ast)
                                   target class? env))))
    ast))
