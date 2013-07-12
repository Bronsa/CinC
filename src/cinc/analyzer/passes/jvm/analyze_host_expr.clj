(ns cinc.analyzer.passes.jvm.analyze-host-expr
  (:require [cinc.analyzer :as ana]
            [cinc.analyzer.utils :refer [postwalk ctx]]
            [cinc.analyzer.jvm.utils :refer :all]))

(defn analyze-host-call
  [target-type method args target-expr class? env]
  (let [op (case target-type
             :static   :static-call
             :instance :instance-call)]
    (merge
     {:op     op
      :method method
      :args   args}
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
     :class       class
     :instance    target-expr
     :field       sym}))

(defn -analyze-host-expr
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
    (if-let [class (maybe-class (-> target-expr :tag))] ;; else try again after tag inference
      ;; it's tagged: we know the target class at compile time
      (if-let [field (maybe-instance-field target-expr class m-or-f)]
        field
        (if-let [method (maybe-instance-method target-expr class m-or-f)]
          method
          (throw (ex-info (str "cannot find field or no-arg method call "
                               m-or-f " for class " class)
                          {:instance target-expr
                           :m-or-f   m-or-f}))))
      {:op          :host-interop
       :target-expr target-expr
       :m-or-f      m-or-f})))

(defn analyze-host-expr [ast]
  (postwalk ast (fn [{:keys [op form env] :as ast}]
                  (if (#{:host-interop :host-call} op)
                    (let [target (:target-expr ast)
                          class? (maybe-class (:form target))
                          target-type (if class? :static :instance)]
                      (merge {:form form
                              :env  env}
                             (if (= :host-call op)
                               (analyze-host-call target-type (:method ast)
                                                  (:args ast) target class? env)
                               (-analyze-host-expr target-type (:m-or-f ast)
                                                   target class? env))))
                    ast))))
