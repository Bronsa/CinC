(ns cinc.analyzer.passes.jvm.validate
  (:require [cinc.analyzer :refer [-analyze]]
            [cinc.analyzer.utils :refer [prewalk]]
            [cinc.analyzer.jvm.utils :as u]))

(defmulti -validate :op)

(defmethod -validate :maybe-class
  [{:keys [maybe-class env] :as ast}]
  (if-let [the-class (u/maybe-class maybe-class)]
    (-analyze :const the-class env :class)
    (if (.contains (str maybe-class) ".") ;; try and be smart for the exception
      (throw (ex-info (str "class not found: " maybe-class)
                      {:class maybe-class}))
      (throw (ex-info (str "could not resolve var: " maybe-class)
                      {:var maybe-class})))))

(defmethod -validate :maybe-host-form
  [{:keys [maybe-class]}]
  (throw (ex-info (str "No such namespace: " maybe-class)
                  {:ns maybe-class})))

(defmethod -validate :new
  [{:keys [maybe-class] :as ast}]
  (if-let [the-class (u/maybe-class maybe-class)]
    (assoc (dissoc ast :maybe-class)
      :class the-class)
    (throw (ex-info (str "class not found: " maybe-class)
                    {:class maybe-class}))))

(defmethod -validate :catch
  [{:keys [maybe-class] :as ast}]
  (if-let [the-class (u/maybe-class maybe-class)]
    (assoc (dissoc ast :maybe-class)
      :class the-class)
    (throw (ex-info (str "class not found: " maybe-class)
                    {:class maybe-class}))))

(defmethod -validate :static-call
  [{:keys [class method args] :as ast}]
  (let [argc (count args)]
    (if-let [matching-methods (seq (u/static-methods class method argc))]
      ast ;; find matching types or require reflection
      (throw (ex-info (str "No matching method: " method " for class: " class " and arity: " argc)
                      {:method method
                       :class  class
                       :argc   argc})))))

(defmethod -validate :static-field
  [{:keys [class field] :as ast}]
  (if-let [matching-field (u/static-field class field)]
    ast
    (throw (ex-info (str "No matching field: " field " for class: " class)
                    {:field  field
                     :class  class}))))


(defmethod -validate :default [ast] ast)

(defn validate-around
  [{:keys [tag] :as ast}]
  (let [ast (if tag
              (if-let [the-class (u/maybe-class tag)]
                (assoc ast :tag the-class)
                (throw (ex-info (str "class not found: " tag)
                                {:class tag})))
              ast)]
    (-validate ast)))

(defn validate [ast]
  (prewalk ast validate-around))
