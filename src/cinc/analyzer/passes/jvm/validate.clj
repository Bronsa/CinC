(ns cinc.analyzer.passes.jvm.validate
  (:require [cinc.analyzer.utils :refer [walk]]
            [cinc.analyzer.jvm.utils :as u]))

(defmulti -validate :op)

(defmethod -validate :maybe-class
  [{:keys [maybe-class] :as ast}]
  (if-let [the-class (u/maybe-class maybe-class)]
    (assoc (dissoc ast :maybe-class)
      :class the-class)
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

(defmethod -validate :default [ast] ast)

(defn validate [ast]
  (walk ast -validate))
