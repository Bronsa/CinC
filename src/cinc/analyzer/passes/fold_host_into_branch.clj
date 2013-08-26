(ns cinc.analyzer.passes.fold-host-into-branch
  (:require [cinc.analyzer :refer [analyze]]
            [cinc.analyzer.passes :refer [update-children]]))

;; form is invalidated
(defmulti fold-host-into-branch :op)

(defn- transform-path [x env]
  #(if (:path? %)
     (assoc (analyze (list '. (:form %) x) env) :path? true)
     %))

(defmethod fold-host-into-branch :host-call
  [{:keys [target method args env] :as ast}]
  (if (:branch? target)
    (update-children target (transform-path (list* method (map :form args)) env))
    ast))

(defmethod fold-host-into-branch :host-field
  [{:keys [target field env] :as ast}]
  (if (:branch? target)
    (update-children target (transform-path field env))
    ast))

(defmethod fold-host-into-branch :host-interop
  [{:keys [target m-or-f env] :as ast}]
  (if (:branch? target)
    (update-children target (transform-path m-or-f env))
    ast))

(defmethod fold-host-into-branch :default [ast] ast)
