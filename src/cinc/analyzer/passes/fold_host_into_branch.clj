(ns cinc.analyzer.passes.fold-host-into-branch
  (:require [cinc.analyzer :refer [analyze]]
            [cinc.analyzer.passes :refer [update-children]]))

; form is invalidated
(defmulti fold-host-into-branch (fn [ast _] (:op ast)))

(defn- transform-path [x env analyze]
  #(if (:path? %)
     (analyze (list '. (:form %) x) env)
     %))

(defmethod fold-host-into-branch :host-call
  [{:keys [target method args env] :as ast} analyze]
  (if (:branch? target)
    (update-children target (transform-path (list* method (map :form args)) env analyze))
    (if (some :branch? args)
      (loop [args args processed []]
        (let [a (first args)]
          (if (:branch? a)
            (update-children a (fn [c]
                                 (if (:path? c)
                                   (analyze (list '. (:form target)
                                                  (seq (into (into [method]
                                                                   (map :form processed))
                                                             (list* (:form c) (map :form (rest args)))))) env)
                                   c)))
            (recur (next args) (conj processed a)))))
      ast)))

(defmethod fold-host-into-branch :host-field
  [{:keys [target field env] :as ast} analyze]
  (if (:branch? target)
    (update-children target (transform-path field env analyze))
    ast))

(defmethod fold-host-into-branch :host-interop
  [{:keys [target m-or-f env] :as ast} analyze]
  (if (:branch? target)
    (update-children target (transform-path m-or-f env analyze))
    ast))

(defmethod fold-host-into-branch :default [ast _] ast)
