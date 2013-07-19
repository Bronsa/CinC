(ns cinc.analyzer.passes.jvm.box
  (:require [cinc.analyzer.jvm.utils :as u]))


(defmulti box :op)

(defmethod box :instance-call
  [{:keys [class] :as ast}]
  (assoc (update-in ast [:instance] :box true)
    :class (u/box class)))

(defmethod box :instance-field
  [{:keys [class] :as ast}]
  (assoc (update-in ast [:instance] :box true)
    :class (u/box class)))

(defmethod box :default [ast] ast)
