(ns cinc.compiler.jvm.bytecode.emit)

(defmulti emit :op)

(defmethod emit :import
  [{:keys [class env]}]
  (into
   [[:get-static :rt/current-ns]
    [:invoke-virtual [:deref]]
    [:check-cast :ns]
    [:push class]
    [:invoke-static [:class/for-name :string]]
    [:invoke-virtual [:import-class :class]]]
   (if (= :statement (:context env))
     [[:pop]])))
