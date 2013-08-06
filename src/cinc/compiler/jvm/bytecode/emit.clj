(ns cinc.compiler.jvm.bytecode.emit)

(defmulti -emit :op)

(defn emit
  [{:keys [env] :as ast}]
  (into (-emit ast)
        (if (= :statement (:context env))
          [[:pop]])))

(defmethod -emit :import
  [{:keys [class]}]
  [[:get-static :rt/current-ns]
   [:invoke-virtual [:deref]]
   [:check-cast :ns]
   [:push class]
   [:invoke-static [:class/for-name :string]]
   [:invoke-virtual [:import-class :class]]])

(defn emit-as-array [list]
  (into [[:push (int (count list))]
         [:new-array :object]]
        (mapcat (fn [i item]
                  [[:dup]
                   [:push (int i)]
                   (emit item)
                   [:array-store :object]])
                (range) list)))

(defmethod -emit :map
  [{:keys [keys vals]}]
  (conj
   (emit-as-array (interleave keys vals))
   [:invoke-static [:rt/map-unique-keys :objects]]))

(defmethod -emit :vector
  [{:keys [items]}]
  (conj
   (emit-as-array items)
   [:invoke-static [:rt/vector :objects]]))

(defmethod -emit :set
  [{:keys [items]}]
  (conj
   (emit-as-array items)
   [:invoke-static [:rt/set :objects]]))
