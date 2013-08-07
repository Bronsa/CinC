(ns cinc.compiler.jvm.bytecode.emit
  (:require [cinc.analyzer.utils :as u])
  (:require [cinc.analyzer.jvm.utils :refer [asm-type]]))

(defmulti -emit (fn [{:keys [op]} _] op))

(defn emit
  ([ast]
     (emit ast {}))
  ([{:keys [env] :as ast} frame]
     (into (-emit ast frame)
           (when (= :statement (:context env))
             [[:pop]]))))

(defmethod -emit :import
  [{:keys [class]} frame]
  [[:get-static :rt/current-ns]
   [:invoke-virtual [:deref]]
   [:check-cast :ns]
   [:push class]
   [:invoke-static [:class/for-name :string]]
   [:invoke-virtual [:import-class :class]]])

(defmethod -emit :throw
  [{:keys [exception]} frame]
  [(emit exception)
   [:check-cast :throwable]
   [:throw-exception]])

(defn emit-constant [id frame]
  (let [c (get-in frame [:constants id])]
    [:get-static (frame :class) (str "const__" id) (asm-type (class c))]))

(defn emit-var [var frame]
  (emit-constant (get-in frame [:vars var]) frame))

(defmethod -emit :def
  [{:keys [var meta init]} frame]
  (into
   [(emit-var var frame)]
   (when (u/dynamic? var) ;; why not when macro?
     [[:push true]
      [:invoke-virtual [:set-dynamic :bool]]])
   (when meta
     [[:dup]
      (emit meta frame)
      [:check-cast :i-persistent-map]
      [:invoke-virtual [:set-meta :i-persistent-map]]])
   (when init
     [[:dup]
      (emit init frame)
      [:invoke-virtual [:bind-root :object]]])))

(defn emit-as-array [list frame]
  (into [[:push (int (count list))]
         [:new-array :object]]
        (mapcat (fn [i item]
                  [[:dup]
                   [:push (int i)]
                   (emit item frame)
                   [:array-store :object]])
                (range) list)))

(defmethod -emit :map
  [{:keys [keys vals]} frame]
  (conj
   (emit-as-array (interleave keys vals) frame)
   [:invoke-static [:rt/map-unique-keys :objects]]))

(defmethod -emit :vector
  [{:keys [items]} frame]
  (conj
   (emit-as-array items frame)
   [:invoke-static [:rt/vector :objects]]))

(defmethod -emit :set
  [{:keys [items]} frame]
  (conj
   (emit-as-array items frame)
   [:invoke-static [:rt/set :objects]]))
