(ns cinc.analyzer.passes.jvm.box
  (:require [cinc.analyzer.jvm.utils :as u]))


(defmulti box :op)

(defmacro if-let-box [class then else]
  `(let [c# ~class
         ~class (u/box c#)]
     (if (not= c# ~class)
       ~then
       ~else)))

(defmethod box :instance-call
  [{:keys [class] :as ast}]
  (if-let-box class
   (assoc (update-in ast [:instance] :box true)
     :class class)
   ast))

(defmethod box :instance-field
  [{:keys [class] :as ast}]
  (if-let-box class
    (assoc (update-in ast [:instance] :box true)
      :class class)
    ast))

(defn -box [x]
  (assoc x :box true))

(defmethod box :if
  [{:keys [test then else box] :as ast}]
  (if (:box then)
    ast
    (let [test (if (and (not (:box test))
                        (= Boolean/TYPE (:tag test)))
                 test (assoc test :box true))
          [then else] (if box (mapv -box [then else]) [then else])]
      (assoc ast
        :test test
        :then then
        :else else))))

(defmethod box :def
  [ast]
  (assoc-in ast [:init :box] true))

(defmethod box :vector
  [{:keys [items] :as ast}]
  (assoc ast :items (mapv -box items)))

(defmethod box :set
  [{:keys [items] :as ast}]
  (assoc ast :items (mapv -box items)))

(defmethod box :map
  [{:keys [keys vals] :as ast}]
  (let [keys (mapv -box keys)
        vals (mapv -box vals)]
    (assoc ast
      :keys keys
      :vals vals)))

(defmethod box :do
  [{:keys [box] :as ast}]
  (if box
    (assoc-in ast [:ret :box] true)
    ast))

(defmethod box :default [ast] ast)
