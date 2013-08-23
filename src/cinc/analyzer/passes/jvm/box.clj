(ns cinc.analyzer.passes.jvm.box
  (:require [cinc.analyzer.jvm.utils :as u]))

(defmulti box :op)

(defmacro if-let-box [class then else]
  `(let [c# ~class
         ~class (u/box c#)]
     (if (u/primitive? c#)
       ~then
       ~else)))

(defmethod box :instance-call
  [{:keys [class] :as ast}]
  (if-let-box class
   (assoc (assoc-in ast [:instance] :box true)
     :class class)
   ast))

(defmethod box :instance-field
  [{:keys [class] :as ast}]
  (if-let-box class
    (assoc (assoc-in ast [:instance] :box true)
      :class class)
    ast))

(defn -box [{:keys [tag] :as ast}]
  (if (u/primitive? tag)
    (assoc ast :box true)
    ast))

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
  [{:keys [init] :as ast}]
  (if init
    (update-in ast [:init] -box)
    ast))

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
    (update-in ast [:ret] -box)
    ast))

(defmethod box :default [ast] ast)
