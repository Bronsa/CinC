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

(defmethod box :if
  [{:keys [test then else box] :as ast}]
  (if (:box ast)
    ast
    (let [test (if (and (not (:box test))
                        (= Boolean/TYPE (:tag test)))
                 test (assoc test :box true))
          [then else] (if box (mapv #(assoc % :box true) [then else]) [then else])]
      (assoc ast
        :test test
        :then then
        :else else))))

(defmethod box :default [ast] ast)
