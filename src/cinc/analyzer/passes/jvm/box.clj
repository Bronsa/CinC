(ns cinc.analyzer.passes.jvm.box
  (:require [cinc.analyzer.jvm.utils :as u])
  (:require [cinc.analyzer.utils :refer [protocol-node?]]))

(defmulti box :op)

(defmacro if-let-box [class then else]
  `(let [c# ~class
         ~class (u/box c#)]
     (if (u/primitive? c#)
       ~then
       ~else)))

(defn -box [{:keys [tag] :as ast}]
  (if (u/primitive? tag)
    (assoc ast :tag (u/box tag))
    ast))

(defn boxed? [tag expr]
  (and (not (u/primitive? tag))
       (u/primitive? (:tag expr))))

(defmethod box :instance-call
  [{:keys [class] :as ast}]
  (if-let-box class
    (assoc (update-in ast [:instance :tag] u/box) :class class)
    ast))

(defmethod box :instance-field
  [{:keys [class] :as ast}]
  (if-let-box class
    (assoc (update-in ast [:instance :tag] u/box) :class class)
    ast))

(defmethod box :def
  [{:keys [init] :as ast}]
  (if (and init (u/primitive? (:tag init)))
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
  [{:keys [tag ret] :as ast}]
  (if (boxed? tag ret)
    (update-in ast [:ret] -box)
    ast))

(defmethod box :keyword-invoke
  [{:keys [args] :as ast}]
  (assoc ast :args (mapv -box args)))

(defmethod box :let
  [{:keys [tag body] :as ast}]
  (if (boxed? tag body)
    (update-in ast [:body] -box)
    ast))

(defmethod box :letfn
  [{:keys [tag body] :as ast}]
  (if (boxed? tag body)
    (update-in ast [:body] -box)
    ast))

(defmethod box :loop
  [{:keys [tag body] :as ast}]
  (if (boxed? tag body)
    (update-in ast [:body] -box)
    ast))

(defmethod box :fn-method
  [{:keys [tag] :as ast}]
  (if (not (u/primitive? tag))
    (update-in ast [:body] -box)
    ast))

;; (defmethod box :if
;;   [{:keys [test then else box] :as ast}]
;;   (if (:box then)
;;     ast
;;     (let [test (if (and (not (:box test))
;;                         (= Boolean/TYPE (:tag test)))
;;                  test (assoc test :box true))
;;           [then else] (if box (mapv -box [then else]) [then else])]
;;       (merge ast
;;              {:test test
;;               :then then
;;               :else else}))))

;; (defmethod box :invoke
;;   [{:keys [fn args] :as ast}]
;;   (if-not (and (#{:var :the-var} (:op fn))
;;                (protocol-node? (:var fn)))
;;     (assoc ast :args (mapv -box args))
;;     ast))

(defmethod box :default [ast] ast)
