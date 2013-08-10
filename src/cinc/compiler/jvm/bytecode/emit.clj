(ns cinc.compiler.jvm.bytecode.emit
  (:require [cinc.analyzer.utils :as u]
            [cinc.analyzer.jvm.utils :refer [asm-type]])
  (:import [org.objectweb.asm Opcodes]))

(defmulti -emit (fn [{:keys [op]} _] op))
(defmulti -emit-set! (fn [{:keys [op]} _] op))

(def nil-expr
  {:op :const :type :nil :form nil})

(defn emit
  ([ast]
     (emit ast {}))
  ([{:keys [env] :as ast} frame]
     (let [bytecode (-emit ast frame)]
       (into bytecode
             (if (= :statement (:context env))
               (when (#{:value} (meta bytecode))
                 [[:pop]])
               (when (#{:untyped} (meta bytecode))
                 [(emit nil-expr)]))))))

(defmethod -emit :import
  [{:keys [class]} frame]
  ^:value
  [[:get-static :rt/current-ns :var]
   [:invoke-virtual [:deref]]
   [:check-cast :ns]
   [:push class]
   [:invoke-static [:class/for-name :string]]
   [:invoke-virtual [:import-class :class]]])

(defmethod -emit :throw
  [{:keys [exception]} frame]
  (into
   (emit exception)
   [:check-cast :throwable]
   [:throw-exception]))

(defmethod -emit :monitor-enter
  [{:keys [target]} frame]
  (with-meta
    (into
     (emit target frame)
     [:monitor-enter])
    {:untyped true}))

(defmethod -emit :monitor-exit
  [{:keys [target]} frame]
  (with-meta
    (into
     (emit target frame)
     [:monitor-exit])
    {:untyped true}))

(defn emit-constant [id frame]
  (let [c (get-in frame [:constants id])]
    ^:value
    [(case c
       ;; (true false)
       ;; [:get-static (if c :boolean/TRUE :boolean/FALSE) :boolean]

       nil
       [:visit-inst Opcodes/ACONST_NULL]

       [:get-static (frame :class) (str "const__" id) (class c)])])) ;; asm-type (after specialize)

(defmethod -emit :const
  [{:keys [id]} frame]
  (emit-constant id frame))

(defn emit-var [var frame]
  (emit-constant (get-in frame [:vars var]) frame))

(defmethod -emit :var
  [{:keys [var]} frame]
  (into
   (emit-var var frame)
   [:invoke-virtual [(if (u/dynamic? var) :get :get-raw-root)]]))

(defmethod -emit-set! :var
  [{:keys [var val]} frame]
  (into
   (emit-var var frame)
   (conj
    (emit val frame)
    [:invoke-virtual [:set :object]])))

(defmethod -emit :the-var
  [{:keys [var]} frame]
  (emit-var var frame))

(defmethod -emit :def
  [{:keys [var meta init]} frame]
  (into
   (emit-var var frame)
   (when (u/dynamic? var) ;; why not when macro?
     [[:push true]
      [:invoke-virtual [:set-dynamic :bool]]])
   (when meta
     (into
      [[:dup]]
      (conj
       (emit meta frame)
       [:check-cast :i-persistent-map]
       [:invoke-virtual [:set-meta :i-persistent-map]])))
   (when init
     (into
      [[:dup]]
      (conj
       (emit init frame)
       [:invoke-virtual [:bind-root :object]])))))

(defmethod -emit :set!
  [{:keys [target val]} frame]
  (-emit-set! target val frame))

(defn emit-as-array [list frame]
  (into
   ^:value
   [[:push (int (count list))]
    [:new-array :object]]
   (mapcat (fn [i item]
             (into
              [[:dup]
               [:push (int i)]]
              (conj
               (emit item frame)
               [:array-store :object])))
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

(defmethod -emit :with-meta
  [{:keys [meta expr]} frame]
  (with-meta
    (into
     (emit expr frame)
     (into
      [[:check-cast :i-obj]]
      (conj
       (emit meta frame)
       [:check-cast :i-persistent-map]
       [:invoke-interface [:i-obj/with-meta :i-persistent-map]]))
     {:value true})))
