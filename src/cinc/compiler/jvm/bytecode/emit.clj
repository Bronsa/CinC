(ns cinc.compiler.jvm.bytecode.emit
  (:require [cinc.analyzer.utils :as u]
            [cinc.analyzer.jvm.utils :refer [asm-type]])
  (:import [org.objectweb.asm Opcodes]))

(defmulti -emit (fn [{:keys [op]} _] op))
(defmulti -emit-set! (fn [{:keys [op]} _] op))

(def nil-expr
  {:op :const :type :nil :form nil})

(defn emit-box [tag]
  [])

(defn emit
  ([ast]
     (emit ast {}))
  ([{:keys [env box tag] :as ast} frame]
     (let [bytecode (-emit ast frame)
           statement? (= :statement (:context env))
           m (meta bytecode)]
       (if statement?
         (if (:const m)
           []
           (into bytecode
                 (when (and (not= :untyped m)
                            (not= Void/TYPE tag))
                   (if (#{Double/TYPE Long/TYPE} tag)
                     [[:pop2]]
                     [[:pop]]))))
         (into bytecode
               (when (= :untyped m)
                 (emit nil-expr))
               (when box
                 (emit-box tag)))))))

(defmethod -emit :import
  [{:keys [class]} frame]
  [[:get-static :rt/current-ns :var]
   [:invoke-virtual [:deref] :object]
   [:check-cast :ns]
   [:push class]
   [:invoke-static [:class/for-name :string] :class]
   [:invoke-virtual [:import-class :class]] :class])

(defmethod -emit :throw
  [{:keys [exception]} frame]
  (into
   (emit exception)
   [:check-cast :throwable]
   [:throw-exception]))

(defmethod -emit :monitor-enter
  [{:keys [target]} frame]
  `^:untyped
  [~@(emit target frame)
   [:monitor-enter]])

(defmethod -emit :monitor-exit
  [{:keys [target]} frame]
  `^:untyped
  [~@(emit target frame)
   [:monitor-exit]])

(defn emit-constant [id frame]
  (let [c (get-in frame [:constants id])]
    ^:const
    [(case c
       (true false)
       [:get-static (if c :boolean/true :boolean/false) :boolean]

       nil
       [:visit-inst :opcodes/aconst-null]

       [:get-static (symbol (name (frame :class)) (str "const__" id)) (class c)])]))

(defmethod -emit :const
  [{:keys [id]} frame]
  (emit-constant id frame))

(defn emit-var [var frame]
  (emit-constant (get-in frame [:vars var]) frame))

(defmethod -emit :var
  [{:keys [var]} frame]
  (into
   (emit-var var frame)
   [:invoke-virtual [(if (u/dynamic? var) :get :get-raw-root)] :object]))

(defmethod -emit-set! :var
  [{:keys [var val]} frame]
  `[~@(emit-var var frame)
    ~@(emit val frame)
    [:invoke-virtual [:set :object] :object]])

(defmethod -emit :the-var
  [{:keys [var]} frame]
  (emit-var var frame))

(defmethod -emit :def
  [{:keys [var meta init]} frame]
  `[~@(emit-var var frame)
    ~@(when (u/dynamic? var) ;; why not when macro?
        [[:push true]
         [:invoke-virtual [:set-dynamic :bool] :var]])
    ~@(when meta
      (into
       [[:dup]]
       (conj
        (emit meta frame)
        [:check-cast :i-persistent-map]
        [:invoke-virtual [:set-meta :i-persistent-map] :void])))
    ~@(when init
        (into
         [[:dup]]
         (conj
          (emit init frame)
          [:invoke-virtual [:bind-root :object] :void])))])

(defmethod -emit :set!
  [{:keys [target val]} frame]
  (-emit-set! target val frame))

(defn emit-as-array [list frame]
  (into
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
   [:invoke-static [:rt/map-unique-keys :objects] :i-persistent-map]))

(defmethod -emit :vector
  [{:keys [items]} frame]
  (conj
   (emit-as-array items frame)
   [:invoke-static [:rt/vector :objects] :i-persistent-vector]))

(defmethod -emit :set
  [{:keys [items]} frame]
  (conj
   (emit-as-array items frame)
   [:invoke-static [:rt/set :objects] :i-persistent-set]))

(defmethod -emit :with-meta
  [{:keys [meta expr]} frame]
  (into
   (emit expr frame)
   (into
    [[:check-cast :i-obj]]
    (conj
     (emit meta frame)
     [:check-cast :i-persistent-map]
     [:invoke-interface [:i-obj/with-meta :i-persistent-map] :i-obj]))))

(defmethod -emit :do
  [{:keys [statements ret]} frame]
  (vec (mapcat #(emit % frame) (conj statements ret))))
