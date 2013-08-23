(ns cinc.compiler.jvm.bytecode.emit
  (:require [cinc.analyzer.utils :as u]
            [cinc.analyzer.jvm.utils :refer [asm-type primitive?]]))

(defmulti -emit (fn [{:keys [op]} _] op))
(defmulti -emit-set! (fn [{:keys [op]} _] op))

(def nil-expr
  {:op :const :type :nil :form nil})

;; TODO: emit box/unbox
(defn emit-box [tag box]
  [])

(defn emit-cast [tag cast]
  (if (not (or (primitive? tag)
             (primitive? cast)))
    [[:check-cast cast]]
    (emit-box tag cast)))

(defn emit
  ([ast]
     (emit ast {}))
  ([{:keys [env box tag cast] :as ast} frame]
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
               (when cast
                 (emit-cast tag cast))
               (when box
                 (emit-box tag box)))))))

(defmethod -emit :import
  [{:keys [class]} frame]
  [[:get-static :clojure.lang.RT/CURRENT_NS :var]
   [:invoke-virtual [:clojure.lang.Var/deref] :java.lang.Object]
   [:check-cast :clojure.lang.Namespace]
   [:push class]
   [:invoke-static [:java.lang.Class/forName :java.lang.String] :java.lang.Class]
   [:invoke-virtual [:clojure.lang.Namespace/importClass :java.lang.Class]] :java.lang.Class])

(defmethod -emit :throw
  [{:keys [exception]} frame]
  (into
   (emit exception)
   [:check-cast :java.lang.Throwable]
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

(defn emit-constant
  ([id frame] (emit-constant id nil frame))
  ([id tag frame]
     (let [c (get-in frame [:constants id])
           tag (or tag (class c))]
       ^:const
       [(case c
          (true false)
          [:get-static (if c :java.lang.Boolean/TRUE :java.lang.Boolean/FALSE)
           :java.lang.Boolean]

          nil
          [:insn :org.objectweb.asm.Opcodes/ACONST_NULL]

          [:get-static (keyword (name (frame :class)) (str "const__" id)) tag])])))

(defmethod -emit :const
  [{:keys [id tag]} frame]
  (emit-constant id tag frame))

(defn emit-var [var frame]
  (emit-constant (get-in frame [:vars var]) frame))

(defmethod -emit :var
  [{:keys [var]} frame]
  (into
   (emit-var var frame)
   [:invoke-virtual [(if (u/dynamic? var)
                       :clojure.lang.Var/get
                       :clojure.lang.Var/getRawRoot)] :java.lang.Object]))

(defmethod -emit-set! :var
  [{:keys [var val]} frame]
  `[~@(emit-var var frame)
    ~@(emit val frame)
    [:invoke-virtual [:clojure.lang.Var/set :java.lang.Object] :java.lang.Object]])

(defmethod -emit :the-var
  [{:keys [var]} frame]
  (emit-var var frame))

(defmethod -emit :def
  [{:keys [var meta init]} frame]
  `[~@(emit-var var frame)
    ~@(when (u/dynamic? var) ;; why not when macro?
        [[:push true]
         [:invoke-virtual [:clojure.lang.Var/setDynamic :boolean] :clojure.lang.Var]])
    ~@(when meta
      (into
       [[:dup]]
       (conj
        (emit meta frame)
        [:check-cast :clojure.lang.IPersistentMap]
        [:invoke-virtual [:clojure.lang.Var/setMeta :clojure.lang.IPersistentMap] :void])))
    ~@(when init
        (into
         [[:dup]]
         (conj
          (emit init frame)
          [:invoke-virtual [:clojure.lang.Var/bindRoot :java.lang.Object] :void])))])

(defmethod -emit :set!
  [{:keys [target val]} frame]
  (-emit-set! target val frame))

(defn emit-as-array [list frame]
  (into
   [[:push (int (count list))]
    [:new-array :java.lang.Object]]
   (mapcat (fn [i item]
             (into
              [[:dup]
               [:push (int i)]]
              (conj
               (emit item frame)
               [:array-store :java.lang.Object])))
           (range) list)))

(defmethod -emit :map
  [{:keys [keys vals]} frame]
  (conj
   (emit-as-array (interleave keys vals) frame)
   [:invoke-static [:clojure.lang.RT/mapUniqueKeys :objects] :clojure.lang.IPersistentMap]))

(defmethod -emit :vector
  [{:keys [items]} frame]
  (conj
   (emit-as-array items frame)
   [:invoke-static [:clojure.lang.RT/vector :objects] :clojure.lang.IPersistentVector]))

(defmethod -emit :set
  [{:keys [items]} frame]
  (conj
   (emit-as-array items frame)
   [:invoke-static [:clojure.lang.RT/set :objects] :clojure.lang.IPersistentSet]))

(defmethod -emit :with-meta
  [{:keys [meta expr]} frame]
  (into
   (emit expr frame)
   (into
    [[:check-cast :clojure.lang.IObj]]
    (conj
     (emit meta frame)
     [:check-cast :clojure.lang.IPersistentMap]
     [:invoke-interface [:clojure.lang.IObj/withMeta :clojure.lang.IPersistentMap]
      :clojure.lang.IObj]))))

(defmethod -emit :do
  [{:keys [statements ret]} frame]
  (vec (mapcat #(emit % frame) (conj statements ret))))

(defn label []
  (keyword (gensym "label__")))

(defn local [] ;; use :local :name?
  (keyword (gensym "local__")))

(defmethod -emit :try
  [{:keys [body catches finally env]} frame]
  (let [[start-label end-label ret-label finally-label] (repeatedly label)
        catches (mapv #(assoc %
                         :start-label (label)
                         :end-label (label)
                         :c-local (local)) catches)
        context (:context env)
        [ret-local finally-local] (repeatedly local)]

    `[[:mark ~start-label]
      ~@(emit body frame)
      ~@(when (not= :statement context) ;; do this automatically on emit?
          [[:var-insn :istore :java.lang.Object ret-local]]) ;; specialize type?
      [:mark ~end-label]
      ~@(emit finally frame) ;; check for null?
      [:go-to ~ret-label]

      ~@(mapcat
         (fn [{:keys [body start-label end-label c-local]}]
           `[[:mark ~start-label]
             [:var-insn :istore :java.lang.Object c-local]
             ~@(emit body frame)
             ~@(when (not= :statement context)
                 [[:var-insn :istore :java.lang.Object ret-local]])
             [:mark ~end-label]
             ~@(emit finally frame)
             [:go-to ~ret-label]])
         catches)

      [:mark ~finally-label]
      [:var-insn :istore :java.lang.Object ~finally-local]
      ~@(emit finally frame)
      [:var-insn :iload :java.lang.Object ~finally-local]
      [:throw-exception]

      [:mark ~ret-label]
      ~@(when (not= :statement context)
          [[:var-insn [:iload :java.lang.Object ret-local]]])
      [:mark ~(label)]

      ~@(for [{:keys [^Class class] :as c} catches]
          [:try-catch-block start-label end-label (:start-label c)
           (-> class .getName (.replace \. \/))])

      [:try-catch-block start-label end-label finally-label nil]
      ~@(for [{:keys [start-label end-label] :as c} catches]
          [:try-catch-block start-label end-label finally-label nil])

      ~@(for [{:keys [local start-label end-label c-local] :as c} catches]
          [:local-variable (:name local) :objects nil start-label end-label c-local])]))

(defmethod -emit :static-field
  [{:keys [field tag class env]} frame]
  (let [l (label)
        line (:line env)]
    `[~@(when line
          [[:mark l]
           [:line-number line l]])
      ~[:get-static class field tag]]))
