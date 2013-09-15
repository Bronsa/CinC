(ns cinc.compiler.jvm.bytecode.emit
  (:require [cinc.analyzer.utils :as u]
            [cinc.analyzer.jvm.utils :refer [primitive? numeric? box] :as j.u]
            [clojure.string :as s]
            [cinc.compiler.jvm.bytecode.transform :as t]))

(defmulti -emit (fn [{:keys [op]} _] op))
(defmulti -emit-set! (fn [{:keys [op]} _] op))

(def nil-expr
  {:op :const :type :nil :form nil})

(defn emit-box [tag box]
  (if (and (primitive? tag)
           (not (primitive? box)))
    (cond
     (numeric? tag)
     [[:invoke-static [:clojure.lang.RT/box tag] :java.lang.Number]
      [:check-cast box]]
     (= Character box)
     [[:invoke-static [:clojure.lang.RT/box tag] :java.lang.Character]]
     (= Boolean box)
     [[:invoke-static [:clojure.lang.RT/box tag] :java.lang.Boolean]])
    [])) ;; TODO: emit unbox

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
               `[~@(when (= :untyped m)
                     (emit nil-expr frame))
                 ~@(when box
                     (emit-box tag (j.u/box tag)))
                 ~@(when cast
                     (emit-cast tag cast))])))))

(defmethod -emit :import
  [{:keys [class]} frame]
  [[:get-static :clojure.lang.RT/CURRENT_NS :clojure.lang.Var]
   [:invoke-virtual [:clojure.lang.Var/deref] :java.lang.Object]
   [:check-cast :clojure.lang.Namespace]
   [:push class]
   [:invoke-static [:java.lang.Class/forName :java.lang.String] :java.lang.Class]
   [:invoke-virtual [:clojure.lang.Namespace/importClass :java.lang.Class]] :java.lang.Class])

(defmethod -emit :throw
  [{:keys [exception]} frame]
  (into
   (emit exception frame)
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
  [const frame]
  (let [{:keys [id tag]} (get-in frame [:constants const])
        tag (or tag (class const))]
    ^:const
    [(case const
       (true false)
       [:get-static (if const :java.lang.Boolean/TRUE :java.lang.Boolean/FALSE)
        :java.lang.Boolean]

       nil
       [:insn :org.objectweb.asm.Opcodes/ACONST_NULL]

       (if (string? const) ;; or primitive number
         [:push const]
         [:get-static (frame :class) (str "const__" id) tag]))]))

(defmethod -emit :const
  [{:keys [form]} frame]
  (emit-constant form frame))

(defmethod -emit :quote
  [{:keys [const]} frame]
  (-emit const frame))

(defn emit-var [var frame]
  (emit-constant var frame))

(defmethod -emit :var
  [{:keys [var]} frame]
  (conj
   (emit-var var frame)
   [:invoke-virtual [(if (u/dynamic? var)
                          :clojure.lang.Var/get
                          :clojure.lang.Var/getRawRoot)] :java.lang.Object]))

(defmethod -emit-set! :var
  [{:keys [target val]} frame]
  `[~@(emit-var (:var target) frame)
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
        `[[:dup]
          ~@(emit meta frame)
          [:check-cast :clojure.lang.IPersistentMap]
          [:invoke-virtual [:clojure.lang.Var/setMeta :clojure.lang.IPersistentMap] :void]])
    ~@(when init
        `[[:dup]
          ~@(emit init frame)
          [:invoke-virtual [:clojure.lang.Var/bindRoot :java.lang.Object] :void]])])

(defmethod -emit :set!
  [ast frame]
  (-emit-set! ast frame))

(defn emit-as-array [list frame]
  `[[:push ~(int (count list))]
    [:new-array :java.lang.Object]
    ~@(mapcat (fn [i item]
                `[[:dup]
                  [:push ~(int i)]
                  ~@(emit item frame)
                  [:array-store :java.lang.Object]])
              (range) list)])

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
   `[[:check-cast :clojure.lang.IObj]
     ~@(emit meta frame)
     [:check-cast :clojure.lang.IPersistentMap]
     [:invoke-interface [:clojure.lang.IObj/withMeta :clojure.lang.IPersistentMap]
      :clojure.lang.IObj]]))

(defmethod -emit :do
  [{:keys [statements ret]} frame]
  (vec (mapcat #(emit % frame) (conj statements ret))))

(defn label []
  (keyword (gensym "label__")))

(defn local []
  (keyword (gensym "local__")))

(defmethod -emit :try
  [{:keys [body catches finally env tag]} frame]
  (let [[start-label end-label ret-label finally-label] (repeatedly label)
        catches (mapv #(assoc %
                         :start-label (label)
                         :end-label (label)) catches)
        context (:context env)
        [ret-local finally-local] (repeatedly local)]

    `[[:mark ~start-label]
      ~@(emit body frame)
      ~@(when (not= :statement context) ;; do this automatically on emit?
          [[:var-insn :java.lang.Object/ISTORE ret-local]])
      [:mark ~end-label]
      ~@(when finally
          (emit finally frame))
      [:go-to ~ret-label]

      ~@(mapcat
         (fn [{:keys [body start-label end-label local]}]
           `[[:mark ~start-label]
             [:var-insn :java.lang.Object/ISTORE (:name local)]
             ~@(emit body frame)
             ~@(when (not= :statement context)
                 [[:var-insn :java.lang.Object/ISTORE ret-local]])
             [:mark ~end-label]
             ~@(emit finally frame)
             [:go-to ~ret-label]])
         catches)
      ~@(when finally
          `[[:mark ~finally-label]
            [:var-insn :java.lang.Object/ISTORE ~finally-local]
            ~@(emit finally frame)
            [:var-insn :java.lang.Object/ILOAD ~finally-local]
            [:throw-exception]])

      [:mark ~ret-label]
      ~@(when (not= :statement context)
          `[[:var-insn [:java.lang.Object/ILOAD ~ret-local]]
            ~@(when tag
                [:check-cast tag])])
      [:mark ~(label)]

      ~@(for [{:keys [^Class class] :as c} catches]
          [:try-catch-block start-label end-label (:start-label c) class])

      ~@(when finally
          `[~[:try-catch-block start-label end-label finally-label nil]
            ~@(for [{:keys [start-label end-label] :as c} catches]
                [:try-catch-block start-label end-label finally-label nil])])

      ~@(for [{:keys [local start-label end-label] :as c} catches]
          [:local-variable (:name local) ; or :form?
           :objects nil start-label end-label (:name local)])])) ;; generate idx based on name

(defn emit-line-number
  [{:keys [line]} & [l]]
  (when line
    (let [l (or l (label))]
      [[:mark l]
       [:line-number line l]])))

(defmethod -emit :static-field
  [{:keys [field tag class env]} frame]
  `^:const
  [~@(emit-line-number env)
   ~[:get-static class field tag]])

(defmethod -emit-set! :static-field
  [{:keys [target val env]} frame]
  `[~@(emit-line-number env)
    ~@(emit val frame)
    [:dup]
    ~@(emit-cast (:tag val) (:tag target))
    ~[:put-static (:class target) (:field target) (:tag target)]])

(defmethod -emit :instance-field
  [{:keys [instance class field env tag]} frame]
  `^:const
  [~@(emit-line-number env)
   ~@(emit instance frame)
   ~[:check-cast class]
   ~[:get-field class field tag]])

(defmethod -emit-set! :instance-field
  [{:keys [target val env]} frame]
  `[~@(emit-line-number env)
    ~@(emit (:instance target) frame)
    ~[:check-cast (:class target)]
    ~@(emit val frame)
    [:dup-x1]
    ~@(emit-cast (:tag val) (:tag target))
    ~[:put-field (:class target) (:field target) (:tag target)]])

(defmethod -emit :keyword-invoke
  [{:keys [env fn args] :as ast} frame]
  (let [id (:id fn)
        [end-label fault-label] (repeatedly label)]
    `[~@(emit-line-number env)
      [:get-static ~(name (frame :class)) ~(str "thunk__" id) :clojure.lang.ILookupThunk]
      [:dup]
      ~@(emit fn frame)
      [:dup-x2]
      [:invoke-interface [:clojure.lang.ILookupThunk/get :java.lang.Object] :java.lang.Object]
      [:dup-x2]
      [:jump-insn :org.objectweb.asm.Opcodes/IF_ACMPEQ ~fault-label]
      [:pop]
      [:go-to ~end-label]

      [:mark ~fault-label]
      [:swap]
      [:pop]
      [:dup]
      [:get-static ~(name (frame :class)) ~(str "site__" id) :clojure.lang.KeywordLookupSite]
      [:swap]
      [:invoke-interface [:clojure.lang.ILookupThunk/fault :java.lang.Object] :java.lang.Object]
      [:dup]
      [:put-static ~(name (frame :class)) ~(str "thunk__" id) :clojure.lang.ILookupThunk]
      [:swap]
      [:invoke-interface [:clojure.lang.ILookupThunk/get :java.lang.Object] :java.lang.Object]
      [:mark ~end-label]]))

(defn arg-types [args]
  (mapv #(or (:cast %) (:tag %)) args))

(defmethod -emit :new
  [{:keys [env ^Class class args validated? tag]} frame]
  (if validated?
    `[[:new-instance ~class]
      [:dup]
      ~@(mapcat #(emit % frame) args)
      [:invoke-constructor [(keyword (.getName class) "<init>") ~@(arg-types args)] ~tag]]
    `[[:push ~(.getName class)]
      [:invoke-static [:java.lang.Class/forName :java.lang.String] :java.lang.Class]
      ~@(emit-as-array args frame)
      [:invoke-static [:clojure.lang.Reflector/invokeCostructor :objects] :java.lang.Object]]))

(defmethod -emit :static-call
  [{:keys [env tag validated? args method ^Class class]} frame]
  (if validated?
    `[~@(emit-line-number env)
      ~@(mapcat #(emit % frame) args)
      [:invoke-static [~(keyword (.getName class) (str method)) ~@(arg-types args)] ~tag]]
    `[[:push ~(.getName class)]
      [:invoke-static [:java.lang.Class/forName :java.lang.String] :java.lang.Class]
      [:push ~(str method)]
      ~@(emit-as-array args frame)
      [:invoke-static [:clojure.lang.Reflector/invokeStaticMethod
                       :java.lang.Class :java.lang.String :objects]
       :java.lang.Object]]))

(defmethod -emit :instance-call
  [{:keys [env tag validated? args method ^Class class instance]} frame]
  (if validated?
    `[~@(emit-line-number env)
      ~(emit instance frame)
      [:check-cast ~class]
      ~@(mapcat #(emit % frame) args)
      [(if (.isInterface class)
         :invoke-interface
         :invoke-virtual)
       [~(keyword (str class) (str method)) ~@(arg-types args)] ~tag]]
    `[~(emit instance frame)
      [:push ~(str method)]
      ~@(emit-as-array args frame)
      [:invoke-static [:clojure.lang.Reflector/invokeInstanceMethod
                       :java.lang.Object :java.lang.String :objects]
       :java.lang.Object]]))

(defmethod -emit :host-interop
  [{:keys [m-or-f target env]} frame]
  `[~@(emit target frame)
    [:push ~(str m-or-f)]
    [:invoke-static [:clojure.lang.Reflector/invokeNoArgInstanceMember :java.lang.Object :java.lang.String] :Object]])

(defmethod -emit-set! :host-interop
  [{:keys [target val env]} frame]
  `[~@(emit-line-number env)
    ~@(emit (:target target) frame)
    [:push ~(str (:m-or-f target))]
    ~@(emit val frame)
    [:invoke-static [:clojure.lang.Reflector/setInstanceField :java.lang.Object :java.lang.String :java.lang.Object] :java.lang.Object]])

;; todo: intrinsics
(defmethod -emit :if
  [{:keys [test then else env]} frame]
  (let [[null-label false-label end-label] (repeatedly label)]
    `[~@(emit-line-number env)
      ~@(emit test frame)
      ~@(if (:box test)
          [[:dup]
           [:if-null null-label]
           [:get-static :java.lang.Boolean/FALSE :java.lang.Boolean]
           [:jump-insn :org.objectweb.asm.Opcodes/IF_ACMPEQ false-label]]
          [[:if-z-cmp :org.objectweb.asm.commons.GeneratorAdapter/EQ false-label]])
      ~@(emit then frame)
      [:go-to ~end-label]
      [:mark ~null-label]
      [:pop]
      [:mark ~false-label]
      ~@(emit (or else nil-expr) frame)
      [:mark ~end-label]]))

(defn emit-args-and-invoke [args frame]
  `[~@(mapcat #(emit % frame) (take 20 args))
    ~@(when-let [args (seq (drop 20 args))]
        (emit-as-array args frame))
    [:invoke-interface [:clojure.lang.IFn/invoke ~@(repeat (min 21 (count args)) :java.lang.Object)] :java.lang.Object]])

(defmethod -emit :invoke
  [{:keys [fn args env]} frame]
  (if (and (= :var (:op fn))
           (u/protocol-node? (:var fn)))

    (let [[on-label call-label end-label] (repeatedly label)
          v (:var fn)
          [target & args] args
          id (:id fn)
          ^Class pinterface (:on-interface @(:protocol v))]
      `[~@(emit target frame)
        [:dup]

        [:load-this]
        [:get-field ~(name (frame :class)) ~(str "cached__class__" id) :java.lang.Class]
        [:jump-insn :org.objectweb.asm.Opcodes/IF_ACMPEQ ~call-label]

        [:dup]
        [:instance-of ~pinterface]
        [:if-z-cmp :org.objectweb.asm.commons.GeneratorAdapter/EQ ~on-label]

        [:dup]
        [:invoke-static [:clojure.lang.Util/classOf :java.lang.Object] :java.lang.Class]
        [:load-this]
        [:swap]
        [:put-field ~(frame :class) ~(str "cached__class__" id) :java.lang.Class]

        [:mark ~call-label]
        ~@(emit-var v frame)
        [:invoke-virtual [:clojure.lang.Var/getRawRoot] :java.lang.Object]
        [:swap]
        ~@(emit-args-and-invoke args frame)
        [:go-to ~end-label]

        [:mark ~on-label]

        ~@(mapcat #(emit % frame) args)
        [:invoke-interface [~(keyword (.getName pinterface)
                                      (munge (str (:name fn))))
                            ~@(repeat (count args) :java.lang.Object)] :java.lang.Object]

        [:mark ~end-label]])

    `[~@(emit fn frame)
      [:check-cast :clojure.lang.IFn]
      ~@(emit-args-and-invoke args frame)]))

(defn emit-shift-mask
  [{:keys [shift mask]}]
  (when (not (zero? mask))
    [[:push (int shift)]
     [:insn :org.objectweb.asm.Opcodes/ISHR]
     [:push (int mask)]
     [:insn :org.objectweb.asm.Opcodes/IAND]]))

(defn emit-test-ints
  [{:keys [test test-type] :as ast} frame default-label]
  (cond
   (nil? (:tag test))
   ;; reflection warning
   `[~@(emit test frame)
     [:instance-of :java.lang.Number]
     [:if-z-cmp :org.objectweb.asm.commons.GeneratorAdapter/EQ ~default-label]
     ~@(emit test frame) ;; can we avoid emitting this twice?
     [:check-cast :java.lang.Number]
     [:invoke-virtual [:java.lang.Number/intValue] :int]
     ~@(emit-shift-mask ast)]

   (#{Long/TYPE Integer/TYPE Short/TYPE Byte/TYPE} (:tag test))
   `[~@(emit (assoc test :cast Integer/TYPE) frame)
     ~@(emit-shift-mask ast)]

   :else
   [[:go-to default-label]]))

(defn emit-test-hashes
  [{:keys [test] :as ast} frame]
  `[~@(emit test frame)
    [:invoke-static [:clojure.lang.Util/hash :java.lang.Object] :int]
    ~@(emit-shift-mask ast)])

(defn emit-then-ints
  [tag comp test then default-label mask frame]
  (cond
   (nil? tag)
   `[~@(emit comp frame)
     ~@(emit test frame)
     [:invoke-static [:clojure.lang.Util/equiv :java.lang.Object :java.lang.Object] :boolean]
     [:if-z-cmp :org.objectweb.asm.commons.GeneratorAdapter/EQ ~default-label]
     ~@(emit then frame)]

   (= tag Long/TYPE)
   `[~@(emit test frame)
     ~@(emit comp frame)
     [:if-cmp :long :org.objectweb.asm.commons.GeneratorAdapter/NE ~default-label]
     ~@(emit then frame)]

   (#{Integer/TYPE Short/TYPE Byte/TYPE} tag)
   `[~@(when (not (zero? mask))
         `[~@(emit test frame)
           ~@(emit (assoc comp :cast Long/TYPE) frame)
           [:if-cmp :long :org.objectweb.asm.commons.GeneratorAdapter/NE ~default-label]])
     ~@(emit then frame)]

   :else
   [[:go-to default-label]]))

(defn emit-then-hashes
  [comp test then test-type default-label frame]
  `[~@(emit comp frame)
    ~@(emit test frame)
    ~@(if (= :hash-identity test-type)
        [[:jump-insn :org.objectweb.asm.Opcodes/IF_ACMPEQ default-label]]
        [[:invoke-static [:clojure.lang.Util/equiv :java.lang.Object :java.lang.Object] :boolean]
         [:if-z-cmp :org.objectweb.asm.commons.GeneratorAdapter/EQ ~default-label]])
    ~@(emit then frame)])

(defmethod -emit :case
  [{:keys [test default tests thens shift mask low high switch-type test-type skip-check? env] :as ast} frame]
  (let [testc (count tests)
        tests (zipmap (mapv :hash tests) (mapv :test))
        thens (apply sorted-map (mapcat (juxt :hash :then) thens))
        [default-label end-label] (repeatedly label)
        labels (zipmap (keys tests) (repeatedly label))]
    `[~@(emit-line-number env)
      ~@(if (= :int test-type)
          (emit-test-ints ast frame default-label)
          (emit-test-hashes ast frame))
      ~(if (= :sparse switch-type)
         [:lookup-switch-insn default-label (keys tests) (vals labels)] ; to array
         [:table-switch-insn low high default-label
          (mapv (fn [i] (if (contains? labels i) (labels i) default-label)) (range low high))])
      ~@(mapcat (fn [[i label]]
                  `[[:mark ~label]
                    ~@(cond
                       (= :int test-type)
                       (emit-then-ints (:tag test) test (tests i) (thens i) default-label mask frame)

                       (contains? skip-check? i)
                       [(emit (thens i) frame)]

                       :else
                       (emit-then-hashes test (tests i) (thens i) test-type default-label frame))
                    [:go-to ~end-label]])
                labels)]))

(defn emit-bindings [bindings labels frame]
  (mapcat (fn [{:keys [init tag] :as binding} label]
            `[~@(emit init frame)
              [:var-insn ~(keyword (if tag (.getName ^Class tag)
                                       "java.lang.Object") "ISTORE")
               ~(:name binding)]
              ~@(when label
                  [[:mark label]])])
          bindings labels))

(defn emit-let
  [{:keys [op bindings body env]} frame]
  (let [loop? (= :loop op)
        [end-label loop-label & labels] (repeatedly (+ 2 (count bindings)) label)]
    `[~@(emit-bindings bindings labels frame)
      ~@(emit body (merge frame (when loop? {:loop-label loop-label})))
      [:mark ~end-label]
      ~@(mapv (fn [{:keys [name tag]} label]
                [:local-variable name (or tag :java.lang.Object) nil label end-label name])
              bindings labels)]))
(defmethod -emit :let
  [ast frame]
  (emit-let ast frame))

(defmethod -emit :loop
  [ast frame]
  (emit-let ast frame))

(defmethod -emit :recur
  [{:keys [loop-locals args]} {:keys [loop-label] :as frame}]
  `[~@(mapcat (fn [arg binding]
                `[~@(emit arg frame)
                  ~(if (= :arg (:local binding))
                     [:store-arg (:name binding)]
                     [:var-insn :java.lang.Object/ISTORE (:name binding)])]) args loop-locals)
    [:go-to ~loop-label]])

(defn prim-or-obj [tag]
  (if (and tag (primitive? tag)) ;; should be only long/double
    tag
    :java.lang.Object))

;; handle invokePrim
(defmethod -emit :fn-method
  [{:keys [params tag fixed-arity variadic? body env]} frame]
  (let [method-name (if variadic? :do-invoke :invoke)
        return-type (prim-or-obj tag)
        arg-types (repeat (count params) :java.lang.Object)
        [loop-label end-label] (repeatedly label)

        code
        `[[:start-method]
          [:mark ~loop-label]
          ~@(emit-line-number env loop-label)
          ~@(emit body (assoc frame :loop-label loop-label))
          [:mark ~end-label]
          [:local-variable :this :java.lang.Object nil ~loop-label ~end-label :this]
          ~@(mapv (fn [{:keys [tag name]}]
                    [:local-variable name :java.lang.Object nil loop-label end-label name]) params) ;; cast when emitting locals?
          [:return-value]
          [:end-method]]]

    [{:op     :method
      :attr   #{:public}
      :method [(into [method-name] arg-types) return-type]
      :code   code}]))

;; emit local, deftype/reify, letfn

(defmethod -emit :local
  [{:keys [to-clear? local name tag]} {:keys [closed-overs class] :as frame}]
  (cond

   (closed-overs name)
   `[[:load-this]
     ~[:get-field class name tag]
     ~@(when to-clear?
         [[:load-this]
          [:insn :org.objectweb.asm.Opcodes/ACONST_NULL]
          [:put-field class name tag]])]

   (= :arg local)
   `[[:load-arg ~name] ;; why -1?
     ~@(when to-clear?
         [[:insn :org.objectweb.asm.Opcodes/ACONST_NULL]
          [:store-arg name]])]

   :else
   `[~[:var-insn (keyword (.getName ^Class tag) "ILOAD") name]
     ~@(when to-clear?
         [[:insn :org.objectweb.asm.Opcodes/ACONST_NULL]
          [:var-insn (keyword (.getName ^Class tag) "ISTORE") name]])]))

(defmulti -emit-value (fn [type _] type))

(defn emit-value [t form]
  `[~@(-emit-value t form)
    ~@(when (and (u/obj? form)
                 (seq (meta form)))
        `[[:check-cast :clojure.lang.IObj]
          ~@(emit-value :map (meta form))
          [:check-cast :clojure.lang.IPersistentMap]
          [:invoke-interface [:clojure.lang.IObj/withMeta :clojure.lang.IPersistentMap]
           :clojure.lang.IObj]])])

;; should probably never hit those
(defmethod -emit-value :nil [_ _]
  [[:insn :org.objectweb.asm.Opcodes/ACONST_NULL]])

(defmethod -emit-value :string [_ s]
  [[:push s]])

(defmethod -emit-value :bool [_ b]
  [[:get-static (if b :java.lang.Boolean/TRUE :java.lang.Boolean/FALSE)
    :java.lang.Boolean]])

(defmethod -emit-value :number [_ n]
  [[:push n]
   (cond
    (instance? Long n)
    [:invoke-static [:java.lang.Long/valueOf :long] :java.lang.Long]

    (instance? Integer n)
    [:invoke-static [:java.lang.Integer/valueOf :int] :java.lang.Integer]

    (instance? Double n)
    [:invoke-static [:java.lang.Double/valueOf :double] :java.lang.Double]

    (instance? Float n)
    [:invoke-static [:java.lang.Float/valueOf :float] :java.lang.Float])])

(defmethod -emit-value :class [_ c]
  (if (primitive? c)
    [[:get-static (box c) "TYPE" :java.lang.Class]]
    [[:push (.getName ^Class c)]
     [:invoke-static [:java.lang.Class/forName :java.lang.String] :java.lang.Class]]))

(defmethod -emit-value :symbol [_ s]
  `[~@(if-let [ns (namespace s)]
        [[:push (namespace s)]]
        [[:insn :org.objectweb.asm.Opcodes/ACONST_NULL]
         [:check-cast :java.lang.String]])
    [:push ~(name s)]
    [:invoke-static [:clojure.lang.Symbol/intern :java.lang.String :java.lang.String]
     :clojure.lang.Symbol]])

(defmethod -emit-value :keyword [_ k]
  `[~@(if-let [ns (namespace k)]
        [[:push (namespace k)]]
        [[:insn :org.objectweb.asm.Opcodes/ACONST_NULL]
         [:check-cast :java.lang.String]])
    [:push ~(name k)]
    [:invoke-static [:clojure.lang.Keyword/intern :java.lang.String :java.lang.String]
     :clojure.lang.Keyword]])

(defmethod -emit-value :var [_ ^clojure.lang.Var v]
  (let [name (str (.sym v))
        ns (str (ns-name (.ns v)))]
    [[:push ns]
     [:push name]
     [:invoke-static [:clojure.lang.RT/var :java.lang.String :java.lang.String]
      :clojure.lang.Var]]))

;; todo record/type

(defn emit-values-as-array [list]
  `[[:push ~(int (count list))]
    [:new-array :java.lang.Object]
    ~@(mapcat (fn [i item]
                `[[:dup]
                  [:push ~(int i)]
                  ~@(emit-value (u/classify item) item)
                  [:array-store :java.lang.Object]])
              (range) list)])

(defmethod -emit-value :map [_ m]
  (let [arr (mapcat identity m)]
    `[~@(emit-values-as-array arr)
      [:invoke-static [:clojure.lang.RT/map :objects] :clojure.lang.IPersistentMap]]))

(defmethod -emit-value :vector [_ v]
  `[~@(emit-values-as-array v)
    [:invoke-static [:clojure.lang.RT/vector :objects] :clojure.lang.IPersistentVector]])

(defmethod -emit-value :set [_ s]
  `[~@(emit-values-as-array s)
    [:invoke-static [:clojure.lang.RT/set :objects] :clojure.lang.IPersistentSet]])

(defmethod -emit-value :seq [_ s]
  `[~@(emit-values-as-array s)
    [:invoke-static [:java.util.Arrays/asList :objects] :java.util.List]
    [:invoke-static [:clojure.lang.PersistentList/create :java.util.List]
     :clojure.lang.IPersistentList]])

(defmethod -emit-value :char [_ c]
  [[:push c]
   [:invoke-static [:java.lang.Character/valueOf :char] :java.lang.Character]])

(defmethod -emit-value :regex [_ r]
  `[~@(emit-value :string (str r))
    [:invoke-static [:java.util.regex.Pattern/compile :java.lang.String]
     :java.util.regex.Pattern]])

(defn emit-constants [{:keys [class constants]}]
  (mapcat (fn [{:keys [val id tag type]}]
            (let [v (emit-value (or type (u/classify val)) val)]
              `[~@(if (primitive? tag)
                    (butlast v)
                    (conj v [:check-cast tag]))
                ~[:put-static class (str "const__" id) tag]]))
          (vals constants)))

(defn emit-keyword-callsites
  [{:keys [keyword-callsites constants class]}]
  (mapcat (fn [k]
            (let [{:keys [id]} (k constants)]
              `[[:new-instance :clojure.lang.KeywordLookupSite]
                [:dup]
                ~@(emit-value :keyword k)
                [:invoke-constructor [:clojure.lang.KeywordLookupSite/<init> :clojure.lang.Keyword] :void]
                [:dup]
                ~[:put-static class (str "site__" id) :clojure.lang.KeywordLookupSite]
                ~[:put-static class (str "thunk__" id) :clojure.lang.ILookupThunk]]))
          keyword-callsites))


;; TODO: generalize this for deftype/reify: needs  mutable field handling + altCtor + annotations

(defmethod -emit :fn
  [{:keys [local meta methods variadic? constants closed-overs keyword-callsites
           protocol-callsites env] :as ast}
   {:keys [class] :as frame}]
  (let [class-name (str (or class (munge (ns-name *ns*)))
                        "$"
                        (gensym (str (or (and (:form local)
                                              (s/replace (:form local) "." "_DOT_"))
                                         "fn") "__")))
        frame (merge frame
                     {:class              class-name
                      :constants          constants
                      :closed-overs       closed-overs
                      :keyword-callsites  keyword-callsites
                      :protocol-callsites protocol-callsites})
        super (if variadic? :clojure.lang.RestFn :clojure.lang.AFunction)

        consts (mapv (fn [{:keys [id tag]}]
                       {:op   :field
                        :attr #{:public :final :static}
                        :name (str "const__" id)
                        :tag  tag})
                     (vals constants))

        meta-field (when meta
                     [{:op   :field
                       :attr #{:public :final :static}
                       :name "__meta"
                       :tag  :clojure.lang.IPersistentMap}])

        keyword-callsites (mapcat (fn [k]
                                    (let [{:keys [id]} (k constants)]
                                      [{:op   :field
                                        :attr #{:public :final :static}
                                        :name (str "site__" id)
                                        :tag  :clojure.lang.KeywordLookupSite}
                                       {:op   :field
                                        :attr #{:public :final :static}
                                        :name (str "thunk__" id)
                                        :tag  :clojure.lang.ILookupThunk}]))
                                  keyword-callsites)

        protocol-callsites  (mapcat (fn [p]
                                      (let [{:keys [id]} (p constants)]
                                        [{:op   :field
                                          :attr #{:private}
                                          :name (str "cached__class__" id)
                                          :tag  :java.lang.Class}
                                         {:op   :field
                                          :attr #{:private}
                                          :name (str "cached__proto__fn__" id)
                                          :tag  :clojure.lang.AFunction}
                                         {:op   :field
                                          :attr #{:private}
                                          :name (str "cached__proto__impl__" id)
                                          :tag  :clojure.lang.IFn}]))
                                    protocol-callsites)

        closed-overs (mapv (fn [{:keys [name tag]}]
                             {:op   :field
                              :attr #{}
                              :name name
                              :tag  tag}) (vals closed-overs))

        ctor-types (into (if meta [:clojure.lang.IPersistentMap] [])
                         (repeat (count closed-overs) :java.lang.Object))

        class-ctors [{:op     :method
                      :attr   #{:public :static}
                      :method [[:<clinit>] :void]
                      :code   `[[:start-method]
                                ~@(emit-line-number env)
                                ~@(when (seq constants)
                                    (emit-constants frame))
                                ~@(when (seq keyword-callsites)
                                    (emit-keyword-callsites frame))
                                [:return-value]
                                [:end-method]]}
                     (let [[start-label end-label] (repeatedly label)]
                       {:op     :method
                        :attr   #{:public}
                        :method `[[:<init> ~@ctor-types] :void]
                        :code   `[[:start-method]
                                  ~@(emit-line-number env)
                                  [:label ~start-label]
                                  [:load-this]
                                  [:invoke-constructor [~(keyword (name super) "<init>")] :void]
                                  ~@(when meta
                                      [[:load-this]
                                       [:var-insn :clojure.lang.IPersistentMap/ILOAD :__meta]
                                       [:put-field ~class-name :__meta :clojure.lang.IPersistentMap]])

                                  ~@(mapcat
                                     (fn [{:keys [name tag]}]
                                       [[:var-insn (keyword (.getName ^Class tag) "ILOAD") name]
                                        [:put-field class-name name tag]])
                                     closed-overs)

                                  [:label ~end-label]
                                  [:return-value]
                                  [:end-method]]})]

        kw-callsite-method (when-let [kw-cs (seq (frame :keyword-callsites))]
                             (let [cs-count (count kw-cs)
                                   [end-label & labels] (repeatedly (inc cs-count) label)]
                               [{:op     :method
                                 :attr   #{:public}
                                 :method [[:swapThunk :int :clojure.lang.ILookupThunk] :void]
                                 :code   `[[:start-method]
                                           [:load-arg 0]
                                           ~[:table-switch-insn 0 (dec cs-count) end-label labels]
                                           ~@(mapcat (fn [i l]
                                                       [[:mark l]
                                                        [:load-arg 1]
                                                        [:put-static class-name (str "thunk__" i) :clojure.lang.ILookupThunk]
                                                        [:go-to end-label]])
                                                     (range) labels)
                                           [:mark ~end-label]
                                           [:return-value]
                                           [:end-method]]}]))

        variadic-method (when variadic?
                          (let [required-arity (->> methods (filter :variadic?) first :fixed-arity)]
                            [{:op     :method
                              :attr   #{:public}
                              :method [[:getRequiredArity] :int]
                              :code   `[[:start-method]
                                        [:push (int required-arity)]
                                        [:return-value]
                                        [:end-method]]}]))

        meta-methods (when meta
                       [{:op     :method
                         :attr   #{:public}
                         :method `[[:<init> ~@(rest ctor-types)] :void]
                         :code   `[[:start-method]
                                   [:load-this]
                                   [:insn :org.objectweb.asm.Opcodes/ACONST_NULL]
                                   [:load-args]
                                   [:invoke-constructor [~(keyword class-name "<init>")
                                                         ~@ctor-types] :void]
                                   [:return-value]
                                   [:end-method]]}
                        {:op     :method
                         :attr   #{:public}
                         :method`[[:meta] :clojure.lang.IPersistentMap]
                         :code   [[:start-method]
                                  [:load-this]
                                  [:get-field class-name :__meta :clojure.lang.IPersistentMap]
                                  [:return-value]
                                  [:end-method]]}
                        {:op     :method
                         :attr   #{:public}
                         :method`[[:withMeta :clojure.lang.IPersistentMap] :clojure.lang.IObj]
                         :code   `[[:start-method]
                                   [:new-instance ~class-name]
                                   [:dup]
                                   [:load-arg 0]
                                   ~@(mapcat
                                      (fn [{:keys [name tag]}]
                                        [[:load-this]
                                         [:get-field class-name name tag]])
                                      closed-overs)
                                   [:invoke-constructor [~(keyword class-name "<init>")
                                                         ~@ctor-types] :void]
                                   [:return-value]
                                   [:end-method]]}])

        jvm-ast
        {:op        :class
         :attr      #{:public :super :final}
         :name      (s/replace class-name \. \/)
         :super     (s/replace (name super) \. \/)
         :fields    `[~@consts ~@ keyword-callsites
                      ~@meta-field ~@closed-overs ~@protocol-callsites]
         :methods   `[~@class-ctors ~@kw-callsite-method ~@variadic-method
                      ~@meta-methods ~@(mapcat #(emit % frame) methods)]}

        bc
        (t/-compile jvm-ast)]

    (with-meta
      `[[:new-instance ~class-name]
        [:dup]
        ~@(when meta
            [[:insn :org.objectweb.asm.Opcodes/ACONST_NULL]])
        ~@(mapcat #(emit (assoc % :op :local) frame) closed-overs) ;; need to clear?
        [:invoke-constructor [~(keyword class-name "<init>")
                              ~@ctor-types] :void]]
      {:class (.defineClass (clojure.lang.RT/baseLoader) class-name bc nil)})))
