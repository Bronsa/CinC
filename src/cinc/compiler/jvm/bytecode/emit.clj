(ns cinc.compiler.jvm.bytecode.emit
  (:require [cinc.analyzer.utils :as u]
            [cinc.analyzer.jvm.utils :refer [primitive? numeric? box] :as j.u]
            [clojure.string :as s]
            [cinc.compiler.jvm.bytecode.transform :as t]
            [cinc.compiler.jvm.bytecode.intrinsics :refer [intrinsic]]))

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
     [[:invoke-static [:clojure.lang.RT/box :char] :java.lang.Character]]
     (= Boolean box)
     [[:invoke-static [:clojure.lang.RT/box :boolean] :java.lang.Object]
      [:check-cast :java.lang.Boolean]])
    (when (primitive? box)
      [[:invoke-static [(keyword "clojure.lang.RT"
                                 (str (.getName ^Class box)
                                      "Cast"))
                        (if (primitive? tag) tag
                            :java.lang.Object)] box]])))

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
                 (when (and (not (:untyped m))
                            (not (:container m))
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
                     (if box
                       (when (not (and box (= cast (j.u/box tag))))
                         (emit-cast (j.u/box tag) cast))
                       ;;when-not (= tag cast) ;temporary disable until we stabilize
                       (emit-cast tag cast)))])))))

(defmethod -emit :import
  [{:keys [class]} frame]
  [[:get-static :clojure.lang.RT/CURRENT_NS :clojure.lang.Var]
   [:invoke-virtual [:clojure.lang.Var/deref] :java.lang.Object]
   [:check-cast :clojure.lang.Namespace]
   [:push (.getName ^Class class)]
   [:invoke-static [:java.lang.Class/forName :java.lang.String] :java.lang.Class]
   [:invoke-virtual [:clojure.lang.Namespace/importClass :java.lang.Class] :java.lang.Class]])

(defmethod -emit :throw
  [{:keys [exception]} frame]
  (conj
   (emit (assoc exception :cast :java.lang.Throwable) frame)
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
       [:insn :ACONST_NULL]
       ;; push primitive numbers
       [:get-static (frame :class) (str "const__" id) tag])]))

(defmethod -emit :const
  [{:keys [form]} frame]
  (emit-constant form frame))

(defmethod -emit :quote
  [{:keys [expr]} frame]
  (-emit expr frame))

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
          ~@(emit (assoc meta :cast :clojure.lang.IPersistentMap) frame)
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
   (emit (assoc expr :cast :clojure.lang.IObj) frame)
   `[~@(emit (assoc meta :cast :clojure.lang.IPersistentMap) frame)
     [:invoke-interface [:clojure.lang.IObj/withMeta :clojure.lang.IPersistentMap]
      :clojure.lang.IObj]]))

(defmethod -emit :do
  [{:keys [statements ret]} frame]
  (with-meta
    (vec (mapcat #(emit % frame) (conj statements ret)))
    {:container true}))

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


    `^:container
    [[:mark ~start-label]
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
            [:var-insn :java.lang.Object/ISTORE ~(:name local)]
            ~@(emit body frame)
            ~@(when (not= :statement context)
                [[:var-insn :java.lang.Object/ISTORE ret-local]])
            [:mark ~end-label]
            ~@(when finally
                (emit finally frame))
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
         `[[:var-insn :java.lang.Object/ILOAD ~ret-local]
           ~@(when tag
               [[:check-cast tag]])])
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
   ~@(emit (assoc instance :cast class) frame)
   ~[:get-field class field tag]])

(defmethod -emit-set! :instance-field
  [{:keys [target val env]} frame]
  `[~@(emit-line-number env)
    ~@(emit (assoc (:instance target) :cast (:class target)) frame)
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
      [:jump-insn :IF_ACMPEQ ~fault-label]
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
      [:invoke-constructor [~(keyword (.getName class) "<init>") ~@(arg-types args)] :void]]
    `[[:push ~(.getName class)]
      [:invoke-static [:java.lang.Class/forName :java.lang.String] :java.lang.Class]
      ~@(emit-as-array args frame)
      [:invoke-static [:clojure.lang.Reflector/invokeCostructor :objects] :java.lang.Object]]))

(defn emit-intrinsic [^Class class method args]
  (let [args (mapv (fn [{:keys [cast tag]}] (or cast tag)) args)
        m    (str (.getMethod class (name method) (into-array Class args)))]
    (when-let [ops (intrinsic m)]
      (mapv (fn [op] [:insn op]) ops))))

(defmethod -emit :static-call
  [{:keys [env tag validated? args method ^Class class]} frame]
  (if validated?
    `[~@(emit-line-number env)
      ~@(mapcat #(emit % frame) args)
      ~@(or
         (emit-intrinsic class method args)
         `[[:invoke-static [~(keyword (.getName class) (str method)) ~@(arg-types args)] ~tag]])]
    `[[:push ~(.getName class)]
      [:invoke-static [:java.lang.Class/forName :java.lang.String] :java.lang.Class]
      [:push ~(str method)]
      ~@(emit-as-array (mapv #(assoc % :cast Object) args) frame)
      [:invoke-static [:clojure.lang.Reflector/invokeStaticMethod
                       :java.lang.Class :java.lang.String :objects]
       :java.lang.Object]
      ~@(when tag
          (emit-cast Object tag))]))

(defmethod -emit :instance-call
  [{:keys [env tag validated? args method ^Class class instance]} frame]
  (if validated?
    `[~@(emit-line-number env)
      ~@(emit (assoc instance :cast class) frame)
      ~@(mapcat #(emit % frame) args)
      [~(if (.isInterface class)
          :invoke-interface
          :invoke-virtual)
       [~(keyword (.getName class) (str method)) ~@(arg-types args)] ~tag]]
    `[~@(emit instance frame)
      [:push ~(str method)]
      ~@(emit-as-array (mapv #(assoc % :cast Object) args) frame)
      [:invoke-static [:clojure.lang.Reflector/invokeInstanceMethod
                       :java.lang.Object :java.lang.String :objects]
       :java.lang.Object]
      ~@(when tag
          (emit-cast Object tag))]))

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

(defmethod -emit :instance?
  [{:keys [target class]} frame]
  `[~@(emit target frame)
    ~[:instance-of class]])

(defmethod -emit :if
  [{:keys [test then else env]} frame]
  (let [[null-label false-label end-label] (repeatedly label)]
    `^:container
    [~@(emit-line-number env)
     ~@(emit test frame)
     ~@(if (:box test)
         [[:dup]
          [:if-null null-label]
          [:get-static :java.lang.Boolean/FALSE :java.lang.Boolean]
          [:jump-insn :IF_ACMPEQ false-label]]
         [[:if-z-cmp :EQ false-label]])
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
        [:jump-insn :IF_ACMPEQ ~call-label]

        [:dup]
        [:instance-of ~pinterface]
        [:if-z-cmp :EQ ~on-label]

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

    `[~@(emit (assoc fn :cast :clojure.lang.IFn) frame)
      ~@(emit-args-and-invoke args frame)]))

(defn emit-shift-mask
  [{:keys [shift mask]}]
  (when (not (zero? mask))
    [[:push (int shift)]
     [:insn :ISHR]
     [:push (int mask)]
     [:insn :IAND]]))

(defn emit-test-ints
  [{:keys [test test-type] :as ast} frame default-label]
  (cond
   (nil? (:tag test))
   ;; reflection warning
   `[~@(emit test frame)
     [:instance-of :java.lang.Number]
     [:if-z-cmp :EQ ~default-label]
     ~@(emit (assoc test :cast Integer/TYPE) frame) ;; can we avoid emitting this twice?
     ~@(emit-shift-mask ast)]

   (numeric? (:tag test))
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
     [:if-z-cmp :EQ ~default-label]
     ~@(emit then frame)]

   (= tag Long)
   `[~@(emit (assoc test :cast Long/TYPE) frame)
     ~@(emit (assoc comp :cast Long/TYPE) frame)
     [:if-cmp :long :NE ~default-label]
     ~@(emit then frame)]

   (#{Integer Short Byte} tag)
   `[~@(when (not (zero? mask))
         `[~@(emit (assoc test :cast Long/TYPE) frame)
           ~@(emit (assoc comp :cast Long/TYPE) frame)
           [:if-cmp :long :NE ~default-label]])
     ~@(emit then frame)]

   :else
   [[:go-to default-label]]))

(defn emit-then-hashes
  [comp test then test-type default-label frame]
  `[~@(emit comp frame)
    ~@(emit test frame)
    ~@(if (= :hash-identity test-type)
        [[:jump-insn :IF_ACMPEQ default-label]]
        [[:invoke-static [:clojure.lang.Util/equiv :java.lang.Object :java.lang.Object] :boolean]
         [:if-z-cmp :EQ default-label]])
    ~@(emit then frame)])

(defmethod -emit :case
  [{:keys [test default tests thens shift mask low high switch-type test-type skip-check? env] :as ast} frame]
  (let [testc (count tests)
        tests (zipmap (mapv :hash tests) (mapv :test tests))
        thens (apply sorted-map (mapcat (juxt :hash :then) thens))
        [default-label end-label] (repeatedly label)
        labels (zipmap (keys tests) (repeatedly label))]
    `^:container
    [~@(emit-line-number env)
     ~@(if (= :int test-type)
         (emit-test-ints ast frame default-label)
         (emit-test-hashes ast frame))
     ~(if (= :sparse switch-type)
        [:lookup-switch-insn default-label (keys tests) (vals labels)] ; to array
        [:table-switch-insn low high default-label
         (mapv (fn [i] (if (contains? labels i) (labels i) default-label)) (range low (inc high)))])
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
               labels)
     [:mark ~default-label]
     ~@(emit default frame)
     [:mark ~end-label]]))

(defn emit-bindings [bindings labels frame]
  (mapcat (fn [{:keys [init tag name] :as binding} label]
            `[~@(emit init frame)
              [:var-insn ~(keyword (if tag (.getName ^Class tag)
                                       "java.lang.Object") "ISTORE")
               ~name]
              ~@(when label
                  [[:mark label]])])
          bindings labels))

(defn emit-let
  [{:keys [op bindings body env]} frame]
  (let [loop? (= :loop op)
        [end-label loop-label & labels] (repeatedly (+ 2 (count bindings)) label)]
    `^:container
    [~@(emit-bindings bindings labels frame)
     [:mark ~loop-label]
     ~@(emit body (merge frame (when loop? {:loop-label loop-label
                                            :loop-locals bindings})))
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

(defn emit-letfn-bindings [bindings  class-names frame]
  (let [binds (set (mapv :name bindings))]
    (mapcat (fn [{:keys [init tag name]} class-name]
              (let [{:keys [closed-overs]} init]
                `[[:var-insn ~(keyword (if tag (.getName ^Class tag)
                                           "java.lang.Object") "ILOAD") ~name]
                  [:check-cast ~class-name]

                  ~@(mapcat (fn [[k c]]
                              (when (binds c)
                                `[~@(emit (assoc c :op :local)
                                          (assoc frame :closed-overs closed-overs))
                                  ~[:put-field class-name k (:tag c)]]))
                            closed-overs)

                  [:pop]]))
            bindings class-names)))


(defn emit-binds [bindings frame]
  (mapv
   (fn [{:keys [init tag name] :as binding}]
     (let [init (emit init frame)
           class-name (.getName ^Class (:class (meta init)))]
       `[~class-name
         [~@init
          [:var-insn ~(keyword (if tag (.getName ^Class tag)
                                   "java.lang.Object") "ISTORE")
           ~name]]]))
   bindings))

(defmethod -emit :letfn
  [{:keys [bindings body env]} frame]
  (let [[loop-label end-label] (repeatedly label)]
    `^:container
    [~@(emit-bindings (mapv #(assoc % :init nil-expr) bindings) (repeat nil) frame)

     ~@(let [binds (emit-binds bindings frame)
             bindings-emit(mapcat second binds)
             class-names (mapv first binds)]
         `[~@bindings-emit
           ~@(emit-letfn-bindings bindings class-names frame)])

     [:mark ~loop-label]
     ~@(emit body frame)
     [:mark ~end-label]
     ~@(mapv (fn [{:keys [name tag]}]
               [:local-variable name (or tag :java.lang.Object) nil loop-label end-label name])
             bindings)]))

(defmethod -emit :recur
  [{:keys [exprs]} {:keys [loop-label loop-locals] :as frame}]
  `[~@(mapcat (fn [arg binding]
                `[~@(emit arg frame)
                  ~(if (= :arg (:local binding))
                     [:store-arg (:arg-id binding)]
                     [:var-insn :java.lang.Object/ISTORE (:name binding)])]) exprs loop-locals)
    [:go-to ~loop-label]])

(defn prim-or-obj [tag]
  (if (and tag (primitive? tag)) ;; should be only long/double
    tag
    :java.lang.Object))

;; handle invokePrim
(defmethod -emit :fn-method
  [{:keys [params tag fixed-arity variadic? body env]} frame]
  (let [method-name (if variadic? :doInvoke :invoke)
        return-type (prim-or-obj tag)
        arg-types (repeat (count params) :java.lang.Object)
        [loop-label end-label] (repeatedly label)

        code
        `[[:start-method]
          [:local-variable :this :clojure.lang.AFunction nil ~loop-label ~end-label :this]
          ~@(mapv (fn [{:keys [tag name]}]
                    [:local-variable name :java.lang.Object nil loop-label end-label name])
                  params) ;; cast when emitting locals?
          [:mark ~loop-label]
          ~@(emit-line-number env loop-label)
          ~@(emit (assoc body :box true)
                  (assoc frame
                    :loop-label  loop-label
                    :loop-locals params))
          [:mark ~end-label]
          [:return-value]
          [:end-method]]]

    [{:op     :method
      :attr   #{:public}
      :method [(into [method-name] arg-types) :java.lang.Object]
      :code   code}]))

;; emit local, deftype/reify, letfn

(defmethod -emit :local
  [{:keys [to-clear? local name tag arg-id]} {:keys [closed-overs class] :as frame}]
  (let [to-clear? (and to-clear?
                       (not (primitive? tag)))]
   (cond

    (closed-overs name)
    `[[:load-this]
      ~[:get-field class name tag]
      ~@(when to-clear?
          [[:load-this]
           [:insn :ACONST_NULL]
           [:put-field class name tag]])]

    (= :arg local)
    `[[:load-arg ~arg-id]
      ~@(when to-clear?
          [[:insn :ACONST_NULL]
           [:store-arg arg-id]])
      ~@(when tag
          [[:check-cast tag]])]

    (= :fn local)
    [[:var-insn :clojure.lang.AFunction/ILOAD :this]]

    :else
    `[~[:var-insn (keyword (if tag (.getName ^Class tag)
                               "java.lang.Object") "ILOAD") name]
      ~@(when to-clear?
          [[:insn :ACONST_NULL]
           [:var-insn (keyword (if tag (.getName ^Class tag)
                                   "java.lang.Object") "ISTORE") name]])])))

(defmulti emit-value (fn [type _] type))

;; should probably never hit those
(defmethod emit-value :nil [_ _]
  [[:insn :ACONST_NULL]])

(defmethod emit-value :string [_ s]
  [[:push s]])

(defmethod emit-value :bool [_ b]
  [[:get-static (if b :java.lang.Boolean/TRUE :java.lang.Boolean/FALSE)
    :java.lang.Boolean]])

(defmethod emit-value :number [_ n]
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

(defmethod emit-value :class [_ c]
  (if (primitive? c)
    [[:get-static (box c) "TYPE" :java.lang.Class]]
    [[:push (.getName ^Class c)]
     [:invoke-static [:java.lang.Class/forName :java.lang.String] :java.lang.Class]]))

(defmethod emit-value :symbol [_ s]
  [[:push (namespace s)]
   [:push (name s)]
   [:invoke-static [:clojure.lang.Symbol/intern :java.lang.String :java.lang.String]
    :clojure.lang.Symbol]])

(defmethod emit-value :keyword [_ k]
  [[:push (namespace k)]
   [:push (name k)]
   [:invoke-static [:clojure.lang.Keyword/intern :java.lang.String :java.lang.String]
    :clojure.lang.Keyword]])

(defmethod emit-value :var [_ ^clojure.lang.Var v]
  (let [name (name (.sym v))
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

(defmethod emit-value :map [_ m]
  (let [arr (mapcat identity m)]
    `[~@(emit-values-as-array arr)
      [:invoke-static [:clojure.lang.RT/map :objects] :clojure.lang.IPersistentMap]]))

(defmethod emit-value :vector [_ v]
  `[~@(emit-values-as-array v)
    [:invoke-static [:clojure.lang.RT/vector :objects] :clojure.lang.IPersistentVector]])

(defmethod emit-value :set [_ s]
  `[~@(emit-values-as-array s)
    [:invoke-static [:clojure.lang.RT/set :objects] :clojure.lang.IPersistentSet]])

(defmethod emit-value :seq [_ s]
  `[~@(emit-values-as-array s)
    [:invoke-static [:java.util.Arrays/asList :objects] :java.util.List]
    [:invoke-static [:clojure.lang.PersistentList/create :java.util.List]
     :clojure.lang.IPersistentList]])

(defmethod emit-value :char [_ c]
  [[:push c]
   [:invoke-static [:java.lang.Character/valueOf :char] :java.lang.Character]])

(defmethod emit-value :regex [_ r]
  `[~@(emit-value :string (str r))
    [:invoke-static [:java.util.regex.Pattern/compile :java.lang.String]
     :java.util.regex.Pattern]])

(defn emit-constants [{:keys [class constants]}]
  (mapcat (fn [{:keys [val id tag type]}]
            (let [v (emit-value (or type (u/classify val)) val)]
              `[~@(if (primitive? tag)
                    (butlast v)
                    v)
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
   {:keys [class debug?] :as frame}]
  (let [class-name (str (or class (munge (ns-name *ns*)))
                        "$"
                        (gensym (str (or (and (:form local)
                                              (s/replace (:form local) "." "_DOT_"))
                                         "fn") "__")))
        old-frame frame
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

        closed-overs (mapv (fn [{:keys [name tag] :as local}]
                             (merge local
                                    {:op   :field
                                     :attr #{}
                                     :tag  (or tag Object)})) (vals closed-overs))

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
                                  ~@(mapcat
                                     (fn [{:keys [name tag]} id]
                                       [[:load-this]
                                        [:var-insn (keyword (.getName ^Class tag) "ILOAD") id]

                                        [:check-cast tag]
                                        [:put-field class-name name tag]])
                                     closed-overs (rest (range)))

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
                                        [:push ~(int required-arity)]
                                        [:return-value]
                                        [:end-method]]}]))

        meta-methods (when meta
                       [{:op     :method
                         :attr   #{:public}
                         :method `[[:<init> ~@(rest ctor-types)] :void]
                         :code   `[[:start-method]
                                   [:load-this]
                                   [:insn :ACONST_NULL]
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
         :debug?    debug?
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
            [[:insn :ACONST_NULL]])
        ~@(mapcat #(emit (assoc % :op :local) old-frame) closed-overs) ;; need to clear?
        [:invoke-constructor [~(keyword class-name "<init>")
                              ~@ctor-types] :void]]
      {:class (.defineClass ^clojure.lang.DynamicClassLoader (clojure.lang.RT/baseLoader)
                            class-name bc nil)})))
