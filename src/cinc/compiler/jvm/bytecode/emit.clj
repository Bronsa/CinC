(ns cinc.compiler.jvm.bytecode.emit
  (:require [cinc.analyzer.utils :as u]
            [cinc.analyzer.jvm.utils :refer [asm-type primitive? numeric?] :as j.u]))

(defmulti -emit (fn [{:keys [op]} _] op))
(defmulti -emit-set! (fn [{:keys [op]} _] op))

(def nil-expr
  {:op :const :type :nil :form nil})

(defn emit-box [tag box]
  (if (and (primitive? tag)
           (not (primitive? box)))
    (cond
     (numeric? tag)
     [[:invoke-static [:clojure.lang.RT/box tag] :java.lang.Number] ; or bool/char
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
               (when (= :untyped m)
                 (emit nil-expr frame))
               (when box
                 (emit-box tag (j.u/box tag)))
               (when cast
                 (emit-cast tag cast)))))))

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

          (if (string? c)
            [:push c]
            [:get-static (keyword (name (frame :class)) (str "const__" id)) tag]))])))

(defmethod -emit :const
  [{:keys [id tag]} frame]
  (emit-constant id tag frame))

(defmethod -emit :quote
  [{:keys [const]} frame]
  (-emit const frame))

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
  [ast frame]
  (-emit-set! ast frame))

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

(defn local []
  (keyword (gensym "local__")))

(defmethod -emit :try
  [{:keys [body catches finally env]} frame]
  (let [[start-label end-label ret-label finally-label] (repeatedly label)
        catches (mapv #(assoc %
                         :start-label (label)
                         :end-label (label)) catches)
        context (:context env)
        [ret-local finally-local] (repeatedly local)]

    `[[:mark ~start-label]
      ~@(emit body frame)
      ~@(when (not= :statement context) ;; do this automatically on emit?
          [[:var-insn :java.lang.Object/ISTORE ret-local]]) ;; specialize type?
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
          [[:var-insn [:java.lang.Object/ILOAD ret-local]]])
      [:mark ~(label)]

      ~@(for [{:keys [^Class class] :as c} catches]
          [:try-catch-block start-label end-label (:start-label c)
           (-> class .getName (.replace \. \/))])

      ~@(when finally
          `[~[:try-catch-block start-label end-label finally-label nil]
            ~@(for [{:keys [start-label end-label] :as c} catches]
                [:try-catch-block start-label end-label finally-label nil])])

      ~@(for [{:keys [local start-label end-label] :as c} catches]
          [:local-variable (str (:name local)) ; or :form?
           :objects nil start-label end-label (:name local)])])) ;; generate idx based on name

(defn emit-line-number
  [{:keys [line]}]
  (when line
    (let [l (label)]
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
        [end-label fault-label] (constantly label)]
    `[~@(emit-line-number env)
      [:get-static ~(keyword (name (frame :class)) (str "thunk__" id)) :clojure.lang.ILookupThunk]
      [:dup]
      ~@(emit fn frame)
      [:dup-x2]
      [:invoke-interface [:clojure.lang.ILookupThunk/get :java.lang.Object] :java.lang.Object]
      [:dup-x2]
      [:jump-inst :org.objectweb.asm.Opcodes/IF_ACMPEQ ~fault-label]
      [:pop]
      [:go-to ~end-label]

      [:mark ~fault-label]
      [:swap]
      [:pop]
      [:dup]
      [:get-static ~(keyword (name (frame :class)) (str "site__" id)) :clojure.lang.KeywordLookupSite]
      [:swap]
      [:invoke-interface [:clojure.lang.ILookupThunk/fault :java.lang.Object] :java.lang.Object]
      [:dup]
      [:put-static ~(keyword (name (frame :class)) (str "thunk__" id)) :clojure.lang.ILookupThunk]
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
      ~@(mapv #(emit % frame) args)
      [:invoke-constructor ~class [:<init> ~@(arg-types args)] ~tag]]
    `[[:push ~(.getName class)]
      [:invoke-static [:java.lang.Class/forName :java.lang.String] :java.lang.Class]
      ~@(emit-as-array args frame)
      [:invoke-static [:clojure.lang.Reflector/invokeCostructor :objects] :java.lang.Object]]))

(defmethod -emit :static-call
  [{:keys [env tag validated? args method ^Class class]} frame]
  (if validated?
    `[~@(emit-line-number env)
      ~@(mapv #(emit % frame) args)
      [:invoke-static [~(keyword (str class) (str method)) ~@(arg-types args)] ~tag]]
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
      ~@(mapv #(emit % frame) args)
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
  `[~@(mapv #(emit % frame) (take 20 args))
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
        [:get-field ~(keyword (name (frame :class)) (str "cached__class__" id)) :java.lang.Class]
        [:jump-insn :org.objectweb.asm.Opcodes/IF_ACMPEQ ~call-label]

        [:dup]
        [:instance-of ~pinterface]
        [:if-z-cmp :org.objectweb.asm.commons.GeneratorAdapter/EQ ~on-label]

        [:dup]
        [:invoke-static [:clojure.lang.Util/classOf :java.lang.Object] :java.lang.Class]
        [:load-this]
        [:swap]
        [:put-field ~(keyword (name (frame :class)) (str "cached__class__" id)) :java.lang.Class]

        [:mark ~call-label]
        ~@(emit-var v frame)
        [:invoke-virtual [:clojure.lang.Var/getRawRoot] :java.lang.Object]
        [:swap]
        ~@(emit-args-and-invoke args frame)
        [:go-to ~end-label]

        [:mark ~on-label]

        ~@(mapv #(emit % frame) args)
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
    [[:push shift]
     [:insn :org.objectweb.asm.Opcodes/ISHR]
     [:push mask]
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
  [(mapcat (fn [{:keys [init tag] :as binding} label]
             `[~@(emit init frame)
               [:var-insn ~(keyword (if tag (.getName ^Class tag)
                                        "java.lang.Object") "ISTORE") ;; .getOpcode
                ~(:name binding)] ;; generate idx
               [:mark ~label]])
           bindings labels)])

(defn emit-let
  [{:keys [op bindings body env]} frame]
  (let [loop? (= :loop op)
        [end-label loop-label & labels] (repeatedly (+ 2 (count bindings)) label)]
    `[~@(emit-bindings bindings labels frame)
      ~@(emit body (merge frame (when loop? {:loop-label loop-label})))
      [:mark ~end-label]
      ~@(mapv (fn [{:keys [name tag]} label]
                [:local-variable (str name) (or tag :java.lang.Object) nil label end-label name])
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
