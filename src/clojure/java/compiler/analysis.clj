(in-ns 'clojure.java.compiler)

(defn- pprints [& args]
  (binding [*print-level* 6] (apply pprint args)))

(def ^:private prims
  {"byte" Byte/TYPE "bool" Boolean/TYPE "char" Character/TYPE "int" Integer/TYPE "long" Long/TYPE "float" Float/TYPE "double" Double/TYPE "void" Void/TYPE})

(defmulti maybe-class class)
(defmethod maybe-class java.lang.Class [c] c)
(defmethod maybe-class java.lang.String [s]
  (if-let [ret (prims s)]
    ret
    (if-let [ret (maybe-class (symbol s))]
      ret
      (try
        (RT/classForName s)
        (catch Exception e nil)))))
(defmethod maybe-class clojure.lang.Symbol [sym]
  ; TODO: I have no idea what this used to do
  ;    (if(Util.equals(sym,COMPILE_STUB_SYM.get()))
  ;    return (Class) COMPILE_STUB_CLASS.get();
  (when-not (namespace sym)
    (if-let [ret (prims (name sym))]
      ret
      (let [ret (resolve sym)]
        (when (class? ret)
          ret)))))

(defn- primitive? [o]
  (let [c (maybe-class o)]
    (and
      (not (or (nil? c) (= c Void/TYPE)))
      (.isPrimitive c))))

(defn- asm-type [s]
  (when s
    (let [class (maybe-class s)]
      (if class
        (Type/getType class)
        (Type/getType s)))))

(defn- asm-method
  ([{:keys [name return-types parameter-types]}]
    (apply asm-method name return-types parameter-types))
  ([name return-type & args]
    (Method. (str name) (asm-type return-type) (into-array Type (map asm-type args)))))

(defn dynamic? [v]
  (or (:dynamic (meta v))
      (when-let [var (cond
                       (symbol? v) (resolve v)
                       (var? v) v)]
        (.isDynamic var))))

(defn protocol-node? [ast]
  (when-let [name (-> ast :f :info :name)]
    (when-let [var (resolve name)]
      (-> var meta :protocol))))

(defmulti expression-type
  "Returns the type of the ast node provided, or Object if unknown. Respects :tag metadata"
  :op)

(defn tagged-type [o]
  (if-let [tag (-> o meta :tag)]
    tag
    java.lang.Object))

(defmethod expression-type :default [{type :type}]
  (if type type java.lang.Object))

(defmethod expression-type :constant [ast]
  [ast]
  (let [class (-> ast :form class)
        boxed (:box ast)]
    (condp #(isa? %2 %1) class
             java.lang.Integer (if boxed Long Long/TYPE)
             java.lang.Long (if boxed Long Long/TYPE)
             java.lang.Float (if boxed Double Double/TYPE)
             java.lang.Double (if boxed Double Double/TYPE)
             java.lang.String java.lang.String
             java.lang.Class java.lang.Class
             clojure.lang.Keyword clojure.lang.Keyword
             clojure.lang.Symbol clojure.lang.Symbol
             clojure.lang.IPersistentMap clojure.lang.IPersistentMap
             clojure.lang.IPersistentVector clojure.lang.IPersistentVector
             nil nil
             java.lang.Object)))

(defmethod expression-type :local [{:keys [info]}]
  (expression-type (:init info)))

(defmethod expression-type :def [form]
  clojure.lang.Var)

(defmethod expression-type :var
  [{:as form :keys [info]}]
  (let [sym (:name info)
        var (resolve (:form form))]
    (if var
      (class @var)
      java.lang.Object)))

(defmethod expression-type :do
  [{:keys [ret]}]
  (expression-type ret))

(defmethod expression-type :let
  [{:keys [ret]}]
  (expression-type ret))

(defmethod expression-type :if
  [{:keys [then else]}]
  (let [then-type (expression-type then)
        else-type (expression-type else)]
    (if (= then-type else-type)
      then-type
      (cond
        (nil? then-type) else-type
        (nil? else-type) then-type
        :else java.lang.Object))))

(defmethod expression-type :recur
  [form]
  nil)

(defmulti convertible? (fn [t1 t2] [(maybe-class t1) (maybe-class t2)]))

(defmethod convertible? [java.lang.Object java.lang.Number] [t1 ts] true)
(defmethod convertible? [java.lang.Object Long/TYPE] [t1 ts] true)
(defmethod convertible? :default [t1 t2]
  (if (= t1 t2) true (println "Conversion not implemented: " [t1 t2])))


(defn- match [name args]
  (fn match-method [method]
    (and (= name (:name method))
      (= (count args) (-> method :parameter-types count))
      (every? true? (map #(do #_(println (expression-type %1) %2) (convertible? (expression-type %1) (maybe-class %2))) args (:parameter-types method))))))

;; ---

(defn- rprintln [args]
  (println "---" args "---")
  args)

(defn- node? [form] (:op form))

(defn- walk-node [f form]
  (letfn [(walk-child [child]
            (if (node? child) (f child) child))
          (walk-children [child]
            (cond
              (node? child) (f child)

              (instance? clojure.lang.MapEntry child)
              (vec (map walk-children (seq child)))

              (instance? clojure.lang.Seqable child)
              (into (empty child) (map walk-children (seq child)))

              :else child))]
    (into {} (walk-children (seq form)))))


(defn- map-children [f form]
  (let [walk-children
          (fn [child]
            (if-let [s (and (sequential? child) (seq child))]
              (into [] (map f s))
              [(f child)]))]
    (reduce into [] (map walk-children (vals form)))))

(defn ast-processor
  [pres posts]
  (let [pre  (apply comp pres)
        post (apply comp posts)]
    (fn this [form]
             (let [form (pre form)
                   form (walk-node this form)]
               (post form)))))

(defmulti set-box :op)

(defn boxed? [form]
  (:box (set-box form)))

(defmethod set-box :map
  [form]
  (walk-node #(assoc % :box true) (assoc form :box true)))

(defmethod set-box :vector
  [form]
  (walk-node #(assoc % :box true) (assoc form :box true)))

(defmethod set-box :def
  [form]
  (assoc-in form [:init :box] true))

(defmethod set-box :invoke
  [form]
  (if-not (protocol-node? form)
    (walk-node #(assoc % :box true) (assoc form :box true))
    form))

(defmethod set-box :do
  [form]
  (if (:box form)
    (assoc-in form [:ret :box] true)
    form))

(defmethod set-box :let
  [form]
  ;; TODO: Smarter boxing for loops
  (let [form (if (:loop form) (assoc form :box true) form)]
    (if (:box form)
      (assoc-in form [:ret :box] true)
      form)))

(defmethod set-box :if
  [form]
  ;; Always box the test, otherwise (if nil) can't work
  (let [form (assoc-in form [:test :box] true)]
    (if (or (:box form) (boxed? (:then form)) (boxed? (:else form)))
      (-> form
        (assoc-in [:then :box] true)
        (assoc-in [:else :box] true))
      form)))

(defmethod set-box :fn
  [form]
  ;; TODO: this needs to check type hints, etc
  (walk-node #(assoc % :box true) form))

(defmethod set-box :reify
  [form]
  ;; TODO: this needs to check type hints, etc
  (walk-node #(assoc % :box true) form))

(defmethod set-box :method
  [form]
  (if (:box form)
    (assoc-in form [:ret :box] true)
    form))

(defmethod set-box :dot
  [form]
  (assoc-in form [:target :box] true))

(defmethod set-box :default
  [form]
  form)

(defmulti exported (fn [attribute form] (:op form)))

(defmethod exported :default
  [attribute form]
  (attribute form))

(defmethod exported :fn [_ _] #{})
(defmethod exported :reify [_ _] #{})

(declare collect-vars)

(defmethod exported :let
  [attribute form]
  (condp = attribute
    ; lets shouldn't export their own locals as referenced, they still need to export any locals used in inits though
    :referenced-locals
    (let [bindings (:bindings form)
          inits (map :init bindings)
          init-vars (map collect-vars inits)
          init-locals (mapcat :referenced-locals init-vars)
          init-local-names (into #{} (map :name init-locals))
          locals (into #{} (map :name bindings))
          referenced-locals (:referenced-locals form)]
        (remove #(and (contains? locals (:name %)) (not (contains? init-local-names (:name %)))) referenced-locals))

    ;default
    (attribute form)))

(defn- collect-attribute
  [form attribute]
  (->> form
    (map-children (partial exported attribute))
    (reduce into #{})
    (assoc form attribute)))

(defn- collect
  [form & attributes]
  (reduce collect-attribute form attributes))

(defmulti collect-constants :op)
(defmethod collect-constants :default
  [form]
  (collect form :constants))

(defmethod collect-constants :constant
  [form]
  (assoc form :constants #{{:value (:form form) :type (expression-type form)}}))


(defmulti collect-callsites :op)
(defmethod collect-callsites :default
  [form]
  (collect form :callsites))

(defmethod collect-callsites :invoke
  [form]
  (let [s (-> form :f :info :name)]
    (if (protocol-node? form)
      (assoc form :callsites #{s})
      form)))


(defmulti collect-vars :op)
(defmethod collect-vars :default
  [form]
  (collect form :vars :referenced-locals))

(defmethod collect-vars :var
  [{:as form :keys [info env]}]
  (let [sym (:name info)
        lb (-> env :locals sym)
        v (clojure.analyzer/resolve-var env sym)
        o (resolve sym)]
    (when-not (:name v)
      (throw (Util/runtimeException (str "No such var: " sym))))
    (cond
      ;; Transform vars that represent classes into constants
      (instance? java.lang.Class o)
      (assoc form :op :constant :form o)
      ;; Transform vars into a new :local op, and track references to them so we know what to capture when we create closures
      lb
      (let [form (assoc form :op :local)]
        (assoc form :referenced-locals #{{:name sym :type (expression-type form)}}))
      :else
      (assoc form :vars #{sym}))))

(defmethod collect-vars :local
  [form]
  (assoc form :referenced-locals #{{:name (-> form :info :name) :type (expression-type form)}}))


(defmethod collect-vars :def
  [form]
  (assoc form :vars #{(:name form)}))

(defmulti compute-type :op)
(defmethod compute-type :default [form] form)

(defn- compute-host-method
  [class meth]
  (let [t (-> class type-reflect :members)
        matches (select (match (:name meth) (:params meth)) t)
        _ (when-not (= (count matches) 1)
            (throw (IllegalArgumentException.
              (str "No single method: " (:name meth) " of " class " found with arguments: " (:params meth)))))]
    (first matches)))

(defmethod compute-type :constant
  [form]
  (assoc form :type (expression-type form)))

(defmethod compute-type :var
  [form]
  (assoc form :type (expression-type form)))

(defmethod compute-type :local
  [form]
  (assoc form :type (expression-type form)))

(defmethod compute-type :method
  [form]
  (if (:class form)
    (let [class (maybe-class (:class form))
          host-method (compute-host-method class form)]
      (assoc form :host-method host-method :type (maybe-class (:return-type host-method))))
    form))

(defmethod compute-type :new
  [{:as form :keys [ctor]}]
  (assoc form :type (-> ctor :info :name resolve)))

;(defmethod compute-type :fn
  ; Symbol meta have a :tag?
  ; Var have a :tag?
  ; Find the correct overload in arglists, does it have a tag? )

(def process-frames (ast-processor [set-box]
                      [compute-type collect-constants collect-vars collect-callsites]))
