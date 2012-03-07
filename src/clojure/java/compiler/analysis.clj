(in-ns 'clojure.java.compiler)

(def ^:private prims
  {"byte" Byte/TYPE "bool" Boolean/TYPE "char" Character/TYPE "int" Integer/TYPE "long" Long/TYPE "float" Float/TYPE "double" Double/TYPE})

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

(defn- var! [sym]
  (when-let [ns (namespace sym)]
    (RT/var ns (name sym))))

(defn dynamic? [v]
  (or (:dynamic (meta v))
      (when-let [var (cond
                       (symbol? v) (resolve v)
                       (var? v) v)]
        (.isDynamic var))))

(defmulti expression-type
  "Returns the type of the ast node provided, or Object if unknown. Respects :tag metadata"
  :op )

(defmethod expression-type :default [{tag :tag}]
  (if tag tag java.lang.Object))

(defmethod expression-type :constant [ast]
  [ast]
  (let [class (-> ast :form class)
        unboxed (:unboxed ast)]
    (condp = class
             java.lang.Integer (if unboxed Long/TYPE Long)
             java.lang.Long (if unboxed Long/TYPE Long)
             java.lang.Float (if unboxed Double/TYPE Double)
             java.lang.Double (if unboxed Double/TYPE Double)
             java.lang.String java.lang.String
             clojure.lang.Keyword clojure.lang.Keyword
             nil nil
             java.lang.Object)))

(defmulti convertible? (fn [t1 t2] [(maybe-class t1) (maybe-class t2)]))
(defmethod convertible? :default [t1 t2]
  (if (= t1 t2) true (println "Conversion not implemented: " [t1 t2])))


(defn- match [name args]
  (fn match-method [method]
    (and (= name (:name method))
      (= (count args) (-> method :parameter-types count))
      #_(every? true? (map #(do (println %) (convertible? %)) args (:parameter-types method))))))

;; ---


(defn- rprintln [args]
  (println "---" args)
  args)

(defn- node? [form] (:op form))

(defn- walk-node [f form]
  (let [walk-child
        (fn [child]
          (if (node? child) (f child) child))
        walk-children
        (fn [[key child]]
          (when-let [new-child (cond
                                  (node? child) (f child)

                                  (instance? clojure.lang.Seqable child)
                                  (into (empty child) (map walk-child  (seq child)))

                                  :else child)]
            [key new-child]))]
    (into {} (map walk-children (seq form)))))


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

(defmulti set-unbox :op)

(defmethod set-unbox :default
  [{:as form :keys [unbox op]}]
  (walk-node #(assoc % :unbox (or unbox (= op :let))) form))

(defmulti exported (fn [attribute form] (:op form)))

(defmethod exported :default
  [attribute form]
  (attribute form))

(defmethod exported :fn [_ _] #{})
(defmethod exported :reify [_ _] #{})

(defn- collect
  [attribute form]
  (->> form
    (map-children (partial exported attribute))
    (reduce into #{})
    (assoc form attribute)))

(defmulti collect-constants :op)
(defmethod collect-constants :default
  [form]
  (collect :constants form))

(defmethod collect-constants :constant
  [form]
  (assoc form :constants #{{:value (:form form) :type (expression-type form)}}))


(defmulti collect-callsites :op)
(defmethod collect-callsites :default
  [form]
  (collect :callsites form))

(defn- pprints [& args]
  (binding [*print-level* 5] (apply pprint args)))

(defmethod collect-callsites :invoke
  [form]
  (let [s (-> form :f :info :name)]
    (if (and s (-> s var! meta :protocol))
      (assoc form :callsites #{s})
      form)))

(defmulti collect-vars :op)
(defmethod collect-vars :default
  [form]
  (collect :vars form))

(defmethod collect-vars :var
  [{:as form :keys [info env]}]
  (let [sym (:name info)
        lb (-> env :locals sym)
        v (clojure.analyzer/resolve-var env sym)]
    (when-not (:name v)
      (throw (Util/runtimeException (str "No such var: " sym))))
    (if-not lb
      (assoc form :vars #{sym})
      form)))

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

(defmethod compute-type :method
  [form]
  (if (:class form)
    (let [class (maybe-class (:class form))
          host-method (compute-host-method class form)]
      (assoc form :host-method host-method :type (:return-type host-method)))
    form))

;(defmethod compute-type :fn
  ; Symbol meta have a :tag?
  ; Var have a :tag?
  ; Find the correct overload in arglists, does it have a tag? )

(def process-frames (ast-processor [set-unbox]
                      [collect-constants collect-vars collect-callsites compute-type]))
