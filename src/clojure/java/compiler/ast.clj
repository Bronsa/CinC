(in-ns 'clojure.java.compiler)

(declare compute-type)

(defn expression-type [form]
  (if-let [type (:type form)]
    type
    (-> form compute-type :type)))

(defn protocol-node? [ast]
  (when-let [name (-> ast :f :info :name)]
    (when-let [var (resolve name)]
      (-> var meta :protocol))))

(defmulti convertible? (fn [t1 t2] [(maybe-class t1) (maybe-class t2)]))

(defmethod convertible? [java.lang.Object java.lang.Number] [t1 ts] true)
(defmethod convertible? [java.lang.Object Integer/TYPE] [t1 ts] true)
(defmethod convertible? [java.lang.Object Long/TYPE] [t1 ts] true)
(defmethod convertible? [Long/TYPE java.lang.Object] [t1 ts] true)
(defmethod convertible? [Long/TYPE Integer/TYPE] [t1 ts] true)

(defmethod convertible? :default [t1 t2]
  (if (= t1 t2) true (.isAssignableFrom t2 t1)))


(defn match [name args pred]
  (fn match-method [method]
    (let [meth-parms (map maybe-class (:parameter-types method))]
      (and (= name (:name method))
           (= (count args) (count meth-parms))
           (every? true? (map pred args meth-parms))))))

;; ---

(defn- walk-node [f form]
  (walk form f))

(defn- map-children [f form]
  (map f (children form)))

(defn ast-processor
  [pres posts]
  (let [pre  (apply comp pres)
        post (apply comp posts)]
    (fn this [form]
      (when form
        (let [form (pre form)
              form (walk form this)]
          (post form))))))

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

(defmethod set-box :binding
  [form]
  (if (:box form)
    (assoc-in form [:init :box] true)
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
  (case attribute
    ; lets shouldn't export their own locals as referenced, they still need to export any locals used in inits though
    :referenced-locals
    (let [bindings (:bindings form)
          init-locals (mapcat :referenced-locals bindings)
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
  (assoc form :constants #{{:value (:form form) :type (:type form)}}))


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

;; ---

(defmulti collect-vars :op)
(defmethod collect-vars :default
  [form]
  (collect form :vars :referenced-locals))

(defmethod collect-vars :var
  [{:as form :keys [info env]}]
  (let [v (:name info)]
    (if-not (-> env :locals v)
      (assoc form :vars #{v})
      (assoc form :referenced-locals #{{:name (-> form :info :name) :type (:type form)}}))))

(defmethod collect-vars :def
  [form]
  (assoc form :vars #{(:name form)}))

(defmulti transform :op)
(defmethod transform :default [form] form)
(defmethod transform :var
  [{:as form :keys [info env]}]
  (let [sym (:name info)
        v (resolve-var env sym)
        o (resolve sym)]
    (when-not (:name v)
      (throw (Util/runtimeException (str "No such var: " sym))))
    (cond
      ;; Transform vars that represent classes into constants
      (instance? java.lang.Class o)
      (assoc form :op :constant :form o :type java.lang.Class)
      :else
      form)))

(defmulti compute-type :op)
(defmethod compute-type nil [form] form)
;(defmethod compute-type :default [form] form)

(defmethod compute-type :def
  [form]
  (assoc form :type clojure.lang.Var))

(defmethod compute-type :vector [form] (assoc form :type clojure.lang.IPersistentVector))
(defmethod compute-type :map [form] (assoc form :type clojure.lang.IPersistentMap))

(defmethod compute-type :constant
  [{:as form :keys [box]}]
  (let [class (class (:form form))
        type (condp #(isa? %2 %1) class
               java.lang.Integer (if box java.lang.Long Long/TYPE)
               java.lang.Long (if box java.lang.Long Long/TYPE)
               java.lang.Float (if box java.lang.Double Double/TYPE)
               java.lang.Double (if box java.lang.Double Double/TYPE)
               java.lang.String java.lang.String
               java.lang.Class java.lang.Class
               clojure.lang.Keyword clojure.lang.Keyword
               clojure.lang.Symbol clojure.lang.Symbol
               clojure.lang.IPersistentMap clojure.lang.IPersistentMap
               clojure.lang.IPersistentVector clojure.lang.IPersistentVector
               java.lang.Object)]
  (assoc form :type type)))

(defn- compute-local-type
  [info]
  (if-let [init (:init info)]
    (expression-type init)
    java.lang.Object))

(defmethod compute-type :var
  [{:as form :keys [info env]}]
  ;; TODO: Check :tag
  (let [sym (:name info)
        lb (-> env :locals sym)
        var (resolve sym)
        type (if var (class @var))]
    (if lb
      (assoc form :type (compute-local-type info))
      (assoc form :type type)))) ;; TODO: Fail here if var doesn't resolve?

(defmethod compute-type :fn
  [form]
  (assoc form :type clojure.lang.IFn))

(defmethod compute-type :invoke
  [form]
  ; Symbol meta have a :tag?
  ; Var have a :tag?
  ; Find the correct overload in arglists, does it have a tag? )
  (let [tag (-> form :f :info :name resolve meta :tag)]
    (assoc form :type tag)
    (assoc form :type java.lang.Object)))

(defn compute-host-method
  [env class name args]
  (let [members (-> class type-reflect :members)
        matches (select (match name args convertible?) members)]
    (if (= (count matches) 1)
      (first matches)
      (let [matches (select (match name args =) matches)]
        (if (= (count matches) 1)
              (first matches))))))

(defn compute-host-field
  [env class field]
  (let [members (-> class (type-reflect :ancestors true) :members)
        matches (select #(= (:name %) field) members)]
    (if (= (count matches) 1)
      (first matches)
      (when *warn-on-reflection*
        (.format (RT/errPrintWriter)
          "Reflection warning, %s:%d - reference to field %s can't be resolved.\n"
          (into-array Object [*file* (:line env) (name field)]))
        nil))))

(defmethod compute-type :method
  [{:as form :keys [env class name params]}]
  (if-let [class (maybe-class class)]
    (let [host-method (compute-host-method env class name (map tagged-type params))]
      (assoc form :host-method host-method :type (maybe-class (:return-type host-method))))
    form))

;(defn- )
;meth (find-best-method class name args
;                             (apply str "No single method: " name " of class: " class " found with args: " (map :type args)))
;{:keys [name return-type parameter-types]} meth
;m (apply asm-method name return-type parameter-types)
;return-type (maybe-class return-type)
;parameter-types (map maybe-class parameter-types)

(defmethod compute-type :dot
  [{:as form :keys [target field method args env box]}]
  (if-let [class (expression-type target)]
    (if field
      (let [host-field (compute-host-field env class field)
            type (-> host-field :type maybe-class)]
        (assoc form :host-field host-field :type type))
      (let [host-method (compute-host-method env class method (map expression-type args))
            type (-> host-method :return-type maybe-class)]
        (assoc form :host-method host-method :type type)))
    form))

(defmethod compute-type :reify
  [{:as form :keys [name]}]
  (let [name (if name name (gensym "reify__"))]
    (assoc form :name name :class (resolve name))))

(defmethod compute-type :new
  [{:as form :keys [ctor]}]
  (assoc form :type (-> ctor :info :name resolve)))

(defmethod compute-type :do
  [{:as form :keys [ret]}]
  (assoc form :type (expression-type ret)))

(defmethod compute-type :binding
  [{:as form :keys [init]}]
  (assoc form :type (expression-type init)))

(defmethod compute-type :let
  [{:as form :keys [ret]}]
  (assoc form :type (expression-type ret)))

(defmethod compute-type :recur
  [form]
  form)

(defmethod compute-type :if
  [{:as form :keys [then else]}]
  (let [then-type (expression-type then)
        else-type (expression-type else)
        type (if (= then-type else-type)
               then-type
               (cond
                 (nil? then-type) else-type
                 (nil? else-type) then-type
                 (convertible? else-type then-type) then-type
                 (convertible? then-type else-type) else-type
                 :else nil))]
    (assoc form :type type)))

(def process-frames (ast-processor [set-box]
                      [collect-constants collect-vars collect-callsites compute-type transform]))
