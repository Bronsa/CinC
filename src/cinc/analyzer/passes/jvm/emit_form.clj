(ns cinc.analyzer.passes.jvm.emit-form)

(defmulti emit-form :op)

(defmethod emit-form :local
  [{:keys [name]}]
  name)

(defmethod emit-form :binding
  [{:keys [name]}]
  name)

(defmethod emit-form :var
  [{:keys [name]}]
  name)

(defmethod emit-form :const
  [{:keys [form]}]
  form)

(defmethod emit-form :quote
  [{:keys [expr]}]
  (list 'quote (emit-form expr)))

(defmethod emit-form :vector
  [{:keys [items]}]
  (mapv emit-form items))

(defmethod emit-form :set
  [{:keys [items]}]
  (set (mapv emit-form items)))

(defmethod emit-form :map
  [{:keys [keys vals]}]
  (apply hash-map (interleave (mapv emit-form keys)
                              (mapv emit-form vals))))

(defmethod emit-form :with-meta
  [{:keys [expr meta]}]
  (with-meta (emit-form expr)
    (emit-form meta)))

(defmethod emit-form :the-var
  [{:keys [^clojure.lang.Var var]}]
  (list 'var (symbol (name (ns-name (.ns var)))
                     (name (.sym var)))))

(defmethod emit-form :do
  [{:keys [ret statements]}]
  `(do ~@(mapv emit-form statements)
       ~(emit-form ret)))

(defmethod emit-form :if
  [{:keys [test then else]}]
  `(if ~(emit-form test)
     ~(emit-form then)
     ~(emit-form else)))

(defmethod emit-form :new
  [{:keys [class args]}]
  `(new ~(emit-form class) ~@(mapv emit-form args)))

(defmethod emit-form :set!
  [{:keys [target val]}]
  `(set! ~(emit-form target) ~(emit-form val)))

(defmethod emit-form :try
  [{:keys [body catches finally]}]
  `(try ~(emit-form body)
        ~@(mapv emit-form catches)
        ~@(when finally
            [`(finally ~@(emit-form finally))])))

(defmethod emit-form :catch
  [{:keys [class local body]}]
  `(catch ~class ~(emit-form local)
     ~(emit-form body)))

(defmethod emit-form :throw
  [{:keys [exception]}]
  `(throw ~(emit-form exception)))

(defn emit-bindings [bindings]
  (mapcat (fn [{:keys [name init]}]
            [name (emit-form init)])
          bindings))

(defmethod emit-form :letfn
  [{:keys [bindings body]}]
  `(letfn* [~@(emit-bindings bindings)]
           ~(emit-form body)))

(defmethod emit-form :let
  [{:keys [bindings body]}]
  `(let* [~@(emit-bindings bindings)]
           ~(emit-form body)))

(defmethod emit-form :loop
  [{:keys [bindings body]}]
  `(loop* [~@(emit-bindings bindings)]
           ~(emit-form body)))

(defmethod emit-form :recur
  [{:keys [exprs]}]
  `(recur ~@(mapv emit-form exprs)))

(defmethod emit-form :fn-method
  [{:keys [variadic? params body]}]
  (let [params (if variadic? (concat (butlast params) '[&] (last params)) params)]
    `(~(mapv emit-form params)
      ~(emit-form body))))

(defmethod emit-form :fn
  [{:keys [name methods]}]
  `(fn* ~name
        ~@(mapv emit-form methods)))

(defmethod emit-form :def
  [{:keys [name doc init]}]
  `(def ~name ~@[doc] ~@[(emit-form init)]))

(defmethod emit-form :invoke
  [{:keys [fn args]}]
  `(~fn ~@args))

(defmethod emit-form :monitor-enter
  [{:keys [target]}]
  `(monitor-enter ~target))

(defmethod emit-form :monitor-exit
  [{:keys [target]}]
  `(monitor-exit ~target))

(defmethod emit-form :import
  [{:keys [class]}]
  `(clojure.core/import* ~class))

(defmethod emit-form :class
  [{:keys [class]}]
  class)

(defmethod emit-form :new
  [{:keys [class]}]
  `(new ~class))

(defmethod emit-form :var
  [{:keys [^clojure.lang.Var var]}]
  `(var ~(symbol (name (.sym var)) (ns-name (.ns var)))))

(defmethod emit-form :method
  [{:keys [params body this name]}]
  (let [params (into [this] params)]
    `(~name ~(mapv emit-form params)
            ~(emit-form body))))

(defmethod emit-form :deftype
  [{:keys [name class-name fields interfaces methods]}]
  `(deftype* ~name ~class-name ~(mapv emit-form fields)
     :implements ~(vec interfaces)
     ~@(mapv emit-form methods)))

(defmethod emit-form :reify
  [{:keys [interfaces methods]}]
  `(reify* ~(vec interfaces)
           ~@(mapv emit-form methods)))

(defmethod emit-form :case
  [{:keys [test default tests thens shift mask low high switch-type test-type skip-check?]}]
  `(case* ~(emit-form test)
          ~shift ~mask
          ~(emit-form default)
          ~(apply sorted-map
                  (mapcat (fn [{:keys [hash test]} {:keys [then]}]
                            [hash [(emit-form test) (emit-form then)]])
                          tests thens))
          ~switch-type ~test-type ~skip-check?))

(defmethod emit-form :static-field
  [{:keys [class field]}]
  (symbol (.getName ^Class class) (name field)))

(defmethod emit-form :static-call
  [{:keys [class method args]}]
  `(~(symbol (.getName ^Class class) (name method))
    ~@(map emit-form args)))

(defmethod emit-form :instance-field
  [{:keys [instance field]}]
  `((symbol (str ".-" (name field))) ~(emit-form instance)))

(defmethod emit-form :instance-call
  [{:keys [instance method args]}]
  `((symbol (str "." (name method))) ~(emit-form instance)
    ~@(map emit-form args)))

(defmethod emit-form :host-expr
  [{:keys [target m-or-f]}]
  `((symbol (str "." (name m-or-f))) ~(emit-form target)))
