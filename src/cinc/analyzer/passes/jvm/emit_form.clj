(ns cinc.analyzer.passes.jvm.emit-form)

(defmulti -emit-form :op)

(defmethod -emit-form :local
  [{:keys [name]}]
  name)

(defmethod -emit-form :var
  [{:keys [name]}]
  name)

(defmethod -emit-form :const
  [{:keys [form]}]
  form)

(defmethod -emit-form :quote
  [{:keys [expr]}]
  (list 'quote (-emit-form expr)))

(defmethod -emit-form :vector
  [{:keys [items]}]
  (mapv -emit-form items))

(defmethod -emit-form :set
  [{:keys [items]}]
  (set (mapv -emit-form items)))

(defmethod -emit-form :map
  [{:keys [keys vals]}]
  (apply hash-map (interleave (mapv -emit-form keys)
                              (mapv -emit-form vals))))

;; discard meta
(defmethod -emit-form :with-meta
  [{:keys [expr]}]
  (-emit-form expr))

(defmethod -emit-form :the-var
  [{:keys [^clojure.lang.Var var]}]
  (list 'var (symbol (name (ns-name (.ns var)))
                     (name (.sym var)))))

(defmethod -emit-form :do
  [{:keys [ret statements]}]
  `(do ~@(mapv -emit-form statements)
       ~(-emit-form ret)))

(defmethod -emit-form :if
  [{:keys [test then else]}]
  `(if ~(-emit-form test)
     ~(-emit-form then)
     ~(-emit-form else)))

(defmethod -emit-form :new
  [{:keys [class args]}]
  `(new ~(-emit-form class) ~@(mapv -emit-form args)))

(defmethod -emit-form :set!
  [{:keys [target val]}]
  `(set! ~(-emit-form target) ~(-emit-form val)))

(defmethod -emit-form :try
  [{:keys [body catches finally]}]
  `(try ~(-emit-form body)
        ~@(mapv -emit-form catches)
        ~@(when finally
            [`(finally ~@(-emit-form finally))])))

(defmethod -emit-form :catch
  [{:keys [class local body]}]
  `(catch ~class ~(-emit-form local)
     ~(-emit-form body)))

(defmethod -emit-form :throw
  [{:keys [exception]}]
  `(throw ~(-emit-form exception)))

(defn emit-bindings [bindings]
  (mapcat (fn [{:keys [name init]}] [name (-emit-form init)]) bindings))

(defmethod -emit-form :letfn
  [{:keys [bindings body]}]
  `(letfn* [~@(emit-bindings bindings)]
           ~(-emit-form body)))

(defmethod -emit-form :let
  [{:keys [bindings body]}]
  `(let* [~@(emit-bindings bindings)]
           ~(-emit-form body)))

(defmethod -emit-form :loop
  [{:keys [bindings body]}]
  `(loop* [~@(emit-bindings bindings)]
           ~(-emit-form body)))

(defmethod -emit-form :recur
  [{:keys [exprs]}]
  `(recur ~@(mapv -emit-form exprs)))

(defmethod -emit-form :fn-method
  [{:keys [variadic? params body]}]
  (let [params (if variadic? (concat (butlast params) '[&] (last params)) params)]
    `(~(mapv -emit-form params)
      ~(-emit-form body))))

(defmethod -emit-form :fn
  [{:keys [name methods]}]
  `(fn* ~name
        ~@(mapv -emit-form methods)))

(defmethod -emit-form :def
  [{:keys [name doc init]}]
  `(def ~name ~@[doc] ~@[init]))

(defmethod -emit-form :invoke
  [{:keys [fn args]}]
  `(~fn ~@args))

(defmethod -emit-form :monitor-enter
  [{:keys [target]}]
  `(monitor-enter ~target))

(defmethod -emit-form :monitor-exit
  [{:keys [target]}]
  `(monitor-exit ~target))

(defmethod -emit-form :clojure.core/import*
  [{:keys [class]}]
  `(clojure.core/import* ~class))

(defn emit-form [ast]
  (str (seq (-emit-form ast))))
