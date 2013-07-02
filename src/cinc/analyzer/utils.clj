(ns cinc.analyzer.utils
  (:import (clojure.lang IRecord IType IObj
                         IReference Var)
           java.util.regex.Pattern))

(defmulti walk (fn [{:keys [op]} f] op))

(defn walk-coll [f]
  (fn [coll]
    (into (empty coll)
          (mapv #(walk % f) coll))))

(defn walk-in [ast keys f]
  (update-in ast keys walk f))

(defn walk-in-coll [ast keys f]
  (update-in ast keys (walk-coll f)))

(defmethod walk :default [ast f]
  (f ast))

(defn ctx
  "Returns a copy of the passe environment with :context set to ctx"
  [env ctx]
  (assoc env :context ctx))

(definline record? [x]
  (instance? IRecord x))
(definline type? [x]
  (instance? IType x))
(definline obj? [x]
  (instance? IObj x))
(definline reference? [x]
  (instance? IReference x))
(definline regex? [x]
  (instance? Pattern x))

(defn classify
  "Returns a keyword describing the form type"
  [form]
  (cond
   (keyword? form) :keyword
   (symbol? form)  :symbol
   (string? form)  :string
   (number? form)  :number
   (type? form)    :type
   (record? form)  :record
   (map? form)     :map
   (vector? form)  :vector
   (set? form)     :set
   (seq? form)     :seq
   (char? form)    :char
   (regex? form)   :regex
   (class? form)   :class
   :else           :unknown))

(definline private? [var]
  (:private (meta var)))
(definline macro? [var]
  (:macro (meta var)))
(defn constant? [var]
  (:const (meta var)))

(defn resolve-ns [ns]
  (when ns
    (or (find-ns ns)
        ((ns-aliases *ns*) ns))))

(defn resolve-var
  ([sym] (resolve-var sym false))
  ([sym allow-macro?]
     (let [name (-> sym name symbol)
           ns (when-let [ns (namespace sym)]
                (symbol ns))
           full-ns (resolve-ns ns)]
       (when (or (not ns)
                 (and ns full-ns))
         (if-let [var (if full-ns
                        ((ns-interns full-ns) name)
                        ((ns-map *ns*) name))]
           (when (var? var)
             (let [var-ns (.ns ^Var var)]
               (when (and (not= *ns* var-ns)
                          (private? var))
                 (throw (ex-info (str "var: " sym " is not public") {:var sym})))
               (if (and (macro? var) (not allow-macro?))
                 (throw (ex-info (str "can't take value of a macro: " var) {:var var}))
                 var)))
           (when full-ns
             (throw (ex-info (str "no such var: " sym) {:var sym}))))))))

(defn maybe-var [sym]
  (try (resolve-var sym true)
       (catch Exception _)))

(defn get-line [x env]
  (or (-> x meta :line)
      (:line env)))
(defn get-col [x env]
  (or (-> x meta :column)
      (:column env)))
