;:   Copyright (c) Nicola Mometto, Rich Hickey & contributors.
;;   The use and distribution terms for this software are covered by the
;;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;;   which can be found in the file epl-v10.html at the root of this distribution.
;;   By using this software in any fashion, you are agreeing to be bound by
;;   the terms of this license.
;;   You must not remove this notice, or any other, from this software.

(ns clojure.tools.analyzer.utils
  (:import (clojure.lang IRecord IType IObj
                         IReference Var)
           java.util.regex.Pattern))

(defmacro update! [target f & args]
  (list 'set! target (list* f target args)))

(defn ctx
  "Returns a copy of the passe environment with :context set to ctx"
  [env ctx]
  (assoc env :context ctx))

(defn record? [x]
  (instance? IRecord x))
(defn type? [x]
  (instance? IType x))
(defn obj? [x]
  (instance? IObj x))
(defn reference? [x]
  (instance? IReference x))
(defn regex? [x]
  (instance? Pattern x))
(defn boolean? [x]
  (or (true? x) (false? x)))

(defn classify
  "Returns a keyword describing the form type"
  [form]
  (cond
   (nil? form)     :nil
   (boolean? form) :bool
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
   (var? form)     :var
   :else           :unknown))

(defn private? [var]
  (:private (meta var)))
(defn macro? [var]
  (:macro (meta var)))
(defn constant? [var]
  (:const (meta var)))
(defn dynamic? [var]
  (or (:dynamic (meta var))
      (when (var? var)
        (.isDynamic ^Var var))))
(defn protocol-node? [var]
  (boolean (:protocol (meta var))))

(defn resolve-ns [ns-sym {:keys [ns namespaces]}]
  (when ns-sym
    (or (:ns (@namespaces ns-sym))
        (get (:aliases ns) ns-sym))))

(defn maybe-var [sym {:keys [ns namespaces] :as env}]
  (when (symbol? sym)
    (let [name (-> sym name symbol)
          sym-ns (when-let [ns (namespace sym)]
                   (symbol ns))
          full-ns (resolve-ns sym-ns env)]
      (when (or (not sym-ns) full-ns)
        (if-let [var (-> (@namespaces (or full-ns ns)) :mappings (get name))]
          (when (var? var)
            var))))))

(defn resolve-var [sym env]
  (or (maybe-var sym env)
      (when (symbol? sym)
       (when-let [ns (namespace sym)]
         (when (resolve-ns (symbol ns) env)
           (throw (ex-info (str "no such var: " sym) {:var sym})))))))

;; should also use :variadic? and :max-fixed-arity
(defn arglist-for-arity [fn argc]
  (let [arglists (->> fn :arglists (sort-by count)) ;; :init :arglists when vars won't map to Vars
        arglist (->> arglists (filter #(= argc (count %))) first)
        last-arglist (last arglists)]
    (or arglist
        (when (and (seq (filter '#{&} last-arglist))
                   (>= argc (- (count last-arglist) 2)))
          last-arglist))))

(defn get-line [x env]
  (-> x meta :line))
(defn get-col [x env]
  (-> x meta :column))

(defn -source-info [x env]
  (merge
   (when-let [file (and (not= *file* "NO_SOURCE_FILE")
                        *file*)]
     {:file file})
   (when-let [line (get-line x env)]
     {:line line})
   (when-let [column (get-col x env)]
     {:column column})))
