(set! *warn-on-reflection* true)
(ns cinc.host-utils
  (:require [clojure.reflect :as reflect])
  (:import (clojure.lang RT Symbol Var)
           (org.objectweb.asm Type)))

(defn private? [var]
  (:private (meta var)))
(defn macro? [var]
  (:macro (meta var)))

(defn resolve-ns [ns]
  (when ns
    (or (find-ns ns)
        ((ns-aliases *ns*) ns))))

(defn resolve-var [sym]
  (let [name (-> sym name symbol)
        ns (when-let [ns (namespace sym)]
             (symbol ns))
        full-ns (resolve-ns ns)]
    (when (or (not ns)
              (and ns full-ns))
      (if-let [var (if full-ns
                     ((ns-interns full-ns) name)
                     ((ns-map *ns*) name))]
        (let [var-ns (.ns ^Var var)]
          (when (and (not= *ns* var-ns)
                     (private? var))
            (throw (ex-info (str "var: " sym " is not public") {:var sym})))
          (when (macro? var)
            (throw (ex-info (str "can't take value of a macro: " var) {:var var})))
          var)
        (when full-ns
          (throw (ex-info (str "no such var: " sym) {:var sym})))))))

(let [reflector (reflect/->JavaReflector (RT/baseLoader))]
  (defn type-reflect [typeref & options]
    (apply reflect/type-reflect typeref :reflector reflector options)))

(def ^:private prims
  {"byte" Byte/TYPE
   "bool" Boolean/TYPE
   "char" Character/TYPE
   "int" Integer/TYPE
   "long" Long/TYPE
   "float" Float/TYPE
   "double" Double/TYPE
   "void" Void/TYPE})

(defmulti maybe-class class)

(defn- ^Type asm-type [^String s]
  (when s
    (if-let [^Class class (maybe-class s)]
      (Type/getType class)
      (Type/getType s))))

(defn array-class [element-type]
  (RT/classForName
   (str "[" (-> element-type
              maybe-class
              asm-type
              .getDescriptor
              (.replace \/ \.)))))

(defn maybe-class-from-string [s]
  (try
    (RT/classForName s)
    (catch Exception _
      (if-let [maybe-class ((ns-map *ns*) (symbol s))]
        (if (class? maybe-class)
          maybe-class)))))

(defmethod maybe-class nil [_] nil)
(defmethod maybe-class Class [c] c)
(defmethod maybe-class String [s]
  (maybe-class (symbol s)))

(defmethod maybe-class Symbol [sym]
  (when-not (namespace sym)
    (if (.endsWith (name sym) "<>")
      (let [str (name sym)
            base-type (maybe-class (subs str 0 (- (count str) 2)))]
        (array-class base-type))
      (if-let [ret (prims (name sym))]
        ret
        (maybe-class-from-string (str sym))))))

(defn static-field [class field]
  (let [members (-> class
                  (reflect/type-reflect :ancestors true)
                  :members)]
    (when-let [[member] (filter #(= field (:name %)) members)]
      (when (:static (:flags member))
        member))))

(defn maybe-host-expr [sym]
  (if-let [c (namespace sym)]
    (if-let [class (maybe-class c)]
      (let [field (-> sym name symbol)]
        (if (static-field class field)
          {:op    :static-field
           :class class
           :field field}
          (throw (ex-info (str "unable to find static field: " field " in " class)
                          {:field field
                           :class class})))))
    (if-let [class (maybe-class sym)]
      {:op    :class
       :class class}
      (throw (ex-info (str "Class not found: " sym)
                      {:class sym})))))
