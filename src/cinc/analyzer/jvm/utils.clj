(ns cinc.analyzer.jvm.utils
  (:require [clojure.reflect :as reflect])
  (:import (clojure.lang RT Symbol Var)
           (org.objectweb.asm Type)))

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
        (when (class? maybe-class)
          maybe-class)))))

(defmethod maybe-class :default [_] nil)
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

(defmulti convertible? (fn [from to] [(maybe-class from) (maybe-class to)]))

(defmethod convertible? [java.lang.Object java.lang.Number] [t1 ts] true)
(defmethod convertible? [java.lang.Object Integer/TYPE] [t1 ts] true)
(defmethod convertible? [java.lang.Object Long/TYPE] [t1 ts] true)
(defmethod convertible? [Long/TYPE java.lang.Object] [t1 ts] true)
(defmethod convertible? [Long/TYPE Integer/TYPE] [t1 ts] true)

(defmethod convertible? :default [^Class t1 ^Class t2]
  (if (= t1 t2) true (.isAssignableFrom t2 t1)))

(defn primitive? [o]
  (let [^Class c (maybe-class o)]
    (and
     (not (or (nil? c) (= c Void/TYPE)))
     (.isPrimitive c))))

(defn members [class member]
  (let [members (-> (maybe-class class)
                  (reflect/type-reflect :ancestors true)
                  :members)]
    (when-let [members (filter #(= member (:name %)) members)]
      members)))

(defn static-members [class f]
  (when-let [members (members class f)]
    (when-let [statics (filter (comp :static :flags) members)]
      statics)))

(defn instance-members [class f]
  (when-let [members (members class f)]
    (when-let [i-members (remove (comp :static :flags) members)]
      i-members)))

(defn static-methods [class method argc]
  (filter #(= argc (count (:parameter-types %)))
          (filter :return-type (static-members class method))))

(defn instance-methods [class method argc]
  (filter #(= argc (count (:parameter-types %)))
          (filter :return-type (instance-members class method))))

(defn static-field [class f]
  (when-let [statics (static-members class f)]
    (when-let [[member] (filter (every-pred (comp nil? seq :parameter-types)
                                            (comp nil? :return-type))
                                statics)]
      member)))

(defn instance-field [class f]
  (when-let [i-members (instance-members class f)]
    (when-let [[member] (filter (every-pred (comp nil? seq :parameter-types)
                                            (comp nil? :return-type))
                                i-members)]
      member)))

(defn static-method [class method]
  (static-methods class method 0))

(defn instance-method [class method]
  (instance-methods class method 0))
