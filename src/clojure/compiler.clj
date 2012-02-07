(ns clojure.compiler
  (:require [clojure.java.io :as io]
            [clojure.string :as string])
  (:use [clojure analyzer set walk])
  (:import [org.objectweb.asm Type Opcodes ClassWriter]
           [org.objectweb.asm.commons Method GeneratorAdapter]
           [clojure.lang DynamicClassLoader]))

(defmulti ^:private emit :op)

(defmulti emit-constant class)

(def ^:dynamic *gen* nil)

(def ^:dynamic *loader* (DynamicClassLoader.))

(def ifn-type (Type/getType clojure.lang.IFn))

(def object-type (Type/getType Object))

(def max-positional-arity 20)

(def arg-types (into-array (for [i (range max-positional-arity )]
                             (into-array Type (repeat i object-type)))))

;(defmacro emit-wrap [env & body]
;  `(let [env# ~env]
;     ))

(defn debug-info [name source-path line]
  (str "SMAP\n"
    name ".java\n"
    "Clojure\n"
    "*S Clojure\n"
    "*F\n"
    "+ 1 " name "\n"
    source-path "\n"
    "*L\n"
    line
    "*E"))

(defn load-class [name bytecode form]
  (.defineClass *loader* name bytecode form))

(def unique (atom 0))

(defn- new-frame []
  (atom {}))

(def ^:dynamic *frame* (new-frame))

(defn- collect-vars [form]
  (when (= (:op form) :var)
    {:vars [(-> form :info :name)]}))

(defn- collect-constants [form]
  (when (= (:op form) :constant)
    {:constants [(:form form)]}))

(def new-frame-ops {})

(defn new-frame? [form]
  (or (new-frame-ops (:op form))
    (= :statement (-> form :env :context))))

(defn- process [f ast]
  (let [post-fn (fn [form]
                  (swap! *frame* (comp vec distinct (partial merge-with union)) (f form))
                  form)]
    (if (new-frame? ast)
      (binding [*frame* (new-frame)]
        (merge (walk (partial process f) post-fn ast) @*frame*))
      (walk (partial process f) post-fn ast))))

(defn- emit-vars [cv {vars :vars}]
  (doseq [v vars]
    (.visitField cv
      (+ Opcodes/ACC_PUBLIC Opcodes/ACC_SUPER Opcodes/ACC_STATIC) (str v) (Type/getType clojure.lang.Var) nil nil)))

(defmulti type-of class)

(defmethod type-of :default object-type)

(defn- emit-constants [cv {constants :constants}]
  (doall (map-indexed
    (fn [i v]
      (.visitField cv (+ Opcodes/ACC_PUBLIC Opcodes/ACC_SUPER Opcodes/ACC_STATIC) (str "CONSTANT" i) (type-of v) nil v)))))

(defn eval [form]
  (let [env {:ns (@namespaces *ns*) :context :statement :locals {}}
        cw (ClassWriter. ClassWriter/COMPUTE_MAXS)
        ast (analyze env form)
        ast (process #(merge (collect-vars %) (collect-constants %)) ast)
        name (str "repl/Temp" (swap! unique inc))]
    (-> cw
      (.visit Opcodes/V1_5 (+ Opcodes/ACC_PUBLIC Opcodes/ACC_SUPER) name, nil, "java/lang/Object", nil)
      ;(.visitSource name (debug-info name source-path line))
      (.visitSource name nil)
      (emit-vars form)
      (emit-constants form)
      (emit-constructors form))
    (binding [*gen* (GeneratorAdapter. Opcodes/ACC_PUBLIC (Method/getMethod "Object invoke()") nil nil cw)
              *loader* (DynamicClassLoader.)]
      (.visitCode *gen*)
      (emit ast)
      (.returnValue *gen*)
      (.endMethod *gen*))
    (.visitEnd cw)
    (let [bytecode (.toByteArray cw)
          class (load-class bytecode)
          instance (.newInstance class)]
      (.invoke instance))))

(defn load
  [f]
  (let [res (or (io/resource f) (io/as-url (io/as-file f)))]
    (assert res (str "Can't find " f " in classpath"))
    (binding [*file* (.getPath res)]
      (with-open [r (io/reader res)]
        (let [env {:ns (@namespaces *ns*) :context :statement :locals {}}
              pbr (clojure.lang.LineNumberingPushbackReader. r)
              eof (Object.)]
          (loop [r (read pbr false eof false)]
            (let [env (assoc env :ns (@namespaces *ns*))]
              (when-not (identical? eof r)
                (eval r)
                (recur
                  (read pbr false eof false))))))))))

(defmethod ^:private emit :invoke [{:keys [f args env]}]
  (.visitLineNumber *gen* (:line env) (.mark *gen*))
  (emit f)
  (.checkCast *gen* ifn-type)
  (doseq [arg args]
    (emit arg))
  (.invokeInterface *gen* ifn-type (Method. "invoke" object-type (get arg-types (count args)))))

(defmethod ^:private emit :var
  [{:keys [info env] :as arg}]

)