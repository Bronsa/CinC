(ns clojure.compiler
  (:require [clojure.java.io :as io]
            [clojure.string :as string])
  (:use [clojure analyzer set walk])
  (:import [org.objectweb.asm Type Opcodes ClassWriter]
           [org.objectweb.asm.commons Method GeneratorAdapter]
           [org.objectweb.asm.util TraceClassVisitor]
           [clojure.lang DynamicClassLoader]))

(def char-map
  {\- "_",
   \: "_COLON_",
   \+ "_PLUS_",
   \> "_GT_",
   \< "_LT_",
   \= "_EQ_",
   \~ "_TILDE_",
   \! "_BANG_",
   \@ "_CIRCA_",
   \# "_SHARP_",
   \' "_SINGLEQUOTE_",
   \" "_DOUBLEQUOTE_",
   \% "_PERCENT_",
   \^ "_CARET_",
   \& "_AMPERSAND_",
   \* "_STAR_",
   \| "_BAR_",
   \{ "_LBRACE_",
   \} "_RBRACE_",
   \[ "_LBRACK_",
   \] "_RBRACK_",
   \/ "_SLASH_",
   \\ "_BSLASH_",
   \? "_QMARK_",
   \. "_DOT_"})

(defn munge [s]
  (symbol (apply str (map #(char-map % %) (str s)))))

(defmulti ^:private emit :op)

(defmulti emit-constant class)

(def ^:dynamic *gen* nil)

(def ^:dynamic *loader* (DynamicClassLoader.))

(def object-type (Type/getType Object))

(def ifn-type (Type/getType clojure.lang.IFn))

(def var-type (Type/getType clojure.lang.Var))

(def max-positional-arity 20)

(def arg-types (into-array (for [i (range max-positional-arity )]
                             (into-array Type (repeat i object-type)))))

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
                  (swap! *frame* (partial merge-with (comp vec distinct union)) (f form))
                  form)]
    (if (new-frame? ast)
      (binding [*frame* (new-frame)]
        (merge (walk (partial process f) post-fn ast) @*frame*))
      (walk (partial process f) post-fn ast))))

(defn- emit-vars [cv {vars :vars}]
  (doseq [v vars]
    (.visitField cv
      (+ Opcodes/ACC_PUBLIC Opcodes/ACC_SUPER Opcodes/ACC_STATIC) (str (munge v)) (.getDescriptor var-type) nil nil)))

(defmulti type-of class)

(defmethod type-of :default [o] object-type)

(defn- emit-constants [cv {constants :constants}]
  (doall (map-indexed
    (fn [i v]
      (.visitField cv
        (+ Opcodes/ACC_PUBLIC Opcodes/ACC_SUPER Opcodes/ACC_STATIC)
        (str "CONSTANT" i)
        (.getDescriptor (type-of v))
        nil
        nil))
    constants)))

(defn- emit-constructors [cv {constructors :constructors}])

(defn- emit-class [cw internal-name ast]
  (doto cw
    (.visit Opcodes/V1_5 (+ Opcodes/ACC_PUBLIC Opcodes/ACC_SUPER) internal-name nil "java/lang/Object" nil)
    ;(.visitSource name (debug-info name source-path line))
    (.visitSource internal-name nil)
    (emit-vars ast)
    (emit-constants ast)
    (emit-constructors ast))
  (binding [*gen* (GeneratorAdapter. Opcodes/ACC_PUBLIC (Method/getMethod "Object invoke()") nil nil cw)
            *frame* (new-frame)]
    (swap! *frame* assoc :class internal-name)
    (.visitCode *gen*)
    (emit ast)
    (.returnValue *gen*)
    (.endMethod *gen*)
    (.visitEnd cw)))

(defn eval [form]
  (let [env {:ns (@namespaces *ns*) :context :statement :locals {}}
        cw (ClassWriter. ClassWriter/COMPUTE_MAXS)
        ast (analyze env form)
        ast (process #(merge (collect-vars %) (collect-constants %)) ast)
        id (swap! unique inc)
        internal-name (str "repl/Temp" id)
        binary-name (str "repl.Temp" id)]
    (emit-class cw internal-name ast)
    (binding [*loader* (DynamicClassLoader.)]
      (let [bytecode (.toByteArray cw)
          class (load-class binary-name bytecode form)
          instance (.newInstance class)]
        (.invoke instance)))))

(defn- trace-eval [form]
  (let [env {:ns (@namespaces *ns*) :context :statement :locals {}}
        cw (TraceClassVisitor. (java.io.PrintWriter. *out*))
        ast (analyze env form)
        ast (process #(merge (collect-vars %) (collect-constants %)) ast)
        id (swap! unique inc)
        internal-name (str "repl/Temp" id)
        binary-name (str "repl.Temp" id)]
    (emit-class cw internal-name ast)))


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

(def ^:private var-get-method (Method/getMethod "Object get()"))

(def ^:private var-get-raw-method (Method/getMethod "Object getRawRoot()"))

(defmethod ^:private emit :var
  [{:keys [info env] :as arg}]
  (let [v (resolve (-> env :ns :name) (:name info))]
    (.getStatic *gen* object-type (str (munge v)), var-type)
    (.invokeVirtual *gen* var-type (if (.isDynamic v) var-get-method var-get-raw-method))))

(defmulti emit-constant class)
(defmethod emit-constant :default [{value :form}]
  (.push *gen* value))

(defmethod ^:private emit :constant
  [{:keys [form env]}]
  (emit-constant form))

(defmethod ^:private emit :default [args] (println "???" args))