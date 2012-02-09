(ns clojure.compiler
    (:require [clojure.java.io :as io]
              [clojure.string :as string])
    (:use [clojure analyzer set walk])
    (:import [org.objectweb.asm Type Opcodes ClassReader ClassWriter]
             [org.objectweb.asm.commons Method GeneratorAdapter]
             [org.objectweb.asm.util CheckClassAdapter TraceClassVisitor]
             [clojure.lang DynamicClassLoader]))

(def max-positional-arity 20)

(def ^:private char-map
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

(defmulti ^:private emit :op )

(defmulti ^:private emit-constant class)

(def ^:dynamic ^:private *gen* nil)

(def ^:dynamic ^:private *loader* (DynamicClassLoader.))

(def ^:private object-type (Type/getType Object))

(def ^:private ifn-type (Type/getType clojure.lang.IFn))
(def ^:private var-type (Type/getType clojure.lang.Var))
(def ^:private symbol-type (Type/getType clojure.lang.Symbol))
(def ^:private arg-types (into-array (for [i (range max-positional-arity)]
                                         (into-array Type (repeat i object-type)))))

(defn load-class [name bytecode form]
    (.defineClass *loader* name bytecode form))

(def ^:private unique (atom 0))

(defn ^:private new-frame []
    (atom {}))

(def ^:dynamic ^:private *frame* (new-frame))

(defn ^:private collect-vars [form]
    (when (= (:op form) :var )
        {:vars [(-> form :info :name )]}))

(defn ^:private collect-constants [form]
    (when (= (:op form) :constant )
        {:constants [(:form form)]}))

(def ^:private new-frame-ops {})

(defn ^:private new-frame? [form]
    (or (new-frame-ops (:op form))
        (= :statement (-> form :env :context ))))

(defn ^:private process-frames [f ast]
    (let [post-fn (fn [form]
        (swap! *frame* (partial merge-with (comp vec distinct union)) (f form))
        form)]
        (if (new-frame? ast)
            (binding [*frame* (new-frame)]
                (merge (walk (partial process-frames f) post-fn ast) @*frame*))
            (walk (partial process-frames f) post-fn ast))))

(defn ^:private emit-vars [cv {:keys [vars env]}]
    (doseq [v vars]
        (let [name (str (munge v))
              var (resolve (-> env :ns :name) v)]
            (.visitField cv
                (+ Opcodes/ACC_PUBLIC Opcodes/ACC_FINAL Opcodes/ACC_STATIC) name (.getDescriptor var-type) nil nil)
            (swap! *frame* assoc-in [:fields var] name))))

(defmulti type-of class)
(defmethod type-of :default [o] object-type)
(defmethod type-of clojure.lang.Var [o] var-type)
(defmethod type-of clojure.lang.Symbol [o] symbol-type)

(defn ^:private emit-constants [cv {constants :constants}]
    (doall (map-indexed
               (fn [i v]
                   (let [name (str "CONSTANT" i)]
                       (.visitField cv
                           (+ Opcodes/ACC_PUBLIC Opcodes/ACC_FINAL Opcodes/ACC_STATIC)
                           name
                           (.getDescriptor (type-of v))
                           nil
                           nil)
                       (swap! *frame* assoc-in [:fields v] name)))
               constants)))

(defmulti ^:private emit-value class)

(defmethod emit-value java.lang.Long [v]
    (.push *gen* v)
    (.box *gen* (Type/getType "J")))

(defmethod emit-value clojure.lang.Symbol [v]
    (.push *gen* (namespace v))
    (.push *gen* (name v))
    (.invokeStatic *gen* (Type/getType clojure.lang.Symbol) (Method/getMethod "clojure.lang.Symbol intern(String,String)")))

(defmethod emit-value clojure.lang.Var [v]
    (.push *gen* (str (.ns v)))
    (.push *gen* (name (.sym v)))
    (.invokeStatic *gen* (Type/getType clojure.lang.RT) (Method/getMethod "clojure.lang.Var var(String,String)")))


(defn ^:private emit-constructors [cv ast]
    (let [m (Method/getMethod "void <init> ()")
          ctor (GeneratorAdapter. Opcodes/ACC_PUBLIC m nil nil cv)]
        (.loadThis ctor)
        (.invokeConstructor ctor object-type m)
        (.returnValue ctor)
        (.endMethod ctor))
    (let [m (Method/getMethod "void <clinit> ()")
          line (-> ast :env :line)
          {:keys [class fields]} @*frame*]
        (binding [*gen* (GeneratorAdapter. Opcodes/ACC_PUBLIC m nil nil cv)]
            (.visitCode *gen*)
            (when line
                (.visitLineNumber *gen* line (.mark *gen*)))
            (doseq [[v n] fields]
                (emit-value v)
                (.checkCast *gen* (type-of v))
                (.putStatic *gen* class n (type-of v)))
            (.returnValue *gen*)
            (.endMethod *gen*))))

(defn ^:private debug-info [name source-path line]
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

(defn ^:private emit-class [internal-name ast]
    (binding [*frame* (new-frame)]
        (let [cw (ClassWriter. ClassWriter/COMPUTE_MAXS)]
            (swap! *frame* merge ast {:class (Type/getType internal-name)})
            (doto cw
                (.visit Opcodes/V1_5 (+ Opcodes/ACC_PUBLIC Opcodes/ACC_SUPER) internal-name nil "java/lang/Object" nil)
;                (.visitSource internal-name (debug-info internal-name "NO_SOURCE_PATH" (-> ast :env :line)))
                (.visitSource internal-name nil)
                (emit-vars ast)
                (emit-constants ast)
                (emit-constructors ast))
            (binding [*gen* (GeneratorAdapter. Opcodes/ACC_PUBLIC (Method/getMethod "Object invoke()") nil nil cw)]
                (.visitCode *gen*)
                (emit ast)
                (.returnValue *gen*)
                (.endMethod *gen*)
                (.visitEnd cw))
            cw)))

(defn eval [form]
    (let [env {:ns (@namespaces *ns*) :context :statement :locals {}}
          ast (analyze env form)
          ast (process-frames #(merge (collect-vars %) (collect-constants %)) ast)
          id (swap! unique inc)
          internal-name (str "repl/Temp" id)
          binary-name (str "repl.Temp" id)
          cw (emit-class internal-name ast)]
        (binding [*loader* (DynamicClassLoader.)]
            (let [bytecode (.toByteArray cw)
                  class (load-class binary-name bytecode form)
                  instance (.newInstance class)]
                (.invoke instance)))))

(defn eval-trace [form]
    (let [env {:ns (@namespaces *ns*) :context :statement :locals {}}
          ast (analyze env form)
          ast (process-frames #(merge (collect-vars %) (collect-constants %)) ast)
          id (swap! unique inc)
          internal-name (str "repl/Temp" id)
          binary-name (str "repl.Temp" id)
          cw (emit-class internal-name ast)]
        (let [cv (ClassReader. (.toByteArray cw))]
            (.accept cv (CheckClassAdapter. (TraceClassVisitor. (java.io.PrintWriter. *out*))) 0))))


(defn load [f]
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


(defmethod emit :invoke [{:keys [f args env]}]
    (.visitLineNumber *gen* (:line env) (.mark *gen*))
    (emit f)
    (.checkCast *gen* ifn-type)
    (doseq [arg args]
        (emit arg))
    (.invokeInterface *gen* ifn-type (Method. "invoke" object-type (get arg-types (count args)))))


(def ^:private var-get-method (Method/getMethod "Object get()"))
(def ^:private var-get-raw-method (Method/getMethod "Object getRawRoot()"))

(defmethod emit :var [{:keys [info env]}]
    (let [v (:name info)
          var (resolve (-> env :ns :name) v)
          {:keys [class fields]} @*frame*]
        (.getStatic *gen* class (fields var) var-type)
        (.invokeVirtual *gen* var-type (if (.isDynamic var) var-get-method var-get-raw-method))))


(defmulti ^:private emit-constant class)
(defmethod emit-constant Long [v]
    (let [{:keys [class fields]} @*frame*]
        (.getStatic *gen* class (fields v) (type-of v))))

(defmethod emit :constant [{:keys [form env]}]
    (emit-constant form))

(defmethod emit :default [args] (println "???" args))