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

(defn ^:private new-frame [] (atom {}))

(def ^:dynamic ^:private *frame*)

(defn ^:private collect-vars [form]
    (case (:op form)
        :var (let [var (-> form :info :name )]
                 (if-not (resolve var)
                     (throw (clojure.lang.Util/runtimeException (str "No such var: " var)))
                     {:vars [var]}))

        :def {:vars [(:name form)]}

        nil
        ))

(defn ^:private collect-constants [form]
    (when (= (:op form) :constant )
        {:constants [(:form form)]}))

(defn ^:private new-frame? [form]
    (#{:fn } (:op form)))

(defn ^:private process-frames-helper [f ast]
    (let [post-fn
          (fn [form]
              (swap! *frame* (partial merge-with (comp vec distinct union)) (f form))
              form)]
        (if (new-frame? ast)
            (binding [*frame* (new-frame)]
                (let [res (walk (partial process-frames-helper f) post-fn ast)]
                    (merge res @*frame*)))
            (walk (partial process-frames-helper f) post-fn ast))))

(defn ^:private process-frames [ast]
    (binding [*frame* (new-frame)]
        (merge (process-frames-helper #(merge (collect-vars %) (collect-constants %)) ast) @*frame*)))

(defn ^:private var! [sym]
    (clojure.lang.RT/var (namespace sym) (name sym)))

(defn dynamic? [v]
    (or (:dynamic (meta v)) (.isDynamic v)))

(defn ^:private emit-vars [cv {:keys [vars env]}]
    (doseq [v vars]
        (let [n (str (munge v))
              var (var! v)]
            (.visitField cv
                (+ Opcodes/ACC_PUBLIC Opcodes/ACC_FINAL Opcodes/ACC_STATIC) n (.getDescriptor var-type) nil nil)
            (swap! *frame* assoc-in [:fields var] n))))

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
          line (-> ast :env :line )
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

(defn ^:private emit-class [internal-name ast emit-methods]
    (binding [*frame* (new-frame)]
        (let [cw (ClassWriter. ClassWriter/COMPUTE_MAXS)]
            (swap! *frame* merge ast {:class (Type/getType internal-name)})
            (doto cw
                (.visit Opcodes/V1_5 (+ Opcodes/ACC_PUBLIC Opcodes/ACC_SUPER) internal-name nil "java/lang/Object" nil)
                ;                (.visitSource internal-name (debug-info internal-name "NO_SOURCE_PATH" (-> ast :env :line)))
                (.visitSource internal-name nil)
                (emit-vars ast)
                (emit-constants ast)
                (emit-constructors ast)
                (emit-methods ast)
                .visitEnd)
            cw)))

(defn ^:private emit-statement [cv ast]
    (binding [*gen* (GeneratorAdapter. Opcodes/ACC_PUBLIC (Method/getMethod "Object invoke()") nil nil cv)]
        (.visitCode *gen*)
        (emit ast)
        (.returnValue *gen*)
        (.endMethod *gen*)))

(defn eval [form]
    (let [env {:ns (@namespaces *ns*) :context :statement :locals {}}
          ast (analyze env form)
          ast (process-frames ast)
          id (swap! unique inc)
          internal-name (str "repl/Temp" id)
          binary-name (str "repl.Temp" id)
          cw (emit-class internal-name ast emit-statement)]
        (binding [*loader* (DynamicClassLoader.)]
            (let [bytecode (.toByteArray cw)
                  class (load-class binary-name bytecode form)
                  instance (.newInstance class)]
                (.invoke instance)))))

(defn eval-trace [form & {:keys [check]}]
    (let [env {:ns (@namespaces *ns*) :context :statement :locals {}}
          ast (analyze env form)
          ast (process-frames ast)
          id (swap! unique inc)
          internal-name (str "repl/Temp" id)
          binary-name (str "repl.Temp" id)
          cw (emit-class internal-name ast emit-statement)]
        (let [cv (ClassReader. (.toByteArray cw))
              v (TraceClassVisitor. (java.io.PrintWriter. *out*))
              v (if check (CheckClassAdapter. v) v)]
            (.accept cv v 0))))


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
          var (var! v)
          {:keys [class fields]} @*frame*]
        (.getStatic *gen* class (fields var) var-type)
        (.invokeVirtual *gen* var-type (if (dynamic? var) var-get-method var-get-raw-method))))

(defmethod emit :def [{:keys [name form init env doc export] :as args}]
    (let [var (var! name)
          {:keys [class fields]} @*frame*]
        (.getStatic *gen* class (fields var) var-type)
        (when (:dynamic (meta form))
            (.push *gen* true)
            (.invokeVirtual *gen* var-type (Method/getMethod "clojure.lang.Var setDynamic(boolean)")))
        (when (meta form)
            (println "TODO: Copy meta on def"))
        (when init
            (.dup *gen*)
            (emit init)
            (.invokeVirtual *gen* var-type (Method/getMethod "void bindRoot(Object)")))))

(defmulti ^:private emit-constant class)
(defmethod emit-constant Long [v]
    (let [{:keys [class fields]} @*frame*]
        (.getStatic *gen* class (fields v) (type-of v))))

(defmethod emit :constant [{:keys [form env]}]
    (emit-constant form))

(defn ^:private notsup [& args]
    (clojure.lang.Util/runtimeException (apply str "Unsupported: " args)))

(defn emit-fn-method [cv {:keys [name params statements ret env recurs] :as args}]
    (binding [*gen*
              (GeneratorAdapter. Opcodes/ACC_PUBLIC
                  (Method/getMethod (str "Object invoke(" (apply str (interpose \, params)) ")")) nil nil cv)]
        (.visitCode *gen*)
        (when recurs (notsup "recurs"))
        (when statements
            (dorun (map emit statements)))
        (emit ret)
        (.returnValue *gen*)
        (.endMethod *gen*)))

(defn ^:private emit-fns [cv {:keys [name env methods max-fixed-arity variadic recur-frames]}]
    (let [loop-locals (seq (mapcat :names (filter #(and % @(:flag %)) recur-frames)))]
        (when loop-locals
            (notsup "loop-locals"))
        (let [maxparams (apply max-key count (map :params methods))
              mmap (zipmap (repeatedly #(gensym (str name "__"))) methods)
              ms (sort-by #(-> % second :params count) (seq mmap))]
            (doseq [[n meth] ms]
                (if (:variadic meth)
                    (notsup '(emit-variadic-fn-method meth))
                    (emit-fn-method cv meth)))
            (when loop-locals
                (notsup "loop-locals")))))

(defmethod emit :fn [ast]
    [ast]
    (let [name (str (or (:name ast) (gensym)))]
        (emit-class name ast emit-fns)))

(defmethod emit :default [args] (clojure.lang.Util/runtimeException (str "Unknown operator: " (:op args) "\nForm: " args)))
