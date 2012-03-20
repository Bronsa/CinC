(ns clojure.java.compiler
  (:refer-clojure :exclude [eval load munge *ns* type])
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [clojure.java.ast :as ast])
  (:refer clojure.java.ast :only [convertible? dynamic? expression-type maybe-class tagged-type])
  (:use [clojure
          [analyzer :only [analyze namespaces *ns*]]
          [walk :only [walk]]
          [reflect :only [type-reflect]]
          [set :only [select]]
          pprint repl]) ; for debugging
  (:import [org.objectweb.asm Type Opcodes ClassReader ClassWriter]
           [org.objectweb.asm.commons Method GeneratorAdapter]
           [org.objectweb.asm.util CheckClassAdapter TraceClassVisitor]
           [clojure.lang DynamicClassLoader RT Util]))

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

(defmacro notsup [& args]
  `(throw (RuntimeException. (str "Unsupported: " ~@args))))

(defn- primitive? [o]
  (let [c (maybe-class o)]
    (and
      (not (or (nil? c) (= c Void/TYPE)))
      (.isPrimitive c))))

(defn- asm-type [s]
  (when s
    (let [class (maybe-class s)]
      (if class
        (Type/getType class)
        (Type/getType s)))))

(defn- asm-method
  ([{:keys [name return-types parameter-types]}]
   (apply asm-method name return-types parameter-types))
  ([name return-type & args]
   (Method. (str name) (asm-type return-type) (into-array Type (map asm-type args)))))

; Frame members (maybe these should be separate variables?):
; :class - ASM type of current class being written
; :statics - Static fields containing vars and constants, map from sym -> {:type :name [:value]}
; :fields - Fields containing closed-overs, map from sym -> {:type :name}
; :locals - Local variable/Argument/Variable capture info, map from sym -> {:type :index}
; :protos - Fields for protocol support
; :loop-label - Label of the top of the current loop for recur
; :loop-types - Types for the current loop top
(def ^:dynamic ^:private *frame*) ; Contains per-class information
(defn- new-frame [& m] (atom (apply hash-map :next-local-index 1 m))) ; 0 is "this"
(defn- copy-frame [& {:as m}] (atom (merge @*frame* m)))

(def ^:dynamic ^:private ^GeneratorAdapter *gen* nil) ; Current GeneratorAdapter to emit to

(def ^:dynamic ^:private ^DynamicClassLoader *loader* nil)

(def ^:private object-type (asm-type java.lang.Object))
(def ^:private obj-array-type (Type/getType (class (make-array Object 0))))
(def ^:private class-type (asm-type java.lang.Class))

(def ^:private ifn-type (asm-type clojure.lang.IFn))
(def ^:private afn-type (asm-type clojure.lang.AFn))
(def ^:private var-type (asm-type clojure.lang.Var))
(def ^:private symbol-type (asm-type clojure.lang.Symbol))
(def ^:private keyword-type (asm-type clojure.lang.Keyword))
(def ^:private rt-type (asm-type clojure.lang.RT))
(def ^:private util-type (asm-type clojure.lang.Util))

(def ^:private arg-types (into-array
                           (concat
                             (for [i (range (inc max-positional-arity))]
                               (into-array Type (repeat i object-type)))
                             [(into-array Type
                               (concat
                                 (repeat max-positional-arity object-type) [obj-array-type]))])))

(def ^:private constructor-method (Method/getMethod "void <init> ()"))
(def ^:private var-get-method (Method/getMethod "Object get()"))
(def ^:private var-get-raw-method (Method/getMethod "Object getRawRoot()"))

(def ^:dynamic *trace-bytecode* false)
(def ^:dynamic *check-bytecode* false)

(defmulti ^:private emit-boxed :op )
(defmulti ^:private emit-unboxed :op )

(defmulti ^:private emit :op)

(defmethod emit :default [ast]
  (if (:box ast)
    (emit-boxed ast)
    (emit-unboxed ast)))

(defn load-class [name bytecode form]
  (let [binary-name (.replace name \/ \.)]
    (when (or *trace-bytecode* *check-bytecode*)
      (let [cr (ClassReader. bytecode)
            w (java.io.PrintWriter. (if *trace-bytecode* *out* (java.io.StringWriter.)))
            v (TraceClassVisitor. w)
            v (if *check-bytecode* (CheckClassAdapter. v) v)]
        (.accept cr v 0)))
    (.defineClass *loader* binary-name bytecode form)))

(declare emit-class emit-box)

(defn- emit-wrapper-fn [cv ast]
  (binding [*gen* (GeneratorAdapter. Opcodes/ACC_PUBLIC (asm-method "invoke" "Object") nil nil cv)]
    (.visitCode *gen*)
    (emit ast)
    (.returnValue *gen*)
    (.endMethod *gen*)))

(defn eval
  ([form & {:keys [trace check]}]
   (binding [*trace-bytecode* trace
             *check-bytecode* check]
     (eval form)))
  ([form]
   (binding [*loader* (if *loader* *loader* (DynamicClassLoader.))]
     (if (= (:op form) :do)
       ;; Special handling for do, pick it apart and eval the pieces
       (let [{:keys [statements ret]} form]
         (when statements
           (dorun (map eval statements)))
         (eval ret))
       (let [env {:ns (@namespaces *ns*) :context :statement :locals {}}
             ast (analyze env form)
             ast (ast/process-frames (assoc ast :box true))
             internal-name (str "repl/Temp" (RT/nextID))
             cw (emit-class internal-name (assoc ast :super "clojure/lang/AFn") emit-wrapper-fn)]
         (let [bytecode (.toByteArray cw)
               class (load-class internal-name bytecode form)
               instance (.newInstance class)]
           (instance)))))))

(defn load [f]
  (let [res (or (io/resource f) (io/as-url (io/as-file f)))]
    (assert res (str "Can't find " f " in classpath"))
    (binding [*file* (.getPath res)
              *loader* (DynamicClassLoader.)] ; Use the same classloader for loading the entire file
      (with-open [r (io/reader res)]
        (let [env {:ns (@namespaces *ns*) :context :statement :locals {}}
              pbr (clojure.lang.LineNumberingPushbackReader. r)
              eof (java.lang.Object.)]
          (loop [r (read pbr false eof false)]
            (let [env (assoc env :ns (@namespaces *ns*))]
              (when-not (identical? eof r)
                (eval r)
                (recur
                  (read pbr false eof false))))))))))

(defn- emit-vars [cv {:keys [vars env]}]
  (doseq [v vars]
    (let [sym (symbol (namespace v) (name v))
          name (str (munge v))]
      (.visitField cv
        (+ Opcodes/ACC_PUBLIC Opcodes/ACC_FINAL Opcodes/ACC_STATIC) name (.getDescriptor var-type) nil nil)
      (swap! *frame* assoc-in [:statics sym] {:name name :type clojure.lang.Var :value v}))))

(defn- emit-constants [cv {constants :constants}]
  (dorun
    (map-indexed
      (fn [i v]
        (let [name (str "CONSTANT" i)]
          (.visitField cv (+ Opcodes/ACC_PUBLIC Opcodes/ACC_FINAL Opcodes/ACC_STATIC)
            name
            (-> v :type asm-type .getDescriptor)
            nil
            nil)
          (swap! *frame* assoc-in [:statics (:value v)] (assoc v :name name))))
      ;; nil is handled separately with a bytecode instruction
      (remove #(nil? (:value %)) constants))))

(defn- emit-proto-callsites [cv {:keys [callsites env]}]
  (dorun
    (map-indexed
      (fn [i site]
        (let [cached-class (str "__cached_class__" i)
              cached-proto-fn (str "__cached_proto_fn__" i)
              cached-proto-impl (str "__cached_proto_impl__" i)]
          (.visitField cv (+ Opcodes/ACC_PRIVATE) cached-class (.getDescriptor class-type) nil nil)
          (.visitField cv (+ Opcodes/ACC_PRIVATE) cached-proto-fn (.getDescriptor afn-type) nil nil)
          (.visitField cv (+ Opcodes/ACC_PRIVATE) cached-proto-impl (.getDescriptor ifn-type) nil nil)
          (swap! *frame* assoc-in [:protos site]
            {:cached-class cached-class :cached-proto-fn cached-proto-fn :cached-proto-impl cached-proto-impl})))
      callsites)))

(defn- closed-overs [{:as form :keys [env referenced-locals params]}]
  (remove (fn [{name :name}] (or (-> env :locals name :this)
                                 (not (contains? (:locals env) name))))
    referenced-locals))

(defn- emit-closed-overs [cv {:as form :keys [env params]}]
  (doseq [{:as lb :keys [name type]} (closed-overs form)]
    (let [mname (str (munge name))]
      (.visitField cv (+ Opcodes/ACC_PRIVATE Opcodes/ACC_FINAL) mname (-> lb :type asm-type .getDescriptor) nil nil)
      (swap! *frame* assoc-in [:fields name] (assoc lb :name mname)))))

(defmulti ^:private emit-value (fn [type value] type))

(defmethod emit-value java.lang.Boolean [t v]
  (.push *gen* (boolean v))
  (.box *gen* (asm-type Boolean/TYPE)))

(defmethod emit-value Boolean/TYPE [t v]
  (.push *gen* (boolean v)))

(defmethod emit-value java.lang.Long [t v]
  (.push *gen* (long v))
  (.box *gen* (asm-type Long/TYPE)))

(defmethod emit-value Long/TYPE [t v]
  (.push *gen* (long v)))

(defmethod emit-value java.lang.String [t ^String v]
  (.push *gen* v))

(defmethod emit-value java.lang.Class [t v]
  (.push *gen* (asm-type v)))

(defmethod emit-value clojure.lang.Symbol [t v]
  (.push *gen* (namespace v))
  (.push *gen* (name v))
  (.invokeStatic *gen* symbol-type (Method/getMethod "clojure.lang.Symbol intern(String,String)")))

(defmethod emit-value clojure.lang.Var [t v]
  (.push *gen* (namespace v))
  (.push *gen* (name v))
  (.invokeStatic *gen* rt-type (Method/getMethod "clojure.lang.Var var(String,String)")))

(defmethod emit-value clojure.lang.Keyword [t v]
  (.push *gen* (namespace v))
  (.push *gen* (name v))
  (.invokeStatic *gen* rt-type (Method/getMethod "clojure.lang.Keyword keyword(String,String)")))

(defn- emit-vals-as-array [list]
  (.push *gen* (int (count list)))
  (.newArray *gen* object-type)
  (dorun
    (map-indexed
      (fn [i item]
        (.dup *gen*)
        (.push *gen* (int i))
        (emit-value (class item) item)
        (.arrayStore *gen* object-type))
      list)))

(defn- emit-as-array [list]
  (.push *gen* (int (count list)))
  (.newArray *gen* object-type)
  (dorun
    (map-indexed
      (fn [i item]
        (.dup *gen*)
        (.push *gen* (int i))
        (emit item)
        (.arrayStore *gen* object-type))
      list)))

(defmethod emit-value clojure.lang.IPersistentMap [t v]
  (emit-vals-as-array (reduce into [] v))
  (.invokeStatic *gen* rt-type (Method/getMethod "clojure.lang.IPersistentMap map(Object[])")))

(defmethod emit-value clojure.lang.IPersistentVector [t v]
  (emit-vals-as-array v)
  (.invokeStatic *gen* rt-type (Method/getMethod "clojure.lang.IPersistentVector vector(Object[])")))

(defmethod emit-value :default [t v]
  (notsup "Don't know how to emit value: " [t v]))

(defn- emit-constructor [cv class super params]
  (binding [*gen* (GeneratorAdapter. Opcodes/ACC_PUBLIC (apply asm-method "<init>" "void" (map :type params)) nil nil cv)]
    (.loadThis *gen*)
    (.invokeConstructor *gen* (asm-type super) constructor-method)
    (dorun (map-indexed
             (fn [i {:keys [name type]}]
               (let [lb (-> @*frame* :fields name)]
                 (.loadThis *gen*)
                 (.loadArg *gen* i)
                 (.putField *gen* class (:name lb) (-> lb :type asm-type))))
             params))
    (.returnValue *gen*)
    (.endMethod *gen*)))

(defn- emit-constructors [cv ast]
  (let [class (:class @*frame*)
        super (:super ast)
        closed-overs (closed-overs ast)]
    (emit-constructor cv class super closed-overs))
  (let [m (Method/getMethod "void <clinit> ()")
        line (-> ast :env :line )
        {:keys [class statics]} @*frame*]
    (binding [*gen* (GeneratorAdapter. Opcodes/ACC_PUBLIC m nil nil cv)]
      (.visitCode *gen*)
      (when line
        (.visitLineNumber *gen* line (.mark *gen*)))
      (doseq [{:keys [name type value]} (vals statics)]
        (emit-value type value)
        (.putStatic *gen* class name (asm-type type)))
      (.returnValue *gen*)
      (.endMethod *gen*))))

(defn- debug-info [name source-path line]
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

(defn- emit-class [internal-name ast emit-methods]
  (binding [*frame* (new-frame :class (Type/getType internal-name))]
    (let [cw (ClassWriter. ClassWriter/COMPUTE_MAXS)
          super (-> ast :super asm-type .getInternalName)
          interfaces (into-array String (map #(-> % asm-type .getInternalName) (:interfaces ast)))]
      (doto cw
        (.visit Opcodes/V1_5 (+ Opcodes/ACC_PUBLIC Opcodes/ACC_SUPER) internal-name nil super interfaces)
        ;                (.visitSource internal-name (debug-info internal-name "NO_SOURCE_PATH" (-> ast :env :line)))
        (.visitSource internal-name nil)
        (emit-vars ast)
        (emit-constants ast)
        (emit-proto-callsites ast)
        (emit-closed-overs ast)
        (emit-constructors ast)
        (emit-methods ast)
        .visitEnd)
      cw)))

(defn- size-of [type]
  (condp = type Long/TYPE 2 Double/TYPE 2 1))

(defn- next-local [class]
  (let [next (:next-local-index @*frame*)
        size (size-of class)]
    (swap! *frame* assoc :next-local-index (+ next size))
    next))

(defn- asm-pop [type]
  (if (= 2 (size-of type))
    (.pop2 *gen*)
    (.pop *gen*)))

(defn- emit-args-and-call [args first-to-emit]
  (let [n (- (count args) first-to-emit)]
    (doseq [arg (subvec args first-to-emit (min (+ first-to-emit n) max-positional-arity))]
      (emit arg))
    (when (> n max-positional-arity)
      (emit-as-array (subvec args max-positional-arity)))
    ; Java clojure calls method.emitClearLocals here, but it does nothing?
    (.invokeInterface *gen* ifn-type (Method. "invoke" object-type (get arg-types (min (count args) (inc max-positional-arity)))))))

(defn- emit-unchecked-cast [t]
  (let [m
        (cond
          (= t Integer/TYPE) (Method/getMethod "int uncheckedIntCast(Object)")
          (= t Float/TYPE) (Method/getMethod "float uncheckedFloatCast(Object)")
          (= t Double/TYPE) (Method/getMethod "double uncheckedDoubleCast(Object)")
          (= t Long/TYPE) (Method/getMethod "long uncheckedLongCast(Object)")
          (= t Byte/TYPE) (Method/getMethod "byte uncheckedByteCast(Object)")
          (= t Short/TYPE) (Method/getMethod "short uncheckedShortCast(Object)"))]
    (.invokeStatic *gen* rt-type m)))

(defn- emit-checked-cast [t]
  (let [m
        (cond
          (= t Integer/TYPE) (Method/getMethod "int intCast(Object)")
          (= t Float/TYPE) (Method/getMethod "float floatCast(Object)")
          (= t Double/TYPE) (Method/getMethod "double doubleCast(Object)")
          (= t Long/TYPE) (Method/getMethod "long longCast(Object)")
          (= t Byte/TYPE) (Method/getMethod "byte byteCast(Object)")
          (= t Short/TYPE) (Method/getMethod "short shortCast(Object)"))]
    (.invokeStatic *gen* rt-type m)))

(defn- emit-cast [t]
  (cond
    (= t Boolean/TYPE)
    (do
      (.checkCast *gen* (asm-type java.lang.Boolean))
      (.invokeVirtual *gen* Type/BOOLEAN_TYPE (Method/getMethod "boolean booleanValue()")))

    (= t Character/TYPE)
    (do
      (.checkCast *gen* (asm-type java.lang.Character))
      (.invokeVirtual *gen* Type/CHAR_TYPE (Method/getMethod "char charValue()")))

    (primitive? t)
    (do
      (.checkCast *gen* (asm-type java.lang.Number))
      (if *unchecked-math*
        (emit-unchecked-cast t)
        (emit-checked-cast t)))

    :else
    (.checkCast *gen* (asm-type t))))

(defmulti emit-convert (fn [actual-type desired-type] [actual-type desired-type]))
(defmethod emit-convert [java.lang.Object Integer/TYPE]
  [actual-type desired-type]
  (emit-cast desired-type))
(defmethod emit-convert [java.lang.Object Long/TYPE]
  [actual-type desired-type]
  (emit-cast desired-type))
(defmethod emit-convert [java.lang.Object java.lang.Number]
  [actual-type desired-type]
  (emit-cast desired-type))
(defmethod emit-convert :default
  [actual-type desired-type]
  (when-not (= actual-type desired-type) (println "Conversion not implemented" [actual-type desired-type])))

(defn- emit-typed-arg [param-type {:as arg arg-type :type}]
  (assert arg-type (str "Missing type for arg " arg))
  (emit arg)
  (cond
    (= param-type arg-type)
    nil

    (convertible? arg-type param-type)
    (emit-convert arg-type param-type)

    :else
    (emit-cast param-type)))

(defn- emit-typed-args [param-types args]
  (doall (map emit-typed-arg param-types args)))

(defn- emit-box [type]
  (.box *gen* (asm-type type)))

(defn- find-method [class filter error-msg]
  (let [members (-> class (type-reflect :ancestors true) :members)
        methods (select filter members)
        _ (when-not (= (count methods) 1)
            (throw (IllegalArgumentException. error-msg)))]
    (first methods)))

#_(defn- find-best-method [class name args error-msg]
  (let [members (-> class (type-reflect :ancestors true) :members)
        methods (select (match name args convertible?) members)
        arg-classes (map :type args)]
    (if (= (count methods) 1)
      (first methods)
      (let [exacts (into []
                     (for [meth methods]
                       [(count (filter true? (map = (map maybe-class (:parameter-types meth)) arg-classes))) meth]))
            exacts (reverse (sort-by first exacts))
            [arank a] (first exacts)
            [brank b] (fnext exacts)]
        (if-not (= arank brank)
          a
          (throw (Exception. error-msg)))))))


(defn- emit-invoke-proto [{:keys [f args box]}]
  (let [{:keys [class statics protos]} @*frame*
        on-label (.newLabel *gen*)
        call-label (.newLabel *gen*)
        end-label (.newLabel *gen*)
        fsym (-> f :info :name )
        fvar (resolve fsym)
        proto @(-> fvar meta :protocol)
        e (get args 0)
        protocol-on (maybe-class (:on proto))]
    ; load the first arg, so we can see its type
    (emit e)
    (.dup *gen*)
    (.invokeStatic *gen* util-type (Method/getMethod "Class classOf(Object)"))
    (.loadThis *gen*)
    (.getField *gen* class (-> protos fsym :cached-class ) class-type) ; target,class,cached-class
    ; Check if first arg type is same as cached
    (.visitJumpInsn *gen* Opcodes/IF_ACMPEQ call-label) ; target
    (when protocol-on
      (.dup *gen*) ; target, target
      (.instanceOf *gen* (asm-type protocol-on))
      (.ifZCmp *gen* GeneratorAdapter/NE on-label))
    (.dup *gen*) ; target, target
    (.invokeStatic *gen* util-type (Method/getMethod "Class classOf(Object)")) ; target, class
    (.loadThis *gen*)
    (.swap *gen*)
    (.putField *gen* class (-> protos fsym :cached-class) class-type) ; target

    ; Slow path through proto-fn
    (.mark *gen* call-label) ; target
    (.getStatic *gen* class (-> fsym statics :name) var-type)
    (.invokeVirtual *gen* var-type var-get-raw-method) ; target, proto-fn
    (.swap *gen*)
    (emit-args-and-call args 1)
    (.goTo *gen* end-label)

    ; Fast path through interface
    (.mark *gen* on-label)
    (when protocol-on
      (let [mmap (:method-map proto)
            key (or (-> fsym name keyword mmap)
                    (throw (IllegalArgumentException.
                      (str "No method of interface: " protocol-on
                        " found for function: " fsym " of protocol: " (-> fvar meta :protocol)
                        " (The protocol method may have been defined before and removed.)"))))
            meth-name (-> key name munge)
            arg-types (map expression-type (rest args))
            meth (find-method protocol-on (ast/match meth-name arg-types convertible?)
                                          (apply str "No single method: " meth-name " of class: " protocol-on
                                                                    " found with args: " arg-types))]
        (emit-typed-args (:parameter-types meth) (rest args))
        (when (= (-> f :info :env :context ) :return )
          ; emit-clear-locals
          (println "Clear locals")
          )
        (let [{:keys [name return-type parameter-types]} meth
              m (apply asm-method name return-type parameter-types)]
          (.invokeInterface *gen* (asm-type protocol-on) m)
          (when box (emit-box return-type)))
        (.mark *gen* end-label)))))

(defn- emit-invoke-fn [{:keys [f args env]}]
  (emit f)
  (.checkCast *gen* ifn-type)
  (emit-args-and-call args 0))

(defmethod emit :invoke [ast]
  (.visitLineNumber *gen* (-> ast :env :line ) (.mark *gen*))
  (if (ast/protocol-node? ast)
    (emit-invoke-proto ast)
    (emit-invoke-fn ast)))

(defn- emit-instance [type args]
  (.newInstance *gen* type)
  (.dup *gen*)
  (doseq [arg args]
    (emit arg))
  (.invokeConstructor *gen* type (apply asm-method "<init>" "void" (map :type args))))

(defmethod emit :new
  [{:keys [ctor args env]}]
  (let [type (-> ctor :form asm-type)]
    (emit-instance type args)))

(defn- emit-local [v]
  (let [lb (-> @*frame* :locals v)
        _ (if-not lb (throw (Exception. (str "No local binding for: " v " in frame: " @*frame*))))
        opcode (-> lb :type asm-type (.getOpcode Opcodes/ILOAD))
        index (:index lb)]
    (.visitVarInsn *gen* opcode index)))

(defn- emit-var [v]
  (let [{:keys [class statics]} @*frame*]
    (.getStatic *gen* class (:name (statics v)) var-type)
    (.invokeVirtual *gen* var-type (if (dynamic? v) var-get-method var-get-raw-method))))

(defmethod emit :var [{:as form :keys [env info box]}]
  (let [v (:name info)
        lb (-> env :locals v)]
    (if lb
      (emit-local v)
      (emit-var v)))
  (when box (emit-box (expression-type form))))

(defmulti emit-test (fn [ast null-label false-label] (:op ast)))

(defmethod emit-test :default [ast null-label false-label]
  (emit ast)
  (doto *gen*
    .dup
    (.ifNull null-label)
    (.getStatic (asm-type java.lang.Boolean) "FALSE" (asm-type java.lang.Boolean))
    (.visitJumpInsn Opcodes/IF_ACMPEQ false-label)))

(defmethod emit :if
  [{:keys [test then else env box]}]
  (let [line (:line env)
        null-label (.newLabel *gen*)
        false-label (.newLabel *gen*)
        end-label (.newLabel *gen*)]
    (.visitLineNumber *gen* line (.mark *gen*))
    (emit-test test null-label false-label)
    (emit then)
    (.goTo *gen* end-label)

    (.mark *gen* null-label)
    (asm-pop (expression-type test))

    (.mark *gen* false-label)
    (emit else)

    (.mark *gen* end-label)))

(defmethod emit :def [{:keys [name form init env doc export] :as args}]
  (let [sym (second form)
        symbol (symbol (str *ns*) (str sym))
        {:keys [class statics]} @*frame*]
    (.getStatic *gen* class (:name (statics symbol)) var-type)
    (when (dynamic? sym)
      (.push *gen* true)
      (.invokeVirtual *gen* var-type (Method/getMethod "clojure.lang.Var setDynamic(boolean)")))
    (when-let [meta (meta sym)]
      (.dup *gen*)
      (emit-value clojure.lang.IPersistentMap meta)
      (.checkCast *gen* (asm-type clojure.lang.IPersistentMap))
      (.invokeVirtual *gen* var-type (Method/getMethod "void setMeta(clojure.lang.IPersistentMap)")))
    (when init
      (.dup *gen*)
      (emit init)
      (.invokeVirtual *gen* var-type (Method/getMethod "void bindRoot(Object)")))))

(defn- emit-constant [v box]
  (let [{:keys [class statics]} @*frame*
        {:keys [name type]} (statics v)]
    (.getStatic *gen* class name (asm-type type))
    (when box (emit-box type))))

(defmethod emit-boxed :constant [{:keys [form env]}]
  (if (nil? form)
    (.visitInsn *gen* Opcodes/ACONST_NULL)
    (emit-constant form true)))

(defmethod emit-unboxed :constant [{:keys [form env]}]
  (if (nil? form)
    (throw (Exception. "Can't emit primitive null"))
    (emit-constant form false)))

(defn- emit-statement [form]
  (emit form)
  (asm-pop (expression-type form)))

(defn compute-locals [{:as form :keys [env params referenced-locals]}]
  (into {}
    (concat
      (let [type java.lang.Object] ; TODO: compute actual type for prims
        (for [sym params]
          [sym {:index (next-local type) :type type :label (.mark *gen*)}]))
      (for [{:keys [name type]} referenced-locals :when (not (some #{name} params))]
        (let [sym name
              this (-> env :locals sym :this)
              name (-> @*frame* :fields sym :name)
              index (if this 0 (next-local type))]
          (when-not this
            (.loadThis *gen*)
            (.getField *gen* (:class @*frame*) name (asm-type type))
            (.visitVarInsn *gen* (-> type asm-type (.getOpcode Opcodes/ISTORE)) index))
          [sym {:index index :type type :label (.mark *gen*)}])))))

(defn emit-method [cv {:as form :keys [name params statements ret env recurs type] :or {name "invoke" type java.lang.Object}}]
  (binding [*gen* (GeneratorAdapter. Opcodes/ACC_PUBLIC (apply asm-method name type (map tagged-type params)) nil nil cv)
            *frame* (copy-frame)]
    (.visitCode *gen*)
    (swap! *frame* assoc :locals (compute-locals form))
    (let [end-label (.newLabel *gen*)]
      (swap! *frame* assoc :loop-label (.mark *gen*) :loop-types (map tagged-type params))
      (when statements
        (dorun (map emit-statement statements)))
      (emit ret)
      (.mark *gen* end-label)
      (doseq [[name {:keys [type label index]}] (:locals @*frame*)]
        (.visitLocalVariable *gen* (str name) (-> type asm-type .getDescriptor) nil label end-label index))
      (.unbox *gen* (asm-type type))
      (.returnValue *gen*)
      (.endMethod *gen*))))

(defn- emit-fn-methods [cv {:keys [name env methods max-fixed-arity variadic recur-frames] :as ast}]
  (doseq [meth methods]
    (if (:variadic meth)
      (notsup '(emit-variadic-fn-method meth))
      (emit-method cv meth))))

(defn- emit-closure [type args]
  (.newInstance *gen* type)
  (.dup *gen*)
  (doseq [{name :name} args]
    (emit-local name))
  (.invokeConstructor *gen* type (apply asm-method "<init>" "void" (map :type args))))

(defmethod emit :fn [ast]
  (let [name (str (or (:name ast) (gensym)))
        cw (emit-class name (assoc ast :super "clojure/lang/AFn") emit-fn-methods)
        bytecode (.toByteArray cw)
        class (load-class name bytecode ast)
        type (asm-type class)]
    (emit-closure type (closed-overs ast))))

(defmethod emit :do
  [{:keys [statements ret env box]}]
  (when statements
    (dorun (map emit-statement statements)))
  (emit ret))

(defn- emit-bindings [bindings]
  (into {}
    (map
      (fn [{:keys [name init]}]
        (emit init)
        (let [type (expression-type init)
              opcode (-> type asm-type (.getOpcode Opcodes/ISTORE))
              i (next-local type)]
          (.visitVarInsn *gen* opcode i)
          (swap! *frame* assoc-in [:locals name] {:index i :type type :label (.mark *gen*)})
          [name {:index i :type type :label (.mark *gen*)}]))
      bindings)))

(defmethod emit :let [{:keys [bindings statements ret env loop box]}]
  (binding [*frame* (copy-frame)]
    (let [bs (emit-bindings bindings)]
      (when loop
        (swap! *frame* assoc :loop-label (.mark *gen*) :loop-types (map #(-> % :name bs :type) bindings)))
      (when statements
        (dorun (map emit-statement statements)))
      (emit ret)
      (let [end-label (.mark *gen*)]
        (doseq [[name {:keys [type label index]}] bs]
          (.visitLocalVariable *gen* (str name) (-> type asm-type .getDescriptor) nil label end-label index))))))

(defmethod emit :recur [{:as form :keys [env frame exprs box]}]
  (emit-typed-args (:loop-types @*frame*) exprs)
  (dorun (map
           (fn [name]
             (let [{:keys [type index]} (-> @*frame* :locals name)]
               (.visitVarInsn *gen* (-> type asm-type (.getOpcode Opcodes/ISTORE)) index)))
           (:names frame)))
  (.goTo *gen* (:loop-label @*frame*)))

(defn- emit-field
  [env target field host-field box]
  (if-let [host-field (or host-field (ast/compute-host-field env (expression-type target) field))]
    (let [class (-> target expression-type asm-type)
          {:keys [name type]} host-field]
      (.checkCast *gen* class)
      (.getField *gen* class (clojure.core/name name) (asm-type type))
      (when box (emit-box type)))
    (do
      (.push *gen* (name field))
      (.invokeStatic *gen* (asm-type clojure.lang.Reflector)
                           (Method/getMethod "Object invokeNoArgInstanceMember(Object,String)")))))

(defn- emit-method-call [env target method args host-method box]
  (if-let [host-method (or host-method (ast/compute-host-method env (expression-type target) method (map expression-type args)))]
    (let [class (asm-type (expression-type target))
          {:keys [name parameter-types return-type declaring-class]} host-method
          meth (apply asm-method name return-type (map maybe-class parameter-types))
          declaring-class (maybe-class declaring-class)]
      (.checkCast *gen* class)
      (emit-typed-args (map maybe-class parameter-types) args)
      (if (.isInterface declaring-class)
        (.invokeInterface *gen* class meth)
        (.invokeVirtual *gen* class meth))
      (when box (emit-box (maybe-class return-type))))
    (do
      (when *warn-on-reflection*
        (.format (RT/errPrintWriter)
          "Reflection warning, %s:%d - call to %s can't be resolved.\n"
          (into-array Object [*file* (:line env) (str method)])))
      (.push *gen* (name method))
      (emit-as-array (map #(assoc % :box true) args))
      (.invokeStatic *gen* (asm-type clojure.lang.Reflector)
                           (Method/getMethod "Object invokeInstanceMethod(Object,String,Object[])")))))

(defmethod emit :dot
  [{:as form :keys [target field method host-field host-method args env box]}]
  (emit target)
  (if field
    (emit-field env target field host-field box)
    (emit-method-call env target method args host-method box)))

(defn- emit-fns
  [cv {:as ast :keys [name type fns]}]
  (doseq [fn fns]
    (emit-fn-methods cv fn)))

(defmethod emit :reify
  [{:as ast :keys [name ancestors]}]
  (let [c (-> ancestors first maybe-class)
        [super interfaces] (if (and c (.isInterface c))
          [java.lang.Object ancestors]
          [(first ancestors) (rest ancestors)])
        ast (assoc ast :super super :interfaces interfaces)
        cw (emit-class (str name) ast emit-fn-methods)
        bytecode (.toByteArray cw)
        class (load-class (str name) bytecode ast)]
    (emit-closure (asm-type class) (closed-overs ast))))

(defmethod emit :vector [args]
  (emit-as-array (:children args))
  (.invokeStatic *gen* rt-type (Method/getMethod "clojure.lang.IPersistentVector vector(Object[])")))

(defmethod emit :map [{:as form :keys [keys vals]}]
  (emit-as-array (interleave keys vals))
  (.invokeStatic *gen* rt-type (Method/getMethod "clojure.lang.IPersistentMap map(Object[])")))

(defmethod emit-boxed :default [args] (notsup "Unknown boxed operator: " (:op args) "\nForm: " args))
(defmethod emit-unboxed :default [args] (notsup "Unknown unboxed operator: " (:op args) "\nForm: " args))
