(ns cinc.compiler.jvm.bytecode.transform
  (:refer-clojure :exclude [name])
  (:alias c.c clojure.core)
  (:require [clojure.string :as s]
            [cinc.analyzer.jvm.utils :refer [maybe-class]])
  (:import (org.objectweb.asm Type)
           (org.objectweb.asm.commons Method)))

(def rename {:insn               :visit-insn
             :var-insn           :visit-var-insn
             :try-catch-block    :visit-try-catch-block
             :line-number        :visit-line-number
             :jump-insn          :visit-jump-insn
             :lookup-switch-insn :visit-lookup-switch-insn
             :table-switch-insn  :visit-table-switch-insn
             :local-variable     :visit-local-variable})

(def special {})

(defn capitalize [[h & t]]
  (apply str (cons (s/upper-case h) t)))

(defn camel-case [s]
  (let [[head & rest] (s/split s #"-")]
    (s/join (cons head (map capitalize rest)))))

(defn name [x]
  (if (class? x)
    (.getName ^Class x)
    (c.c/name x)))

(defn normalize [inst]
  (let [inst (rename inst inst)]
    (symbol (str "." (special inst (camel-case (name inst)))))))

(def prim {"int"     "I"
           "float"   "F"
           "double"  "D"
           "long"    "L"
           "boolean" "Z"
           "byte"    "B"
           "char"    "C"
           "void"    "V"})

(defn maybe-prim [x]
  (prim x x))

(defn class-desc
  ([c] (class-desc c false))
  ([c arr?]
     (let [c-desc (if (class? c)
                    (maybe-prim (.getName ^Class c))
                    (str (when arr? \[) (prim c (str \L (s/replace c \. \/) \;))))]
      (Type/getType ^String c-desc))))

(defn method-desc [ret method args]
  (Method/getMethod (str (name ret) " " method \( (s/join ", " (map name args)) \))))

(defn fix [inst]
  (case inst
    (:invoke-static :invoke-virtual)
    (fn [[[m & args] ret]]
      (let [class (class-desc (namespace m))
            method (method-desc ret (name m) args)]
        (list class method)))

    (:check-cast :new-array :array-store)
    (fn [[class]] (list (class-desc (name class))))

    (:insn)
    (fn [[f]] (list (symbol (name f))))

    (:get-static)
    (fn [[f t]]
      (list (class-desc (namespace f)) (name f) (class-desc (name t))))
    identity))

(defn transform [bc]
  (concat '(doto *gen*)
          (seq (map (fn [[inst & args]]
                      (list* (normalize inst) ((fix inst) args))) bc))))
