(ns cinc.compiler.jvm.bytecode.transform
  (:refer-clojure :exclude [name symbol])
  (:alias c.c clojure.core)
  (:require [clojure.string :as s]
            [cinc.analyzer.jvm.utils :refer [maybe-class]]
            [cinc.analyzer.utils :refer [update!]])
  (:import (org.objectweb.asm Type Label)
           (org.objectweb.asm.commons Method)))

(def rename {:insn               :visit-insn
             :start-method       :visit-code
             :var-insn           :visit-var-insn
             :try-catch-block    :visit-try-catch-block
             :line-number        :visit-line-number
             :jump-insn          :visit-jump-insn
             :lookup-switch-insn :visit-lookup-switch-insn
             :table-switch-insn  :visit-table-switch-insn
             :local-variable     :visit-local-variable})

(defn capitalize [[h & t]]
  (apply str (cons (s/upper-case h) t)))

(defn camel-case [s]
  (let [[head & rest] (s/split s #"-")]
    (s/join (cons head (map capitalize rest)))))

(defn name [x]
  (when x
    (if (class? x)
      (.getName ^Class x)
      (c.c/name x))))

(defn symbol
  ([x] (c.c/symbol (name x)))
  ([ns n] (c.c/symbol (name ns) (name n))))

(defn normalize [inst]
  (let [inst (rename inst inst)]
    (symbol (str "." (camel-case (name inst))))))

(def prim {"int"     "I"
           "float"   "F"
           "double"  "D"
           "long"    "L"
           "boolean" "Z"
           "byte"    "B"
           "char"    "C"
           "void"    "V"})

(defn class-desc
  ([c] (class-desc c false))
  ([c arr?]
     (when-let [c (name c)]
       (prim c
             (str (when arr? \[) \L (s/replace c \. \/) \;)))))

(defn class-type [c-desc]
  (Type/getType ^String (class-desc c-desc)))

(defn method-desc [ret method args]
  (Method/getMethod (str (name ret) " " method \( (s/join ", " (map name args)) \))))

(def ^:dynamic *labels* #{})
(def ^:dynamic *locals* #{})

(defn fix [inst]
  (case inst
    (:invoke-static :invoke-virtual :invoke-interface :invoke-constructor)
    (fn [[[m & args] ret]]
      (let [class (class-type (namespace m))
            method (method-desc ret (name m) args)]
        (list class method)))

    (:check-cast :new-array :array-store :new-instance :instance-of)
    (fn [[class]] (list (class-type class)))

    (:get-static :put-static :get-field :put-field)
    (fn [args]
      (let [[c f t] (if (= 3 (count args)) args
                        [(namespace (first args)) (name (first args)) (second args)])]
       (list (class-type c) (name f) (class-type (name t)))))

    (:mark)
    (fn [[label]]
      (let [label (symbol label)]
        (update! *labels* conj label)
        (list label)))

    (:var-insn)
    (fn [[insn label]]
      (list (list '.getOpcode (class-type (namespace insn))
                  (symbol "org.objectweb.asm.Opcodes" insn)) (symbol label)))

    (:try-catch-block)
    (fn [[l1 l2 l3 t]]
      (list (symbol l1) (symbol l2) (symbol l3) (class-desc t)))

    (:local-variable)
    (fn [[desc tag _ l1 l2 local]]
      (let [local (symbol local)]
        (update! *locals* conj local)
        (list (name desc) (class-type tag) nil (symbol l1) (symbol l2) local)))

    (:line-number)
    (fn [[line label]]
      (list (int line) (symbol label)))

    (:lookup-switch-insn)
    (fn [[l t lbs]]
      (list (symbol l) (int-array t) (into-array Label lbs)))

    (:table-switch-insn)
    (fn [[l h l lbs]]
      (list (int l) (int h) (symbol l) (into-array Label lbs)))

    ;;default
    (fn [args] (seq (map symbol args)))))

(defn transform [gen bc]
  (binding [*labels* *labels*
            *locals* *locals*]
    (let [calls (seq (map (fn [[inst & args]]
                            (list* (normalize inst) ((fix inst) args))) bc))]
      (eval ;; ugh
       `(let [*gen*# ~gen
              [~@*labels*] (repeatedly #(.newLabel *gen*#))
              [~@*locals*] (range)]
          (doto *gen*
            ~@calls))))))
