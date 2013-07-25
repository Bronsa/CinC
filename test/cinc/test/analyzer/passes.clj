(ns cinc.test.analyzer.passes
  (:refer-clojure :exclude [macroexpand-1])
  (:require  [clojure.test :refer :all]
             [cinc.analyzer :refer [analyze]]
             [cinc.analyzer.utils :refer [prewalk postwalk]]
             [cinc.analyzer.passes.source-info :refer [source-info]]
             [cinc.analyzer.passes.elide-meta :refer [elide-meta]]
             [cinc.analyzer.passes.constant-lifter :refer [constant-lift]]
             [cinc.analyzer.passes.warn-earmuff :refer [warn-earmuff]]
             [cinc.analyzer.passes.collect :refer [collect]]
             [cinc.analyzer.passes.jvm.clear-locals :refer [annotate-branch clear-locals]]
             [cinc.analyzer.passes.jvm.validate :refer [validate]]
             [cinc.analyzer.passes.jvm.infer-tag :refer [infer-tag infer-constant-tag]]
             [cinc.analyzer.passes.jvm.analyze-host-expr :refer [analyze-host-expr]])
  (:import (clojure.lang IPersistentVector IPersistentMap
                         IPersistentSet ISeq Keyword Var
                         Symbol IFn)
           java.util.regex.Pattern))

(defmacro ast [form]
  `(analyze '~form {:context :expr}))

(def ^:const pi 3.14)

(deftest source-info-test
  (is (= 1 (-> {:form ^{:line 1} [1]} source-info :env :line)))
  (is (= 1 (-> {:form ^{:column 1} [1]} source-info :env :column))))

;; elides are set at compile-time
(deftest elide-meta-test)

(deftest infer-constant-tag-test
  (is (= IPersistentVector (-> {:op :const :type :vector} infer-constant-tag :tag)))
  (is (= IPersistentVector (-> (ast []) infer-constant-tag :tag)))
  (is (= IPersistentMap (-> (ast {}) infer-constant-tag :tag)))
  (is (= IPersistentSet (-> (ast #{}) infer-constant-tag :tag)))
  (is (= ISeq (-> (ast '()) infer-constant-tag :tag)))
  (is (= Object (-> {:op :const :type :class :form Object} infer-constant-tag :tag)))
  (is (= String (-> (ast "foo") infer-constant-tag :tag)))
  (is (= Keyword (-> (ast :foo) infer-constant-tag :tag)))
  (is (= Character (-> (ast \f) infer-constant-tag :tag)))
  (is (= Number (-> (ast 1) infer-constant-tag :tag)))
  (is (= Pattern (-> (ast #"foo") infer-constant-tag :tag)))
  (is (= Var (-> (ast #'+)  infer-constant-tag :tag)))
  (is (= Boolean (-> (ast true) infer-constant-tag :tag)))
  (is (= IFn (-> (ast #()) infer-constant-tag :tag))))

(deftest annotate-branch-test
  (let [i-ast (annotate-branch (ast (if 1 2 3)))]
    (is (:branch? i-ast))
    (is (= true (-> i-ast :test :should-not-clear)))
    (is (= true (-> i-ast :then :path?)))
    (is (= true (-> i-ast :else :path?))))

  (let [fn-ast (prewalk (ast (fn ([]) ([x]))) annotate-branch)]
    (is (every? :path? (-> fn-ast :methods))))

  (let [r-ast (prewalk (ast (reify Object (toString [this] x))) annotate-branch)]
    (is (every? :path? (-> r-ast :methods))))

  (let [c-ast (-> (ast (case 1 0 0 2 2 1)) :body :ret (prewalk annotate-branch))]
    (is (:branch? c-ast))
    (is (= true (-> c-ast :test :should-not-clear)))
    (is (= true (-> c-ast :default :path?)))
    (is (every? :path? (-> c-ast :thens)))))

(deftest constant-lift-test
  (is (= :const (-> (ast {:a {:b :c}}) (postwalk constant-lift) :op)))
  (is (not= :const (-> (ast {:a {:b #()}}) (postwalk constant-lift) :op)))
  (is (= :const (-> (ast [:foo 1 "bar" #{#"baz" {23 cinc.test.analyzer.passes/pi}}])
                  (postwalk constant-lift) :op))))
