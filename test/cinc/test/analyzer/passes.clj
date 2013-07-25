(ns cinc.test.analyzer.passes
  (:refer-clojure :exclude [macroexpand-1])
  (:require  [clojure.test :refer :all]
             [cinc.analyzer :refer [analyze]]
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

;; (defmacro ast [form]
;;   `(analyze '~form {:context :expr}))

(deftest source-info-test
  (is (= 1 (-> {:form ^{:line 1} [1]} source-info :env :line)))
  (is (= 1 (-> {:form ^{:column 1} [1]} source-info :env :column))))

;; elides are set at compile-time
(deftest elide-meta-test)

(deftest infer-constant-tag-test
  (is (= IPersistentVector (-> {:op :const :type :vector} infer-constant-tag :tag)))
  (is (= IPersistentVector (-> {:op :vector} infer-constant-tag :tag)))
  (is (= IPersistentMap (-> {:op :map} infer-constant-tag :tag)))
  (is (= IPersistentSet (-> {:op :set} infer-constant-tag :tag)))
  (is (= ISeq (-> {:op :seq} infer-constant-tag :tag)))
  (is (= Object (-> {:op :const :type :class :form Object} infer-constant-tag :tag)))
  (is (= String (-> {:op :const :type :string} infer-constant-tag :tag))))
