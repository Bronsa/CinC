(ns cinc.test.analyzer.passes
  (:refer-clojure :exclude [macroexpand-1])
  (:require [clojure.test :refer :all]
            [clojure.set :as set]
            [cinc.analyzer :refer [analyze macroexpand-1]]
            [cinc.analyzer.jvm :as jvm]
            [cinc.analyzer.utils :refer [walk prewalk postwalk cycling]]
            [cinc.analyzer.passes.source-info :refer [source-info]]
            [cinc.analyzer.passes.elide-meta :refer [elide-meta]]
            [cinc.analyzer.passes.constant-lifter :refer [constant-lift]]
            [cinc.analyzer.passes.warn-earmuff :refer [warn-earmuff]]
            [cinc.analyzer.passes.collect :refer [collect]]
            [cinc.analyzer.passes.jvm.clear-locals :refer [annotate-branch clear-locals]]
            [cinc.analyzer.passes.jvm.validate :refer [validate]]
            [cinc.analyzer.passes.jvm.infer-tag :refer [infer-tag infer-constant-tag]]
            [cinc.analyzer.passes.jvm.analyze-host-expr :refer [analyze-host-expr]])
  (:import (clojure.lang PersistentVector IPersistentMap
                         IPersistentSet ISeq Keyword Var
                         Symbol AFunction)
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
  (is (= PersistentVector (-> {:op :const :type :vector} infer-constant-tag :tag)))
  (is (= PersistentVector (-> (ast []) infer-constant-tag :tag)))
  (is (= IPersistentMap (-> (ast {}) infer-constant-tag :tag)))
  (is (= IPersistentSet (-> (ast #{}) infer-constant-tag :tag)))
  (is (= ISeq (-> (ast '()) infer-constant-tag :tag)))
  (is (= Class (-> {:op :const :type :class :form Object} infer-constant-tag :tag)))
  (is (= String (-> (ast "foo") infer-constant-tag :tag)))
  (is (= Keyword (-> (ast :foo) infer-constant-tag :tag)))
  (is (= Character (-> (ast \f) infer-constant-tag :tag)))
  (is (= Long (-> (ast 1) infer-constant-tag :tag)))
  (is (= Pattern (-> (ast #"foo") infer-constant-tag :tag)))
  (is (= Var (-> (ast #'+)  infer-constant-tag :tag)))
  (is (= Boolean (-> (ast true) infer-constant-tag :tag)))
  (is (= AFunction (-> (ast #()) infer-constant-tag :tag))))

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

(deftest infer-tag-test
  (let [t-ast (-> (ast (let [a 1 b (if "" a 2)] b))
                (walk infer-constant-tag
                      (cycling infer-tag)))]
    (is (every? #(= Long %) (->> t-ast :bindings (mapv :tag))))
    (is (= Long (-> t-ast :body :ret :tag)))))

(deftest infer-validate-test
  (let [t-ast (-> (binding [macroexpand-1 jvm/macroexpand-1]
                   (ast (let [a 1
                              b 2
                              c (str a)
                              d (Integer/parseInt c b)]
                          (Integer/getInteger c d))))
                (walk infer-constant-tag
                      (cycling infer-tag analyze-host-expr validate)))]
    (is (= Integer (-> t-ast :body :ret :tag)))
    (is (= Integer (-> t-ast :tag)))
    (is (= Long (->> t-ast :bindings (filter #(= 'a (:name %))) first :tag)))
    (is (= String (->> t-ast :bindings (filter #(= 'c (:name %))) first :tag)))
    (is (= Integer/TYPE (->> t-ast :bindings (filter #(= 'd (:name %))) first :tag))))

  (let [so-ast (binding [macroexpand-1 jvm/macroexpand-1]
                 (-> (ast (.println System/out "foo"))
                   (walk infer-constant-tag
                         (cycling infer-tag analyze-host-expr validate))))]

    (is (= Void/TYPE (-> so-ast :tag))))

  (binding [macroexpand-1 jvm/macroexpand-1]
    (let [l-ast (postwalk (ast (fn [x] (Long. x)))
                          (cycling infer-tag analyze-host-expr validate))]
      (is (= Long (-> l-ast :methods first :tag)))))

  (binding [macroexpand-1 jvm/macroexpand-1]
    (let [d-ast (postwalk (ast (Double/isInfinite 2))
                          (cycling infer-tag analyze-host-expr validate))]
      (is (= Boolean/TYPE (-> d-ast :tag)))
      (is (= Double/TYPE (->> d-ast :args first :tag))))))

(deftest collect-test
  (let [c-test (-> (ast (let [a 1 b 2] (fn [x] (fn [] [+ (:foo {}) x a]))))
                 (postwalk (comp validate constant-lift))
                 (prewalk (collect :constants
                                   :callsites
                                   :closed-overs
                                   :vars))
                 :body :ret)]
    (is (= '#{a} (-> c-test :closed-overs)))
    (is (set/subset? #{:foo #' + {}}
                     (-> c-test :constants keys set))) ;; it registers metadata too (line+col info)
    (is (= #{#'+} (-> c-test :vars keys set)))
    (is (= '#{a x} (-> c-test :methods first :body :ret :closed-overs)))

    (is (= #{:foo} (-> c-test :keyword-callsites)))))

(deftest clear-locals-test
  (let [f-expr (-> (ast (fn [x] (if x x x) x (if x (do x x) (if x x x))))
                 (prewalk annotate-branch)
                 clear-locals :methods first :body)]
    (is (= true (-> f-expr :statements first :test :should-not-clear)))
    (is (= true (-> f-expr :statements first :then :to-clear? nil?)))
    (is (= true (-> f-expr :statements first :else :to-clear? nil?)))
    (is (= true (-> f-expr :statements second :to-clear? nil?)))
    (is (= true (-> f-expr :ret :test :should-not-clear)))
    (is (= true (-> f-expr :ret :then :statements first :to-clear? nil?)))
    (is (= true (-> f-expr :ret :then :ret :to-clear?)))
    (is (= true (-> f-expr :ret :else :test :should-not-clear)))
    (is (= true (-> f-expr :ret :else :then :to-clear?)))
    (is (= true (-> f-expr :ret :else :else :to-clear?)))))

(defmacro jvm-ast [form]
  `(jvm/analyze '~form {:context :expr}))

(deftest uniquify-test
  (let [f-expr (jvm-ast (let [x 1 y x x (let [x x] x)]
                          (fn [y] x)))]
    (is (= 'x__#2 (-> f-expr :body :ret :methods first :body :ret :name)))
    (is (= 'y__#1 (-> f-expr :body :ret :methods first :params first :name)))
    (is (set/subset? '#{x__#2} (-> f-expr :body :ret :closed-overs)))))


(deftest all-tests-all-pass
  (is (= PersistentVector (-> (jvm-ast []) :tag)))
  (is (= IPersistentMap (-> (jvm-ast {}) :tag)))
  (is (= IPersistentSet (-> (jvm-ast #{}) :tag)))
  (is (= ISeq (-> (jvm-ast ()) :tag)))
  (is (= Class (-> (jvm-ast Object) :tag)))
  (is (= String (-> (jvm-ast "foo") :tag)))
  (is (= Keyword (-> (jvm-ast :foo) :tag)))
  (is (= Character (-> (jvm-ast \f) :tag)))
  (is (= Long (-> (jvm-ast 1) :tag)))
  (is (= Pattern (-> (jvm-ast #"foo") :tag)))
  (is (= Var (-> (jvm-ast #'+)  :tag)))
  (is (= Boolean (-> (jvm-ast true) :tag)))
  (is (= AFunction (-> (jvm-ast #()) :tag)))

  (let [i-ast (jvm-ast (if 1 2 3))]
    (is (:branch? i-ast))
    (is (= true (-> i-ast :test :should-not-clear)))
    (is (= true (-> i-ast :then :path?)))
    (is (= true (-> i-ast :else :path?))))

  (let [fn-ast (jvm-ast (fn ([]) ([x])))]
    (is (every? :path? (-> fn-ast :methods))))

  (let [r-ast (jvm-ast (reify Object (toString [this] "")))]
    (is (every? :path? (-> r-ast :methods))))

  (let [c-ast (-> (jvm-ast (case 1 0 0 2 2 1)) :body :ret)]
    (is (:branch? c-ast))
    (is (= true (-> c-ast :test :should-not-clear)))
    (is (= true (-> c-ast :default :path?)))
    (is (every? :path? (-> c-ast :thens))))

  (let [t-ast (jvm-ast (let [a 1 b (if "" a 2)] b))]
    (is (every? #(= Long %) (->> t-ast :bindings (mapv :tag))))
    (is (= Long (-> t-ast :body :ret :tag))))

  (let [d-ast (jvm-ast (Double/isInfinite 2))]
      (is (= Boolean/TYPE (-> d-ast :tag)))
      (is (= Double/TYPE (->> d-ast :args first :tag))))

  (let [t-ast (jvm-ast (let [a 1
                             b 2
                             c (str a)
                             d (Integer/parseInt c b)]
                         (Integer/getInteger c d)))]
    (is (= Integer (-> t-ast :body :ret :tag)))
    (is (= Integer (-> t-ast :tag)))
    (is (= Long (->> t-ast :bindings (filter #(= 'a__#0 (:name %))) first :tag)))
    (is (= String (->> t-ast :bindings (filter #(= 'c__#0 (:name %))) first :tag)))
    (is (= Integer/TYPE (->> t-ast :bindings (filter #(= 'd__#0 (:name %))) first :tag))))

  (let [so-ast (jvm-ast (.println System/out "foo"))]
    (is (= Void/TYPE (-> so-ast :tag))))

  (let [c-test (-> (jvm-ast (let [a 1 b 2] (fn [x] (fn [] [+ (:foo {}) x a]))))
                 :body :ret)]
    (is (= '#{a__#0} (-> c-test :closed-overs)))
    (is (set/subset? #{:foo #' + {}}
                     (-> c-test :constants keys set))) ;; it registers metadata too (line+col info)
    (is (= #{#'+} (-> c-test :vars keys set)))
    (is (= '#{a__#0 x__#0} (-> c-test :methods first :body :ret :closed-overs)))

    (is (= #{:foo} (-> c-test :keyword-callsites))))

  (is (jvm-ast (set! clojure.lang.Agent/pooledExecutor nil)))
  (is (jvm-ast (deftype x [^:volatile-mutable a] Object (toString [this] (set! (.a this) "") a))))

  (let [dt-ast (jvm-ast (deftype* x user.x [a b]
                          :implements [Appendable]
                          (append [this ^char x] this)))]
    (is (= :deftype (-> dt-ast :op)))
    (is (= '[a b] (->> dt-ast :fields (mapv :name))))
    (is (= '[append] (->> dt-ast :methods (mapv :name))))
    (is (= 'user.x (-> dt-ast :class-name .getName symbol))))

  (let [r-ast (jvm-ast (reify
                         Object (toString [this] "")
                         Appendable (append [this ^char x] this)
                         (meta [this] {})))]
    (is (= :reify (-> r-ast :op)))
    (is (= #{Appendable clojure.lang.IObj} (-> r-ast :interfaces)))
    (is (= '#{toString append meta} (->> r-ast :methods (mapv :name) set)))
    (is (= clojure.lang.IMeta (->> r-ast :methods (filter #(= 'meta (:name %))) first :interface))))

  (let [f-expr (-> (jvm-ast (fn [x] (if x x x) x (if x (do x x) (if x x x))))
                 :methods first :body)]
    (is (= true (-> f-expr :statements first :test :should-not-clear)))
    (is (= true (-> f-expr :statements first :then :to-clear? nil?)))
    (is (= true (-> f-expr :statements first :else :to-clear? nil?)))
    (is (= true (-> f-expr :statements second :to-clear? nil?)))
    (is (= true (-> f-expr :ret :test :should-not-clear)))
    (is (= true (-> f-expr :ret :then :statements first :to-clear? nil?)))
    (is (= true (-> f-expr :ret :then :ret :to-clear?)))
    (is (= true (-> f-expr :ret :else :test :should-not-clear)))
    (is (= true (-> f-expr :ret :else :then :to-clear?)))
    (is (= true (-> f-expr :ret :else :else :to-clear?)))))
