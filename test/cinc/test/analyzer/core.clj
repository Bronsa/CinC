(ns cinc.test.analyzer.core
  (:refer-clojure :exclude [macroexpand-1])
  (:require [clojure.test :refer :all]
            [cinc.analyzer :refer [analyze macroexpand-1]]))

(defmacro ast [form]
  `(analyze '~form {:context :expr}))

(defmacro mexpand [form]
  `(macroexpand-1 '~form {:context :expr}))

(defmacro foo []
  1)

(deftest analyzer-test

  (let [nil-ast (ast nil)]
    (is (= :const (:op nil-ast)))
    (is (= :nil (:type nil-ast)))
    (is (:literal? nil-ast)))

  (let [v-ast (ast ^:foo [1 2])]
    (is (= :with-meta (:op v-ast)))
    (is (= :map (-> v-ast :meta :op)))
    (is (= {:foo true} (-> v-ast :meta :form)))
    (is (= [1 2] (-> v-ast :expr :form))))

  (let [m-ast (ast {:a 1 :b 2})]
    (is (= {:a 1 :b 2} (:form m-ast)))
    (is (= [:a :b] (->> m-ast :keys (mapv :form))))
    (is (= [1 2] (->> m-ast :vals (mapv :form)))))

  (is (= 'a (mexpand a)))
  (is (= ::foo (mexpand ::foo)))
  (is (= '(new foo) (mexpand (foo.))))
  (is (= '(new foo a) (mexpand (foo. a))))
  (is (= 'foo/bar (mexpand foo/bar)))
  (is (= '(. bar (foo 1)) (mexpand (.foo bar 1))))
  (is (= '(. bar foo) (mexpand (.foo bar))))
  (is (= 1 (mexpand (cinc.test.analyzer.core/foo))))

  (let [s-ast (ast '+)]
    (is (= :symbol (:type s-ast)))
    (is (= '+ (:form s-ast))))

  (let [v-ast (ast +)]
    (is (= :var (:op v-ast)))
    (is (= '+ (:form v-ast)))
    (is (= #'+ (:var v-ast)))
    (is (= 'clojure.core (:ns v-ast)))
    (is (not (:assignable? v-ast))))

  (is (:assignable? (ast *warn-on-reflection*)))

  (let [mh-ast (ast foo/bar)]
    (is (= :maybe-host-form (:op mh-ast)))
    (is (= 'foo (:maybe-class mh-ast)))
    (is (= 'bar (:maybe-field mh-ast))))

  (let [mc-ast (ast bar)]
    (is (= :maybe-class (:op mc-ast)))
    (is (= 'bar (:maybe-class mc-ast))))

  (let [l-ast (ast (let [a 1] a))]
    (is (= :local (-> l-ast :body :ret :op)))
    (is (= :let (-> l-ast :body :ret :local)))
    (is (= 1 (-> l-ast :body :ret :init :form))))

  (let [do-ast (ast (do 1 2 3))]
    (is (= 3 (-> do-ast :ret :form)))
    (is (= [1 2] (->> do-ast :statements (mapv :form))))
    (is (= :statement (-> do-ast :statements first :env :context))))

  (let [if-ast (ast (if 1 2 3))]
    (is (= [1 2 3] (->> if-ast ((juxt :test :then :else)) (mapv :form)))))

  (let [new-ast (ast (foo. 1 2))]
    (is (= 'foo (:maybe-class new-ast)))
    (is (= [1 2] (->> new-ast :args (mapv :form)))))

  (let [v-ast (ast #'+)]
    (is (= :the-var (:op v-ast)))
    (is (= #'+ (:var v-ast))))

  (let [q-ast (ast '^{a b} [c d])]
    (is (= :const (-> q-ast :meta :op)))
    (is (= :const (-> q-ast :expr :op)))
    (is (= '{a b} (-> q-ast :meta :form)))
    (is (= '[c d] (-> q-ast :expr :form))))

  (let [s-ast (ast (set! *warn-on-reflection* true))]
    (is (= :set! (:op s-ast)))
    (is (= #'*warn-on-reflection* (-> s-ast :target :var)))
    (is (= true (-> s-ast :val :form))))

  (let [t-ast (ast (try 0 (catch E1 e e) (catch E2 e 2) (finally 3)))]
    (is (= 0 (-> t-ast :body :ret :form)))
    (is (= 2 (-> t-ast :catches second :body :ret :form)))
    (is (= 'E1 (-> t-ast :catches first :maybe-class)))
    (is (= 'e (-> t-ast :catches first :local :name)))
    (is (= 3 (-> t-ast :finally :ret :form))))

  (let [lfn-ast (ast (letfn [(a [] (b)) (b [] (a))] a))]
    (is (= :letfn (-> lfn-ast :body :ret :local)))
    (is (= '[a b] (->> lfn-ast :bindings (mapv :name)))))

  (let [l-ast (ast (loop [x 1] (recur 2)))]
    (is (= :loop (-> l-ast :bindings first :local)))
    (is (= :return (-> l-ast :body :env :context))))

  (let [f-ast (ast (fn a ([y & x] [x y]) ([] a) ([z] z)))]
    (is (= 1 (-> f-ast :max-fixed-arity)))
    (is (:variadic? f-ast))
    (is (= 'a (-> f-ast :name)))
    (is (= true (-> f-ast :methods first :variadic?))))

  (let [d-ast (ast (def ^{c d} a 1))]
    (is (= 'a (-> d-ast :name)))
    (is (= '{c d} (-> d-ast :var meta))))

  (let [hc-ast (ast (.foo bar baz))]
    (is (= :host-call (-> hc-ast :op)))
    (is (= 'foo (-> hc-ast :method))))

  (let [hf-ast (ast (.-foo bar))]
    (is (= :host-field (-> hf-ast :op)))
    (is (= 'foo (-> hf-ast :field))))

  (let [hi-ast (ast (.foo bar))]
    (is (= :host-interop (-> hi-ast :op)))
    (is (= 'foo (-> hi-ast :m-or-f))))

  (let [i-ast (ast (1 2))]
    (is (= :invoke (-> i-ast :op)))
    (is (= 1 (-> i-ast :fn :form)))
    (is (= [2] (->> i-ast :args (mapv :form))))))
