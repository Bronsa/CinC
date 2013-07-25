(ns cinc.test.analyzer.jvm
  (:refer-clojure :exclude [macroexpand-1])
  (:require [clojure.test :refer :all]
            [cinc.analyzer :refer [analyze]]
            [cinc.analyzer.jvm :refer [macroexpand-1]]))

(defmacro ast [form]
  `(analyze '~form {:context :expr}))

(defmacro mexpand [form]
  `(macroexpand-1 '~form {:context :expr}))

(deftest macroexpander-test
  (is (= (list '. (list 'clojure.core/identity java.lang.Object) 'toString)
         (mexpand (.toString Object))))
  (is (= (list '. java.lang.Integer '(parseInt "2")) (mexpand (Integer/parseInt "2")))))

(deftest analyzer-test
  (is (= :monitor-enter (-> (ast (monitor-enter 1)) :op)))
  (is (= :monitor-exit (-> (ast (monitor-exit 1)) :op)))
  (is (= :import (-> (ast (clojure.core/import* Integer)) :op)))

  (let [r-ast (ast (reify
                     Object (toString [this] "")
                     Appendable (append [this ^char x] this)))]
    (is (= :reify (-> r-ast :op)))
    (is (= #{Appendable clojure.lang.IObj} (-> r-ast :interfaces)))
    (is (= '#{toString append} (->> r-ast :methods (mapv :name) set))))

  (let [dt-ast (ast (deftype* x user.x [a b]
                      :implements [Appendable]
                      (append [this ^char x] this)))]
    (is (= :deftype (-> dt-ast :op)))
    (is (= '[a b] (->> dt-ast :fields (mapv :name))))
    (is (= '[append] (->> dt-ast :methods (mapv :name))))
    (is (= 'user.x (-> dt-ast :class-name))))

  (let [c-ast (ast (case* 1 0 0 :number {2 [2 :two] 3 [3 :three]} :compact :int))]
    (is (= :number (-> c-ast :default :form)))
    (is (= #{2 3} (->> c-ast :tests (mapv (comp :form :test)) set)))
    (is (= #{:three :two} (->> c-ast :thens (mapv (comp :form :then)) set)))
    (is (= 3 (-> c-ast :high)))
    (is (= :int (-> c-ast :test-type)))
    (is (= :compact (-> c-ast :switch-type)))
    (is (= 2 (-> c-ast :low)))
    (is (= 0 (-> c-ast :shift)))
    (is (= 0 (-> c-ast :mask)))))
