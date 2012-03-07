(ns test.clojure.java.compiler
  (:require [clojure.java.compiler :as c])
  (:use [clojure.test]))

(in-ns 'user)
(defprotocol TestProtocol
  (foo [t]))

(defrecord test-record-implements []
  TestProtocol
  (foo [t] 1))

(defrecord test-record-extends [])

(defrecord test-field [a])

(def a 1)
(extend-protocol TestProtocol
  test-record-extends
  (foo [t] 2))
(def rec-implements (test-record-implements.))
(def rec-extends (test-record-extends.))
(def rec-field (test-field. 1))

(defn max-args-fn [a & rest] :success)

(in-ns 'test.clojure.java.compiler)

(deftest test-eval
  (is (= 1 (c/eval '1)))
  (testing "invocation"
    (is (= 3 (c/eval '(+ 1 2))))
    (is (= :success (c/eval '(user/max-args-fn :a :b :c :d :e :f :g :h :i :j :k :l :m :n :o :p :q :r :s :t :u :v :w :x :y :z)))
      (str "functions with more than " clojure.java.compiler/max-positional-arity " arguments")))
  (testing "vector"
    (is (= [1 2] (c/eval '[1 2]))))
  (testing "map"
    (is (= {:x 1 :y 2} (c/eval '{:x 1 :y 2}))))
  (testing "if"
    (is (= :true (c/eval '(if :true :true :false))))
    (is (= :false (c/eval '(if nil :true :false)))))
  (testing "let"
    (is (= 9 (c/eval '(let [x 9] x))))
    (is (= 10 (c/eval '(let [x 8] (+ x 2)))))
    (is (= [1 2] (c/eval '(let [x 1] (let [y 2] [x y])))) "Nested lets"))
  (testing "vars"
    (is (= 3 (c/eval '(+ a 2))))
    (is (c/eval '(def b 3)))
    (is (= {:ns (find-ns 'user), :name 'c, :tag 'int} (meta (c/eval '(def ^int c 9))))) "metadata on vars")
  (testing "protocol invocation"
    (is (= 1 (c/eval '(foo rec-implements))))
    (is (= 2 (c/eval '(foo rec-extends)))))
  (testing "interop"
    (is (= 1 (c/eval '(.-a rec-field))))
    (is (= "1" (c/eval '(. 1 (toString))))))
  (testing "fn"
    (is (= 1 ((c/eval '(fn [a] 1)) 1)))
    (is (= 10 ((c/eval '(fn b [a] (if (< a 10) (b (inc a)) a))) 1))))
  (testing "reify"
    (is (= 1 ((c/eval '(reify clojure.lang.IFn (invoke [this] 1))))))
    (is (= "1" (str (c/eval '(reify Object (toString [this] "1"))))))
    (is (= 3 ((c/eval '(reify clojure.lang.IFn (invoke [this a] (+ a 2)))) 1)))
    (is (= "9" ((c/eval '(reify
                           Object
                           (toString [this] (str (.hashCode this)))
                           (hashCode [this] 9)
                           clojure.lang.IFn
                           (invoke [this] (str this)))))))))
