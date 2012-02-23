(ns test.clojure.compiler
  (:require [clojure.compiler :as c])
  (:use [clojure.test]))

(in-ns 'user)

(def a 1)

(defprotocol TestProtocol
  (foo [t]))

(defrecord test-record-implements []
  TestProtocol
  (foo [t] 1))

(defrecord test-record-extends [])

(extend-protocol TestProtocol
  test-record-extends
  (foo [t] 2))

(def rec-implements (test-record-implements.))
(def rec-extends (test-record-extends.))

(defrecord test-field [a])

(def rec-field (test-field. 1))

(in-ns 'test.clojure.compiler)

(deftest test-eval
  (is (= 1 (c/eval '1)))
  (is (= 3 (c/eval '(+ 1 2))))
  (testing "if"
    (is (= :true (c/eval '(if :true :true :false))))
    (is (= :false (c/eval '(if nil :true :false)))))
  (testing "let"
    (is (= 9 (c/eval '(let [x 9] x))))
    (is (= 10 (c/eval '(let [x 8] (+ x 2))))))
  (testing "vars"
    (is (= 3 (c/eval '(+ a 2))))
    (is (c/eval '(def b 3))))
  (testing "protocol invocation"
    (is (= 1 (c/eval '(foo rec-implements))))
    (is (= 2 (c/eval '(foo rec-extends)))))
  (testing "interop"
    (is (= 1 (c/eval '(.-a rec-field))))
    (is (= "1" (c/eval '(. 1 (toString)))))))
