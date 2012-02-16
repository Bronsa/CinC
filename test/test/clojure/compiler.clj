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

(in-ns 'test.clojure.compiler)

(deftest test-eval
  (is (= 1 (c/eval '1)))
  (is (= 3 (c/eval '(+ 1 2))))
  (testing "vars"
    (is (= 3 (c/eval '(+ a 2))))
    (is (c/eval '(def b 3))))
  (testing "protocol invocation"
    (is (= 1 (c/eval '(foo rec-implements))))
    (is (= 2 (c/eval '(foo rec-extends))))))
