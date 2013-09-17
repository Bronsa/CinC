(ns cinc.compiler.jvm.bytecode
  (:refer-clojure :exclude [eval])
  (:require [cinc.analyzer.jvm :as a]
            [cinc.compiler.jvm.bytecode.emit :as e]))

(defn eval
  ([form] (eval form false))
  ([form debug?]
     (let [r (e/emit (a/analyze `(^:once fn* [] ~form) {:context :expression})
                     {:debug? debug?})
           {:keys [class]} (meta r)]
       ((.newInstance class)))))
