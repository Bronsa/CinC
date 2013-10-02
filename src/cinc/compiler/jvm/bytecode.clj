(ns cinc.compiler.jvm.bytecode
  (:refer-clojure :exclude [eval])
  (:require [cinc.analyzer.jvm :as a]
            [cinc.compiler.jvm.bytecode.emit :as e])
  (:import clojure.lang.IFn))

(defn eval
  ([form] (eval form false))
  ([form debug?]
     (let [r (e/emit (a/analyze `(^:once fn* [] ~form) {:context :expr})
                     {:debug? debug?
                      :class-loader (clojure.lang.RT/makeClassLoader)})
           {:keys [class]} (meta r)]
       (.invoke ^IFn (.newInstance ^Class class)))))
