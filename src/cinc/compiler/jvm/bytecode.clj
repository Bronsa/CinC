(ns cinc.compiler.jvm.bytecode
  (:require [cinc.analyzer.jvm :as a]
            [cinc.compiler.jvm.bytecode.emit :as e]))

(defn eval [form]
  (let [r (e/emit (a/analyze `(^:once fn* [] ~form) {:context :expression}))
        {:keys [class]} (meta r)]
    ((.newInstance class))))
