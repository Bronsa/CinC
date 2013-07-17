(ns cinc.analyzer.passes.warn-earmuff
  (:require [cinc.analyzer.utils :refer [dynamic?]]))

(defn warn-earmuff
  [{:keys [op name var] :as ast}]
  (let [name (str name)]
    (when (and (= :def op)
               (.startsWith name "*")
               (.endsWith name "*")
               (not (dynamic? var)))
      (binding [*out* *err*]
        (println "Warning:" name "not declared dynamic and this is not dynamically rebindable,"
                 "but its name suggests otherwise."
                 "Please either indicate ^:dynamic" name "or change the name"))))
  ast)
