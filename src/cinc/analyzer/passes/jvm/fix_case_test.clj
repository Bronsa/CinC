(ns cinc.analyzer.passes.jvm.fix-case-test)

(defn fix-case-test [ast]
  (when (:case-test ast)
    (swap! (:atom ast) assoc :case-test true))
  ast)
