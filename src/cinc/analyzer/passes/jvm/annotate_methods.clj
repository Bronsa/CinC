(ns cinc.analyzer.passes.jvm.annotate-methods
  (:require [cinc.analyzer.jvm.utils :refer [type-reflect]]))

(defn annotate-methods
  [{:keys [op methods interfaces] :as ast}]
  (case op
    (:reify :deftype)
    (let [all-methods
          (into #{}
                (mapcat (fn [class]
                          (mapv (fn [method]
                                  (dissoc method :exception-types))
                                (remove (fn [{:keys [flags return-type]}]
                                          (or (some #{:static :final} flags)
                                              (not-any? #{:public :protected} flags)
                                              (not return-type)))
                                        (:members (type-reflect class :ancestors true)))))
                        (conj interfaces Object)))]
      (assoc ast :methods (mapv (fn [{:keys [name params] :as ast}]
                                  (let [argc (count params)]
                                   (assoc ast :methods
                                          (filter #(and (= name (:name %))
                                                        (= argc (count (:parameter-types %))))
                                                  all-methods)))) methods)))
    ast))
