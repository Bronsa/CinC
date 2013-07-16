(ns cinc.analyzer.passes.constant-lifter
  (:require [cinc.analyzer :refer [-analyze]]
            [cinc.analyzer.utils :refer [constant?]]))

(defmulti constant-lift :op)

(defmethod constant-lift :vector
  [{:keys [items form env] :as ast}]
  (if (and (every? :literal? items)
           (not (meta form)))
    (-analyze :const (mapv :form items) env :vector)
    ast))

(defmethod constant-lift :map
  [{:keys [keys vals form env] :as ast}]
  (if (and (every? :literal? keys)
           (every? :literal? vals)
           (not (meta form)))
    (-analyze :const (zipmap (map :form keys)
                             (map :form vals)) env :map)
    ast))

(defmethod constant-lift :set
  [{:keys [items form env] :as ast}]
  (if (and (every? :literal? items)
           (not (meta form)))
    (-analyze :const (set (mapv :form items)) env :set)
    ast))

(defmethod constant-lift :var
  [{:keys [var env] :as ast}]
  (if (constant? var)
    (-analyze :const @var env :var)
    ast))

(defmethod constant-lift :default [ast] ast)
