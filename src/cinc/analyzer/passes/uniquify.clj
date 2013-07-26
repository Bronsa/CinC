(ns cinc.analyzer.passes.uniquify
  (:require [cinc.analyzer.utils :refer [prewalk update!]]))

(def ^:dynamic *locals* {})
(def ^:dynamic *locals-frame* {})
(def ^:dynamic *locals-init* {})

(defmulti -uniquify-locals :op)

(defn normalize [name]
  (if-let [idx (*locals-frame* name)]
    (symbol (str name "__#" idx))
    name))

(defn denormalize [name]
  (let [[_ s] (re-find #"(.+?)__#\d+" (str name))]
    (and s (symbol s))))

(defn uniquify [name]
  (when (not (*locals* (denormalize name)))
    (update! *locals* update-in [name] (fnil inc -1))
    (update! *locals-frame* assoc-in [name] (*locals* name))))

(defn uniquify-cleanup [name]
  (when-let [name (denormalize name)]
    (when (*locals* name)
      (update! *locals-frame* update-in [name] dec))))

(declare uniquify-locals*)

(defn uniquify-bindings
  [{:keys [bindings] :as ast}]
  (let [bindings (for [{:keys [init name] :as b} bindings]
                   (let [init (binding [*locals-frame* *locals-frame*]
                                (uniquify-locals* init))]
                     (uniquify name)
                     (let [name (normalize name)]
                       (update! *locals-init* assoc name init)
                       (assoc b
                         :name name
                         :init init))))]
    (assoc ast :bindings (vec bindings))))

(defmethod -uniquify-locals :let
  [ast]
  (uniquify-bindings ast))

(defmethod -uniquify-locals :loop
  [ast]
  (uniquify-bindings ast))

(defmethod -uniquify-locals :letfn
  [ast]
  (uniquify-bindings ast))

(defmethod -uniquify-locals :local
  [{:keys [name local init] :as ast}]
  (if (not= :field local)
    (let [name (normalize name)]
      (merge ast
             {:name name}
             (when-let [init (*locals-init* name)]
               {:init init})))
    ast))

(defmethod -uniquify-locals :binding
  [{:keys [name local] :as ast}]
  (if (not (#{:field :let :letfn :loop} local))
    (do (assoc ast :name (normalize name)))
    ast))

(defmethod -uniquify-locals :default [ast] ast)

(defmethod -uniquify-locals :fn-method
  [{:keys [params] :as ast}]
  (doseq [{:keys [name]} params]
    (uniquify name))
  ast)

(defmethod -uniquify-locals :method
  [{:keys [params this] :as ast}]
  (doseq [{:keys [name]} params]
    (uniquify name))
  (uniquify this)
  (assoc ast :this (normalize this)))

(defmethod -uniquify-locals :fn
  [{:keys [name] :as ast}]
  (if name
    (do (uniquify name)
        (assoc ast :name (normalize name)))
    ast))

(defmethod -uniquify-locals :catch
  [{:keys [local] :as ast}]
  (uniquify (:name local))
  ast)

(defn uniquify-locals* [ast]
  (prewalk ast -uniquify-locals))

(defn uniquify-locals [ast]
  (binding [*locals*       *locals*
            *locals-frame* *locals-frame*
            *locals-init*  *locals-init*]
    (uniquify-locals* ast)))
