(ns cinc.analyzer.passes.jvm.validate
  (:require [cinc.analyzer :refer [-analyze]]
            [cinc.analyzer.utils :refer [arglist-for-arity]]
            [cinc.analyzer.jvm.utils :as u])
  (:import (clojure.lang IFn)))

(defmulti -validate :op)

(defmethod -validate :maybe-class
  [{:keys [maybe-class env] :as ast}]
  (if-let [the-class (u/maybe-class maybe-class)]
    (-analyze :const the-class env :class)
    (if (.contains (str maybe-class) ".") ;; try and be smart for the exception
      (throw (ex-info (str "class not found: " maybe-class)
                      {:class maybe-class}))
      (throw (ex-info (str "could not resolve var: " maybe-class)
                      {:var maybe-class})))))

(defmethod -validate :maybe-host-form
  [{:keys [maybe-class]}]
  (throw (ex-info (str "No such namespace: " maybe-class)
                  {:ns maybe-class})))

(defmethod -validate :catch
  [{:keys [maybe-class] :as ast}]
  (if maybe-class
    (if-let [the-class (u/maybe-class maybe-class)]
      (assoc (dissoc ast :maybe-class)
        :class the-class)
      (throw (ex-info (str "class not found: " maybe-class)
                      {:class maybe-class})))
    ast))

(defn tag-match? [arg-tags meth]
  (every? identity (map u/convertible? arg-tags (:parameter-types meth))))

(defmethod -validate :new
  [{:keys [maybe-class args] :as ast}]
  (if maybe-class
    (if-let [the-class (u/maybe-class maybe-class)]
      (let [c-name (symbol (.getName the-class))
            argc (count args)]
        (if-let [[ctor & rest] (->> (filter #(= (count (:parameter-types %)) argc)
                                           (u/members the-class c-name))
                                   (filter (partial tag-match? (mapv :tag args)))
                                   seq)]
          (if (empty? rest)
            (let [arg-tags (mapv u/maybe-class (:parameter-types ctor))
                  args (mapv (fn [arg tag] (assoc arg :tag tag)) args arg-tags)]
              (assoc (dissoc ast :maybe-class)
                :class the-class
                :args args))
            (throw (ex-info (str "ambiguous signature for ctor of class: " the-class)
                            {:class the-class
                             :args  args})))
          (throw (ex-info (str "no ctor found for ctor of class: " the-class " and give signature")
                          {:class the-class
                           :args  args}))))
      (throw (ex-info (str "class not found: " maybe-class)
                      {:class maybe-class})))
    ast))

(defmethod -validate :static-call
  [{:keys [class method args tag] :as ast}]
  (if tag
    ast
    (let [argc (count args)]
      (if-let [matching-methods (seq (u/static-methods class method argc))]
        (if-let [[m & rest] (seq (filter (partial tag-match? (mapv :tag args)) matching-methods))]
          (if (empty? rest)
            (let [ret-tag (u/maybe-class (:return-type m))
                  arg-tags (mapv u/maybe-class (:parameter-types m))
                  args (mapv (fn [arg tag] (assoc arg :tag tag)) args arg-tags)]
              (assoc ast
                :tag ret-tag
                :args args))
            ast)
          (throw (ex-info (str "No matching method: " method " for class: " class " and given signature")
                          {:method method
                           :class  class
                           :args   args})))
        (throw (ex-info (str "No matching method: " method " for class: " class " and arity: " argc)
                        {:method method
                         :class  class
                         :argc   argc}))))))

(defmethod -validate :instance-call
  [{:keys [class method args tag] :as ast}]
  (if (and class (not tag))
    (let [argc (count args)]
      (if-let [matching-methods (seq (u/instance-methods class method argc))]
        (if-let [[m & rest] (seq (filter (partial tag-match? (mapv :tag args)) matching-methods))]
          (if (empty? rest)
            (let [ret-tag (u/maybe-class (:return-type m))
                  arg-tags (mapv u/maybe-class (:parameter-types m))
                  args (mapv (fn [arg tag] (assoc arg :tag tag)) args arg-tags)]
              (assoc ast
                :tag ret-tag
                :args args))
            ast)
          (throw (ex-info (str "No matching method: " method " for class: " class " and given signature")
                          {:method method
                           :class  class
                           :args   args})))
        (throw (ex-info (str "No matching method: " method " for class: " class " and arity: " argc)
                        {:method method
                         :class  class
                         :argc   argc}))))
    ast))

(defmethod -validate :import
  [{:keys [maybe-class] :as ast}]
  (if maybe-class
    (if-let [the-class (u/maybe-class maybe-class)]
      (assoc (dissoc ast :maybe-class)
        :class the-class)
      (throw (ex-info (str "class not found: " maybe-class)
                      {:class maybe-class})))
    ast))

(defn validate-tag [tag]
  (if (set? tag)
    (set (mapv validate-tag tag))
    (if-let [the-class (u/maybe-class tag)]
      the-class
      (throw (ex-info (str "class not found: " tag)
                      {:class tag})))))

(defmethod -validate :def
  [{:keys [var init] :as ast}]
  (when-let [tag (:tag init)]
    (alter-meta! var assoc :tag tag))
  (when-let [arglists (:arg-lists init)]
    (doseq [arglist arglists]
      (when-let [tag (:tag (meta arglist))]
        (validate-tag tag)))
    (alter-meta! var assoc :arg-lists arglists))
  ast)

(defmethod -validate :invoke
  [{:keys [args fn form] :as ast}]
  (let [argc (count args)]
    (if (and (= :const (:op fn))
             (= :keyword (:type fn)))
      (if (<= 1 argc 2)
        (assoc ast :op :keyword-invoke)
        (throw (ex-info (str "Cannot invoke keyword with " argc " arguments")
                        {:form form})))
      (do
        (when (:arg-lists fn)
          (when-not (doto (arglist-for-arity fn argc))
            (throw (ex-info (str "No matching arity found for function: " (:name fn))
                            {:arity (count args)
                             :fn    fn }))))
        (when (= :const (:op fn))
          (when (not (instance? IFn (:form fn)))
            (throw (ex-info (str (class (:form fn)) " is not a function, but it's used as such")
                            {:form form}))))
        ast))))

(defn -deftype [name class-name args interfaces]
  (eval (list 'deftype* name class-name args :implements (vec interfaces))))

(defmethod -validate :deftype
  [{:keys [name class-name fields interfaces] :as ast}]
  (if class-name
    (do(-deftype name class-name (mapv :name fields) interfaces)
       (dissoc (assoc ast :tag (u/maybe-class class-name)) :class-name))
    ast))

(defmethod -validate :method
  [{:keys [name interfaces tag params fixed-arity] :as ast}]
  (if interfaces
    (let [interfaces (conj interfaces Object)
          methods (seq (filter identity
                               (mapcat #(u/instance-methods % name fixed-arity) interfaces)))]
      (if-let [[m & rest] (seq (filter (partial tag-match? (mapv :tag params)) methods))]
        (if (empty? rest)
          (let [ret-tag (u/maybe-class (:return-type m))
                i-tag (u/maybe-class (:declaring-class m))
                arg-tags (mapv u/maybe-class (:parameter-types m))
                args (mapv (fn [arg tag] (assoc arg :tag tag)) params arg-tags)]
            (assoc (dissoc ast :interfaces)
              :interface i-tag
              :tag ret-tag
              :args args))
          (throw (ex-info (str "ambiguous method signature for method: " name)
                          {:method     name
                           :interfaces interfaces
                           :params     params})))
        (throw (ex-info (str "no such method found: " name " with given signature in any of the"
                             " provided interfaces: " interfaces)
                        {:method     name
                         :interfaces interfaces
                         :params     params}))))
    ast))

(defmethod -validate :default [ast] ast)

(defn validate
  [{:keys [tag] :as ast}]
  (let [ast (if tag
              (assoc ast :tag (validate-tag tag))
              ast)]
    (-validate ast)))
