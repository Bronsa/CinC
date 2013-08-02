(ns cinc.analyzer.passes.jvm.validate
  (:require [cinc.analyzer :refer [-analyze]]
            [cinc.analyzer.utils :refer [arglist-for-arity]]
            [cinc.analyzer.jvm.utils :as u])
  (:import (clojure.lang IFn)))

(defmulti -validate :op)

(defmethod -validate :maybe-class
  [{:keys [maybe-class env] :as ast}]
  (if-let [the-class (u/maybe-class maybe-class)]
    (assoc (-analyze :const the-class env :class)
      :tag Class)
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

(defmethod -validate :set!
  [{:keys [target] :as ast}]
  (when (and (not (:assignable? target))
             (not (= :host-interop (:op target))))
    (throw (ex-info "cannot set! non-assignable target" {:target target})))
  ast)

(defn tag-match? [arg-tags meth]
  (every? identity (map u/convertible? arg-tags (:parameter-types meth))))

(defn subsume [tags methods]
  (let [match? (fn [[x y]] (or (nil? y) (= (u/maybe-class x) (u/maybe-class y))))
        methods (or (seq (filter #(every? match? (mapv list (:parameter-types %) tags)) methods))
                    methods)]
    (remove (fn [x] (some #(and (not= % x)
                               (u/subsumes (:parameter-types %)
                                           (:parameter-types x))) methods))
            methods)))

(defmethod -validate :new
  [{:keys [maybe-class args] :as ast}]
  (if maybe-class
    (if-let [the-class (u/maybe-class maybe-class)]
      (let [c-name (symbol (.getName the-class))
            argc (count args)
            tags (mapv :tag args)]
        (if-let [[ctor & rest] (->> (filter #(= (count (:parameter-types %)) argc)
                                            (u/members the-class c-name))
                                    (filter (partial tag-match? tags))
                                    (subsume tags))]
          (if (empty? rest)
            (let [arg-tags (mapv u/maybe-class (:parameter-types ctor))
                  args (mapv (fn [arg tag] (assoc arg :tag tag)) args arg-tags)]
              (assoc (dissoc ast :maybe-class)
                :class the-class
                :args args))
            (assoc ast :class the-class))
          (throw (ex-info (str "no ctor found for ctor of class: " the-class " and give signature")
                          {:class the-class
                           :args  args}))))
      (throw (ex-info (str "class not found: " maybe-class)
                      {:class maybe-class})))
    ast))

(defn validate-call [class method args tag ast type]
  (let [argc (count args)
        f (if (= :static type) u/static-methods u/instance-methods)
        tags (mapv :tag args)]
    (if-let [matching-methods (seq (f class method argc))]
      (if-let [[m & rest :as matching] (subsume tags (filter (partial tag-match? tags) matching-methods))]
        (if (empty? rest)
          (let [ret-tag  (u/maybe-class (:return-type m))
                arg-tags (mapv u/maybe-class (:parameter-types m))
                args     (mapv (fn [arg tag] (assoc arg :tag tag)) args arg-tags)]
            (assoc ast
              :tag  ret-tag
              :args args))
          (if (reduce = (mapv (comp u/maybe-class :return-type) matching))
            (assoc ast :tag (:return-type m))
            ast))
        (throw (ex-info (str "No matching method: " method " for class: " class " and given signature")
                        {:method method
                         :class  class
                         :args   args})))
      (throw (ex-info (str "No matching method: " method " for class: " class " and arity: " argc)
                      {:method method
                       :class  class
                       :argc   argc})))))

(defmethod -validate :static-call
  [{:keys [class method args tag] :as ast}]
  (if tag
    ast
    (validate-call class method args tag ast :static)))

(defmethod -validate :instance-call
  [{:keys [class method args tag] :as ast}]
  (if (and class (not tag))
    (validate-call class method args tag ast :instance)
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
  (if-let [the-class (u/maybe-class tag)]
    the-class
    (throw (ex-info (str "class not found: " tag)
                    {:class tag}))))

(defmethod -validate :def
  [{:keys [var init] :as ast}]
  (when-let [tag (:tag init)]
    (alter-meta! var assoc :tag tag))
  (when-let [arglists (:arglists init)]
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
        (when (:arglists fn)
          (when-not (arglist-for-arity fn argc)
            (throw (ex-info (str "No matching arity found for function: " (:name fn))
                            {:arity (count args)
                             :fn    fn }))))
        (when (and (= :const (:op fn))
                   (not (instance? IFn (:form fn))))
          (throw (ex-info (str (class (:form fn)) " is not a function, but it's used as such")
                          {:form form})))
        ast))))

(defn validate-interfaces [interfaces]
  (when-not (every? #(.isInterface ^Class %) (disj interfaces Object))
    (throw (ex-info "only interfaces or Object can be implemented by deftype/reify"
                    {:interfaces interfaces}))))

(defmethod -validate :deftype
  [{:keys [name class-name fields interfaces] :as ast}]
  (validate-interfaces interfaces)
  (assoc ast :class-name (u/maybe-class class-name)))

(defmethod -validate :reify
  [{:keys [interfaces class-name] :as ast}]
  (validate-interfaces interfaces)
  (assoc ast :class-name (u/maybe-class class-name)))

(defmethod -validate :method
  [{:keys [name interfaces tag params fixed-arity] :as ast}]
  (if interfaces
    (let [interfaces (conj interfaces Object)
          methods (seq (filter identity
                               (mapcat #(u/instance-methods % name fixed-arity) interfaces)))]
      (if-let [[m & rest] (seq (filter (partial tag-match? (mapv :tag params)) methods))]
        (if (empty? rest)
          (let [ret-tag  (u/maybe-class (:return-type m))
                i-tag    (u/maybe-class (:declaring-class m))
                arg-tags (mapv u/maybe-class (:parameter-types m))
                args     (mapv (fn [arg tag] (assoc arg :tag tag)) params arg-tags)]
            (assoc (dissoc ast :interfaces)
              :interface i-tag
              :tag       ret-tag
              :args      args))
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
