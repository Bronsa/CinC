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

(defn try-best-match [tags methods]
  (let [exact-match? (fn [[x y]] (or (nil? y) (= (u/maybe-class x) (u/maybe-class y))))
        filter-methods (fn [methods f] (seq (filter #(every? f (mapv list (:parameter-types %) tags)) methods)))
        methods (or (filter-methods methods exact-match?) methods)]
    (or
     (seq
      (filter #(reduce (fn [subsumes? m]
                         (and subsumes?
                              (or (= m %)
                                  (and (= (:parameter-types %) (:parameter-types m))
                                       (let [dc1 (:declaring-class %)
                                             dc2 (:declaring-class m)]
                                         (and (u/subsumes? dc1 dc2)
                                              (or (not= dc1 dc2)
                                                  (and (some #{:synthetic :bridge :abstract} (:flags m))
                                                       (not-any? #{:synthetic :bridge :abstract} (:flags %)))))))
                                  (and (not= (:parameter-types %) (:parameter-types m))
                                       (every? (fn [[m1 m2 t]]
                                            (if (nil? t)
                                              (= Object (u/maybe-class m1))
                                              (u/subsumes? m1 m2)))
                                          (mapv list (:parameter-types %) (:parameter-types m) tags))))))
                       true methods) methods))
     methods)))

(defn validate-class
  [{:keys [maybe-class args] :as ast}]
  (if maybe-class
    (if-let [the-class (u/maybe-class maybe-class)]
      (assoc (dissoc ast :maybe-class) :class the-class)
      (throw (ex-info (str "class not found: " maybe-class)
                      {:class maybe-class})))
    ast))

(defmethod -validate :new
  [{:keys [validated?] :as ast}]
  (if validated?
    ast
    (let [{:keys [args ^Class class] :as ast} (validate-class ast)
          c-name (symbol (.getName class))
          argc (count args)
          tags (mapv :tag args)]
      (if-let [[ctor & rest] (->> (filter #(= (count (:parameter-types %)) argc)
                                          (u/members class c-name))
                                  (filter (partial tag-match? tags))
                                  (try-best-match tags))]
        (if (empty? rest)
          (let [arg-tags (mapv u/maybe-class (:parameter-types ctor))
                args (mapv (fn [arg tag] (assoc arg :args tag))
                           args arg-tags)]
            (assoc ast
              :args       args
              :validated? true))
          ast)
        (throw (ex-info (str "no ctor found for ctor of class: " class " and give signature")
                        {:class class
                         :args  args}))))))

(defn validate-call [class method args tag ast type]
  (let [argc (count args)
        f (if (= :static type) u/static-methods u/instance-methods)
        tags (mapv :tag args)]
    (if-let [matching-methods (seq (f class method argc))]
      (if-let [[m & rest :as matching] (try-best-match tags (filter (partial tag-match? tags) matching-methods))]
        (if (empty? rest)
          (let [ret-tag  (u/maybe-class (:return-type m))
                arg-tags (mapv u/maybe-class (:parameter-types m))
                args (mapv (fn [arg tag] (assoc arg :tag tag)) args arg-tags)]
            (assoc ast
              :validated? true
              :ret-tag    ret-tag
              :tag        (or tag ret-tag)
              :args       args))
          (if (apply = (mapv (comp u/maybe-class :return-type) matching))
            (let [ret-tag (u/maybe-class (:return-type m))]
              (assoc ast
                :ret-tag ret-tag
                :tag     (or tag ret-tag)))
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
  [{:keys [class method validated? tag args] :as ast}]
  (if validated?
    ast
    (validate-call class method args tag ast :static)))

(defmethod -validate :instance-call
  [{:keys [class validated? method tag args] :as ast}]
  (if (and class (not validated?))
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
    #_(alter-meta! var assoc :tag tag))
  (when-let [arglists (:arglists init)]
    (doseq [arglist arglists]
      (when-let [tag (:tag (meta arglist))]
        (validate-tag tag)))
    #_(alter-meta! var assoc :arg-lists arglists))
  ast)

(defmethod -validate :invoke
  [{:keys [args tag env fn form] :as ast}]
  (let [argc (count args)
        op (:op fn)]
    (if (and (= :const op)
             (= :keyword (:type fn)))
      (if (<= 1 argc 2)
        (assoc ast :op :keyword-invoke)
        (throw (ex-info (str "Cannot invoke keyword with " argc " arguments")
                        {:form form})))
      (if (and (= 2 argc)
               (= :var op)
               (= #'clojure.core/instance? (:var fn))
               (= :const (:op (first args)))
               (= :class (:type (first args))))
        {:op       :instance?
         :class    (:form (first args))
         :target   (second args)
         :form     form
         :env      env
         :tag      Boolean/TYPE
         :children [:target]}
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
          ast)))))

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
                               (mapcat #(u/instance-methods % name fixed-arity) interfaces)))
          tags (mapv :tag params)]
      (if-let [[m & rest :as matches]
               (try-best-match tags
                               (seq (filter (partial tag-match? tags) methods)))]
        (if (or (empty? rest)
                (and (apply = (mapv :return-type matches))
                     (apply = (mapv :parameter-types matches))))
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
                           :params     params
                           :matches    matches})))
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
