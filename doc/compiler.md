# The CinC compilation process

This will desceribe all the phases involved in interpreting a simple clojure expression, `(let [a 1] (println a))`

# Reading

We need to transform the expression from a string to a clojure data-structure, we'll use `read-string`

```clojure
user=> (read-string "(let [a 1] (println a))")
(let [a 1] (println a))
```

# Evaluating

After the form is read, it's passed to the `eval` function to be executed; this is where the magic begins.

Let's look at the `cinc.compiler.jvm.bytecode/eval` function:

```clojure
(defn eval
  ([form] (eval form false))
  ([form debug?]
     (let [r (e/emit (a/analyze `(^:once fn* [] ~form) {:context :expr})
                     {:debug? debug?
                      :class-loader (clojure.lang.RT/makeClassLoader)})
           {:keys [class]} (meta r)]
       ((.newInstance ^Class class)))))
```

Let's see what happens to `form` (our expr)

# Wrapping in a fn

Since most jvm passes annotate their results in a `:fn` node, we need to wrap the top-level form in a fn.

```clojure
user=>(let [expr '(let [a 1] (println a))] `(^:once fn* [] ~expr))
(fn* [] (let [a 1] (println a)))
```

# Analyzing

The resulting expression is then analyzed to transform it in an AST.
Since `cinc.analyzer.jvm/analyze` involves multiple pass over the ast, we'll see how every pass modifies the expression.

The `analyze` function:
``` clojure
(defn analyze
  [form env]
  (binding [ana/macroexpand-1 macroexpand-1]
    (-> (-analyze form env)
      uniquify-locals
      (walk (fn [ast]
              (-> ast
                warn-earmuff
                annotate-branch
                source-info
                elide-meta))
            (fn analyze
              [ast]
              ((comp (validate-loop-locals analyze)
                  (cycling infer-tag analyze-host-expr validate)
                  infer-constant-tag
                  constant-lift) ast)))
      (prewalk (comp (collect :constants
                           :callsites
                           :closed-overs)
                  box))
      clear-locals)))
```

First, we run the analyzer over the form, the default env is `{:context :expr}`

## -analyze

The basic AST that results from the `-analyze` pass is (a bit cleaned-up):
```clojure
{:children [:methods],
 :op :fn,
 :env {:context :expr},
 :form (fn* [] (let [a 1] (println a))),
 :name nil,
 :variadic? false,
 :max-fixed-arity 0,
 :methods
 [{:op :fn-method,
   :form ([] (let [a 1] (println a))),
   :env {:once true, :context :expr},
   :variadic? false,
   :params [],
   :fixed-arity 0,
   :body
   {:op :do,
    :env {:once true, :context :return, :loop-locals 0},
    :form (do (let [a 1] (println a))),
    :statements [],
    :ret
    {:op :let,
     :form (let* [a 1] (println a)),
     :env {:once true, :context :return, :loop-locals 0},
     :body
     {:op :do,
      :env {:once true, :context :return, :loop-locals 0},
      :form (do (println a)),
      :statements [],
      :ret
      {:children [:args :fn],
       :meta {:line 1, :column 203},
       :op :invoke,
       :form (println a),
       :env {:once true, :context :return, :loop-locals 0},
       :fn
       {:form println,
        :env {:once true, :context :expr, :loop-locals 0},
        :op :var,
        :name println,
        :ns clojure.core,
        :assignable? false,
        :var #'clojure.core/println},
       :args
       [{:assignable? false,
         :op :local,
         :env {:once true, :context :expr, :loop-locals 0},
         :name a,
         :init
         {:op :const,
          :env {:once true, :context :expr, :loop-locals 0},
          :type :number,
          :literal? true,
          :form 1},
         :form a,
         :local :let,
         :children [:init]}]},
      :children [:statements :ret]},
     :bindings
     [{:op :binding,
       :env {:once true, :context :expr, :loop-locals 0},
       :name a,
       :init
       {:op :const,
        :env {:once true, :context :expr, :loop-locals 0},
        :type :number,
        :literal? true,
        :form 1},
       :form a,
       :local :let,
       :children [:init]}],
     :children [:bindings :body]},
    :children [:statements :ret]},
   :children [:params :body]}]}
```

## passes

For a description of what all the passes do on the AST see: [passes](doc/passes.md).

After all the passes have run, the AST now looks like

```clojure
{:arglists [[]],
 :children [:methods],
 :form (fn* [] (let [a 1] (println a))),
 :protocol-callsites #{},
 :op :fn,
 :name nil,
 :keyword-callsites #{},
 :max-fixed-arity 0,
 :methods
 [{:children [:params :body],
   :fixed-arity 0,
   :form ([] (let [a 1] (println a))),
   :op :fn-method,
   :variadic? false,
   :env {:once true, :context :expr},
   :params [],
   :path? true,
   :arglist [],
   :body
   {:box true,
    :op :do,
    :env {:once true, :context :return},
    :form (do (let [a 1] (println a))),
    :statements [],
    :ret
    {:box true,
     :op :let,
     :form (let* [a 1] (println a)),
     :env
     {:line 1,
      :column 26,
      :once true,
      :context :return},
     :body
     {:box true,
      :op :do,
      :env {:once true, :context :return},
      :form (do (println a)),
      :statements [],
      :ret
      {:box true,
       :children [:args :fn],
       :meta {:line 1, :column 37},
       :op :invoke,
       :form (println a),
       :env
       {:line 1,
        :column 37,
        :once true,
        :context :return},
       :fn
       {:assignable? false,
        :form println,
        :ns clojure.core,
        :op :var,
        :name println,
        :env {:once true, :context :expr},
        :id 0,
        :var #'clojure.core/println,
        :tag clojure.lang.Var},
       :args
       [{:children [],
         :assignable? false,
         :form a,
         :op :local,
         :name a__#0,
         :local :let,
         :env {:once true, :context :expr},
         :tag java.lang.Long,
         :to-clear? true}]},
      :children [:statements :ret]},
     :bindings
     [{:tag java.lang.Long,
       :op :binding,
       :env {:once true, :context :expr},
       :name a__#0,
       :init
       {:id {:id 1, :tag java.lang.Long, :val 1, :type :number},
        :tag java.lang.Long,
        :op :const,
        :env {:once true, :context :expr},
        :type :number,
        :literal? true,
        :form 1},
       :form a,
       :local :let,
       :children [:init]}],
     :children [:bindings :body]},
    :children [:statements :ret]}}],
 :variadic? false,
 :env {:line 1, :column 11, :context :expr},
 :constants
 {1 {:id 1, :tag java.lang.Long, :val 1, :type :number},
  #'clojure.core/println
  {:id 0,
   :tag clojure.lang.Var,
   :val #'clojure.core/println,
   :type :var}},
 :tag clojure.lang.AFunction,
 :closed-overs {}}
```
We can see that the AST has been annotated with tag info and that every Var/constant has now an id.

The `:fn` node now contains a map `:constants` of constant => constant-node
```clojure
:constants {1 {:id 1, :tag java.lang.Long, :val 1, :type :number},
            #'clojure.core/println {:id 0, :tag clojure.lang.Var, :val #'clojure.core/println, :type :var}}
```

# Emission

A new dynamic-classloader is then created, and passed to the `emit` function along with the AST

```clojure
(e/emit (a/analyze '(fn* [] (let [a 1] (println a))) {:context :expr})
        {:class-loader (clojure.lang.RT/makeClassLoader)})
```

The `emit` function will then walk every node calling `:emit` on it, resulting in the following AST:

``` clojure
{:super clojure/lang/AFunction,
 :op :class,
 :name cinc/compiler/jvm/bytecode$fn__12845,
 :interfaces nil,
 :methods
 [{:op :method,
   :attr #{:static :public},
   :method [[:<clinit>] :void],
   :code
   [[:start-method]
    [:push 1]
    [:invoke-static [:java.lang.Long/valueOf :long] :java.lang.Long]
    [:check-cast java.lang.Long]
    [:put-static cinc.compiler.jvm.bytecode$fn__12845 const__1 java.lang.Long]
    [:push clojure.core]
    [:push println]
    [:invoke-static [:clojure.lang.RT/var :java.lang.String :java.lang.String] :clojure.lang.Var]
    [:check-cast clojure.lang.Var]
    [:put-static cinc.compiler.jvm.bytecode$fn__12845 const__0 clojure.lang.Var]
    [:return-value]
    [:end-method]]}
  {:op :method,
   :attr #{:public},
   :method [[:<init>] :void],
   :code
   [[:start-method]
    [:label :label__12846]
    [:load-this]
    [:invoke-constructor [:clojure.lang.AFunction/<init>] :void]
    [:label :label__12847]
    [:return-value]
    [:end-method]]}
  {:op :method,
   :attr #{:public},
   :method [[:invoke] :java.lang.Object],
   :code
   [[:start-method]
    [:local-variable :this :clojure.lang.AFunction nil :label__12848 :label__12849 :this]
    [:mark :label__12848]
    [:get-static cinc.compiler.jvm.bytecode$fn__12845 const__1 java.lang.Long]
    [:var-insn :java.lang.Long/ISTORE a__#0]
    [:mark :label__12852]
    [:mark :label__12851]
    [:get-static cinc.compiler.jvm.bytecode$fn__12845 const__0 clojure.lang.Var]
    [:invoke-virtual [:clojure.lang.Var/getRawRoot] :java.lang.Object]
    [:check-cast :clojure.lang.IFn]
    [:var-insn :java.lang.Long/ILOAD a__#0]
    [:insn :ACONST_NULL]
    [:var-insn :java.lang.Long/ISTORE a__#0]
    [:invoke-interface [:clojure.lang.IFn/invoke :java.lang.Object] :java.lang.Object]
    [:mark :label__12850]
    [:local-variable a__#0 java.lang.Long nil :label__12852 :label__12850  a__#0]
    [:mark :label__12849]
    [:return-value]
    [:end-method]]}],
 :fields
 [{:op :field,
   :attr #{:static :public :final},
   :name const__1,
   :tag java.lang.Long}
  {:op :field,
   :attr #{:static :public :final},
   :name const__0,
   :tag clojure.lang.Var}],
 :attr #{:super :public :final},
 :annotations nil}
```

This AST will then be `-compile`d inside `-emit :fn`, and the resulting compiled bytecode will be instantiated in a new class in the dynamic-class-loader

```clojure
(.defineClass ^clojure.lang.DynamicClassLoader class-loader class-name bc nil)
```

The `eval` function will then create a new instance of this class (that is the wrapping fn) and invoke it to evaluate the form.

```clojure
((.newInstance class))
```
