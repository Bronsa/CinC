# Passes description

Passes use the walking mechanism to be applied to the whole AST.
Most passes don't do any walking by default and can thus be combined with other passes in a single walk, other passes like `uniquify` and `jvm.clear-locals` wrap a walker themselves and thus need to be in a separate walk.

Some passes depend on other passes, some needs explicitely to be used as prewalks or postwalks to work correctly and some groups of passes need to be run an indeterminate number of times in order to work completely, a correct way to use all the passes in the most efficient way is as done by `analyze.jvm/analyze`:

```clojure
(-> (-analyze form env)
      uniquify-locals
      (walk (fn [ast]
              (-> ast
                remove-locals
                warn-earmuff
                annotate-branch
                source-info
                elide-meta))
            (comp (cycling infer-tag analyze-host-expr validate box)
               infer-constant-tag
               constant-lift))
      (prewalk (collect :constants
                        :callsites
                        :closed-overs
                        :vars))
      clear-locals)
```

### constant-lift

This pass doesn't wrap any walking and doesn't depend on any other pass but **must** be run in a postwalk.

This pass transforms `:map`, `:vector`, `:set` nodes whose items are *all* constants in a `const` node
e.g
```clojure
user=> (def ^:const pi 3.14)
; #'user/pi
user=> (analyze '[1 {:foo pi}] {:context :expr})
; {:op :vector, :env {}, :items [{:op :const, :env {:context :expr}, :type :number, :literal? true, :form 1} {:op :map, :env {:context :expr}, :keys [{:op :const, :env {:context :expr}, :type :keyword, :literal? true, :form :foo}], :vals [{:form pi, :env {:context :expr}, :op :var, :name pi, :ns user, :assignable? false, :var #'user/pi}], :form {:foo pi}}], :form [1 {:foo pi}]}
user=> (postwalk *1 constant-lift)
; {:op :const, :env {}, :type :vector, :literal? true, :form [1 {:foo 3.14}]}
```

### remove-locals

This pass doesn't wrap any walking, doesn't depend on any other pass and doesn't need any specific walking.

This pass simply dissoc `:locals` from the `:env` of every node since it is no longer needed and would be invalidated by other passes.
If some pass will ever need to know the locals of the environment of a specific node, it would need to rebuild the `:locals` node afresh and dissoc it after the pass.

### warn-earmuff

This pass doesn't wrap any walking, doesn't depend on any other pass and doesn't need any specific walking.

This pass emits a warning if a var is defined with earmuffs and it's not marked as dynamic.

### elide-meta

This pass doesn't wrap any walking, doesn't depend on any other pass and doesn't need any specific walking.

This pass removes from nodes with explicit `:meta` fields (`:with-meta` and `:def`) the meadata keys specified by the `:elide-emta` set in `clojure.core/*compiler-options*`, it should be noted that this variable is set only at compile-time.

### source-info

This pass doesn't wrap any walking, doesn't depend on any other pass and doesn't need any specific walking.

This pass adds explicit `:file`, `:line` and `:column` info on the node environment, when such info is available.

It should be noted that this pass should be run **before** elide-meta since that pass could elide any of `:file`, `:line` or `:column`

### uniquify-locals

This pass wraps a walking and as such cannot be combined with other passes, this pass should be run **before** any pass that works on locals (such as `clear-locals`) and invalidates `:locals` in env.

This pass uniquifies all locals so that a local name is never used twice in the same analysis unit e.g.

```clojure
user=> (-> (-analyze '(let [x 1 x x] x) {:context :expr}) (prewalk remove-locals))
; {:op :let, :form (let* [x 1 x x] x), :env {:context :expr}, :body {:op :do, :env {:context :expr}, :form (do x), :statements [], :ret {:assignable? false, :op :local, :env {:context :expr}, :name x, :init {:assignable? false, :op :local, :env {:context :expr}, :name x, :init {:op :const, :env {:context :expr}, :type :number, :literal? true, :form 1}, :form x, :local :let}, :form x, :local :let}}, :bindings [{:op :binding, :env {:context :expr}, :name x, :init {:op :const, :env {:context :expr}, :type :number, :literal? true, :form 1}, :form x, :local :let} {:op :binding, :env {:context :expr}, :name x, :init {:assignable? false, :op :local, :env {:context :expr}, :name x, :init {:op :const, :env {:context :expr}, :type :number, :literal? true, :form 1}, :form x, :local :let}, :form x, :local :let}]}
user=> (uniquify-locals *1)
; {:op :let, :form (let* [x 1 x x] x), :env {:context :expr}, :body {:op :do, :env {:context :expr}, :form (do x), :statements [], :ret {:assignable? false, :op :local, :env {:context :expr}, :name x__#1, :init {:assignable? false, :op :local, :env {:context :expr}, :name x__#0, :init {:op :const, :env {:context :expr}, :type :number, :literal? true, :form 1}, :form x, :local :let}, :form x, :local :let}}, :bindings [{:op :binding, :env {:context :expr}, :name x__#0, :init {:op :const, :env {:context :expr}, :type :number, :literal? true, :form 1}, :form x, :local :let} {:op :binding, :env {:context :expr}, :name x__#1, :init {:assignable? false, :op :local, :env {:context :expr}, :name x__#0, :init {:op :const, :env {:context :expr}, :type :number, :literal? true, :form 1}, :form x, :local :let}, :form x, :local :let}]}
```

The first `x` is transformed in `x__#0`, the second in `x__#1`, this avoids local shadowing.

### annotate-branch

This pass doesn't wrap any walking, doesn't depend on any other pass and doesn't need any specific walking; it **must** be run **before** `clear-locals` in order for it to work.

This pass adds annotation about what nodes are branches or paths, and which nodes can be cleared and which cannot.

### clear-locals

This pass wraps a walking and as such cannot be combined with other passes, this pass depends on **annotate-branch** and **uniquify-locals** in order to run correctly.

This pass annotates where and which locals should be cleared, and which should not.

It must be noted that this pass marks as `:to-clear?` locals that are closed over a non `:once` fn too.
The emitter should then not clear every local marked `:to-clear` that is closed over by a non `:once` fn,  making the `collect` pass a **de-facto dependency**.

### collect

This pass doesn't wrap any walking but depends on `uniquify-locals` and **must** be run in a prewalk; additionally, if `constant-lift` is run, this pass must be run **after** it, in a different walk.

This pass adds to `:fn`, `:deftype` and `:reify` nodes info about:
* constants
* vars
* keyword and protocol callsites
* closed overs

It should be noted that `collect` takes as arguments the keywords regarding the infos to be collected (e.g `(collect :constants :vars)` to collect only constants and vars) and returns the actual pass.

### infer-constant-tag

This pass doesn't wrap any walking, doesn't depend on any other pass and doesn't need any specific walking, it should be notet that if `constant-lift` is run, this pass must run **after** it.

This pass adds `:tag` info to every `:const` node.

### infer-tag/analyze-host-expr/validate/box

Those pass don't wrap any walking, but **must** be run in a cycling postwalk in this order and **depend** on `infer-constant-tag`.

* `infer-tag` infers the tag of non constant expressions
* `analyze-host-expr` use reflection to tag and specialize host forms
* `validate` use reflection to validate and tag host forms
* `box` marks nodes to be boxed with `:box` true (still **incomplete**)

#### infer-tag

This pass adds `:tag` all the AST nodes that don't have one and it can be infered.

It also adds `:arglist`, a vector with tagged args to `:fn-method` that get propagated in `:arglists`, a vector of `:arglist` in the `:fn` node; this gets propagated to the locals that refer to the function.

Note that the tag is not validated and can be either a Class or still a Symbol.

#### analyze-host-expr

After this pass, `:host-call` and `:host-field` nodes are no longer present, the pass tries to classify the host expr in `#{:static-field :static-call :instance-call :instance-field}`, if it cannot infer any of those, it will return a `:host-interop` node.

Follows a description of the newly introduced nodes, it should be noted that all those nodes contains a `:tag` field so no `infer-tag` is needed

##### :static-field

* `:assignable?` true if the field is not final
* `:class` the class to which the field belongs
* `:field` the name of the field, a symbol

##### :static-call

* `:class` the class to which the method belongs
* `:method` the name of the methods, a symbol

##### :instance-field

* `:instance` the analyzed expression of the instance
* `:assignable?` true if the field is not final
* `:class` the class to which the field belongs
* `:field` the name of the field, a symbol

##### :instance-call

* `:instance` the analyzed expression of the instance
* `:assignable?` true if the field is not final
* `:class` the class to which the method belongs
* `:method` the name of the methods, a symbol

#### validate

The tags are validated to a Class, if no class can be resolved for the tag, an exception is thrown.
This pass does diffent kind of validation depending on the node:

##### :maybe-class

If the symbol can be resolved to a class, the node gets transformed to a `:const` node with `:type :class` and `:tag Class`, other an exception is thrown.

##### :maybe-host-form

If this node is hit, it means that the macroexpander found out that in `foo/bar` where foo was neither a Class nor a Namespace, so an exception is thrown.

##### :catch/import

The class tries to get resolved, if it can, `:maybe-class` gets renamed to `:class` and bound to the resolved class, otherwise an exception is thrown.

##### :set!

If target is not `:assignable?`, an exception is thrown.

If the target however is a `:host-interop` exception, no exception is thrown since it could be classified later.

##### :new/:static-call/:instance-call

As per `:catch`, `:maybe-class` gets resolved into a `:class` or an exception is thrown.
Additionally reflection is used to check for valid constructor arity.

If no constructor/method with the given arity is found, an exception is thrown.

If more constructors/methods with the given arity are found and the tags on the arguments are sufficient to pick one of those, `:args` are tagged with the exact types of the constructor/method and the node is tagged with the return type, otherwise only the validated node is returned.

##### :deftype/:reify

If one of the classes in `:interface` is not either an interface or `Object`, an exception is thrown

##### :def

`:tag` and `:arg-lists` are added to the var metadata

##### :invoke

If the `:fn` is a keyword, `:op` gets changed to `:keyword-invoke`, if more than 2 args are passed, an exception is thrown.

If the invoked function has `:arglists` info and no matching arity is found, an exception is thrown.

If the invoked function is a `:const` and not an `IFn`, an exception is thrown.

##### :method

If no matching method can be found on the `:interfaces`, an exception is thrown.

If more than one method can be found an no one can be preferred over the others, an exception is thrown.

Otherwise, the node gets tagged with the returning class of the method, `:args` get tagged with their specific type and `:interface` is addedd to the node to denote the interface of the method.
