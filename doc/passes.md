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
user=> (analyze ''[1 {:foo pi}] {:context :expr})
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
* `analyze-host-expr` use reflection to tag and specialize host forms.
* `validate` use reflection to validate and tag host forms
* `box` marks nodes to be boxed with `:box` true (still **incomplete**)
