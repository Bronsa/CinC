# AST nodes description

**Every** node has the following self-explicatory keys:
* `:op`
* `:env` contains `:context`, one of `#{:statement :expr :return}`
* `:form`

Additionally, every node has some specific attributes:

## cinc.analyzer

The macroexpander of cinc.analyzer is platform agnostic so it doesn't try to transform foo/bar in (. foo bar) if foo is a class, as such, it produces a `:maybe-host-form` if foo is not a namespace

### :with-meta

This node wraps: `:const`, `:vector`, `:map`, `:set` if the form contains metadata

* `:meta` the analyzed expression of the metadata, context is set to `:expr`
* ``:expr`` the target analyzed expression, context is set to `:expr`


### :const

If the const comes from a quoted expression, the metadata is also quoted

* `:type` the result of (cinc.analyzer.utils/classify form), annotates the type of the constant (eg `:vector` if the constant is a vector)
* `:literal?` always set to true

### :vector

* `:items` a vector of analyzed expressions of the items of the vector, items context is set to `:expr`

### :map

* `:keys` a vector of analyzed expressions of the keys of the map, keys context is set to `:expr`
* `:vals` a vector of analyzed expressions of the vals of the map, vals context is set to `:expr`

### :set

* `:items` a set of analyzed expressions of the items of the set, items context is set to `:expr`

### :var

* `:name` the name of the var, a symbol
* `:ns` the namespace of the var, a symbol
* `:asssignable?` true if the var is dynamic
* `:var` the var object

### :local/:binding

* `:name` the name of the local symbol
* `:local` the local type: one of `#{:catch :let :letfn :loop :fn :arg :this :field}`

If `:local` is one of `#{:let :letfn :loop}`

* `:init` the analyzed expression of the local init

If `:local` is `:field`

* `:mutable` set to either `:unsynchronized-mutable`, `:volatile-mutable` or `false` depending on  the mutablity of the field

If `:op` is `:local`

* `:assignable?` true if the local is a mutable deftype field

### :maybe-host-form

* `:maybe-class` the class symbol of the (maybe) static field expression
* `:maybe-field` the field symbol of the (maybe) static field expression

### :maybe-class

* `:maybe-class` the symbol of the (maybe) class

### :do

* `:statements` a vector of analyzed expression of the statements in the do expression, statements context is set to `:statement`
* `:ret` the analyzed expression of the last form in the do expression

### :if

* `:test` the analyzed expression of the test part of the if, context is set to `:expr`
* `:then` the analyzed expression of the then part of the if

* `:else` the analyzed expression of the else part of the if, if present


### :new

* `:maybe-class` the symbol of the target of new
* `:args` a vector of analyzed expressions of the arguments to new, args context is set to `:expr`


### :the-var

Node of the (var the-var) special form

* `:var` the var object

### :set!

Can only happen when `:target` is `:assignable?`

* `:target` the analyzed expression of the set! target, context is set to `:expr`
* `:val` the analyzed expression of the set! value, context is set to `:expr`

### :try

* `:body` a `:do` node wrapping the body of the try expression, `:in-try` is set to true in `:env`
* `:catches` a vector of the `:catch` nodes of the try expression
* `:finally` a `:do` node wrapping the body of the finally expression, context is set to `:statement`

### :catch

* `:maybe-class` the exception type symbol
* `:local` the analyzed expression of the exception symbol
* `:body` a `:do` node wrapping the body of the catch expression

### :throw

* `:exception` the analyzed expression of the exception to be thrown, context is set to :expr

### :let/:loop/:letfn

* `:bindings` a vector of analyzed expression of the bindings
* `:body` a `:do` node of the analyzed expression of the body

If `:op` is `:loop`

* `:body` context is set to `:return`, `:loop-locals` is set to the `:bindings` vector in `:env`

### :recur

Can only happen when `:context` is set to `:return` and `:in-try` is not `true`

* `:exprs` an vector of analyzed expressions of new loop bindings, context is set to `:expr`

### :fn

* `:name` the name of the fn, if present
* `:variadic?` true if one of the fn-methods if variadic
* `:max-fixed-arity` the largest arity of non-variadic fn-methods
* `:methods` a vector of the `:fn-method` nodes of the function

### :fn-method

* `:variadic?` true if the method has a variadic arity
* `:fixed-arity` the number of fixed arguments of the methods
* `:params` a vector of the analyzed expressions of the parameters
* `:body` a `:do` node wrapping the body of the fn method

### :def

* `:name` the symbol of the var to be defined
* `:var` the var object to be defined

If present

* `:meta` the analyzed expression of the var's metadata

### :host-call

* `:target-expr ` the analyzed expr of the target of the host call
* `:method` the symbol of the method to be called
* `:args` a vector of the analyzed expressions of the args of the call, context is set to `:expr`

### :host-field

* `:target-expr ` the analyzed expr of the target of the host call
* `:field` the symbol of the field

### :host-interop

* `:target-expr ` the analyzed expr of the target of the host call
* `:m-or-f` the symbol of the field or no-arg method

### :invoke

* `:fn` the analyzed expression of the function to invoke
* `:args` a vector of the analyzed expressions of the args of the call, context is set to `:expr`
* `:meta` the analyzed expression of the invoke form metadata if present, context is set to `:expr`

## cinc.analyzer.jvm

The cinc.analyze.jvm macroexpander transforms foo/bar in a dot expression if foo is a class, as such, if a `:maybe-host-form` occurs it means that foo is neither a namespace or a class, and thus an error is thrown by the `validate` pass

### :monitor-enter/:monitor-exit

* `:target-expr` the analyzed expr of the monitor object, context is set to `expr`

### :import

* `maybe-class` the symbol of the (maybe) class to import

### :reify

* `:methods` a vector of the `:method` nodes of the reify expression
* `:interfaces` a set of the implemented interfaces by the reify expression, plus clojure.lang.IObj

### :deftype

* `:name` the name of the deftype, a symbol
* `:class-name` the class name of the deftype, a symbol
* `:fields` a vectopr of the analyzed fields of the deftype as bindings
* `:methods` a vector of the `:method` nodes of the deftype
* `:interfaces` a set of the implemented interfaces by the deftype

### :method

As `:fn-method` but:

* `:this` the analyzed expression of the this parameter

The this parameter is not part of the method parameters
