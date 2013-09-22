# CinC

CinC is an experimental Clojure analyzer and compiler implemented in pure Clojure.

# Features

CinC currently contains both an analyzer composed of multiple passes and an emitter.

Docs on how the compile process works are in [compiler](doc/compiler.md)

# Analyzer

The jvm analyzer (`cinc.analyzer.jvm/analyze`) returns an AST similar to the one returned by the clojurescript analyzer or by jvm.tools.analyzer.
On top of the simple AST, multiple passes are run in order to transform/annotate the ast with information needed for the jvm bytecode emission.

The basic AST nodes are documented in [analyzer](doc/analyzer.md) while the passes are documented in [passes](doc/passes.md).

Note that some passes remove or add new nodes to the AST.

# Emitter

The bytecode emitter (`cinc.compiler.jvm.bytecode/eval`) takes in an expression, gets the AST from its analysis and emits the corresponing bytecode.

How this process works is documented in [emitter](doc/emitter.md)

# What's not working

Currently primitive types should be considered not working, this means that for example `defrecord` doesn't currently compile since it implements primitive-returning methods.

Primitive support will come soon.
