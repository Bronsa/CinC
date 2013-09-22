# Emission phase description

The emission phase is actually split in two separate phases: emit and -compile/transform.

`-emit` takes an ast and returns a vector containing a data rapresentation of the bytecode to be emitted.

The `-compile` phase takes an AST describing a class to be generated that will contain in its methods the bytecode-vector returned by `-emit` and `transform` will interpret it.

An example of how all this glues together can be seen in [compiler](doc/compiler.md)
