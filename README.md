(Note: repository is now available on both github at https://github.com/remleduff/CinC and bitbucket at https://bitbucket.org/remleduff/cinc)

Clojure in Clojure (pre-pre-pre-alpha)
======================================

For now the only dependencies are asm-4.0 and clojure-1.3

To get started:
---------------

Start your repl of choice (ie, lein repl)

=>(use 'clojure.java.compiler)

user=> (pprint (clojure.analyzer/analyze '(+ 1 2)))  
> {...ast is printed...}

user=> (pprint (process-frames (clojure.analyzer/analyze '(+ 1 2))))  
>{...ast is printed..., additional information is attached to nodes in the AST where classes are generated for use in emitting bytecode}

user=> (eval '(+ 1 2))  
>3

user=> (eval '(+ 1 2) :trace true)  
>... textual representation of the class is printed

user=> (eval '(+ 1 2) :trace true :check true)  
>... textual representation of the class is printed and additional verification is done by ASMStart typing in the blue box...

For some reason, "lein test" doesn't seem to work currently. Until I figure that out, do:

(require 'test.clojure.java.compiler)
(in-ns 'test.clojure.java.compiler)
(test-eval)

