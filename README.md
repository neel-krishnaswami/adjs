A Higher-Order FRP compiler
===========================

This is a repository for a small compiler for the higher-order FRP work
that I and my collaborators have developed, primarily in the following papers:

* [*Higher-Order Reactive Programming without Spacetime Leaks*](http://www.cs.bham.ac.uk/~krishnan/simple-frp.pdf)

  This gives the main implementation strategy. 

* [*A Semantic Model for Graphical User Interfaces*](http://www.cs.bham.ac.uk/~krishnan/icfp11-krishnaswami-benton.pdf)

  This explains the use of linear types. 

* [*Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism*](http://www.cs.bham.ac.uk/~krishnan/bidir.pdf)

  This explains how type inference works. 

To build, you need a recent-ish version of Ocaml. Go into the adjs/ directory and run make. 

For convenience, I used Firefox's let-binding extensions to
Javascript, so you'll need to use it to run programs.