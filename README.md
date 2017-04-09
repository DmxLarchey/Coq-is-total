# Coq contains any provably total mu-recursive function

This development is a proof in [Coq](http://coq.inria.fr) 
that any [mu-recursive](https://en.wikipedia.org/wiki/%CE%9C-recursive_function)
function which defines a total predicate can be represented
by a Coq term. It was developped under Coq 8.5pl3 but
should also compile with Coq 8.6. This code will **NOT compile**
under Coq 8.4 (see below). 

To compile, type

> make all

This code was developped by [Dominique Larchey-Wendling](http://www.loria.fr/~larchey)
and is distributed under the CeCILL Free Software License Agreement. It is complementary
to the paper [*Typing Total Recursive Functions in Coq*](http://www.loria.fr/~larchey) 
which was submitted to ITP'2017.

Starting from Coq 8.5, the syntax of pattern matching has changed. In particular,
the constructor exist (for type sig X) now has 3 arguments instead of two. It is
not possible to write code which is compatible for both Coq 8.4 and Coq 8.5.
