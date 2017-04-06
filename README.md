# Coq contains any provably total mu-recursive function

This development is a proof in [Coq](http://coq.inria.fr) 
that any [mu-recursive](https://en.wikipedia.org/wiki/%CE%9C-recursive_function)
function which defines a total predicate can be represented
by a Coq term. It was developped under Coq 8.5pl3 but
should also compile with Coq 8.6. To compile, type

> make all

This code was developped by [Dominique Larchey-Wendling](http://www.loria.fr/~larchey)
and is distributed under the CeCILL Free Software License Agreement. It is complementary
to the paper [*Typing Total Recursive Functions in Coq*](http://www.loria.fr/~larchey) 
which was submitted to ITP'2017.

