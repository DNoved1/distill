Functionality
=============
* A 'don't delete' annotation for expressions to mark a computation as side-
  effecting.

Refactoring
===========
* Make a MonadGen class to allow Gen from QuickCheck to be used in monad
  transformers. There exists an implementation of such on hackage, but it
  fails to compile on my machine.
* Maybe make a ExprF type for simplifying some recursion through catamorphisms
  and traversals.
* Add type annotations to lambda parameters, so type inference is never
  needed, and so AnnotType can be removed, simplifying some aspects.