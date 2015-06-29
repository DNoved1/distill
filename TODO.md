Functionality
=============
* A 'don't delete' annotation for expressions to mark a computation as side-
  effecting.

Refactoring
===========
* Make a MonadGen class to allow Gen from QuickCheck to be used in monad
  transformers. There exists an implementation of such on hackage, but it
  fails to compile on my machine.
* Since the distill intermediate language is strict, we need to check for
  dependencies in non-lazy, non-lambda expressions in letrec and in declaration
  lists. Eg, 'letrec x = 1:x in x' is not allowed, unless x is lazy.
* When normalizing, we need to check that beta-reductions are type-correct.
* ~~Make forall use same syntactic sugar for multiple parameters as lambdas
  when parsing and pretty-printing~~; create a similar style for lets/letrecs.
* It would be good to print out the line(s) in which the error occurs, along
  with a caret (^) and span (~) to make error identification easier.
