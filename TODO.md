Functionality
=============
* A 'don't delete' annotation for expressions to mark a computation as side-
  effecting.
* More sorts of types; of interest are:
  * ~~Iso-recursive~~
  * Lazy
  * ~~Product~~
  * ~~Coproduct~~
* Add max-depth to normalization so that type-checking doesn't result in the
  program hanging.
* Special case analysis for empty type (principle of explosion).

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
* Specialize pretty-printing expressions so that unique names are rendered
  without the number if no ambiguity would arise.
* Normalize to weak-head normal form for better error messages.
* Fix parser so that names starting with reserved words are allowed.
* Better type-checking error type (aka, not a string).
* inferType / checkType should return the elaborated term (without unknown
  type annotations).
* TODO, allow 1-products/sums - 1 products encoded as tuple of A and Unit,
  1 sums as singleton list.

Testing
=======
* More test-cases for 'reasonable' programs.
* Program coverage via hpc.
* Add product and coproduct expression generators.
