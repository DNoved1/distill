Functionality
=============
* A 'don't delete' annotation for expressions to mark a computation as side-
  effecting.

Refactoring
===========
* Make a MonadGen class to allow Gen from QuickCheck to be used in monad
  transformers. There exists an implementation of such on hackage, but it
  fails to compile on my machine.
