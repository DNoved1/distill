module Distill.UniqueName.Tests
    ( arbitraryUniqueName
    ) where

import Control.Monad
import Test.QuickCheck

import Distill.UniqueName

-- | Generate an arbitrary upto three-letter unique name.
arbitraryUniqueName :: Int -> Gen (Int, UniqueName)
arbitraryUniqueName s = do
    len <- choose (1,3)
    name <- replicateM len (elements (['a'..'z'] ++ ['A'..'Z']))
    return (succ s, UniqueName name s)
