{-# LANGUAGE LambdaCase #-}

module Distill.TestUtil where

import Data.Char
import Test.HUnit hiding (Testable)
import Test.QuickCheck hiding (Result)
import qualified Test.QuickCheck as QC
import Text.Parsec
import Text.Parsec.String

import Distill.SExpr

-- | Convert a QuickCheck Result into a HUnit Assertion.
resultToAssertion :: QC.Result -> Assertion
resultToAssertion = \case
    QC.Failure {QC.reason = err} -> assertFailure err
    _                            -> return ()

-- | Convert a QuickCheck property into a HUnit test case.
quickCheckToHUnit :: Testable prop => prop -> Test
quickCheckToHUnit qcTest = TestCase $
    quickCheckWithResult (stdArgs {chatty = False}) qcTest >>= resultToAssertion

-- | Make a generated structure smaller.
smaller :: Gen a -> Gen a
smaller = scale (`div` 2)

-- | Parse the entirety of a file as an sexpr.
parseSExprFile :: Parser SExpr
parseSExprFile = parseSExpr allowedChars <* eof
  where
    allowedChars c = isAlphaNum c || c `elem` ":*"

-- | A wrapper around 'assertFailure' which is of any type.
assertFalse :: String -> IO a
assertFalse msg = assertFailure msg >> undefined
