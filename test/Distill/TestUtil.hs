{-# LANGUAGE LambdaCase #-}

module Distill.TestUtil where

import Data.Char
import Test.HUnit
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen
import Text.Parsec
import Text.Parsec.String

import Distill.SExpr

-- | Convert a QuickCheck Result into a HUnit Assertion.
resultToAssertion :: QC.Result -> Assertion
resultToAssertion = \case
    QC.Failure {QC.reason = err} -> assertFailure err
    _                            -> return ()

-- | Make a generated structure smaller.
smaller :: Gen a -> Gen a
smaller = scale (`div` 2)

-- | Parse the entirety of a file as an sexpr.
parseSExprFile :: Parser SExpr
parseSExprFile = parseSExpr allowedChars <* eof
  where
    allowedChars c = isAlphaNum c || c `elem` ":*"
