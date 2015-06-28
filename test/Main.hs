module Main where

import System.Exit
import Test.HUnit

import qualified Distill.Expr.Tests
import qualified Distill.Transform.Tests

main :: IO ()
main = do
    counts <- runTestTT $ TestList
        [ Distill.Expr.Tests.tests
        , Distill.Transform.Tests.tests
        ]
    if errors counts /= 0 || failures counts /= 0
        then exitFailure
        else exitSuccess
