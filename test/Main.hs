module Main where

import Data.Char
import System.Exit
import System.IO
import Test.HUnit
import Text.Parsec
import Text.Parsec.String

import Distill.Expr
import Distill.SExpr

parseSExprFile :: Parser SExpr
parseSExprFile = parseSExpr allowedChars <* eof
  where
    allowedChars c = isAlphaNum c || c `elem` ":*"

simpleTest :: Assertion
simpleTest = do
    let fileName = "./test/simple.distill"
    withFile fileName ReadMode $ \file -> do
        contents <- hGetContents file
        let parsed = parse parseSExprFile fileName contents
        sexpr <- case parsed of
            Left err -> assertFailure (show err) >> undefined
            Right sexpr -> return sexpr
        expr <- case fromSExpr sexpr of
            Left err -> assertFailure err >> undefined
            Right expr -> return expr
        case runTCM (inferType expr) [] [] of
            Left err -> assertFailure err >> undefined
            Right type_ -> return ()

main :: IO ()
main = do
    counts <- runTestTT $ TestList
        [ TestLabel "simple" (TestCase simpleTest)
        ]
    if errors counts /= 0 || failures counts /= 0
        then exitFailure
        else exitSuccess
