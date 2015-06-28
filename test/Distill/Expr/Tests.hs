module Distill.Expr.Tests
    ( tests
    , Expr
    , Type
    , Decl
    , UniqueVar(..)
    , WellTypedExpr(..)
    , nextAvailableUnique
    , arbitraryUniqueVar
    , arbitraryExpr
    , arbitraryType
    ) where

import Control.Monad.Reader
import System.IO
import Test.HUnit
import Test.QuickCheck (Arbitrary(..), quickCheckWithResult, stdArgs, chatty)
import Test.QuickCheck.Gen
import Test.QuickCheck.Property
import Text.Parsec (parse)

import Distill.TestUtil
import Distill.Expr

tests :: Test
tests = TestLabel "Distill.Expr.Tests" $ TestList
    [ TestLabel "prop_exprsWellTyped" $ TestCase $
        resultToAssertion =<< quickCheckWithResult (stdArgs {chatty = False})
            prop_exprsWellTyped
    , TestLabel "simpleTest" $ TestCase $ simpleTest
    ]

type Expr = Expr' UniqueVar
type Type = Type' UniqueVar
type Decl = Decl' UniqueVar

data UniqueVar = UniqueVar String Int
  deriving (Eq, Show, Read)

newtype WellTypedExpr = WellTypedExpr Expr
  deriving (Show, Read)

instance Arbitrary WellTypedExpr where
    arbitrary = do
        (_, m, _) <- arbitraryExpr [] 0
        return (WellTypedExpr m)

-- | Determine the next unused integer available for forming 'UniqueVar's.
nextAvailableUnique :: Expr -> Int
nextAvailableUnique = foldVars f 0
  where
    f acc (UniqueVar _ num) = max acc (succ num)

-- | Generate an arbitrary upto three-letter unique variable.
arbitraryUniqueVar :: Int -> Gen (Int, UniqueVar)
arbitraryUniqueVar s = do
    len <- choose (1,3)
    name <- replicateM len (elements (['a'..'z'] ++ ['A'..'Z']))
    return (succ s, UniqueVar name s)

-- | Generate an arbitrary well-typed expression.
arbitraryExpr :: [(UniqueVar, Type)] -> Int -> Gen (Int, Expr, Type)
arbitraryExpr bound s = sized $ \size -> do
    let atomic = size <= 1
    oneof . concat $
        [ [arbitraryVar bound s | atomic && not (null bound)]
        , [arbitraryType' bound s | True]
        , [arbitraryLambda bound s | not atomic]
        , [arbitraryApply bound s | not atomic]
        ]
  where
    arbitraryVar bound s = do
        (x, t) <- elements bound
        return (s, Var x, t)
    arbitraryType' bound s = do
        (s, t) <- smaller $ arbitraryType bound s
        return (s, t, Star)
    arbitraryLambda bound s = do
        (s, x) <- arbitraryUniqueVar s
        (s, t) <- smaller $ arbitraryType bound s
        (s, m, t') <- smaller $ arbitraryExpr ((x, t):bound) s
        return (s, Lambda x t m, Forall x t t')
    arbitraryApply bound s = do
        (s, x) <- arbitraryUniqueVar s
        (s, n, t) <- smaller $ arbitraryExpr bound s
        (s, body, t') <- smaller $ arbitraryExpr ((x, t):bound) s
        let m = Lambda x t body
        return (s, Apply m n, subst x n t')

-- | Generate an arbitrary well-formed type.
arbitraryType :: [(UniqueVar, Type)] -> Int -> Gen (Int, Type)
arbitraryType bound s = sized $ \size -> do
    let atomic = size <= 1
    oneof . concat $
        [ [arbitraryStar bound s | atomic]
        , [arbitraryForall bound s | not atomic]
        ]
  where
    arbitraryStar bound s = return (s, Star)
    arbitraryForall bound s = do
        (s, x) <- arbitraryUniqueVar s
        (s, t) <- smaller $ arbitraryType bound s
        (s, t') <- smaller $ arbitraryType ((x, t):bound) s
        return (s, Forall x t t')

-- | The property that generated expressions are well-typed.
prop_exprsWellTyped :: WellTypedExpr -> Result
prop_exprsWellTyped (WellTypedExpr expr) =
    --let renumbered = renumber UniqueVar 0 [] expr in
    case runTCM (inferType expr) [] [] of
        Left err -> failed {reason = err}
        Right _  -> succeeded

-- | A simple test on parsing and type-checking a file.
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
