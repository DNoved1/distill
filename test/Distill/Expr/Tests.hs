module Distill.Expr.Tests
    ( tests
    , WellTypedExpr(..)
    , arbitraryExpr
    , arbitraryType
    , arbitraryDecls
    ) where

import System.IO
import Test.HUnit
import Test.QuickCheck (Arbitrary(..))
import Test.QuickCheck.Gen
import Test.QuickCheck.Property
import Text.Parsec
import Text.PrettyPrint hiding (char)

import Distill.Expr
import Distill.TestUtil
import Distill.UniqueName
import Distill.UniqueName.Tests

tests :: Test
tests = TestLabel "Distill.Expr.Tests" $ TestList
    [ TestLabel "prop_exprsWellTyped" $ quickCheckToHUnit prop_exprsWellTyped
    , TestLabel "simpleTest" $ simpleTest
    , TestLabel "prop_parsePprInverses" $ quickCheckToHUnit prop_parsePprInverses
    ]

newtype WellTypedExpr = WellTypedExpr Expr
  deriving (Show, Read)

instance Arbitrary WellTypedExpr where
    arbitrary = do
        (_, m, _) <- arbitraryExpr [] 0
        return (WellTypedExpr m)

-- | Generate an arbitrary well-typed expression.
arbitraryExpr :: [(UniqueName, Type)] -> Int -> Gen (Int, Expr, Type)
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
        (s, x) <- arbitraryUniqueName s
        (s, t) <- smaller $ arbitraryType bound s
        (s, m, t') <- smaller $ arbitraryExpr ((x, t):bound) s
        return (s, Lambda x t m, Forall x t t')
    arbitraryApply bound s = do
        (s, x) <- arbitraryUniqueName s
        (s, n, t) <- smaller $ arbitraryExpr bound s
        (s, body, t') <- smaller $ arbitraryExpr ((x, t):bound) s
        let m = Lambda x t body
        return (s, Apply m n, subst x n t')

-- | Generate an arbitrary well-formed type.
arbitraryType :: [(UniqueName, Type)] -> Int -> Gen (Int, Type)
arbitraryType bound s = sized $ \size -> do
    let atomic = size <= 1
    oneof . concat $
        [ [arbitraryStar bound s | atomic]
        , [arbitraryForall bound s | not atomic]
        ]
  where
    arbitraryStar bound s = return (s, Star)
    arbitraryForall bound s = do
        (s, x) <- arbitraryUniqueName s
        (s, t) <- smaller $ arbitraryType bound s
        (s, t') <- smaller $ arbitraryType ((x, t):bound) s
        return (s, Forall x t t')

-- | Generate an arbitrary set of declarations.
arbitraryDecls :: [(UniqueName, Type)] -> Int -> Gen (Int, [Decl])
arbitraryDecls bound s = sized (arbitraryDecls' bound s)
  where
    arbitraryDecls' _ s 0 = return (s, [])
    arbitraryDecls' bound s n = do
        (s, name) <- arbitraryUniqueName s
        (s, expr, type_) <- arbitraryExpr bound s
        let decl = Decl' name type_ expr
        (s, decls) <- arbitraryDecls' ((name, type_):bound) s (pred n)
        return (s, decl:decls)

-- | The property that generated expressions are well-typed.
prop_exprsWellTyped :: WellTypedExpr -> Result
prop_exprsWellTyped (WellTypedExpr expr) =
    case runTCM (inferType expr) [] [] of
        Right _  -> succeeded
        Left err -> failed {reason = err}

-- | A simple test on parsing and type-checking a file.
simpleTest :: Test
simpleTest = TestCase $ do
    let fileName = "./test/simple.distill"
    withFile fileName ReadMode $ \file -> do
        contents <- hGetContents file
        let parsed = parse parseExprFile fileName contents
        expr <- case parsed of
            Left err -> assertFalse (show err)
            Right expr -> return expr
        case runTCM (inferType expr) [] [] of
            Left err -> assertFalse err
            Right _ -> return ()

-- | The property that parsing and pretty-printing are inverse functions.
prop_parsePprInverses :: WellTypedExpr -> Result
prop_parsePprInverses (WellTypedExpr expr) =
    let pprinted = render (pprExpr pprUnique expr)
        parsed = parse (parseExpr "%No-Name%" parseVar) "" pprinted
    in case parsed of
        Left err -> failed
            { reason = "Failed to parse pretty-printed expr.\n"
                    ++ introSpiel pprinted
                    ++ "\tWhile parsing, the following error occured:\n"
                    ++ show err
            }
        Right expr' ->
            let renumbered = renumber UniqueName 0 [] expr'
            in case runTCM (checkEqual expr renumbered) [] [] of
                    Left err -> failed
                        { reason = "Failed to check original expression was "
                                ++ "equal to pretty-printed and parsed "
                                ++ "expression.\n"
                                ++ introSpiel pprinted
                                ++ "\tWhile checking expressions to be equal, "
                                ++ "the following error occured:\n"
                                ++ err
                        }
                    Right () -> succeeded
  where
    parseVar = many1 (alphaNum <|> char '$')
    introSpiel pprinted = "\tStarted with the expression:\n"
                       ++ show expr ++ "\n"
                       ++ "\tWhich was pretty-printed as:\n"
                       ++ pprinted ++ "\n"
