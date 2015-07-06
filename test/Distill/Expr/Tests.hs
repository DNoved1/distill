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

import Distill.Expr.Representation
import Distill.Expr.Syntax
import Distill.Expr.TypeCheck
import Distill.TestUtil
import Distill.UniqueName
import Distill.UniqueName.Tests
import Distill.Util

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
        , [arbitraryFold bound s | not atomic]
        , [arbitraryUnfold bound s | not atomic]
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
        return (s, Apply m n, subst' x n t')
    arbitraryFold bound s = do
        (s, x) <- arbitraryUniqueName s
        (s, m, t) <- smaller $ arbitraryExpr bound s
        let foldedType = Mu x Star t
        return (s, Fold m foldedType, foldedType)
    arbitraryUnfold bound s = do
        let boundMus = filter (isMu . snd) bound
        if not (null boundMus)
            then do
                (y, Mu x t t') <- elements boundMus
                return (s, Unfold (Var y), subst' x (Mu x t t') t')
            else do
                (s, m, Mu x t t') <- arbitraryFold bound s
                return (s, Unfold m, subst' x (Mu x t t') t')
    isMu Mu{} = True
    isMu _    = False
    subst' x m n = fromRight $ runTCM undefined $ subst x m n

-- | Generate an arbitrary well-formed type.
arbitraryType :: [(UniqueName, Type)] -> Int -> Gen (Int, Type)
arbitraryType bound s = sized $ \size -> do
    let atomic = size <= 1
    oneof . concat $
        [ [arbitraryStar bound s | atomic]
        , [arbitraryForall bound s | not atomic]
        , [arbitraryMu bound s | not atomic]
        ]
  where
    arbitraryStar _ s = return (s, Star)
    arbitraryForall bound s = do
        (s, x) <- arbitraryUniqueName s
        (s, t) <- smaller $ arbitraryType bound s
        (s, t') <- smaller $ arbitraryType ((x, t):bound) s
        return (s, Forall x t t')
    arbitraryMu bound s = do
        (s, x) <- arbitraryUniqueName s
        (s, t) <- smaller $ arbitraryType ((x, Star):bound) s
        return (s, Mu x Star t)

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
    let unique = nextAvailableUnique expr in
    case runTCM (uniqueRenamer unique) (inferType expr) of
        Right _  -> succeeded
        Left err -> failed {reason = err}

-- | A simple test on parsing and type-checking a file of declarations.
simpleTest :: Test
simpleTest = TestCase $ do
    let fileName = "./test/simple.distill"
    withFile fileName ReadMode $ \file -> do
        contents <- hGetContents file
        let parsed = parse parseFile fileName contents
        decls <- case parsed of
            Left err -> assertFalse (show err)
            Right decls -> return decls
        let decls' = renumberDecls UniqueName decls
        let assumes = map (\(Decl' x t _) -> (x, t)) decls'
        let defines = map (\(Decl' x _ m) -> (x, m)) decls'
        let tcm = flip mapM_ decls' $ \(Decl' _ t m) -> checkType m t
        let unique = maximum (map nextAvailableUniqueDecl decls')
        let renamer = uniqueRenamer unique
        case runTCM renamer $ assumesIn assumes $ definesIn defines $ tcm of
            Left err -> assertFalse err
            Right _ -> return ()

-- | The property that parsing and pretty-printing are inverse functions.
prop_parsePprInverses :: WellTypedExpr -> Result
prop_parsePprInverses (WellTypedExpr expr) =
    let pprinted = prettyShow expr
        parsed = parse parseExpr "" pprinted
    in case parsed of
        Left err -> failed
            { reason = "Failed to parse pretty-printed expr.\n"
                    ++ introSpiel pprinted
                    ++ "\tWhile parsing, the following error occured:\n"
                    ++ show err
            }
        Right expr' ->
            let renumbered = renumber UniqueName expr'
                unique = nextAvailableUnique renumbered
                renamer = uniqueRenamer unique
            in case runTCM renamer (checkEqual expr renumbered) of
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
    introSpiel pprinted = "\tStarted with the expression:\n"
                       ++ show expr ++ "\n"
                       ++ "\tWhich was pretty-printed as:\n"
                       ++ pprinted ++ "\n"
