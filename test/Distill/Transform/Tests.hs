{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Distill.Transform.Tests (tests) where

import Data.List ((\\))
import Test.HUnit
import Test.QuickCheck hiding (Result, reason)
import Test.QuickCheck.Property
import Text.PrettyPrint

import Distill.Expr
import Distill.Expr.Tests hiding (tests)
import Distill.SExpr
import Distill.TestUtil
import Distill.Transform

tests :: Test
tests = TestLabel "Distill.Transform.Tests" $ TestList
    [ TestLabel "prop_lambdaLiftingCreatesSuperCombinators" $ TestCase $
        resultToAssertion =<< quickCheckWithResult (stdArgs {chatty = False})
            prop_lambdaLiftingCreatesSuperCombinators
    ]

-- | Check that an expression is in supercombinator form, assuming a set of
-- bound names.
isSuperCombinator :: Eq b => [b] -> Expr' b -> Bool
isSuperCombinator bound expr =
    null (freeVars expr \\ bound) && case expr of
        Lambda _ _ -> noLambdaIn (snd (splitLambda expr))
        _          -> noLambdaIn expr
  where
    noLambdaIn = \case
        Var x -> True
        Star -> True
        Let x m n -> noLambdaIn m && noLambdaIn n
        Letrec binds n ->
            let (xs, ts, ms) = unzip3 binds in
            and (noLambdaIn n : map noLambdaIn ts ++ map noLambdaIn ms)
        Forall x t s -> noLambdaIn t && noLambdaIn s
        Lambda x m -> noLambdaIn m
        Apply m n -> noLambdaIn m && noLambdaIn n
        AnnotType m t -> noLambdaIn m && noLambdaIn t
        AnnotSource m s -> noLambdaIn m

-- | The property that lamdba lifting a set of declarations should result
-- in a set of declarations, all of which are supercombinators.
prop_lambdaLiftingCreatesSuperCombinators :: WellTypedExpr -> Result
prop_lambdaLiftingCreatesSuperCombinators (WellTypedExpr expr) =
    let uniqueStart = nextAvailableUnique expr
        decls = lambdaLift
            renumberUnique
            (succ uniqueStart)
            [(UniqueVar "main" uniqueStart, expr)]
        (names, exprs) = unzip decls
        namesToIsSuper = zip names (map (isSuperCombinator names) exprs)
        combine acc (name, isSuper) = if isSuper then acc else name:acc
    in
    case foldl combine [] namesToIsSuper of
        [] -> succeeded
        xs -> failed
            { reason = "Failed to lambda lift fully.\n"
                    ++ "\tThe expression:\n"
                    ++ showExpr expr ++ "\n"
                    ++ "\tWas lambda lifted into the following:\n"
                    ++ unlines (map showDecl decls)
                    ++ "\tThe following declarations are not supercombinators:\n"
                    ++ unlines (map showUniqueVar xs)
            }
  where
    showExpr expr = render $ pprSExpr $ toSExpr showUniqueVar expr
    showDecl (name, expr) = render $ pprSExpr $ List
        [Atom "define", Atom (showUniqueVar name), toSExpr showUniqueVar expr]
    showUniqueVar (UniqueVar name num) = name ++ "$" ++ show num
    renumberUnique (UniqueVar name _) num = UniqueVar name num
