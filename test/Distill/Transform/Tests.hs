{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Distill.Transform.Tests (tests) where

import Control.Monad.State
import Data.Functor.Foldable
import Data.List ((\\))
import Test.HUnit
import Test.QuickCheck hiding (Result, reason)
import Test.QuickCheck.Property

import Distill.Expr
import Distill.Expr.Tests hiding (tests)
import Distill.TestUtil
import Distill.Transform
import Distill.UniqueName
import Distill.Util

tests :: Test
tests = TestLabel "Distill.Transform.Tests" $ TestList
    [ TestLabel "prop_lambdaLiftingCreatesSuperCombinators" $
        quickCheckToHUnit prop_lambdaLiftingCreatesSuperCombinators
    , TestLabel "prop_aNormalizationPreservesTypes" $
        quickCheckToHUnit prop_aNormalizationPreservesTypes
    ]

-- | Check that an expression is in supercombinator form, assuming a set of
-- bound names.
isSuperCombinator :: Eq b => [b] -> Expr' b -> Bool
isSuperCombinator bound expr =
    null (freeVars expr \\ bound) && case expr of
        Lambda{} ->
            let (args, body) = splitLambda expr in
            and (noLambdaIn body : map (noLambdaIn . snd) args)
        _ -> noLambdaIn expr
  where
    noLambdaIn = cata $ \case
        LambdaF{} -> False
        expr -> foldr (&&) True expr

newtype Decls = Decls ([Decl], Int)
  deriving (Show, Read)

instance Arbitrary Decls where
    arbitrary = do
        (s, decls) <- arbitraryDecls [] 0
        return (Decls (decls, s))

-- | The property that lamdba lifting a set of declarations should result
-- in a set of declarations, all of which are supercombinators.
prop_lambdaLiftingCreatesSuperCombinators :: Decls -> Result
prop_lambdaLiftingCreatesSuperCombinators (Decls (decls, nextUnique)) =
    let decls' = lambdaLift renumberUnique nextUnique decls
        (names, exprs) = unzip (map (\(Decl' x _ m) -> (x, m)) decls')
        namesToIsSuper = zip names (map (isSuperCombinator names) exprs)
    in
    case foldl combine [] namesToIsSuper of
        [] -> succeeded
        nonSupers -> failed
            { reason = "Failed to lambda lift fully.\n"
                    ++ "\tThe declarations:\n"
                    ++ unlines (map prettyShow decls)
                    ++ "\tWere lambda lifted into the following:\n"
                    ++ unlines (map prettyShow decls')
                    ++ "\tThe following declarations are not supercombinators:\n"
                    ++ unlines (map prettyShow nonSupers)
            }
  where
    combine acc (name, isSuper) = if isSuper then acc else name:acc

-- | The property that A-Normalization of expressions should not change the
-- typeability or type of an expression.
prop_aNormalizationPreservesTypes :: WellTypedExpr -> Result
prop_aNormalizationPreservesTypes (WellTypedExpr expr) =
    let unique = nextAvailableUnique expr
        type1 = fromRight (runTCM (uniqueRenamer unique) (inferType expr))
        expr' = evalState (aNormalizeExpr (UniqueName "ANF") expr) unique
        unique2 = nextAvailableUnique expr'
        maybeType2 = runTCM (uniqueRenamer unique2) (inferType expr')
    in case maybeType2 of
        Right type2 ->
          let unique3 = max (nextAvailableUnique type1)
                            (nextAvailableUnique type2)
          in case runTCM (uniqueRenamer unique3) (checkEqual type1 type2) of
            Right () -> succeeded
            Left err -> failed
                { reason = "Failed to check that the type of an expression "
                        ++ "after A-Normalization is equivalent to the type "
                        ++ "from before.\n"
                        ++ showExprBeforeAndAfter expr expr'
                        ++ showTypeBeforeAndAfter type1 type2
                        ++ "\tThe error was:\n"
                        ++ err
                }
        Left err -> failed
            { reason = "Failed to type-check an expression after it was "
                    ++ "A-Normalized.\n"
                    ++ showExprBeforeAndAfter expr expr'
                    ++ "\tThe type error was:\n"
                    ++ err
            }
  where
    showExprBeforeAndAfter before after =
           "\tStarted with the expression:\n"
        ++ prettyShow before ++ "\n"
        ++ "\tAfter A-Normalization, the expression became:\n"
        ++ prettyShow after ++ "\n"
    showTypeBeforeAndAfter before after =
           "\tThe expression originally had the type:\n"
        ++ prettyShow before ++ "\n"
        ++ "\tAfter A-Normalization, the expression had type:\n"
        ++ prettyShow after ++ "\n"
