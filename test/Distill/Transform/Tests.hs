{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Distill.Transform.Tests (tests) where

import Data.Functor.Foldable
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
import Distill.UniqueName

tests :: Test
tests = TestLabel "Distill.Transform.Tests" $ TestList
    [ TestLabel "prop_lambdaLiftingCreatesSuperCombinators" $
        quickCheckToHUnit prop_lambdaLiftingCreatesSuperCombinators
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
                    ++ unlines (map showDecl decls)
                    ++ "\tWere lambda lifted into the following:\n"
                    ++ unlines (map showDecl decls')
                    ++ "\tThe following declarations are not supercombinators:\n"
                    ++ unlines (map prettyUnique nonSupers)
            }
  where
    combine acc (name, isSuper) = if isSuper then acc else name:acc
    showDecl (Decl' x t m) = render $ pprSExpr $ List
        [Atom "define", Atom (prettyUnique x), toSExpr prettyUnique m]
