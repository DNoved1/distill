{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

-- | Transformations on distilled expressions. Expressions should be renumbered
-- and type checked before transforming them, in general.
module Distill.Transform
    ( lambdaLift
    ) where

import Control.Arrow ((&&&), second)
import Control.Monad.Reader
import Control.Monad.State
import Data.List ((\\))
import Data.Maybe (fromJust)

import Distill.Expr

-- | Lambda-lift a set of declarations into supercombinator form.
lambdaLift :: Eq b => (b -> Int -> b) -> Int -> [Decl' b] -> [Decl' b]
lambdaLift ctor start decls =
    let state = mapM_ (lambdaLift' ctor) decls in
    snd $ snd $ runState state (start, [])

lambdaLift' :: Eq b => (b -> Int -> b) -> Decl' b -> State (Int, [Decl' b]) ()
lambdaLift' ctor (name, expr) = do
    expr' <- runReaderT (lambdaLiftTop expr) (name, [])
    modify (\(num, decls) -> (num, (name, expr'):decls))
    return ()
  where
    lambdaLiftTop = \case
        Lambda x t m -> do
            let (args, body) = splitLambda (Lambda x t m)
            body' <- assumeArgs args $ lambdaLiftInner body
            return (unsplitLambda (args, body'))
        AnnotSource m s -> AnnotSource <$> lambdaLiftTop m <*> pure s
        expr -> lambdaLiftInner expr
    lambdaLiftInner = \case
        Var x -> return (Var x)
        Star -> return Star
        Let x m n -> Let x <$> lambdaLiftInner m <*> lambdaLiftInner n
        Letrec binds n -> do
            let (xs, ts, ms) = unzip3 binds
            ts' <- mapM lambdaLiftInner ts
            ms' <- mapM lambdaLiftInner ms
            n'  <- lambdaLiftInner n
            return (Letrec (zip3 xs ts' ms') n')
        Forall x t s -> Forall x <$> lambdaLiftInner t <*> lambdaLiftInner s
        Lambda x t m -> do
            newExpr <- lambdaLiftTop (Lambda x t m)
            boundIn <- boundVars
            let freeIn = freeVars newExpr \\ boundIn
            args <- createArgs freeIn
            let newExpr' = unsplitLambda (args, newExpr)
            name <- getName
            (num, decls) <- get
            let newName = ctor name num
            let newDecl = (newName, newExpr')
            put (succ num, newDecl:decls)
            return (unsplitApply (Var newName : map Var freeIn))
        Apply m n -> Apply <$> lambdaLiftInner m <*> lambdaLiftInner n
        AnnotSource m s -> AnnotSource <$> lambdaLiftInner m <*> pure s
    boundVars = do
        (num, decls) <- get
        return (map fst decls)
    assumeArgs args = local (second (args ++))
    createArgs names = do
        (_, boundArgs) <- ask
        -- This will throw an error in the case that there are free variables
        -- in an expression, however it should not happen since type-checking
        -- is a precondition to calling 'lambdaLift'
        return (map (id &&& fromJust . flip lookup boundArgs) names)
    getName = fst <$> ask
