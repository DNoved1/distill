{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

-- | Transformations on distilled expressions. Before transforming expressions,
-- they should first be renumbered, type checked, and had their source
-- annotations deleted.
module Distill.Transform
    ( lambdaLift
    , aNormalizeExpr
    ) where

import Control.Arrow
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor.Foldable hiding (Mu)
import Data.List ((\\))
import Data.Maybe (fromJust)

import Distill.Expr
import Distill.Util

-- | Lambda-lift a set of declarations into supercombinator form.
lambdaLift :: (Eq b, Pretty b) => (b -> Int -> b) -> Int -> [Decl' b] -> [Decl' b]
lambdaLift ctor start decls =
    let declTypes = map (\(Decl' x t _) -> (x, t)) decls
        state = mapM_ (lambdaLift' ctor declTypes) decls in
    snd $ snd $ runState state (start, [])

-- | Lambda-lifts a single declaration into supercombinator form.
lambdaLift' :: (Eq b, Pretty b) => (b -> Int -> b) -> [(b, Type' b)] -> Decl' b
            -> State (Int, [Decl' b]) ()
lambdaLift' ctor assumed (Decl' x t m) = do
    m' <- runReaderT (lambdaLiftOuter m) (x, assumed)
    addDecl (Decl' x t m')
    return ()
  where
    -- Lift a lambda assuming we are at the top level.
    lambdaLiftOuter = \case
        lambda@Lambda{} -> do
            let (args, body) = splitLambda lambda
            let (xs, ts) = unzip args
            ts' <- mapM lambdaLiftInner ts
            let args' = zip xs ts'
            body' <- assumeArgs args $ lambdaLiftInner body
            return (unsplitLambda args' body')
        expr -> lambdaLiftInner expr
    -- Lift a lambda assuming we are inside another expression.
    lambdaLiftInner = \case
        lambda@Lambda{} -> do
            base <- lambdaLiftOuter lambda
            freeArgs <- (freeVars base \\) <$> boundVars
            completed <- unsplitLambda <$> createArgs freeArgs <*> pure base
            type_ <- typeof completed
            name <- createName
            addDecl (Decl' name type_ completed)
            return (unsplitApply (Var name : map Var freeArgs))
        expr -> embed <$> sequence (lambdaLiftInner <$> project expr)
    -- Determine the set of variables bound by declarations.
    boundVars = map (\(Decl' x _ _) -> x) <$> snd <$> get
    -- Assume a set of arguments are a set of types in a sub-computation.
    assumeArgs args = local (second (args ++))
    -- Create a new unique name for a declaration to use.
    createName = ctor <$> (fst <$> ask) <*> (fst <$> get <* modify (first succ))
    -- Add a newly created declaration to the set of declarations.
    addDecl decl = modify (second (decl:))
    -- Creates a list of (Var, Type) pairs, used as arguments for a lambda.
    createArgs names = do
        assumed <- snd <$> ask
        return (map (id &&& fromJust . flip lookup assumed) names)
    -- Determine the type of an expression.
    typeof expr = do
        assumed <- snd <$> ask
        decls <- snd <$> get
        let assumed' = assumed ++ map (\(Decl' x t _) -> (x, t)) decls
        let defined' = map (\(Decl' x _ m) -> (x, m)) decls
        let tcm = assumesIn assumed' $ definesIn defined' $ inferType expr
        return (fromRight (runTCM undefined tcm))

-- | Translate an expression into administrative normal form.
aNormalizeExpr :: (Int -> b) -> Expr' b -> State Int (Expr' b)
aNormalizeExpr ctor = aNormalizeOuter
  where
    -- Normalize expressions to A-normal form; assumes we are not in an apply.
    aNormalizeOuter expr = do
        (lets, expr') <- aNormalizeInner expr
        return (unsplitLet lets expr')
    -- Normalize expressions to simple values; this assumes we are in an apply.
    aNormalizeInner = \case
        Var x -> return ([], Var x)
        Star -> return ([], Star)
        Let x m n -> do
            (mlets, m') <- aNormalizeInner m
            (nlets, n') <- aNormalizeInner n
            return (mlets ++ [(x, m')] ++ nlets, n')
        Forall x t s -> do
            (tlets, t') <- aNormalizeInner t
            s' <- aNormalizeOuter s
            return (tlets, Forall x t' s')
        Lambda x t m -> do
            (tlets, t') <- aNormalizeInner t
            m' <- aNormalizeOuter m
            return (tlets, Lambda x t' m')
        apply@Apply{} -> do
            let args = splitApply apply
            (lets, args') <- unzip <$> mapM aNormalizeInner args
            let apply' = unsplitApply args'
            name <- createName
            return (concat lets ++ [(name, apply')], Var name)
        Mu x t s -> do
            (tlets, t') <- aNormalizeInner t
            s' <- aNormalizeOuter s
            return (tlets, Mu x t' s')
        Fold m t -> do
            (mlets, m') <- aNormalizeInner m
            (tlets, t') <- aNormalizeInner t
            return (mlets ++ tlets, Fold m' t')
        Unfold m -> do
            (mlets, m') <- aNormalizeInner m
            return (mlets, Unfold m')
        UnitT -> return ([], UnitT)
        UnitV -> return ([], UnitV)
        Product x t s -> do
            (tlets, t') <- aNormalizeInner t
            s' <- aNormalizeOuter s
            return (tlets, Product x t' s')
        Pack x m n s -> do
            (mlets, m') <- aNormalizeInner m
            (nlets, n') <- aNormalizeInner n
            s' <- aNormalizeOuter s
            return (mlets ++ nlets, Pack x m' n' s')
        Unpack m x y n -> do
            (mlets, m') <- aNormalizeInner m
            n' <- aNormalizeOuter n
            return (mlets, Unpack m' x y n')
        Coproduct ts -> do
            (tslets, ts') <- unzip <$> mapM aNormalizeInner ts
            return (concat tslets, Coproduct ts')
        Inject m i t -> do
            (mlets, m') <- aNormalizeInner m
            (tlets, t') <- aNormalizeInner t
            return (mlets ++ tlets, Inject m' i t')
        CaseOf m cs -> do
            (mlets, m') <- aNormalizeInner m
            cs' <- forM cs $ \(x, c) -> do
                c' <- aNormalizeOuter c
                return (x, c')
            return (mlets, CaseOf m' cs')
        CaseOfFalse m t -> do
            (mlets, m') <- aNormalizeInner m
            (tlets, t') <- aNormalizeInner t
            return (mlets ++ tlets, CaseOfFalse m' t')
        AnnotSource{} -> unstrippedError
        UnknownType{} -> unstrippedError
    createName = ctor <$> (get <* modify succ)
    unstrippedError = error "Unstripped annotations while A-normalizing."
