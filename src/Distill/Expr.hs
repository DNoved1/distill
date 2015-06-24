{-# LANGUAGE FlexibleContexts #-}

-- | Distill expressions.
module Distill.Expr where

import Control.Monad.Except

-- | Dependently-typed lambda calculus expressions ranging over b, the type of
-- binders.
data Expr' b
    = Var b
    -- | The type of types.
    | Star
    | Forall b (Type' b) (Type' b)
    | Lambda b (Expr' b)
    | Apply (Expr' b) (Expr' b)
    -- | Type annotation.
    | AnnotType (Expr' b) (Type' b)
    -- | Source location annotation.
    | AnnotSource (Expr' b) SourceLoc

-- | A type is an ordinary expression, however a different name is typically
-- used for clarity's sake.
type Type' = Expr'

-- | Source location information, mainly used for helpful error messages.
data SourceLoc = SourceLoc
    { sourceFile        :: String
    , sourceStartCol    :: Int
    , sourceStartLine   :: Int
    , sourceEndCol      :: Int
    , sourceEndLine     :: Int
    , sourceText        :: String
    }

-- | The monad used for type checking. Includes:
--
--     * Either String - For error messages.
data TCM a = TCM { runTCM :: Either String a }

-- | Check that an expression has a certain type. If the expression is not the
-- given type an error will be generated
checkType :: Expr' b -> Type' b -> TCM ()
checkType = undefined

-- | Infer the type of an expression, if possible. If a type cannot be
-- inferred an error will be generated.
inferType :: Expr' b -> TCM (Type' b)
inferType = undefined
