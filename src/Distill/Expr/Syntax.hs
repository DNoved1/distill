{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Distill.Expr.Syntax
    ( Expr'(..)
    , Type'
    , Decl'(..)
    , Expr'F(..)
    , SourceLoc(..)
    , freeVars
    ) where

import Data.Functor.Foldable hiding (Foldable, Mu, Unfoldable)
import qualified Data.Functor.Foldable as RS
import Data.List (delete, union)

-- | Dependently-typed lambda calculus expressions ranging over b, the type of
-- binders.
data Expr' b
    = Var b
    -- | The type of types.
    | Star
    -- | Non-recursive let binding
    | Let b (Expr' b) (Expr' b)
    -- | Dependent product/non-dependent function types.
    | Forall b (Type' b) (Type' b)
    | Lambda b (Type' b) (Expr' b)
    | Apply (Expr' b) (Expr' b)
    -- | Least fixed point types.
    | Mu b (Type' b) (Type' b)
    | Fold (Expr' b) (Type' b)
    | Unfold (Expr' b)
    -- | Dependent sum/non-dependent product types.
    | UnitT
    | UnitV
    | Product b (Type' b) (Type' b)
    | Pack b (Expr' b) (Expr' b) (Type' b)
    | Unpack (Expr' b) b b (Expr' b)
    -- | Coproduct types. The list of types may be empty, in which case it is ⊥.
    | Coproduct [Type' b]
    | Inject (Expr' b) Int (Type' b)
    | CaseOf (Expr' b) [(b, Expr' b)]
    -- | Case analysis on ⊥, where you specify what type you want.
    | CaseOfFalse (Expr' b) (Type' b)
    -- These are only present during parsing and type-checking.
    -- | Source location annotation.
    | AnnotSource (Expr' b) SourceLoc
    -- | An unknown type; used for non-dependent products.
    | UnknownType
  deriving (Foldable, Functor, Traversable, Show, Read)

-- | A type is an ordinary expression, however a different name is typically
-- used for clarity's sake.
type Type' = Expr'

-- | A top-level declaration in a file.
data Decl' b = Decl' b (Type' b) (Expr' b)
  deriving (Show, Read)

-- | Functor view of expressions.
data Expr'F b a
    = VarF b
    | StarF
    | LetF b a a
    | ForallF b a a
    | LambdaF b a a
    | ApplyF a a
    | MuF b a a
    | FoldF a a
    | UnfoldF a
    | UnitTF
    | UnitVF
    | ProductF b a a
    | PackF b a a a
    | UnpackF a b b a
    | CoproductF [a]
    | InjectF a Int a
    | CaseOfF a [(b, a)]
    | CaseOfFalseF a a
    | AnnotSourceF a SourceLoc
    | UnknownTypeF
  deriving (Foldable, Functor, Traversable)

type instance Base (Expr' b) = Expr'F b

instance RS.Foldable (Expr' b) where
    project = \case
        Var x           -> VarF x
        Star            -> StarF
        Let x m n       -> LetF x m n
        Forall x t s    -> ForallF x t s
        Lambda x t m    -> LambdaF x t m
        Apply m n       -> ApplyF m n
        Mu x t s        -> MuF x t s
        Fold m t        -> FoldF m t
        Unfold m        -> UnfoldF m
        UnitT           -> UnitTF
        UnitV           -> UnitVF
        Product x t s   -> ProductF x t s
        Pack x m n s    -> PackF x m n s
        Unpack m x y n  -> UnpackF m x y n
        Coproduct ts    -> CoproductF ts
        Inject m i t    -> InjectF m i t
        CaseOf m cs     -> CaseOfF m cs
        CaseOfFalse m t -> CaseOfFalseF m t
        AnnotSource m s -> AnnotSourceF m s
        UnknownType     -> UnknownTypeF

instance RS.Unfoldable (Expr' b) where
    embed = \case
        VarF x           -> Var x
        StarF            -> Star
        LetF x m n       -> Let x m n
        ForallF x t s    -> Forall x t s
        LambdaF x t m    -> Lambda x t m
        ApplyF m n       -> Apply m n
        MuF x t s        -> Mu x t s
        FoldF m t        -> Fold m t
        UnfoldF m        -> Unfold m
        UnitTF           -> UnitT
        UnitVF           -> UnitV
        ProductF x t s   -> Product x t s
        PackF x m n s    -> Pack x m n s
        UnpackF m x y n  -> Unpack m x y n
        CoproductF ts    -> Coproduct ts
        InjectF m i t    -> Inject m i t
        CaseOfF m cs     -> CaseOf m cs
        CaseOfFalseF m t -> CaseOfFalse m t
        AnnotSourceF m s -> AnnotSource m s
        UnknownTypeF     -> UnknownType

-- | Source location information, mainly used for helpful error messages.
data SourceLoc = SourceLoc
    { sourceFile        :: String
    , sourceStartCol    :: Int
    , sourceStartLine   :: Int
    , sourceEndCol      :: Int
    , sourceEndLine     :: Int
    }
  deriving (Show, Read)

-- | Determine the set of unbound variables in an expression.
freeVars :: Eq b => Expr' b -> [b]
freeVars = cata $ \case
    VarF x          -> [x]
    LetF x m n      -> m `union` delete x n
    ForallF x t s   -> t `union` delete x s
    LambdaF x t m   -> t `union` delete x m
    MuF x t s       -> t `union` delete x s
    ProductF x t s  -> t `union` delete x s
    PackF x m n s   -> m `union` n `union` delete x s
    UnpackF m x y n -> m `union` (delete x . delete y) n
    CaseOfF m cs    -> m `union` (concat . map (uncurry delete)) cs
    expr            -> foldr union [] expr
