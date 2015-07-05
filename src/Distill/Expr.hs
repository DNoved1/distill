{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

-- | Distilled expressions.
module Distill.Expr
    (
    -- * Data types
      Expr'(..)
    , Type'
    , Decl'(..)
    , Expr'F(..)
    , SourceLoc(..)
    -- ** Data views/utilities
    , splitLet
    , unsplitLet
    , splitForall
    , unsplitForall
    , splitLambda
    , unsplitLambda
    , splitApply
    , unsplitApply
    , splitProduct
    , unsplitProduct
    , splitPack
    , unsplitPack
    , splitUnpack
    , unsplitUnpack
    , ignoringSource
    , deleteSourceAnnotations
    -- * Type checking
    , Renamer
    , TCM
    , runTCM
    , assumeIn
    , assumesIn
    , defineIn
    , definesIn
    , checkType
    , inferType
    , checkEqual
    , normalize
    , freeVars
    , renumber
    , renumber'
    , renumberDecls
    , subst
    -- * Pretty-printing and Parsing
    , pprExpr
    , pprDecl
    , parseExpr
    , parseDecl
    , parseFile
    ) where

import Control.Arrow hiding ((<+>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Char (digitToInt)
import Data.Functor.Foldable hiding (Foldable, Unfoldable, Mu)
import qualified Data.Functor.Foldable as RS
import Data.List (delete, intersperse, union)
import Data.Maybe (fromJust)
import Text.Parsec hiding (char)
import Text.Parsec.String
import Text.PrettyPrint

import Distill.Util

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
    -- These are only present during parsing and type-checking.
    -- | Source location annotation.
    | AnnotSource (Expr' b) SourceLoc
    -- | An unknown type; used for non-dependent products.
    | UnknownType
  deriving (Foldable, Functor, Traversable, Show, Read)

-- | A type is an ordinary expression, however a different name is typically
-- used for clarity's sake.
type Type' = Expr'

instance (Eq b, Pretty b) => Pretty (Expr' b) where
    ppr = pprExpr ppr

-- | A top-level declaration in a file.
data Decl' b = Decl' b (Type' b) (Expr' b)
  deriving (Show, Read)

instance (Eq b, Pretty b) => Pretty (Decl' b) where
    ppr = pprDecl ppr

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

-- | Utility to split a let expression into a list of its binds and body.
splitLet :: Expr' b -> ([(b, Expr' b)], Expr' b)
splitLet = \case
    Let x m n -> first ((x,m):) (splitLet n)
    n         -> ([], n)

-- | Utility to create a let expression from a list of its binds and body.
unsplitLet :: [(b, Expr' b)] -> Expr' b -> Expr' b
unsplitLet binds body = foldr ($) body (map (uncurry Let) binds)

-- | Utility to split a forall into a list of its argument types and body.
splitForall :: Type' b -> ([(b, Type' b)], Type' b)
splitForall = \case
    Forall x t s -> first ((x,t):) (splitForall s)
    s            -> ([], s)

-- | Utility to create a forall from a list of its argument types and body.
unsplitForall :: [(b, Type' b)] -> Type' b -> Type' b
unsplitForall args body = foldr ($) body (map (uncurry Forall) args)

-- | Utility to split a lambda into a list of its arguments and its body.
splitLambda :: Expr' b -> ([(b, Type' b)], Expr' b)
splitLambda = \case
    Lambda x t m -> first ((x,t):) (splitLambda m)
    m            -> ([], m)

-- | Utility to create a lambda from a list of its arguments and its body.
unsplitLambda :: [(b, Type' b)] -> Expr' b -> Expr' b
unsplitLambda args body = foldr ($) body (map (uncurry Lambda) args)

-- | Utility to split an application into a list of expressions.
splitApply :: Expr' b -> [Expr' b]
splitApply = \case
    Apply m n -> splitApply m ++ [n]
    m         -> [m]

-- | Utility to convert a list of expressions into an application.
unsplitApply :: [Expr' b] -> Expr' b
unsplitApply = foldl1 Apply

-- | Utility to factor a dependent product type.
splitProduct :: Type' b -> ([(b, Type' b)], Type' b)
splitProduct = \case
    Product x t s -> first ((x,t):) (splitProduct s)
    s             -> ([], s)

-- | Utility to create a product type from it's component dependent factors.
unsplitProduct :: [(b, Type' b)] -> Type' b -> Type' b
unsplitProduct named unnamed = foldr ($) unnamed (map (uncurry Product) named)

-- | Utility to split a value of product type into names, values, and their
-- dependent types. Since the first value cannot depend on previous ones
-- its type is omitted, likewise the name of the last since nothing after
-- can depend upon it.
splitPack :: Eq b => Expr' b
          -> ((b, Expr' b), [(b, Expr' b, Type' b)], (Expr' b, Type' b))
splitPack = \case
    Pack x m n@(Pack y _ _ _) (Product y' t _) | y == y' ->
        let ((z, p), body, tail) = splitPack n
        in ((x, m), (z, p, t):body, tail)
    Pack x m n s -> ((x, m), [], (n, s))
    _ -> error "'splitPack' on non-packed expression."

-- | Utility to create a value of product type. See 'splitPack' for the
-- details of the arguments.
unsplitPack :: (b, Expr' b) -> [(b, Expr' b, Type' b)] -> (Expr' b, Type' b)
            -> Expr' b
unsplitPack (x, m) body tail = uncurry (Pack x m) (foldr f tail body)
  where
    f (x, m, t) (n, s) = (Pack x m n s, Product x t s)

-- | Utility to split a unpacking into the value being unpacked, the names
-- assigned to its factors, and the expression in which the names are bound.
splitUnpack :: Eq b => Expr' b -> (Expr' b, [b], Expr' b)
splitUnpack = \case
    Unpack m x y n@(Unpack (Var y') _ _ _) | y == y' ->
        let (_, names, p) = splitUnpack n
        in (m, x:names, p)
    Unpack m x y n -> (m, [x, y], n)
    _ -> error "'splitUnpack' on non-unpack expression."

-- | Utility to create an unpacking in the opposite manner of 'splitUnpack'.
unsplitUnpack :: Expr' b -> [b] -> Expr' b -> Expr' b
unsplitUnpack m names n = case names of
    [x, y] -> Unpack m x y n
    (x:y:_:_) ->
        let p = unsplitUnpack (Var y) (tail names) n
        in Unpack m x y p
    _ -> error $ "'unsplitUnpack' not provided with enough named arguments."

-- | A view on an expression without the source annotations
ignoringSource :: Expr' b -> Expr' b
ignoringSource = \case
    AnnotSource m _ -> ignoringSource m
    m               -> m

-- | Delete the source annotations once they are no longer needed (usually
-- once type checking has been done).
deleteSourceAnnotations :: Expr' b -> Expr' b
deleteSourceAnnotations = cata $ \case
    AnnotSourceF m _ -> m
    m                -> embed m

-- | The monad used for type checking.
newtype TCM b a = TCM { unTCM ::
                 ReaderT ([(b, Type' b)], [(b, Expr' b)])
                   (StateT (Renamer b)
                     (Either String))
                 a
    } deriving ( Applicative, Functor, Monad
               , MonadReader ([(b, Type' b)], [(b, Expr' b)])
               , MonadState (Renamer b)
               , MonadError String
               )

-- | The type of variable renaming functions. Each function will only be used
-- once and the list should be infinite.
type Renamer b = [b -> b]

-- | Run the type checking monad.
runTCM :: Renamer b -> TCM b a -> Either String a
runTCM renamer tcm =
    flip evalStateT renamer $
    flip runReaderT ([], []) $
    unTCM tcm

-- | Assume a variable is a given type while type checking a certain piece of
-- code. This is useful for introducing abstractions such as in lambdas and
-- dependent products (called 'Forall' here).
assumeIn :: b -> Type' b -> TCM b a -> TCM b a
assumeIn x t = local (first ((x,t):))

-- | Plural version of 'assumeIn'.
assumesIn :: [(b, Type' b)] -> TCM b a -> TCM b a
assumesIn newAssumes = local (first (newAssumes ++))

-- | Get the current set of assumptions.
getAssumptions :: TCM b [(b, Type' b)]
getAssumptions = fst <$> ask

-- | Provide a definition of a constant while type checking a certain piece of
-- code. This is useful for introducing functions that may appear in types
-- and so need to be normalized.
defineIn :: b -> Expr' b -> TCM b a -> TCM b a
defineIn x m = local (second ((x,m):))

-- | Plural version of 'defineIn'.
definesIn :: [(b, Expr' b)] -> TCM b a -> TCM b a
definesIn newDefs = local (second (newDefs ++))

-- | Get the current set of definitions.
getDefinitions :: TCM b [(b, Expr' b)]
getDefinitions = snd <$> ask

-- | Check that an expression has a certain type. If the expression is not the
-- given type an error will be generated
checkType :: (Pretty b, Eq b) => Expr' b -> Type' b -> TCM b ()
checkType expr type_ = checkEqual type_ =<< inferType expr

-- | Infer the type of an expression, if possible. If a type cannot be
-- inferred an error will be generated.
inferType :: (Pretty b, Eq b) => Expr' b -> TCM b (Type' b)
inferType expr = case expr of
    Var x -> do
        assumed <- getAssumptions
        case lookup x assumed of
            Just t -> return t
            Nothing -> throwError $ "Unbound variable '" ++ prettyShow x ++ "'."
    Star -> return Star
    Let x m n -> do
        t <- inferType m
        assumeIn x t $ defineIn x m $ inferType n
    Forall x t s -> do
        checkType t Star
        assumeIn x t $ checkType s Star
        return Star
    Lambda x t m -> do
        checkType t Star
        s <- assumeIn x t $ inferType m
        return (Forall x t s)
    Apply m n -> do
        Forall x t s <- inferType m >>= normalize >>= \case
            correct@Forall{} -> return correct
            incorrect -> throwError $
                "Cannot apply to non-function type '" ++ prettyShow incorrect
                ++ "'."
        checkType n t
        subst x n s
    Mu x t s -> do
        assumeIn x t $ checkType s t
        return t
    Fold m foldedType -> do
        Mu x t s <- normalize foldedType >>= \case
            correct@Mu{} -> return correct
            incorrect -> throwError $
                "Cannot fold into non-mu type '" ++ prettyShow incorrect ++ "'."
        unfoldedType <- subst x (Mu x t s) s
        checkType m unfoldedType
        return foldedType
    Unfold m -> do
        Mu x t s <- inferType m >>= normalize >>= \case
            correct@Mu{} -> return correct
            incorrect -> throwError $
                "Cannot unfold non-mu type '" ++ prettyShow incorrect ++ "'."
        subst x (Mu x t s) s
    UnitT -> return Star
    UnitV -> return UnitT
    Product x t s -> do
        checkType t Star
        assumeIn x t $ checkType s Star
        return Star
    Pack x m n s -> do
        t <- inferType m
        assumeIn x t $ checkType s Star
        case s of
            UnknownType -> do
                s <- inferType n
                return (Product x t s)
            _ -> do
                s' <- inferType n
                assumeIn x t $ defineIn x m $ checkEqual s' s
                return (Product x t s)
    Unpack m x y n -> do
        -- The bind is also x, so no need to re-mention it.
        Product _ t s <- inferType m >>= normalize >>= \case
            correct@(Product z _ _) -> subst z (Var x) correct
            incorrect -> throwError $
                "Cannot unpack non-product type '" ++ prettyShow incorrect
                ++ "'."
        assumeIn x t $ assumeIn y s $ inferType n
    Coproduct ts -> do
        mapM_ (flip checkType Star) ts
        return Star
    Inject m i t -> do
        Coproduct ts <- normalize t >>= \case
            correct@Coproduct{} -> return correct
            incorrect -> throwError $
                "Cannot inject into non-coproduct type '"
                ++ prettyShow incorrect ++ "'."
        when (length ts <= i) $ throwError $
            "Cannot inject into #" ++ show i ++ " of coproduct type '"
            ++ prettyShow (Coproduct ts) ++ "', which only has "
            ++ show (length ts) ++ " summands."
        flip checkEqual (ts !! i) =<< inferType m
        return (Coproduct ts)
    CaseOf m cs -> do
        Coproduct ts <- inferType m >>= normalize >>= \case
            correct@Coproduct{} -> return correct
            incorrect -> throwError $
                "Cannot perform case analysis on non-coproduct type '"
                ++ prettyShow incorrect ++ "'."
        when (length ts /= length cs) $ throwError $
            "Case analysis is non-exhaustive."
        when (null ts) $ throwError $
            "Case analysis must have at least one case."
        branchTypes <- forM (zip ts cs) $ \(t, (x, c)) ->
            assumeIn x t $ inferType c
        let resultType = head branchTypes
        forM_ branchTypes (checkEqual resultType)
            `catchError` (\err -> throwError $ err ++ "\n\t"
            ++ "While checking all case branches have the same type ("
            ++ prettyShow resultType ++ ").")
        return resultType
    AnnotSource m s ->
        catchError
            (inferType m)
            (\err -> throwError $ err ++ "\n\t At [" ++ show (sourceStartLine s)
                ++ ":" ++ show (sourceStartCol s) ++ "]")
    UnknownType ->
        throwError $ "Cannot infer the type of an unknown type."

-- | Check that two expressions are equal up to beta reduction. If they are
-- not, an error will be generated.
checkEqual :: (Eq b, Pretty b) => Expr' b -> Expr' b -> TCM b ()
checkEqual expr1 expr2 = do
    expr1' <- normalize expr1
    expr2' <- normalize expr2
    checkEqual' expr1' expr2'
  where
    checkEqual' :: (Eq b, Pretty b) => Expr' b -> Expr' b -> TCM b ()
    checkEqual' expr1 expr2 =
        case (ignoringSource expr1, ignoringSource expr2) of
            (Var x, Var y) | x == y ->
                return ()
            (Star, Star) ->
                return ()
            (Let x m n, Let y o p) ->
                abstraction (x, m, n) (y, o, p)
            (Forall x t s, Forall y r q) ->
                abstraction (x, t, s) (y, r, q)
            (Lambda x t m, Lambda y s n) ->
                abstraction (x, t, m) (y, s, n)
            (Apply m n, Apply o p) -> do
                checkEqual' m o
                checkEqual' n p
            (Mu x t s, Mu y r q) -> do
                abstraction (x, t, s) (y, r, q)
            (Fold m t, Fold n s) -> do
                checkEqual' m n
                checkEqual' t s
            (Unfold m, Unfold n) ->
                checkEqual' m n
            (UnitT, UnitT) ->
                return ()
            (UnitV, UnitV) ->
                return ()
            (Product x t s, Product y r q) ->
                abstraction (x, t, s) (y, r, q)
            (Pack x m n t, Pack y o p s) -> do
                checkEqual' m o
                checkEqual' n p
                checkEqual' t =<< renameVar y x s
            (Unpack m x y n, Unpack o a b p) -> do
                checkEqual' m o
                checkEqual' n =<< renameVar a x =<< renameVar b y p
            (Coproduct ts, Coproduct ss) -> do
                when (length ts /= length ss) $ throwError $ render $
                    text "Coproducts not equal because the number of their" <+>
                    text "summands is not equal." $$
                    nest 4 (ppr expr1) $$
                    nest 4 (ppr expr2)
                forM_ (zip ts ss) (uncurry checkEqual')
            (Inject m i t, Inject n j s) -> do
                checkEqual' m n
                when (i /= j) $ throwError $ render $
                    text "Cannot make injections equal because their" <+>
                    text "indices differ." $$
                    nest 4 (ppr expr1) $$
                    nest 4 (ppr expr2)
                checkEqual' t s
            (CaseOf m cs, CaseOf n ds) -> do
                checkEqual' m n
                when (length cs /= length ds) $ throwError $ render $
                    text "Cannot make case analyses equal because they" <+>
                    text "a different number of branches." $$
                    nest 4 (ppr expr1) $$
                    nest 4 (ppr expr2)
                forM_ (zip cs ds) $ \((x, m), (y, n)) ->
                    checkEqual' m =<< renameVar y x n
            (m, n) -> throwError $ render $
                text "Cannot make the following two types equal:" $$
                nest 4 (ppr m) $$
                nest 4 (ppr n)
      where
        abstraction (x, t, m) (y, s, n) = do
            checkEqual' t s
            checkEqual' m =<< renameVar y x n
    renameVar x y m
        | x == y    = return m
        | otherwise = subst x (Var y) m

-- | Reduce an expression up to normal form. May generate an error if
-- erroneous reductions would occur, such as applying an argument to a
-- non-function type.
normalize :: (Eq b, Pretty b) => Expr' b -> TCM b (Expr' b)
normalize = cata $ \case
    VarF x -> do
        definitions <- getDefinitions
        case lookup x definitions of
            Just m  -> normalize m
            Nothing -> return (Var x)
    LetF x m n -> do
        m' <- m
        n' <- n
        normalize =<< subst x m' n'
    ApplyF m n ->
        m >>= \case
            Lambda x _ p -> do
                n' <- n
                normalize =<< subst x n' p
            m' -> Apply m' <$> n
    UnfoldF m ->
        m >>= \case
            Fold n _ -> return n
            m' -> return (Unfold m')
    UnpackF m x y n ->
        m >>= \case
            Pack _ o p _ -> normalize =<< subst x o =<< subst y p =<< n
            m' -> Unpack m' x y <$> n
    CaseOfF m cs ->
        m >>= \case
            Inject n i _ -> do
                when (length cs <= i) $ throwError $
                    "Non-exhaustive case analysis during normalization."
                let (x, c) = cs !! i
                normalize =<< subst x n =<< c
            m' -> CaseOf m' <$> sequence (map sequence cs)
    AnnotSourceF m _ -> m
    expr -> embed <$> sequence expr

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

-- | Renumber the identifiers in an expression such that they are unique. No
-- free variables should exist in the expression - if they do an exception may
-- be thrown.
renumber :: Eq b => (b -> Int -> b') -> Expr' b -> Expr' b'
renumber ctor expr = fst (renumber' ctor 0 [] expr)

-- | 'renumber', but with the ability to specify a starting index for renaming
-- and a set of already renumbered names. Also returns the next available index
-- for renumbering; this is useful for subsequent calls.
renumber' :: Eq b => (b -> Int -> b') -> Int -> [(b, b')] -> Expr' b
         -> (Expr' b', Int)
renumber' ctor start rebound =
    flip runState start . flip runReaderT rebound . cata phi
  where
    phi = \case
        VarF x           -> Var . fromJust . lookup x <$> ask
        StarF            -> return Star
        LetF x m n       -> abstraction Let x m n
        ForallF x t s    -> abstraction Forall x t s
        LambdaF x t m    -> abstraction Lambda x t m
        ApplyF m n       -> Apply <$> m <*> n
        MuF x t s        -> abstraction Mu x t s
        FoldF m t        -> Fold <$> m <*> t
        UnfoldF m        -> Unfold <$> m
        UnitTF           -> return UnitT
        UnitVF           -> return UnitV
        ProductF x t s   -> abstraction Product x t s
        PackF x m n s    -> do
            x' <- gensym x
            Pack x' <$> m <*> n <*> local ((x,x'):) s
        UnpackF m x y n  -> do
            x' <- gensym x
            y' <- gensym y
            Unpack <$> m <*> pure x' <*> pure y'
                <*> local (\xs -> (x,x'):(y,y'):xs) n
        CoproductF ts    -> Coproduct <$> sequence ts
        InjectF m i t    -> Inject <$> m <*> pure i <*> t
        CaseOfF m cs     ->
            CaseOf <$> m <*> forM cs (\(x, c) -> do
                x' <- gensym x
                c' <- local ((x,x'):) c
                return (x', c'))
        AnnotSourceF m s -> AnnotSource <$> m <*> pure s
        UnknownTypeF     -> return UnknownType
    gensym old = ctor old <$> getAndModify succ
    abstraction sort x m n = do
        x' <- gensym x
        sort x' <$> m <*> local ((x,x'):) n

-- | Renumber a set of potentially mutually recursive declarations. This will
-- preserve names at the top level.
renumberDecls :: Eq b => (b -> Int -> b') -> [Decl' b] -> [Decl' b']
renumberDecls ctor decls = evalState (mapM renumberDecl decls) (0, [])
  where
    renumberDecl (Decl' x t m) = do
        x' <- ctor x . fst <$> get
        modify (succ *** ((x,x'):))
        t' <- wrappedRenumber t
        m' <- wrappedRenumber m
        return (Decl' x' t' m')
    wrappedRenumber m = do
        (oldState, rebound) <- get
        let (result, newState) = renumber' ctor oldState rebound m
        modify (first (const newState))
        return result

-- | Substitute an identifier for an expression in another expression. In other
-- words, @subst x m n@ corresponds to n[x := m].
subst :: (Eq b, Pretty b) => b -> Expr' b -> Expr' b -> TCM b (Expr' b)
subst z p = para $ \case
    VarF     x     | x == z -> return p
    LetF     x m n | x == z -> abstraction Let     x m n
    ForallF  x t s | x == z -> abstraction Forall  x t s
    LambdaF  x t m | x == z -> abstraction Lambda  x t m
    MuF      x t s | x == z -> abstraction Mu      x t s
    ProductF x t s | x == z -> abstraction Product x t s
    PackF x m n s | x == z -> do
        x' <- gensym x
        m' <- snd m
        n' <- snd n
        s' <- subst z p =<< subst x (Var x') (fst s)
        return (Pack x' m' n' s')
    UnpackF m x y n | x == z || y == z -> do
        m' <- snd m
        x' <- gensym x
        y' <- gensym y
        n' <- subst z p =<< subst x (Var x') =<< subst y (Var y') (fst n)
        return (Unpack m' x' y' n')
    CaseOfF m cs -> do
        CaseOf <$> (snd m) <*> forM cs (\(x, c) -> if x == z
            then do
                x' <- gensym x
                c' <- subst z p =<< subst x (Var x') (fst c)
                return (x', c')
            else sequence (x, snd c))
    expr                    -> embed <$> (sequence (snd <$> expr))
  where
    gensym x = ($ x) <$> head <$> getAndModify tail
    abstraction sort x m n = do
        x' <- gensym x
        m' <- snd m
        n' <- subst z p =<< subst x (Var x') (fst n)
        return (sort x' m' n')

-- | Pretty print an expression.
pprExpr :: Eq b => (b -> Doc) -> Expr' b -> Doc
pprExpr pprVar = recurse . deleteSourceAnnotations
  where
    recurse = \case
        Var x -> pprVar x
        Star -> char '*'
        Let x m n ->
            hsep [text "let", pprVar x, equals, recurse m, text "in"]
            $$ recurse n
        forall@Forall{} ->
            let (args, body) = splitForall forall
                isDependent = snd $ foldr
                    (\(x, t) (free, acc) ->
                        (freeVars t `union` delete x free, (x `elem` free):acc))
                    (freeVars body, [])
                    args
                isAtomic = map (isAtomicExpr . snd) args
                args' = map pprForallArg (zip3 args isDependent isAtomic)
                body' = (parensIf . not . isAtomicExpr) body (recurse body)
            in hsep (intersperse arrow (args' ++ [body']))
        lambda@Lambda{} ->
            let (args, body) = splitLambda lambda
                args' = map pprLambdaArg args
                body' = nest 4 (recurse body)
            in char '\\' <> hsep args' <> fullstop $$ body'
        apply@Apply{} ->
            let args = splitApply apply
                isAtomic = map isAtomicExpr args
                args' = map pprApplyArg (zip args isAtomic)
            in hsep args'
        Mu x t s ->
            text "mu" <+> pprVar x <+> colon <+> recurse t <> fullstop
            <+> recurse s
        Fold m t ->
            let m' = (parensIf . not . isAtomicExpr) m (recurse m)
                t' = (parensIf . not . isAtomicExpr) t (recurse t)
            in text "fold" <+> m' <+> t'
        Unfold m ->
            let m' = (parensIf . not . isAtomicExpr) m (recurse m)
            in text "unfold" <+> m'
        UnitT -> productL <> productR
        UnitV -> packL <> packR
        product@Product{} ->
            let (args, body) = splitProduct product
                isDependent = snd $ (\f -> foldr f (freeVars body, []) args) $
                    \(x, t) (free, acc) ->
                        (freeVars t `union` delete x free, (x `elem` free):acc)
                args' = flip map (zip args isDependent) $ \((x, t), dep) ->
                    if dep
                        then pprVar x <+> colon <+> recurse t
                        else recurse t
                body' = recurse body
                innards = hsep (intersperse productSep (args' ++ [body']))
            in productL <+> innards <+> productR
        pack@Pack{} ->
            let (head@(x, m), body, tail@(n, t)) = splitPack pack
                nameNecessary = packNameNecessary head body tail
                typeNecessary = packTypeNecessary head body tail
                parts = (x, m, undefined) : body ++ [(undefined, n, t)]
                parts' = map pprPackPart (zip3 parts nameNecessary typeNecessary)
                innards = hsep (punctuate comma parts')
            in packL <> innards <> packR
        unpack@Unpack{} ->
            let (head, names, tail) = splitUnpack unpack
                head' = recurse head
                names' = hsep (punctuate comma (map pprVar names))
                tail' = nest 4 (recurse tail)
            in text "unpack" <+> head' <+> equals <+> packL <> names' <> packR
                $$ tail'
        Coproduct ts ->
            let body = hsep (intersperse coproductSep (map recurse ts))
            in coproductL <+> body <+> coproductR
        Inject m i t ->
            let m' = (parensIf . not . isAtomicExpr) m (recurse m)
                i' = int i
                t' = (parensIf . not . isAtomicExpr) t (recurse t)
            in text "inject" <+> m' <+> i' <+> t'
        CaseOf m cs ->
            let m' = (parensIf . not . isAtomicExpr) m (recurse m)
                cs' = flip map cs $ \(x, c) ->
                    nest 4 (char '|' <+> pprVar x <+> arrow <+> recurse c)
            in vcat ((text "caseof" <+> m') : cs')
        AnnotSource m _ -> recurse m
        UnknownType -> char '?'
    parensIf cond = if cond then parens else id
    pprForallArg ((x, t), dependent, atomic) =
        let wrapper = parensIf (not atomic || dependent)
            body = if dependent
                then pprVar x <+> colon <+> recurse t
                else recurse t
        in wrapper body
    pprLambdaArg (x, t) = parens $ pprVar x <+> colon <+> recurse t
    pprApplyArg (m, atomic) =
        let wrapper = parensIf (not atomic)
        in wrapper (recurse m)
    packNameNecessary head body tail =
        let bodyNameNecessary = (\f -> foldr f (freeVars (snd tail), []) body)
                $ \(x, _, t) (free, acc) ->
                    (freeVars t `union` delete x free, (x `elem` free):acc)
            headNameNecessary = fst head `elem` fst bodyNameNecessary
        in headNameNecessary : snd bodyNameNecessary ++ [False]
    packTypeNecessary head body tail =
        let bodyTypeNecessary = (\f -> foldl f ([fst head], []) body)
                $ \(defined, acc) (x, _, t) ->
                    (x:defined, (any (`elem` defined) (freeVars t)):acc)
            tailTypeNecessary = any (`elem` fst bodyTypeNecessary) (snd tail)
        in False : snd bodyTypeNecessary ++ [tailTypeNecessary]
    pprPackPart ((x, m, t), pprName, pprType) =
            (if pprName then pprVar x <+> equals else empty)
        <+> recurse m
        <+> (if pprType then colon <+> recurse t else empty)
    isAtomicExpr = ignoringSource >>> \case
        Var{}       -> True
        Star{}      -> True
        Product{}   -> True
        Pack{}      -> True
        Coproduct{} -> True
        _           -> False
    fullstop = char '.'
    productL = text "(&"
    productR = text "&)"
    productSep = char '&'
    packL = text "<|"
    packR = text "|>"
    coproductL = text "(|"
    coproductR = text "|)"
    coproductSep = char '|'
    arrow = text "->"

-- | Pretty-print a declaration.
pprDecl :: Eq b => (b -> Doc) -> Decl' b -> Doc
pprDecl pprVar (Decl' x t m) =
    text "define" <+> pprVar x $$
    nest 4 (colon <+> pprExpr pprVar t) $$
    nest 4 (equals <+> pprExpr pprVar m)

-- | Parse an expression. The first argument is the name to give to
-- non-dependent function types.
parseExpr :: b -> Parser b -> Parser (Expr' b)
parseExpr defaultName parseVar' = recurse
  where
    recurse = parseArrowed
    parseAtomic = withSource $ choice
        [ try (parseParens recurse)
        , try $ do
            literal "(&"
            factors <- flip sepBy (literal "&") $ choice
                [ try $ do
                    x <- parseVar
                    literal ":"
                    t <- recurse
                    return (x, t)
                , do
                    t <- recurse
                    return (defaultName, t)
                ]
            literal "&)"
            case length factors of
                0 -> return UnitT
                1 -> fail "Product must have 0, 2, or more factors."
                _ -> do
                    let tail' = snd (last factors)
                    let body' = init factors
                    return (unsplitProduct body' tail')
        , do
            literal "(|"
            summands <- sepBy recurse (literal "|")
            literal "|)"
            return (Coproduct summands)
        , do
            literal "<|"
            parts <- flip sepBy (literal ",") $ choice
                [ try $ do
                    x <- parseVar
                    literal "="
                    m <- recurse
                    literal ":"
                    t <- recurse
                    return (x, m, t)
                , try $ do
                    x <- parseVar
                    literal "="
                    m <- recurse
                    return (x, m, UnknownType)
                , try $ do
                    m <- recurse
                    literal ":"
                    t <- recurse
                    return (defaultName, m, t)
                , do
                    m <- recurse
                    return (defaultName, m, UnknownType)
                ]
            literal "|>"
            case length parts of
                0 -> return UnitV
                1 -> fail "Pack must have 0, 2, or more parts."
                _ -> do
                    let head' = (\(x, m, _) -> (x, m)) (head parts)
                    let tail' = (\(_, m, t) -> (m, t)) (last parts)
                    let body' = (init . tail) parts
                    return (unsplitPack head' body' tail')
        , pure Star <* literal "*"
        , Var <$> parseVar
        ]
    parseBasic = withSource $ choice
        [ parseAtomic
        , do
            literal "let"
            x <- parseVar
            literal "="
            m <- recurse
            literal "in"
            n <- recurse
            return (Let x m n)
        , do
            literal "\\"
            args <- many1 parseArg
            literal "."
            body <- recurse
            return (unsplitLambda args body)
        , do
            literal "mu"
            x <- parseVar
            literal ":"
            t <- recurse
            literal "."
            s <- recurse
            return (Mu x t s)
        , do
            literal "fold"
            m <- parseAtomic
            t <- parseAtomic
            return (Fold m t)
        , do
            literal "unfold"
            m <- parseAtomic
            return (Unfold m)
        , do
            literal "unpack"
            m <- recurse
            literal "="
            literal "<|"
            parts <- sepBy parseVar (literal ",")
            literal "|>"
            n <- recurse
            if length parts < 2
                then fail $ "Unpackings can only be applied to products with "
                         ++ "at least two factors."
                else return (unsplitUnpack m parts n)
        , do
            literal "inject"
            m <- parseAtomic
            i <- parseNat
            t <- parseAtomic
            return (Inject m i t)
        , do
            literal "caseof"
            m <- recurse
            cs <- many $ do
                literal "|"
                x <- parseVar
                literal "->"
                c <- recurse
                return (x, c)
            return (CaseOf m cs)
        ]
    parseApplied = withSource $ do
        args <- many1 parseBasic
        return (unsplitApply args)
    parseArrowed = withSource $ do
        argsAndBody <- flip sepBy1 (literal "->") $ choice
            [ try parseArg -- Uses backtracking because it starts with '(',
                           -- just like a parenthesized atomic expression.
            , (,) defaultName <$> parseApplied
            ]
        return $ if null (tail argsAndBody)
            then snd (head argsAndBody)
            else unsplitForall (init argsAndBody) (snd (last argsAndBody))
    literal = parseLiteral
    parseVar = fixParseVar parseVar'
    parseArg = parseParens $ do
        x <- parseVar
        literal ":"
        t <- recurse
        return (x, t)
    withSource p = do
        start <- getPosition
        expr <- p
        end <- getPosition
        return $ AnnotSource expr $ SourceLoc
            { sourceFile = sourceName start
            , sourceStartCol = sourceColumn start
            , sourceStartLine = sourceLine start
            , sourceEndCol = sourceColumn end
            , sourceEndLine = sourceLine end
            }

-- | Parse a declaration.
parseDecl :: b -> Parser b -> Parser (Decl' b)
parseDecl defaultName parseVar' = do
    parseLiteral "define"
    x <- fixParseVar parseVar'
    parseLiteral ":"
    t <- parseExpr defaultName parseVar'
    parseLiteral "="
    m <- parseExpr defaultName parseVar'
    return (Decl' x t m)

-- | Parse an entire file full of declarations.
parseFile :: b -> Parser b -> Parser [Decl' b]
parseFile defaultName parseVar' =
    parseWhitespace *> many (parseDecl defaultName parseVar') <* eof

-- | "Fix" a variable parser so that it won't pick up reserved words and will
-- automatically parse whitespace after itself like all the other parsers.
fixParseVar :: Parser b -> Parser b
fixParseVar parseVar' = try $ do
    -- Uses backtracking because we don't want the variable parser to
    -- pick up reserved words, such as 'let'.
    isReserved <- optionMaybe $ try (string "let")
                            <|> try (string "mu")
                            <|> try (string "fold")
                            <|> try (string "unfold")
                            <|> try (string "define")
    case isReserved of
        Just reserved -> fail $ "'" ++ reserved ++ "' is a reserved word."
        Nothing -> parseVar' <* parseWhitespace

parseLiteral :: String -> Parser String
parseLiteral str = string str <* parseWhitespace

parseWhitespace :: Parser ()
parseWhitespace = void (many (void (oneOf " \t\n") <|> parseComment))
  where
    parseComment = void (string "#" >> many (noneOf "\n") >> string "\n")

parseParens :: Parser a -> Parser a
parseParens = between (parseLiteral "(") (parseLiteral ")")

parseNat :: Parser Int
parseNat = do
    digits <- many1 digit
    return (foldl1 (\acc d -> acc * 10 + d) (map digitToInt digits))
