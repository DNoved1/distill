{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Distill.Expr.TypeCheck
    ( TCM
    , Renamer
    , runTCM
    , assumeIn
    , assumesIn
    , defineIn
    , definesIn
    , checkType
    , inferType
    , checkEqual
    , normalize
    , renumber
    , renumber'
    , renumberDecls
    , subst
    ) where

import Control.Arrow hiding ((<+>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor.Foldable hiding (Foldable, Unfoldable, Mu)
import Data.Maybe (fromJust)
import Text.PrettyPrint

import Distill.Expr.Syntax
import Distill.Expr.Representation
import Distill.Util

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
