{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

-- | Distilled expressions.
module Distill.Expr where

import Control.Arrow
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor.Foldable hiding (Foldable, Unfoldable)
import qualified Data.Functor.Foldable as RS
import Data.List (delete, union)
import Data.Maybe (fromJust)

import Distill.SExpr

-- | Dependently-typed lambda calculus expressions ranging over b, the type of
-- binders.
data Expr' b
    = Var b
    -- | The type of types.
    | Star
    -- | Non-recursive let binding
    | Let b (Expr' b) (Expr' b)
    -- | Dependent product types.
    | Forall b (Type' b) (Type' b)
    | Lambda b (Type' b) (Expr' b)
    | Apply (Expr' b) (Expr' b)
    -- | Source location annotation.
    | AnnotSource (Expr' b) SourceLoc
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
    | AnnotSourceF a SourceLoc
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
        AnnotSource m s -> AnnotSourceF m s

instance RS.Unfoldable (Expr' b) where
    embed = \case
        VarF x           -> Var x
        StarF            -> Star
        LetF x m n       -> Let x m n
        ForallF x t s    -> Forall x t s
        LambdaF x t m    -> Lambda x t m
        ApplyF m n       -> Apply m n
        AnnotSourceF m s -> AnnotSource m s

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
splitApply = reverse . \case
    Apply m n -> n : splitApply m
    m         -> [m]

-- | Utility to convert a list of expressions into an application.
unsplitApply :: [Expr' b] -> Expr' b
unsplitApply = foldl1 Apply

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

-- | The monad used for type checking. Includes:
--
--     * Either String - For error messages.
--     * Reader [(b, Type' b)] - For assumed types, introduced through lambda
--           abstraction.
--     * Reader [(b, Expr' b)] - For definitions, introduced through let
--           bindings or at global scope.
type TCM b a = ReaderT ([(b, Type' b)], [(b, Expr' b)]) (Either String) a

-- | Run the type checking monad.
runTCM :: TCM b a -> [(b, Type' b)] -> [(b, Expr' b)] -> Either String a
runTCM tcm assume defs = runReaderT tcm (assume, defs)

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
checkType :: Eq b => Expr' b -> Type' b -> TCM b ()
checkType expr type_ = case expr of
    AnnotSource m s ->
        checkType m type_
    _ -> do
        type_' <- inferType expr
        checkEqual type_ type_'

-- | Infer the type of an expression, if possible. If a type cannot be
-- inferred an error will be generated.
inferType :: Eq b => Expr' b -> TCM b (Type' b)
inferType expr = case expr of
    Var x -> do
        assumed <- getAssumptions
        case lookup x assumed of
            Just t -> return t
            Nothing -> throwError "Unbound variable."
    Star ->
        return Star
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
        Forall x t s <- inferType m >>= \case
            correct@Forall{} -> return correct
            _ -> throwError "Cannot apply to non-function type."
        checkType n t
        return (subst x t s)
    AnnotSource m _ ->
        inferType m

-- | Check that two expressions are equal up to beta reduction. If they are
-- not, an error will be generated.
checkEqual :: Eq b => Expr' b -> Expr' b -> TCM b ()
checkEqual expr1 expr2 = do
    expr1' <- normalize expr1
    expr2' <- normalize expr2
    checkEqual' expr1' expr2'
  where
    checkEqual' :: Eq b => Expr' b -> Expr' b -> TCM b ()
    checkEqual' expr1 expr2 =
        case (ignoringSource expr1, ignoringSource expr2) of
            (Var x, Var y) | x == y ->
                return ()
            (Star, Star) ->
                return ()
            (Let x m n, Let y o p) -> do
                checkEqual' m o
                checkEqual' n (renameVar y x p)
            (Forall x t s, Forall y r q) -> do
                checkEqual' t (renameVar y x r)
                checkEqual' s (renameVar y x q)
            (Lambda x t m, Lambda y s n) -> do
                checkEqual' t s
                checkEqual' m (renameVar y x n)
            (Apply m n, Apply o p) -> do
                checkEqual' m o
                checkEqual' n p
            (_, _) ->
                throwError "Expressions not equal."
    renameVar x y m
        | x == y    = m
        | otherwise = subst x (Var y) m

-- | Reduce an expression up to normal form. May generate an error if
-- erroneous reductions would occur, such as applying an argument to a
-- non-function type.
normalize :: Eq b => Expr' b -> TCM b (Expr' b)
normalize = cata $ \case
    VarF x -> do
        definitions <- getDefinitions
        case lookup x definitions of
            Just m  -> normalize m
            Nothing -> return (Var x)
    LetF x m n -> normalize =<< subst x <$> m <*> n
    ApplyF m n ->
        (m >>=) $ \case
            (ignoringSource -> Lambda x t p) ->
                normalize =<< subst x <$> n <*> pure p
            m' -> Apply m' <$> n
    expr -> embed <$> sequence expr

-- | Determine the set of unbound variables in an expression.
freeVars :: Eq b => Expr' b -> [b]
freeVars = cata $ \case
    VarF x        -> [x]
    LetF x m n    -> m `union` delete x n
    ForallF x t s -> t `union` delete x s
    LambdaF x t m -> t `union` delete x m
    expr          -> foldr union [] expr

-- | Renumber the identifiers in an expression such that they are unique. No
-- free variables should exist in the expression - if they do an exception may
-- be thrown.
renumber :: Eq b => (b -> Int -> b') -> Int -> [(b, b')] -> Expr' b -> Expr' b'
renumber ctor start rebound =
    flip evalState start . flip runReaderT rebound . cata phi
  where
    phi = \case
        VarF x           -> Var . fromJust . lookup x <$> ask
        StarF            -> return Star
        LetF x m n       -> abstraction Let x m n
        ForallF x t s    -> abstraction Forall x t s
        LambdaF x t m    -> abstraction Lambda x t m
        ApplyF m n       -> Apply <$> m <*> n
        AnnotSourceF m s -> AnnotSource <$> m <*> pure s
    gensym old = ctor old <$> (get <* modify succ)
    abstraction sort x m n = do
        x' <- gensym x
        sort x' <$> m <*> local ((x,x'):) n

-- | Substitute an identifier for an expression in another expression. In other
-- words, @subst x m n@ corresponds to n[x := m].
--
-- It is expected that identifiers will have been made unique prior to
-- executing this function - if not an exception may be thrown.
subst :: Eq b => b -> Expr' b -> Expr' b -> Expr' b
subst z p = cata $ \case
    VarF x        | x == z -> p
    LetF x m n    | x == z -> bomb
    ForallF x t s | x == z -> bomb
    LambdaF x t m | x == z -> bomb
    expr                   -> embed expr
  where
    bomb = error "Substituting through non-unique identifiers."

-- | Serialize an expression into a symbolic-expression; helpful for printing
-- somewhat human readable representations of an expression.
toSExpr :: (b -> String) -> Expr' b -> SExpr
toSExpr showIdent = recurse
  where
    recurse = \case
        Var x -> Atom (showIdent x)
        Star -> Atom "*"
        Let x m n ->
            List [Atom "let", Atom (showIdent x), recurse m, recurse n]
        forall@Forall{} ->
            let (args, body) = splitForall forall in
            List [Atom "forall", List (map argToSExpr args), recurse body]
        lambda@Lambda{} ->
            let (args, body) = splitLambda lambda in
            List [Atom "lambda", List (map argToSExpr args), recurse body]
        apply@Apply{} ->
            let args = splitApply apply in
            List (map recurse args)
        AnnotSource m s -> At (recurse m) s
    argToSExpr (x, t) = List [Atom (showIdent x), recurse t]

-- | Unserialize an expression from a symbolic-expression; helpful for reading
-- in expressions from text files.
fromSExpr :: SExpr -> Either String (Expr' String)
fromSExpr = convertError . recurse
  where
    recurse = \case
        Atom "*" -> return Star
        Atom x -> if x `elem` reservedWords
            then newError $ "'" ++ x ++ "' is a reserved word."
            else return (Var x)
        List [] -> newError "'()' is not a valid expression."
        List (f:args) -> case ignoringAt f of
            Atom "let" -> case args of
                [ignoringAt -> Atom x, m, n] ->
                    Let x <$> recurse m <*> recurse n
                _ -> newError $ "'let' must be applied to three arguments, "
                             ++ "the first of which must be an atom."
            Atom "forall" -> case args of
                [ignoringAt -> List binds, s] -> if not (null binds)
                    then unsplitForall <$> mapM argsFromSExpr binds
                                       <*> recurse s
                    else newError "'forall' must have at least one binder."
                _ -> newError $ "'forall' must be applied to three arguments, "
                             ++ "the first of which must be an atom."
            Atom "lambda" -> case args of
                [ignoringAt -> List binds, m] -> if not (null binds)
                    then unsplitLambda <$> mapM argsFromSExpr binds
                                       <*> recurse m
                    else newError "'lambda' must have at least one binder."
                _ -> newError $ "'lambda' must be applied to two arguments, "
                             ++ "the first of which must be an atom."
            _ -> case args of
                [] -> newError "Cannot apply zero arguments to an expression."
                _ -> unsplitApply <$> mapM recurse (f:args)
        At expr loc ->
            catchError
                (AnnotSource <$> recurse expr <*> pure loc)
                (throwError . augmentError loc)
    argsFromSExpr = \case
        (ignoringAt -> List [ignoringAt -> Atom x, t]) -> (,) x <$> recurse t
        _ -> newError $ "Arguments in a 'lambda' must be a two element list, "
                     ++ "the first of which must be an atom."
    reservedWords = ["let", "forall", "lambda"]
    newError = throwError . (,) Nothing
    augmentError loc = \case
        (Nothing, msg) -> (Just $ "At location [" ++ show (sourceStartLine loc)
                               ++ ":" ++ show (sourceStartCol loc) ++ "]", msg)
        err -> err
    convertError = \case
        Left (Nothing, msg) -> Left msg
        Left (Just loc, msg) -> Left (msg ++ "\n\t" ++ loc)
        Right result -> Right result
