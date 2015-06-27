{-# LANGUAGE LambdaCase #-}

-- TODO, perhaps an annotation marking an expression as side-effecting, and
--       therefore as something which should not be optimized out.

-- | Distill expressions.
module Distill.Expr where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List ((\\), union)

import Distill.SExpr

-- | Dependently-typed lambda calculus expressions ranging over b, the type of
-- binders.
data Expr' b
    = Var b
    -- | The type of types.
    | Star
    -- | Non-recursive let binding
    | Let b (Expr' b) (Expr' b)
    -- | Recursive let binding. Recursive bindings require type annotations
    -- so that constraint satisfaction is not necessary when type-checking.
    | Letrec [(b, Expr' b, Expr' b)] (Expr' b)
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

-- | The monad used for type checking. Includes:
--
--     * Either String - For error messages.
--     * Reader [(b, Type' b)] - For assumed types, introduced through lambda
--           abstraction.
--     * Reader [(b, Expr' b)] - For definitions, introduced through let
--           bindings or at global scope.
type TCM b a = ReaderT ([(b, Type' b)], [(b, Expr' b)]) (Either String) a

-- | Assume a variable is a given type while type checking a certain piece of
-- code. This is useful for introducing abstractions such as in lambdas and
-- dependent products (called 'Forall' here).
assumeIn :: b -> Type' b -> TCM b a -> TCM b a
assumeIn x t = local (\(assume, defs) -> ((x, t):assume, defs))

-- | Plural version of 'assumeIn'.
assumesIn :: [(b, Type' b)] -> TCM b a -> TCM b a
assumesIn newAssumes = local (\(assume, defs) -> (newAssumes ++ assume, defs))

-- | Get the current set of assumptions.
getAssumptions :: TCM b [(b, Type' b)]
getAssumptions = fst <$> ask

-- | Provide a definition of a constant while type checking a certain piece of
-- code. This is useful for introducing functions that may appear in types
-- and so need to be normalized.
defineIn :: b -> Expr' b -> TCM b a -> TCM b a
defineIn x m = local (\(assume, defs) -> (assume, (x,m):defs))

-- | Plural version of 'defineIn'.
definesIn :: [(b, Expr' b)] -> TCM b a -> TCM b a
definesIn newDefs = local (\(assume, defs) -> (assume, newDefs ++ defs))

-- | Get the current set of definitions.
getDefinitions :: TCM b [(b, Expr' b)]
getDefinitions = snd <$> ask

-- | Ignore annotations; useful for pattern matching.
ignoringAnnotations :: Monad m => (Expr' b -> m (Expr' b))
                               -> (Expr' b -> m (Expr' b))
ignoringAnnotations f = \case
    AnnotType m t   -> AnnotType <$> f m <*> pure t
    AnnotSource m s -> AnnotSource <$> f m <*> pure s
    m               -> f m

-- | Strip a top-level annotation; useful for pattern matching.
stripAnnotation :: Expr' b -> Expr' b
stripAnnotation = \case
    AnnotType m _   -> stripAnnotation m
    AnnotSource m _ -> stripAnnotation m
    m               -> m

-- | Check that an expression has a certain type. If the expression is not the
-- given type an error will be generated
checkType :: Eq b => Expr' b -> Type' b -> TCM b ()
checkType expr type_ = case expr of
    Lambda x m -> do
        Forall y t s <- case type_ of
                correct@(Forall _ _ _) -> return correct
                _ -> throwError "Lambda cannot have non-function type."
        checkType t Star
        assumeIn x t $ checkType m s
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
    Letrec binds n -> do
        let (xs, ts, ms) = unzip3 binds
        assumesIn (zip xs ts) $ definesIn (zip xs ms) $ do
            mapM_ (uncurry checkType) (zip ms ts)
            inferType n
        -- TODO, since the distill intermediate language is strict we need to
        -- also check for dependencies on non-lazy, non-function expressions.
        -- Eq, 'letrec x = 1:x in x' is not allowed, unless x is lazy.
    Forall x t s -> do
        checkType t Star
        assumeIn x t $ checkType s Star
        return Star
    Lambda _ _ ->
        throwError "Cannot infer the type of an unannotated lambda."
    Apply m n -> do
        Forall x t s <- inferType m >>= \case
            correct@(Forall _ _ _) -> return correct
            _ -> throwError "Cannot apply to non-function type."
        checkType n t
        return (subst x t s)
    AnnotType m t -> do
        checkType m t
        return t
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
        case (stripAnnotation expr1, stripAnnotation expr2) of
            (Var x, Var y) | x == y ->
                return ()
            (Star, Star) ->
                return ()
            (Let x m n, Let y o p) -> do
                checkEqual' m o
                checkEqual' n (renameVar y x p)
            (Letrec binds1 m, Letrec binds2 n) ->
                -- They could theoretically, but with terrible performance -
                -- it would require checking the permutations for equality.
                throwError $ "Recursive let binds cannot be compared for "
                          ++ "equality."
            (Forall x t s, Forall y r q) -> do
                checkEqual' t (renameVar y x r)
                checkEqual' s (renameVar y x q)
            (Lambda x m, Lambda y n) ->
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
normalize = ignoringAnnotations $ \case
    Var x -> do
        definitions <- getDefinitions
        case lookup x definitions of
            Just m  -> normalize m
            Nothing -> return (Var x)
    Star -> return Star
    Let x m n -> normalize (subst x m n)
    -- May be able to do some normalizing here, but in general we can't.
    Letrec binds m -> Letrec binds <$> normalize m
    Forall x t s -> Forall x <$> normalize t <*> normalize s
    Lambda x m -> Lambda x <$> normalize m
    Apply m n -> do
        (normalize m >>=) $ ignoringAnnotations $ \case
            -- TODO, we need to check that the type of n matches the expected
            --       argument type.
            Lambda x p -> normalize (subst x n p)
            m' -> Apply m' <$> normalize n

-- | Determine the set of unbound variables in an expression.
freeVars :: Eq b => Expr' b -> [b]
freeVars = recurse
  where
    recurse = \case
        Var x           -> [x]
        Star            -> []
        Let x m n       -> recurse m `union` (recurse n \\ [x])
        Letrec binds n  ->
            let (xs, ts, ms) = unzip3 binds in
            union
                (foldr union [] (map recurse (n:ms)) \\ xs)
                (foldr union [] (map recurse ts))
        Forall x t s    -> recurse t `union` (recurse s \\ [x])
        Lambda x m      -> recurse m \\ [x]
        Apply m n       -> recurse m `union` recurse n
        AnnotType m t   -> recurse m `union` recurse t
        AnnotSource m t -> recurse m

-- | Renumber the identifiers in an expression such that they are unique. No
-- free variables should exist in the expression - if they do an exception may
-- be thrown.
renumber :: (Enum b, Eq b) => b -> [(b, b)] -> Expr' b -> Expr' b
renumber start rebound expr =
    flip evalState start $ flip runReaderT rebound $ recurse expr
  where
    recurse = \case
        Var x -> do
            rebound <- ask
            return $ case lookup x rebound of
                Just x' -> Var x'
                Nothing -> error $ "Unbound variable while renumbering "
                                ++ "expression."
        Star ->
            return Star
        Let x m n -> do
            x' <- gensym
            Let x' <$> recurse m <*> local ((x,x'):) (recurse n)
        Letrec binds n -> do
            let (xs, ts, ms) = unzip3 binds
            xs' <- replicateM (length xs) gensym
            ts' <- mapM recurse ts
            local (zip xs xs' ++) $ do
                ms' <- mapM recurse ms
                n' <- recurse n
                return (Letrec (zip3 xs' ts' ms') n')
        Forall x t s -> do
            x' <- gensym
            Forall x' <$> recurse t <*> local ((x,x'):) (recurse s)
        Lambda x m -> do
            x' <- gensym
            Lambda x' <$> local ((x,x'):) (recurse m)
        Apply m n ->
            Apply <$> recurse m <*> recurse n
        AnnotType m t -> AnnotType <$> recurse m <*> recurse t
        AnnotSource m s -> AnnotSource <$> recurse m <*> pure s
    gensym = do
        newsym <- get
        modify succ
        return newsym

-- | Substitute an identifier for an expression in another expression. In other
-- words,
--
-- @subst x m n@
--
-- corresponds to n[x := m].
--
-- It is expected that identifiers will have been made unique prior to
-- executing this function - if not an exception may be thrown.
subst :: Eq b => b -> Expr' b -> Expr' b -> Expr' b
subst z p = \case
    Var x        | x == z    -> p
                 | otherwise -> Var x
    Star                     -> Star
    Let x m n    | x == z    -> bomb
                 | otherwise -> Let x (subst z p m) (subst z p n)
    Letrec binds n           -> Letrec (map substRecBind binds) (subst z p n)
    Forall x t s | x == z    -> bomb
                 | otherwise -> Forall x (subst z p t) (subst z p s)
    Lambda x m   | x == z    -> bomb
                 | otherwise -> Lambda x (subst z p m)
    Apply m n                -> Apply (subst z p m) (subst z p n)
    AnnotType m t            -> AnnotType (subst z p m) (subst z p t)
    AnnotSource m source     -> AnnotSource (subst z p m) source
  where
    bomb = error "Substituting through non-unique identifiers."
    substRecBind (x, t, m) | x == z    = bomb
                           | otherwise = (x, subst z p t, subst z p m)

-- TODO, when parsing and pretty-printing, it would be good to allow some
-- minor syntactic sugar for things like multi-variable lambdas and foralls,
-- and applications of more than two expressions.

-- | Serialize an expression into a symbolic-expression; helpful for printing
-- somewhat human readable representations of an expression.
toSExpr :: (b -> String) -> Expr' b -> SExpr
toSExpr showIdent = recurse
  where
    recurse = \case
        Var x -> Atom (showIdent x)
        Star -> Atom "*"
        Let x m n -> List [Atom "let", Atom (showIdent x), recurse m, recurse n]
        Letrec binds n -> List [ Atom "letrec", List (map recBindToSExpr binds)
                               , recurse n
                               ]
        Forall x t s -> List [ Atom "forall", Atom (showIdent x)
                             , recurse t, recurse s
                             ]
        Lambda x m -> List [Atom "lambda", Atom (showIdent x), recurse m]
        Apply m n -> List [recurse m, recurse n]
        AnnotType m t -> List [Atom ":", recurse m, recurse t]
        AnnotSource m s -> At (recurse m) s
    recBindToSExpr (x, t, m) = List [Atom (showIdent x), recurse t, recurse m]

-- | Unserialize an expression from a symbolic-expression; helpful for reading
-- in expressions from text files.
fromSExpr :: SExpr -> Either String (Expr' String)
fromSExpr = convertError . recurse
  where
    recurse = \case
        Atom "*" ->
            return Star
        Atom x ->
            if x `elem` reservedWords
                then newError $ "'" ++ x ++ "' is a reserved word."
                else return (Var x)
        List [Atom "let", Atom x, m, n] ->
            Let x <$> recurse m <*> recurse n
        List ((Atom "let"):_) ->
            newError $ "'let' must be applied to three arguments, the "
                    ++ "first of which must be an atom."
        List [Atom "letrec", List binds, n] ->
            Letrec <$> mapM recBindFromSExpr binds <*> recurse n
        List ((Atom "letrec"):_) ->
            newError "'letrec' must be applied to two arguments."
        List [Atom "forall", Atom x, t, s] ->
            Forall x <$> recurse t <*> recurse s
        List ((Atom "forall"):_) ->
            newError $ "'forall' must be applied to three arguments, the "
                    ++ "first of which must be an atom."
        List [Atom "lambda", Atom x, m] ->
            Lambda x <$> recurse m
        List ((Atom "lambda"):_) ->
            newError $ "'lambda' must be applied to two arguments, the "
                    ++ "first of which must be an atom."
        List [Atom ":", m, t] ->
            AnnotType <$> recurse m <*> recurse t
        List ((Atom ":"):_) ->
            newError "':' must be applied to two arguments."
        List [] ->
            newError "'()' is not a valid expression."
        List [_] ->
            newError "Cannot apply zero arguments to an expression."
        List xs ->
            foldl1 Apply <$> mapM recurse xs
        At expr loc ->
            catchError
                (AnnotSource <$> recurse expr <*> pure loc)
                (throwError . augmentError loc)
    recBindFromSExpr (List [Atom x, t, m]) = (,,) x <$> recurse t <*> recurse m
    recBindFromSExpr _ = newError $ "Bindings in a 'letrec' must be lists of "
                                 ++ "three elements, the first of which must "
                                 ++ "be an atom."
    reservedWords = ["let", "letrec", "forall", "lambda", ":"]
    newError = throwError . (,) Nothing
    augmentError loc = \case
        -- TODO, it would be good to print out the line(s) in which the
        -- error occurs, along with a caret (^) and span (~) to make error
        -- identification easier.
        (Nothing, msg) -> (Just $ "At location [" ++ show (sourceStartLine loc)
                               ++ ":" ++ show (sourceStartCol loc) ++ "]", msg)
        err -> err
    convertError = \case
        Left (Nothing, msg) -> Left msg
        Left (Just loc, msg) -> Left (msg ++ "\n\t" ++ loc)
        Right result -> Right result
