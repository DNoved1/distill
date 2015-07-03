{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
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
    , ignoringSource
    , deleteSourceAnnotations
    -- * Type checking
    , TCM
    , runTCM
    , checkType
    , inferType
    , checkEqual
    , normalize
    , freeVars
    , renumber
    , subst
    -- * Pretty-printing and Parsing
    , pprExpr
    , parseExpr
    ) where

import Control.Arrow hiding ((<+>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor.Foldable hiding (Foldable, Unfoldable, Mu)
import qualified Data.Functor.Foldable as RS
import Data.List (delete, intersperse, union)
import Data.Maybe (fromJust)
import Text.Parsec hiding (char)
import Text.Parsec.String
import Text.PrettyPrint

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
    -- | Least fixed point types.
    | Mu b (Type' b) (Type' b)
    | Fold (Expr' b) (Type' b)
    | Unfold (Expr' b)
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
    | MuF b a a
    | FoldF a a
    | UnfoldF a
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
        Mu x t s        -> MuF x t s
        Fold m t        -> FoldF m t
        Unfold m        -> UnfoldF m
        AnnotSource m s -> AnnotSourceF m s

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
        AnnotSourceF m s -> AnnotSource m s

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
    Mu x t s -> do
        assumeIn x t $ checkType s t
        return t
    Fold m foldedType -> do
        Mu x t s <- case foldedType of
            correct@Mu{} -> return correct
            incorrect -> throwError "Cannot fold into non-mu type."
        let unfoldedType = subst x (Mu x t s) s
        checkType m unfoldedType
        return foldedType
    Unfold m -> do
        foldedType <- inferType m
        Mu x t s <- case foldedType of
            correct@Mu{} -> return correct
            incorrect -> throwError "Cannot unfold non-mu type."
        let unfoldedType = subst x (Mu x t s) s
        return unfoldedType
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
            (Mu x t s, Mu y r q) -> do
                checkEqual' t (renameVar y x r)
                checkEqual' s (renameVar y x q)
            (Fold m t, Fold n s) -> do
                checkEqual' m n
                checkEqual' t s
            (Unfold m, Unfold n) ->
                checkEqual' m n
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
    UnfoldF m ->
        (m >>=) $ \case
            (ignoringSource -> Fold n t) -> return n
            m' -> return (Unfold m')
    expr -> embed <$> sequence expr

-- | Determine the set of unbound variables in an expression.
freeVars :: Eq b => Expr' b -> [b]
freeVars = cata $ \case
    VarF x        -> [x]
    LetF x m n    -> m `union` delete x n
    ForallF x t s -> t `union` delete x s
    LambdaF x t m -> t `union` delete x m
    MuF x t s     -> t `union` delete x s
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
        MuF x t s        -> abstraction Mu x t s
        FoldF m t        -> Fold <$> m <*> t
        UnfoldF m        -> Unfold <$> m
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
    MuF x t s     | x == z -> bomb
    expr                   -> embed expr
  where
    bomb = error "Substituting through non-unique identifiers."

-- | Pretty print an expression.
pprExpr :: Eq b => (b -> Doc) -> Expr' b -> Doc
pprExpr pprVar = recurse
  where
    recurse = ignoringSource >>> \case
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
            in hsep (intersperse (text "->") (args' ++ [body']))
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
    parensIf cond = if cond then parens else id
    pprForallArg ((x, t), dependent, atomic) =
        let wrapper = parensIf (not atomic)
            body = if dependent
                then pprVar x <+> colon <+> recurse t
                else recurse t
        in wrapper body
    pprLambdaArg (x, t) = parens $ pprVar x <+> colon <+> recurse t
    pprApplyArg (m, atomic) =
        let wrapper = parensIf (not atomic)
        in wrapper (recurse m)
    isAtomicExpr = \case
        Var _ -> True
        Star  -> True
        _     -> False
    fullstop = char '.'

-- | Parse an expression. The first argument is the name to give to
-- non-dependent function types.
parseExpr :: b -> Parser b -> Parser (Expr' b)
parseExpr defaultName parseVar' = recurse
  where
    recurse = parseArrowed
    parseAtomic = withSource $ choice
        [ parens recurse
        , pure Star <* literal "*"
        -- Uses backtracking because we don't want the variable parser to
        -- pick up reserved words, such as 'let'.
        , try $ do
            isReserved <- optionMaybe $ try (string "let")
                                    <|> try (string "mu")
                                    <|> try (string "fold")
                                    <|> try (string "unfold")
            case isReserved of
                Just reserved -> fail $ "'" ++ reserved ++ "' is a reserved "
                                     ++ "word."
                Nothing -> Var <$> parseVar
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
    whitespace = spaces
    literal str = string str *> whitespace
    parens :: Parser a -> Parser a
    parens = between (literal "(") (literal ")")
    parseVar = parseVar' <* whitespace
    parseArg = parens $ do
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
