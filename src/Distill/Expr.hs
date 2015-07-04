{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
splitApply = \case
    Apply m n -> splitApply m ++ [n]
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
    AnnotSource m s ->
        catchError
            (inferType m)
            (\err -> throwError $ err ++ "\n\t At [" ++ show (sourceStartLine s)
                ++ ":" ++ show (sourceStartCol s) ++ "]")

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
            (Let x m n, Let y o p) -> do
                checkEqual' m o
                checkEqual' n =<< renameVar y x p
            (Forall x t s, Forall y r q) -> do
                checkEqual' t =<< renameVar y x r
                checkEqual' s =<< renameVar y x q
            (Lambda x t m, Lambda y s n) -> do
                checkEqual' t s
                checkEqual' m =<< renameVar y x n
            (Apply m n, Apply o p) -> do
                checkEqual' m o
                checkEqual' n p
            (Mu x t s, Mu y r q) -> do
                checkEqual' t =<< renameVar y x r
                checkEqual' s =<< renameVar y x q
            (Fold m t, Fold n s) -> do
                checkEqual' m n
                checkEqual' t s
            (Unfold m, Unfold n) ->
                checkEqual' m n
            (m, n) -> throwError $ render $
                text "Cannot make the following two types equal:" $$
                nest 4 (ppr m) $$
                nest 4 (ppr n)
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
        (m >>=) $ \case
            (ignoringSource -> Lambda x t p) -> do
                n' <- n
                normalize =<< subst x n' p
            m' -> Apply m' <$> n
    UnfoldF m ->
        (m >>=) $ \case
            (ignoringSource -> Fold n t) -> return n
            m' -> return (Unfold m')
    AnnotSourceF m _ -> m
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
        AnnotSourceF m s -> AnnotSource <$> m <*> pure s
    gensym old = ctor old <$> (get <* modify succ)
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
    VarF    x     | x == z -> return p
    LetF    x m n | x == z -> abstraction Let    x (fst m) (fst n)
    ForallF x t s | x == z -> abstraction Forall x (fst t) (fst s)
    LambdaF x t m | x == z -> abstraction Lambda x (fst t) (fst m)
    MuF     x t s | x == z -> abstraction Mu     x (fst t) (fst s)
    expr                   -> embed <$> (sequence (snd <$> expr))
  where
    bomb = error $ "Substituting through non-unique identifiers ("
                ++ prettyShow z ++ ")."
    abstraction sort x m n = do
        rename <- head <$> (get <* modify tail)
        let x' = rename x
        m' <- subst x (Var x') m
        n' <- subst x (Var x') n
        subst z p (sort x' m' n')

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
        let wrapper = parensIf (not atomic || dependent)
            body = if dependent
                then pprVar x <+> colon <+> recurse t
                else recurse t
        in wrapper body
    pprLambdaArg (x, t) = parens $ pprVar x <+> colon <+> recurse t
    pprApplyArg (m, atomic) =
        let wrapper = parensIf (not atomic)
        in wrapper (recurse m)
    isAtomicExpr = ignoringSource >>> \case
        Var _ -> True
        Star  -> True
        _     -> False
    fullstop = char '.'

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
        [ parseParens recurse
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
parseFile defaultName parseVar' = many (parseDecl defaultName parseVar') <* eof

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
