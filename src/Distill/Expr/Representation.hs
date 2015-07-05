{-# LANGUAGE LambdaCase #-}

module Distill.Expr.Representation
    ( splitLet
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
    , pprExpr
    , pprDecl
    , parseExpr
    , parseDecl
    , parseFile
    ) where

import Control.Arrow hiding ((<+>))
import Control.Monad
import Data.Char (digitToInt)
import Data.Functor.Foldable hiding (Mu)
import Data.List (delete, intersperse, union)
import Text.Parsec hiding (char)
import Text.Parsec.String
import Text.PrettyPrint

import Distill.Expr.Syntax
import Distill.Util

instance (Eq b, Pretty b) => Pretty (Expr' b) where
    ppr = pprExpr ppr

instance (Eq b, Pretty b) => Pretty (Decl' b) where
    ppr = pprDecl ppr

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
