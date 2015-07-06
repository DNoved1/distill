{-# LANGUAGE LambdaCase #-}

-- | Pretty printing and parsing distilled expressions.
module Distill.Expr.Representation
    (
    -- * Utility Constructors/Destructors
      splitLet
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
    -- * Parsing
    , parseExpr
    , parseDecl
    , parseFile
    ) where

import Control.Arrow hiding ((<+>))
import Data.Functor.Foldable hiding (Mu)
import Data.List (delete, intersperse, union)
import Text.Parsec hiding (char, tokens)
import qualified Text.Parsec as Parsec
import Text.Parsec.String
import Text.Parsec.Token hiding (colon, comma, parens)
import qualified Text.Parsec.Token as Token
import Text.PrettyPrint

import Distill.Expr.Syntax
import Distill.Util

{-=== Utility Constructors/Destructors ======================================-}

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

{-=== Pretty printing =======================================================-}

instance (Eq b, Pretty b) => Pretty (Expr' b) where
    ppr = \case
        Var x           -> ppr x
        Star            -> char '*'
        Let x m n       -> pprLet x m n
        Forall x t s    -> pprForall x t s
        Lambda x t m    -> pprLambda x t m
        Apply m n       -> pprApply m n
        Mu x t s        -> pprMu x t s
        Fold m t        -> pprFold m t
        Unfold m        -> pprUnfold m
        UnitT           -> productL <> productR
        UnitV           -> packL <> packR
        Product x t s   -> pprProduct x t s
        Pack x m n s    -> pprPack x m n s
        Unpack m x y n  -> pprUnpack m x y n
        Coproduct ts    -> pprCoproduct ts
        Inject m i t    -> pprInject m i t
        CaseOf m cs     -> pprCaseOf m cs
        AnnotSource m _ -> ppr m
        UnknownType     -> char '?'

instance (Eq b, Pretty b) => Pretty (Decl' b) where
    ppr (Decl' x t m) =
        hang (text "define" <+> ppr x) 4
            (vcat [colon <+> ppr t, equals <+> ppr m])

fullstop        = char '.'
productL        = text "(&"
productR        = text "&)"
productSep      = char '&'
packL           = text "<|"
packR           = text "|>"
coproductL      = text "(|"
coproductR      = text "|)"
coproductSep    = char '|'
arrow           = text "->"

isAtomicExpr :: Expr' b -> Bool
isAtomicExpr = ignoringSource >>> \case
    Var{}       -> True
    Star{}      -> True
    Product{}   -> True
    Pack{}      -> True
    Coproduct{} -> True
    _           -> False

parensIf :: Bool -> Doc -> Doc
parensIf cond = if cond then parens else id

parensIfNotAtomic :: (Eq b, Pretty b) => Expr' b -> Doc
parensIfNotAtomic m = (parensIf . not . isAtomicExpr) m (ppr m)

seperatedBy :: [Doc] -> Doc -> Doc
seperatedBy docs sep = hsep (intersperse sep docs)

pprLet :: (Eq b, Pretty b) => b -> Expr' b -> Expr' b -> Doc
pprLet x m n = text "let" <+> ppr x <+> equals <+> ppr m <+> text "in" $$ ppr n

pprForall :: (Eq b, Pretty b) => b -> Type' b -> Type' b -> Doc
pprForall x t s =
    let (args, body) = splitForall (Forall x t s)
        isDependent = snd $ (\f -> foldr f (freeVars body, []) args) $
            \(x, t) (free, acc) ->
                (freeVars t `union` delete x free, (x `elem` free):acc)
        isAtomic = map (isAtomicExpr . snd) args
        args' = map pprForallArg (zip3 args isDependent isAtomic)
        body' = parensIfNotAtomic body
    in (args' ++ [body']) `seperatedBy` arrow
  where
    pprForallArg ((x, t), dependent, atomic) =
        let wrapper = parensIf (not atomic || dependent)
            body = (if dependent then ppr x <+> colon else empty) <+> ppr t
        in wrapper body

pprLambda :: (Eq b, Pretty b) => b -> Type' b -> Expr' b -> Doc
pprLambda x t m =
    let (args, body) = splitLambda (Lambda x t m)
        args' = map pprLambdaArg args
    in char '\\' <> hsep args' <> fullstop $$ nest 4 (ppr body)
  where
    pprLambdaArg (x, t) = parens (ppr x <+> colon <+> ppr t)

pprApply :: (Eq b, Pretty b) => Expr' b -> Expr' b -> Doc
pprApply m n = hsep (map parensIfNotAtomic (splitApply (Apply m n)))

pprMu :: (Eq b, Pretty b) => b -> Type' b -> Type' b -> Doc
pprMu x t s = text "mu" <+> ppr x <+> colon <+> ppr t <> fullstop <+> ppr s

pprFold :: (Eq b, Pretty b) => Expr' b -> Type' b -> Doc
pprFold m t = text "fold" <+> ppr m <+> text "into" <+> ppr t

pprUnfold :: (Eq b, Pretty b) => Expr' b -> Doc
pprUnfold m = text "unfold" <+> ppr m

pprProduct :: (Eq b, Pretty b) => b -> Type' b -> Type' b -> Doc
pprProduct x t s =
    let (args, body) = splitProduct (Product x t s)
        isDependent = snd $ (\f -> foldr f (freeVars body, []) args) $
            \(x, t) (free, acc) ->
                (freeVars t `union` delete x free, (x `elem` free):acc)
        args' = map pprFactor (zip args isDependent)
        body' = ppr body
        innards = (args' ++ [body']) `seperatedBy` productSep
    in productL <+> innards <+> productR
  where
    pprFactor ((x, t), dep) = (if dep then ppr x <+> colon else empty) <+> ppr t

pprPack :: (Eq b, Pretty b) => b -> Expr' b -> Expr' b -> Type' b -> Doc
pprPack x m n s =
    let (head, body, tail) = splitPack (Pack x m n s)
        nameNecessary = packNameNecessary head body tail
        typeNecessary = packTypeNecessary head body tail
        parts = extendHead head : body ++ [extendTail tail]
        parts' = map pprFactor (zip3 parts nameNecessary typeNecessary)
        innards = hsep (punctuate comma parts')
    in packL <> innards <> packR
  where
    -- This is a bit tricky, but note that the type of head is never shown,
    -- and the name of the tail is also never shown.
    extendHead (x, m) = (x, m, undefined)
    extendTail (m, t) = (undefined, m, t)
    packNameNecessary (x, _) body (_, t) =
        let (free, body') = (\f -> foldr f (freeVars t, []) body) $
                \(x, _, t) (free, acc) ->
                    (freeVars t `union` delete x free, (x `elem` free):acc)
            head' = x `elem` free
        in head' : body' ++ [False]
    packTypeNecessary (x, _) body (_, t) =
        let (defined, body') = (\f -> foldl f ([x], []) body) $
                \(defined, acc) (x, _, t) ->
                    (x:defined, (any (`elem` defined) (freeVars t)):acc)
            tail' = any (`elem` defined) (freeVars t)
        in False : body' ++ [tail']
    pprFactor ((x, m, t), pprName, pprType) =
        (if pprName then ppr x <+> equals else empty) <+> ppr m <+>
        (if pprType then colon <+> ppr t else empty)

pprUnpack :: (Eq b, Pretty b) => Expr' b -> b -> b -> Expr' b -> Doc
pprUnpack m x y n =
    let (head, names, tail) = splitUnpack (Unpack m x y n)
        names' = hsep (punctuate comma (map ppr names))
    in text "unpack" <+> ppr head <+> equals
        <+> packL <> names' <> packR <+> text "in"
        $$ nest 4 (ppr tail)

pprCoproduct :: (Eq b, Pretty b) => [Type' b] -> Doc
pprCoproduct ts =
    let innards = map ppr ts `seperatedBy` coproductSep
    in coproductL <+> innards <+> coproductR

pprInject :: (Eq b, Pretty b) => Expr' b -> Int -> Type' b -> Doc
pprInject m i t = text "inject" <+> ppr m <+> int i <+> text "into" <+> ppr t

pprCaseOf :: (Eq b, Pretty b) => Expr' b -> [(b, Expr' b)] -> Doc
pprCaseOf m cs =
    let cs' = map (\(x, c) -> char '|' <+> ppr x <+> arrow <+> ppr c) cs
    in text "caseof" <+> ppr m $$ nest 4 (vcat cs')

{-=== Parsing ===============================================================-}

-- | Parse an expression.
parseExpr :: Parser (Expr' String)
parseExpr = parseArrowed
  where
    parseAtomic = choice
        [ parseVar
        , parseStar
        , try parseProduct
        , try parseCoproduct
        , Token.parens tokens parseExpr
        , parsePack
        ]
    parseBasic = choice $
        [ parseAtomic
        , parseLet
        , parseLambda
        , parseMu
        , parseFold
        , parseUnfold
        , parseUnpack
        , parseInject
        , parseCaseof
        ]
    parseApplied = label' "application" $ withSource $ do
        args <- many1 parseBasic
        return (unsplitApply args)
    parseArrowed =  label' "forall type" $ withSource $ do
        argsAndBody <- flip sepBy1 (symbol tokens "->") $ choice
            [ try parseArg -- Uses backtracking because it starts with '(',
                           -- just like a parenthesized atomic expression.
            , (,) "%No-Name%" <$> parseApplied
            ]
        return $ if null (tail argsAndBody)
            then snd (head argsAndBody)
            else unsplitForall (init argsAndBody) (snd (last argsAndBody))

-- | Parse a declaration.
parseDecl :: Parser (Decl' String)
parseDecl = label' "definition" $ do
    reserved tokens "define"
    x <- identifier tokens
    symbol tokens ":"
    t <- parseExpr
    symbol tokens "="
    m <- parseExpr
    return (Decl' x t m)

-- | Parse an entire file full of declarations.
parseFile :: Parser [Decl' String]
parseFile = whiteSpace tokens >> many parseDecl <* eof

tokens :: TokenParser ()
tokens = makeTokenParser $ LanguageDef
    { commentStart = ""
    , commentEnd = ""
    , commentLine = "#"
    , nestedComments = False
    , identStart = letter
    , identLetter = alphaNum <|> Parsec.char '$'
    , opStart = fail "No operators defined."
    , opLetter = fail "No operators defined"
    , reservedNames =
        [ "caseof"
        , "define"
        , "fold"
        , "in"
        , "inject"
        , "into"
        , "let"
        , "mu"
        , "unfold"
        , "unpack"
        ]
    , reservedOpNames = []
    , caseSensitive = True
    }

label' :: String -> Parser a -> Parser a
label' = flip label

parseVar :: Parser (Expr' String)
parseVar = label' "variable" $ withSource $ do
    x <- identifier tokens
    return (Var x)

parseStar :: Parser (Expr' String)
parseStar = label' "star type" $ withSource $ do
    symbol tokens "*"
    return Star

parseLet :: Parser (Expr' String)
parseLet = label' "let expression" $ withSource $ do
    reserved tokens "let"
    x <- identifier tokens
    symbol tokens "="
    m <- parseExpr
    reserved tokens "in"
    n <- parseExpr
    return (Let x m n)

parseLambda :: Parser (Expr' String)
parseLambda = label' "lambda" $ withSource $ do
    symbol tokens "\\"
    parameters <- many1 parseArg
    symbol tokens "."
    body <- parseExpr
    return (unsplitLambda parameters body)

parseMu :: Parser (Type' String)
parseMu = label' "mu type" $ withSource $ do
    reserved tokens "mu"
    x <- identifier tokens
    symbol tokens ":"
    t <- parseExpr
    symbol tokens "."
    s <- parseExpr
    return (Mu x t s)

parseFold :: Parser (Expr' String)
parseFold = label' "fold expression" $ withSource $ do
    reserved tokens "fold"
    m <- parseExpr
    reserved tokens "into"
    t <- parseExpr
    return (Fold m t)

parseUnfold :: Parser (Expr' String)
parseUnfold = label' "unfold expression" $ withSource $ do
    reserved tokens "unfold"
    m <- parseExpr
    return (Unfold m)

parseProduct :: Parser (Type' String)
parseProduct = label' "product type" $ withSource $ do
    symbol tokens "(&"
    factors <- flip sepBy (symbol tokens "&") $ choice
        [ try $ do
            x <- identifier tokens
            symbol tokens ":"
            t <- parseExpr
            return (x, t)
        , do
            t <- parseExpr
            return ("%No-Name%", t)
        ]
    symbol tokens "&)"
    case length factors of
        0 -> return UnitT
        1 -> fail "Product must have 0, 2, or more factors."
        _ -> do
            let tail' = snd (last factors)
            let body' = init factors
            return (unsplitProduct body' tail')

parsePack :: Parser (Expr' String)
parsePack = label' "product expression" $ withSource $ do
    symbol tokens "<|"
    parts <- flip sepBy (symbol tokens ",") $ do
        (x, m) <- choice
            [ try $ do
                x <- identifier tokens
                symbol tokens "="
                m <- parseExpr
                return (x, m)
            , do
                m <- parseExpr
                return ("%No-Name%", m)
            ]
        t <- option UnknownType $ do
            symbol tokens ":"
            parseExpr
        return (x, m, t)
    symbol tokens "|>"
    case length parts of
        0 -> return UnitV
        1 -> fail "Pack must have 0, 2, or more parts."
        _ -> do
            let head' = (\(x, m, _) -> (x, m)) (head parts)
            let tail' = (\(_, m, t) -> (m, t)) (last parts)
            let body' = (init . tail) parts
            return (unsplitPack head' body' tail')

parseUnpack :: Parser (Expr' String)
parseUnpack = label' "unpack expression" $ withSource $ do
    reserved tokens "unpack"
    m <- parseExpr
    symbol tokens "="
    symbol tokens "<|"
    parts <- sepBy (identifier tokens) (symbol tokens ",")
    symbol tokens "|>"
    reserved tokens "in"
    n <- parseExpr
    if length parts < 2
        then fail $ "Unpackings can only be applied to products with "
                 ++ "at least two factors."
        else return (unsplitUnpack m parts n)

parseCoproduct :: Parser (Type' String)
parseCoproduct = label' "coproduct type" $ withSource $ do
    symbol tokens "(|"
    summands <- sepBy parseExpr (symbol tokens "|")
    symbol tokens "|)"
    return (Coproduct summands)

parseInject :: Parser (Expr' String)
parseInject = label' "inject expression" $ withSource $ do
    reserved tokens "inject"
    m <- parseExpr
    i <- fromIntegral <$> natural tokens
    reserved tokens "into"
    t <- parseExpr
    return (Inject m i t)

parseCaseof :: Parser (Expr' String)
parseCaseof = label' "case analysis" $ withSource $ do
    reserved tokens "caseof"
    m <- parseExpr
    cs <- many $ do
        symbol tokens "|"
        x <- identifier tokens
        symbol tokens "->"
        c <- parseExpr
        return (x, c)
    return (CaseOf m cs)

parseArg :: Parser (String, Type' String)
parseArg = Token.parens tokens $ do
    x <- identifier tokens
    symbol tokens ":"
    t <- parseExpr
    return (x, t)

withSource :: Parser (Expr' b) -> Parser (Expr' b)
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
