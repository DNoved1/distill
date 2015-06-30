{-# LANGUAGE LambdaCase #-}

-- | Symbol-expressions; convienent forms in which to serialize in a human
-- readable way abstract syntax trees.
module Distill.SExpr
    ( SExpr(..)
    , SourceLoc(..)
    , ignoringAt
    , parseSExpr
    , pprSExpr
    ) where

import Text.Parsec
import Text.Parsec.String (Parser)
import Text.PrettyPrint (Doc, parens, sep, text)

-- | Source location information, mainly used for helpful error messages.
data SourceLoc = SourceLoc
    { sourceFile        :: String
    , sourceStartCol    :: Int
    , sourceStartLine   :: Int
    , sourceEndCol      :: Int
    , sourceEndLine     :: Int
    }
  deriving (Show, Read)

-- | A symbolic-expression, ala lisp.
data SExpr
    = Atom String
    | List [SExpr]
    -- | Source location information, for error messages.
    | At SExpr SourceLoc
  deriving (Show, Read)

-- | Ignore source location annotations; useful for pattern-matching.
ignoringAt :: SExpr -> SExpr
ignoringAt (At sexpr _) = ignoringAt sexpr
ignoringAt sexpr = sexpr

-- | Parse a symbolic-expression. The first argument determines what
-- characters are allowed in atoms.
parseSExpr :: (Char -> Bool) -> Parser SExpr
parseSExpr allowedAtomChar = parseAtom <|> parseList
  where
    parseAtom = do
        start <- getPosition
        atom <- many1 (satisfy allowedAtomChar)
        end <- getPosition
        spaces
        return (annotateWithSource (Atom atom) start end)
    parseList = do
        start <- getPosition
        char '(' >> spaces
        list <- many (parseSExpr allowedAtomChar)
        char ')'
        end <- getPosition
        spaces
        return (annotateWithSource (List list) start end)
    annotateWithSource expr start end = At expr $ SourceLoc
        { sourceFile = sourceName start
        , sourceStartCol = sourceColumn start
        , sourceStartLine = sourceLine start
        , sourceEndCol = sourceColumn end
        , sourceEndLine = sourceLine end
        }

-- | Pretty-print a symbolic-expression.
pprSExpr :: SExpr -> Doc
pprSExpr = \case
    Atom atom  -> text atom
    List exprs -> parens $ sep $ map pprSExpr exprs
    At expr _  -> pprSExpr expr
