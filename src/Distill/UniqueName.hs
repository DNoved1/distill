-- | Binders with both a human readable string-based name and a integer to
-- make it unique from any others.
module Distill.UniqueName
    ( UniqueName(..)
    , Expr
    , Type
    , Decl
    , nextAvailableUnique
    , renumberUnique
    , pprUnique
    ) where

import Text.PrettyPrint

import Distill.Expr

-- | Unique human readable names.
data UniqueName = UniqueName String Int
  deriving (Show, Read, Eq, Ord)

-- | Expressions specialized on unique names.
type Expr = Expr' UniqueName
-- | Types specialized on unique names.
type Type = Type' UniqueName
-- | Declarations specialized on unique names.
type Decl = Decl' UniqueName

-- | Determine the next unused integer available for forming a unique name.
nextAvailableUnique :: Expr -> Int
nextAvailableUnique = foldr f 0
  where
    f (UniqueName _ num) acc = max (succ num) acc

-- | Change the number of a unique name to create a new one.
renumberUnique :: UniqueName -> Int -> UniqueName
renumberUnique (UniqueName name _) num = UniqueName name num

-- | Pretty print a unique name.
pprUnique :: UniqueName -> Doc
pprUnique (UniqueName name num) = text name <> char '$' <> int num
