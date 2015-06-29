-- | Binders with both a human readable string-based name and a integer to
-- make it unique from any others.
module Distill.UniqueName
    ( UniqueName(..)
    , Expr
    , Type
    , Decl
    , nextAvailableUnique
    , renumberUnique
    , prettyUnique
    ) where

import Distill.Expr

-- | Unique human readable names.
data UniqueName = UniqueName String Int
  deriving (Show, Read, Eq, Ord)

type Expr = Expr' UniqueName
type Type = Type' UniqueName
type Decl = Decl' UniqueName

-- | Determine the next unused integer available for forming a unique name.
nextAvailableUnique :: Expr -> Int
nextAvailableUnique = foldr f 0
  where
    f (UniqueName _ num) acc = max (succ num) acc

-- | Change the number of a unique name to create a new one.
renumberUnique :: UniqueName -> Int -> UniqueName
renumberUnique (UniqueName name _) num = UniqueName name num

-- | Show a unique name in a human-readable way.
prettyUnique :: UniqueName -> String
prettyUnique (UniqueName name num) = name ++ "$" ++ show num
