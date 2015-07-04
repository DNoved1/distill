{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

-- | Utilities which don't fit in any particular place.
module Distill.Util where

import Text.PrettyPrint

-- | Class of objects which can be pretty-printed.
class Pretty a where
    -- | Pretty-print an object.
    ppr :: a -> Doc

instance Pretty String where
    ppr = text

-- | Convert a pretty-printable object directly to a string.
prettyShow :: Pretty a => a -> String
prettyShow = render . ppr

fromRight :: Either a b -> b
fromRight = \case
    Left  a -> error "'fromRight'"
    Right b -> b
