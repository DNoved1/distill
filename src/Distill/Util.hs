{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

-- | Utilities which don't fit in any particular place.
module Distill.Util where

import Control.Monad.State
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

-- | Unsafely unwrap a value of Either a b.
fromRight :: Either a b -> b
fromRight = \case
    Left  _ -> error "'fromRight'"
    Right b -> b

-- | Get the state, modifying it in the process (but the original state is
-- the value returned).
getAndModify :: MonadState s m => (s -> s) -> m s
getAndModify f = get <* modify f
