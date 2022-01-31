{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module ExtLib_Monad where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
#if __GLASGOW_HASKELL__ >= 900
unsafeCoerce = GHC.Exts.unsafeCoerce#
#else
unsafeCoerce = GHC.Base.unsafeCoerce#
#endif
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

data Monad m =
   Build_Monad (() -> Any -> m) (() -> () -> m -> (Any -> m) -> m)

ret :: (Monad a1) -> a2 -> a1
ret monad x =
  case monad of {
   Build_Monad ret0 _ -> unsafeCoerce ret0 __ x}

bind :: (Monad a1) -> a1 -> (a2 -> a1) -> a1
bind monad x x0 =
  case monad of {
   Build_Monad _ bind0 -> unsafeCoerce bind0 __ __ x x0}

