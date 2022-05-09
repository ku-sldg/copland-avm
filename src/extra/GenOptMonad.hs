module GenOptMonad where

import qualified Prelude

type Opt a = Prelude.Maybe a

ret :: a1 -> Opt a1
ret a =
  Prelude.Just a

bind :: (Opt a1) -> (a1 -> Opt a2) -> Opt a2
bind m f =
  case m of {
   Prelude.Just v -> f v;
   Prelude.Nothing -> Prelude.Nothing}

failm :: Opt a1
failm =
  Prelude.Nothing

