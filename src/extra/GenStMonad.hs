module GenStMonad where

import qualified Prelude
import qualified Datatypes

type St s a = s -> (,) (Prelude.Maybe a) s

ret :: a2 -> St a1 a2
ret a s =
  (,) (Prelude.Just a) s

bind :: (St a1 a2) -> (a2 -> St a1 a3) -> St a1 a3
bind m f s =
  case m s of {
   (,) a s' ->
    case a of {
     Prelude.Just v -> f v s';
     Prelude.Nothing -> (,) Prelude.Nothing s'}}

modify :: (a1 -> a1) -> St a1 ()
modify f s =
  (,) (Prelude.Just ()) (f s)

put :: a1 -> St a1 ()
put s _ =
  (,) (Prelude.Just ()) s

get :: St a1 a1
get s =
  (,) (Prelude.Just s) s

execSt :: (St a1 a2) -> a1 -> a1
execSt h s =
  Datatypes.snd (h s)

