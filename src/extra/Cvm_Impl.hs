module Impl_VM where

import qualified Prelude
import qualified Anno_Term_Defs
import qualified GenStMonad
import qualified MonadVM
import qualified StVM

copland_compile :: Anno_Term_Defs.AnnoTermPar -> StVM.CVM ()
copland_compile t =
  case t of {
   Anno_Term_Defs.Coq_aasp_par a ->
    GenStMonad.bind (MonadVM.do_prim a) MonadVM.put_ev;
   Anno_Term_Defs.Coq_aatt_par q t' ->
    GenStMonad.bind MonadVM.get_ev (\e ->
      GenStMonad.bind (MonadVM.doRemote t' q e) MonadVM.put_ev);
   Anno_Term_Defs.Coq_alseq_par t1 t2 ->
    GenStMonad.bind (copland_compile t1) (\_ -> copland_compile t2);
   Anno_Term_Defs.Coq_abseq_par sp t1 t2 ->
    GenStMonad.bind (MonadVM.split_ev sp) (\pr ->
      case pr of {
       (,) e1 e2 ->
        GenStMonad.bind (MonadVM.put_ev e1) (\_ ->
          GenStMonad.bind (copland_compile t1) (\_ ->
            GenStMonad.bind MonadVM.get_ev (\e1r ->
              GenStMonad.bind (MonadVM.put_ev e2) (\_ ->
                GenStMonad.bind (copland_compile t2) (\_ ->
                  GenStMonad.bind MonadVM.get_ev (\e2r ->
                    MonadVM.join_seq e1r e2r))))))});
   Anno_Term_Defs.Coq_abpar_par loc sp t1 t2 ->
    GenStMonad.bind (MonadVM.split_ev sp) (\pr ->
      case pr of {
       (,) e1 e2 ->
        GenStMonad.bind (MonadVM.start_par_thread loc t2 e2) (\_ ->
          GenStMonad.bind (MonadVM.put_ev e1) (\_ ->
            GenStMonad.bind (copland_compile t1) (\_ ->
              GenStMonad.bind MonadVM.get_ev (\e1r ->
                GenStMonad.bind (MonadVM.wait_par_thread loc t2 e2) (\e2r ->
                  MonadVM.join_par e1r e2r)))))})}

