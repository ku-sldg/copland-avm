Require Import Maps BS.


Require Import List.
Import ListNotations.


(* Specific AM monad state *)
Record AM_St : Type := mkAM_St
                         { am_nonceMap : MapC nat BS;
                           am_nonceId : nat (* ;
                           st_aspmap : asp_map;
                           st_sigmap : sig_map;
                           (*am_pl : Plc *)(*;
                           checked : list nat*) *) }.

Definition empty_amst :=
  mkAM_St [] 0 (* [] [] *) .
