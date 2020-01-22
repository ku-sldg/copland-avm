Require Import Maps.

Definition BS := nat.

(* Specific AM monad state *)
Record AM_St : Type := mkAM_St
                         { am_nonceMap : Map nat BS;
                           am_nonceId : nat;
                           checked : list nat }.
                                         