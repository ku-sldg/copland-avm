Require Import Manifest ResultT String.

Record AM_Manager_Config := 
  mkAM_Man_Conf {
  am_manager_manifest   : Manifest ;
  am_manager_asp_bin    : FS_Location ;
  am_manager_uuid       : UUID ;
}.

Record AM_Manager_St := 
  mkAM_Manager_St {
    am_manager_config : AM_Manager_Config;
  }.

Inductive AM_Manager_Error :=
| am_manager_error : string -> AM_Manager_Error.

Definition AM_Manager A := (ResultT (A * AM_Manager_St) AM_Manager_Error).

