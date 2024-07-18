(* Defining union operations for Manifests and Manifest Environments. *)

Require Import ID_Type Term_Defs_Core Maps String
  Term_Defs Manifest_Admits EqClass ErrorStMonad_Coq.

Require Import Manifest Manifest_Set EnvironmentM.

Require Import List.
Import ListNotations.

Definition manifest_union (m1:Manifest) (m2:Manifest) : Manifest := 
    match (m1, m2) with 
    | ((Build_Manifest myPlc asps1 uuidPlcs1 pubKeyPlcs1 targPlcs1 myPol),
       (Build_Manifest _     asps2 uuidPlcs2 pubKeyPlcs2 targPlcs2 _    )) => 

       Build_Manifest
        myPlc 
        (manset_union asps1 asps2)
        (manset_union uuidPlcs1 uuidPlcs2)
        (manset_union pubKeyPlcs1 pubKeyPlcs2)
        (manset_union targPlcs1 targPlcs2)
        myPol
    end.

Definition environment_union'' (p:Plc) (m1:Manifest) (e2:EnvironmentM) : EnvironmentM := 
  match (map_get e2 p) with 
  | Some m2 => 
    let new_man := manifest_union m2 m1 in  (* m2 first here to preserve plc *)
      map_set e2 p new_man 
  | None => map_set e2 p m1
  end.

                                      (*  B  *)            (*  A  *)        (*  A  *)
Definition env_union_helper (e1_pr:(Plc*Manifest)) (e2:EnvironmentM) : EnvironmentM := 
  environment_union'' (fst e1_pr) (snd e1_pr) e2.


(*
Definition env_union_helper (pr:(Plc*Manifest)) (e:EnvironmentM) : EnvironmentM := 
  environment_union''' e pr.
*)

Definition environment_union (e1:EnvironmentM) (e2:EnvironmentM) : EnvironmentM :=
  fold_right env_union_helper e2 e1.