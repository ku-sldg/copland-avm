(* Defining union operations for Manifests and Manifest Environments. *)

Require Import ID_Type Term_Defs_Core Maps.

Require Import Manifest Manifest_Set EnvironmentM.

Require Import List.
Import ListNotations.

Definition manifest_union_asps (m1:Manifest) (m2:Manifest) : Manifest := 
    match (m1, m2) with 
    | ((Build_Manifest asps1 asp_fs_map1 myPol1),
       (Build_Manifest asps2 _ _)) =>

       Build_Manifest
        (manset_union asps1 asps2)
        asp_fs_map1
        myPol1
    end.

Definition environment_union'' (p:Plc) (m1:Manifest) (e2:EnvironmentM) : EnvironmentM := 
  match (map_get p e2) with 
  | Some m2 => 
    let new_man := manifest_union_asps m2 m1 in  (* m2 first here to preserve plc *)
      map_set p new_man e2
  | None => map_set p m1 e2
  end.

Definition env_union_helper (e1_pr:(Plc*Manifest)) (e2:EnvironmentM) : EnvironmentM := 
  environment_union'' (fst e1_pr) (snd e1_pr) e2.

Definition environment_union (e1:EnvironmentM) (e2:EnvironmentM) : EnvironmentM :=
  fold_right env_union_helper e2 e1.