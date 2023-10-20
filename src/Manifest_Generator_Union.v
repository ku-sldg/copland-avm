Require Import Term_Defs_Core Params_Admits Manifest (* Executable_Dec *)
               Example_Phrases_Admits Example_Phrases Eqb_Evidence
               Manifest_Generator_Helpers Term_Defs ErrorStMonad_Coq.
               (* Executable_Defs_Prop. *)

Require Import EqClass Maps StructTactics.

Require Import EnvironmentM Manifest_Set.

Require Import Manifest_Union Manifest_Generator Cvm_St Cvm_Impl.

Require Import Manifest ManCompSoundness Manifest_Compiler Manifest_Generator_Facts.

Require Import Coq.Program.Tactics.
Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)


(*
Definition manifest_generator_union (p:Plc) (t:Term) (e:EnvironmentM) : EnvironmentM :=
  match t with
  | asp a => asp_manifest_generator a p e
  | att q t' => 
      let e' := at_manifest_generator p q e in 
        manifest_generator' q t' e'
  | lseq t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 e)
  | bseq _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 e)
  | bpar _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 e)
  end.

*)




(*
Definition manifest_generator_terms (p:Plc) (ts:list Term) : EnvironmentM :=
  fold_right (manifest_generator' p) e_empty ts.
*)


(*
Check map.
map
	 : forall A B : Type, (A -> B) -> list A -> list B
*)
             
Definition manifest_generator_plcTerm_list (ls:list (Term*Plc)) : list EnvironmentM := 
    List.map (fun '(t,p) => manifest_generator t p) ls.

(* fold_right (fun '(t,p) => manifest_generator' p t) e_empty ls. *)


(*
Check fold_right.
fold_right
	 : forall A B : Type, (B -> A -> A) -> A -> list B -> A
*)

Definition env_list_union (ls:list EnvironmentM) : EnvironmentM := 
    fold_right environment_union e_empty ls.

Definition mangen_plcTerm_list_union (ls:list (Term*Plc)) : EnvironmentM := 
    env_list_union (manifest_generator_plcTerm_list ls).

Definition empty_Manifest_plc (myPlc:Plc) : Manifest :=
  Build_Manifest 
      myPlc 
      manifest_set_empty
      manifest_set_empty
      manifest_set_empty
      manifest_set_empty
      manifest_set_empty
      empty_PolicyT.

Definition mangen_app_plc (et:Evidence) (p:Plc) : Manifest := 
  manifest_union (empty_Manifest_plc p) (manifest_generator_app et).

Definition lift_manifest_to_env (m:Manifest) : EnvironmentM := 
  map_set e_empty (my_abstract_plc m) m.

Definition manifest_generator_plcEvidence_list (ls:list (Evidence*Plc)) : list EnvironmentM := 
  let ms : list Manifest := List.map (fun '(et,p) => mangen_app_plc et p) ls in 
    List.map lift_manifest_to_env ms.


Definition mangen_plcEvidence_list_union (ls:list (Evidence*Plc)) : EnvironmentM := 
  env_list_union (manifest_generator_plcEvidence_list ls).








(*
Definition man_list_union (myPlc:Plc) (ls: list Manifest) : Manifest := 
    fold_right manifest_union (empty_Manifest_plc myPlc) ls.


Definition manifest_generator_evidence_list (ls:list Evidence) : list Manifest := 
    List.map (fun et => manifest_generator_app et) ls.

Definition mangen_evidence_list_union (myPlc:Plc) (ls:list Evidence) : Manifest := 
    man_list_union myPlc (manifest_generator_evidence_list ls). 

Definition singleton_plc_appraisal_environmentM (myPlc:Plc) (ls:list Evidence) : EnvironmentM := 
    let daMan := mangen_evidence_list_union myPlc ls in 
    map_set e_empty myPlc daMan.

*)



(*
Definition manifest_generator_app (et:Evidence) : Manifest := ...
*)

Definition end_to_end_mangen (ls:list (Evidence*Plc)) (ts: list (Term*Plc)) : EnvironmentM := 
    let app_env := mangen_plcEvidence_list_union ls in (* singleton_plc_appraisal_environmentM myPlc ls in  *)
    let att_env := mangen_plcTerm_list_union ts in 
    environment_union app_env att_env.

(*
asdf 
TODO:  generalize singleton_plc_appraisal_environmentM for multiple appraisal places 
            (: list (Evidence* Plc))
*)


Definition get_all_unique_places (ls: list (Term*Plc)) : list Plc := 
    let lss := map (fun '(t,p) => places p t) ls in 
    let res_dup := concat lss in 
    dedup_list res_dup.


Definition end_to_end_mangen_final (ls:list (Evidence*Plc)) (ts: list (Term*Plc)) : list Manifest := 
    let env : EnvironmentM := end_to_end_mangen ls ts in 
    let unique_plcs : list Plc := get_all_unique_places ts in 
    let res' := map knowsof_myPlc_manifest_update (get_unique_manifests_env' unique_plcs env) in 
        map (pubkeys_manifest_update (list_to_manset unique_plcs)) res'. 



Definition get_final_manifests_env (ts:list Term) (p:Plc) (e:EnvironmentM) : list Manifest :=
    let ms := get_unique_manifests_env ts p e in 
    let ms' := List.map (knowsof_myPlc_manifest_update) ms in
    List.map (pubkeys_manifest_update (list_to_manset (places_terms ts p))) ms'.



(* 


Definition knowsof_myPlc_manifest_update (m:Manifest) : Manifest :=
  knowsof_manifest_update (my_abstract_plc m) m.



Check concat.
concat: forall [A : Type], list (list A) -> list A

Check concat_map.
concat_map
	 : forall (A B : Type) (f : A -> B) (l : list (list A)),
       map f (concat l) = concat (map (map f) l)



Check places.
places
	 : Plc -> Term -> list Plc

Definition places_terms' (ts: list Term) (p:Plc) : list (list Plc) :=
  List.map (places p) ts.

Definition places_terms (ts:list Term) (p:Plc) : list Plc :=
  dedup_list (List.concat (places_terms' ts p)).

Definition fromSome{A:Type} (v:option A) (a:A) : A :=
  match v with 
  | Some v' => v'
  | _ => a 
  end.

Definition get_manifest_env_default (e:EnvironmentM) (p:Plc) : Manifest :=
  let m' := fromSome (map_get e p) empty_Manifest in
    myPlc_manifest_update p m'.

Definition get_unique_manifests_env' (ps:list Plc) (e:EnvironmentM) : list Manifest :=
  List.map (get_manifest_env_default e) ps.

Definition get_unique_manifests_env (ts: list Term) (p:Plc) (e:EnvironmentM) : list Manifest :=
  let ps := places_terms ts p in
    get_unique_manifests_env' ps e.

Definition get_final_manifests_env (ts:list Term) (p:Plc) (e:EnvironmentM) : list Manifest :=
  let ms := get_unique_manifests_env ts p e in 
  let ms' := List.map (knowsof_myPlc_manifest_update) ms in
  List.map (pubkeys_manifest_update (list_to_manset (places_terms ts p))) ms'.


*)