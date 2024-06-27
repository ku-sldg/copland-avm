(*  (Mostly experimental) combination of Manifest Generation for both Attestation and Appraisal.
      Uses the (as-yet-unverified) manifest environment union operation to merge manifests 
      generated for combined Attestation and Appraisal scenarios.        *)

Require Import Term_Defs_Core Params_Admits Manifest
               Example_Phrases_Admits Example_Phrases_Pre_Admits Example_Phrases Eqb_Evidence
               Manifest_Generator_Helpers Term_Defs ErrorStMonad_Coq.

Require Import EqClass Maps StructTactics.

Require Import EnvironmentM Manifest_Set JSON Serializable.

Require Import Manifest_Union Manifest_Generator Cvm_St Cvm_Impl.

Require Import Manifest Manifest_Compiler Manifest_Generator_Facts.

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

(*
Definition mangen_app_plc (et:Evidence) (p:Plc) : Manifest := 
  manifest_union (empty_Manifest_plc p) (manifest_generator_app et p).
  *)

Definition lift_manifest_to_env (m:Manifest) : EnvironmentM := 
  map_set e_empty (my_abstract_plc m) m.

Definition manifest_generator_plcEvidence_list (ls:list (Evidence*Plc)) : list EnvironmentM := 
  List.map (fun '(et,p) => manifest_generator_app et p) ls.

(*
  let ms : list Manifest := List.map (fun '(et,p) => mangen_app_plc et p) ls in 
    List.map lift_manifest_to_env ms.
*)


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

(*
Definition knowsof_myPlc_manifest_update (m:Manifest) : Manifest :=
  knowsof_manifest_update (my_abstract_plc m) m.
*)

Definition Evidence_Plc_list := list (Evidence*Plc).
Open Scope string_scope.

Definition Evidence_Plc_list_to_JSON (ls: Evidence_Plc_list) : JSON :=
  JSON_Object [
    ("Evidence_Plc_list",
      (InJSON_Array 
        (List.map 
          (fun '(et,p) => 
            InJSON_Array [
              InJSON_Object (to_JSON et); 
              InJSON_String (to_string p)
            ]
          ) ls)
      )
    )].

Definition Evidence_Plc_list_from_JSON (js : JSON) 
    : ResultT Evidence_Plc_list string :=
  match (JSON_get_Array "Evidence_Plc_list" js) with
  | resultC jsArr =>
    let res := result_map (fun js => 
      match js with
      | InJSON_Array [InJSON_Object jsEt; InJSON_String jsP] =>
        match (from_JSON jsEt), (from_string jsP) with
        | resultC et,resultC p => resultC (et, p)
        | _, _ => errC "Error in parsing Evidence_Plc_list"
        end
      | _ => errC "Not a pair"
      end
    ) jsArr in
    match res with
    | resultC res => resultC res
    | errC e => errC e
    end
  | errC e => errC e 
  end.

Global Instance Jsonifiable_Evidence_Plc_list : Jsonifiable Evidence_Plc_list := {
  to_JSON := Evidence_Plc_list_to_JSON;
  from_JSON := Evidence_Plc_list_from_JSON
}.

Definition Term_Plc_list := list (Term*Plc).

Definition Term_Plc_list_to_JSON (ls: Term_Plc_list) : JSON :=
  JSON_Object [
    ("Term_Plc_list",
      (InJSON_Array 
        (List.map 
          (fun '(et,p) => 
            InJSON_Array [
              InJSON_Object (to_JSON et); 
              InJSON_String (to_string p)
            ]
          ) ls)
      )
    )].

Definition Term_Plc_list_from_JSON (js : JSON) 
    : ResultT Term_Plc_list string :=
  match (JSON_get_Array "Term_Plc_list" js) with
  | resultC jsArr =>
    let res := result_map (fun js => 
      match js with
      | InJSON_Array [InJSON_Object jsTerm; InJSON_String jsP] =>
        match (from_JSON jsTerm), (from_string jsP) with
        | resultC et,resultC p => resultC (et, p)
        | _, _ => errC "Error in parsing Term_Plc_list"
        end
      | _ => errC "Not a pair"
      end
    ) jsArr in
    match res with
    | resultC res => resultC res
    | errC e => errC e
    end
  | errC e => errC e 
  end.

Global Instance Jsonifiable_Term_Plc_list : Jsonifiable Term_Plc_list := {
  to_JSON := Term_Plc_list_to_JSON;
  from_JSON := Term_Plc_list_from_JSON
}.

Definition knowsof_myPlc_manifest_update_env' (p:(Plc*Manifest)) : (Plc*Manifest) := 
  (fst p, (knowsof_myPlc_manifest_update (snd p))).

Definition update_knowsOf_myPlc_env (env:EnvironmentM) : EnvironmentM := map knowsof_myPlc_manifest_update_env' env.

Definition update_pubkeys_env' (pubs:manifest_set Plc) (p:(Plc*Manifest)) : (Plc*Manifest) := 
  (fst p, (pubkeys_manifest_update pubs (snd p))).

Definition update_pubkeys_env (pubs:manifest_set Plc) (env:EnvironmentM) : EnvironmentM := 
  map (update_pubkeys_env' pubs) env.

Definition end_to_end_mangen' (ls: Evidence_Plc_list) (ts: Term_Plc_list) : EnvironmentM := 
    let app_env := mangen_plcEvidence_list_union ls in (* singleton_plc_appraisal_environmentM myPlc ls in  *)
    let att_env := mangen_plcTerm_list_union ts in 
      environment_union app_env att_env.

Definition manset_union_list{A : Type} `{HA : EqClass A} 
  (lss: manifest_set (manifest_set A)) : manifest_set A := 
    fold_right manset_union [] lss.

Definition get_all_unique_places (ls: Term_Plc_list) (ets: Evidence_Plc_list) : manifest_set Plc := 
  let lss := map (fun '(t,p) => places_manset p t) ls in 
  let ts_ps := manset_union_list lss in
  let ets_ps := map (fun '(et,p) => p) ets in
  (* let ts_res_dup := concat lss in  *)
  manset_union ts_ps ets_ps.

Definition end_to_end_mangen (ls: Evidence_Plc_list) (ts: Term_Plc_list) : EnvironmentM := 
  let ps := get_all_unique_places ts ls in 
    update_pubkeys_env ps (update_knowsOf_myPlc_env (end_to_end_mangen' ls ts)).



Definition end_to_end_mangen_final (ls: Evidence_Plc_list) (ts: Term_Plc_list) : list Manifest :=
  environment_to_manifest_list (end_to_end_mangen ls ts).


(*
Definition appraiser_evidence_demo_phrase : Evidence := 
  eval example_phrase P0 (nn O).

Definition test_end_to_end_mangen : EnvironmentM := 
  let ets : list (Evidence*Plc) := [(appraiser_evidence_demo_phrase, P4)] in 
  let ts : list (Term*Plc) := [(example_phrase, P0)] in
  end_to_end_mangen ets ts.

Definition get_all_unique_places (ls: list (Term*Plc)) (ets: list (Evidence*Plc)) : list Plc := 
    let lss := map (fun '(t,p) => places p t) ls in 
    let ets_ps := map (fun '(et,p) => p) ets in
    let ts_res_dup := concat lss in 
    dedup_list (ts_res_dup ++ ets_ps).

 
Definition end_to_end_mangen_final (ls:list (Evidence*Plc)) (ts: list (Term*Plc)) : list Manifest := 
    let env : EnvironmentM := end_to_end_mangen ls ts in 
    let unique_plcs : list Plc := get_all_unique_places ts ls in 
    let res' := map knowsof_myPlc_manifest_update (get_unique_manifests_env' unique_plcs env) in 
        map (pubkeys_manifest_update (list_to_manset unique_plcs)) res'. 

Locate get_unique_manifests_env'.

*)