(*  (Mostly experimental) combination of Manifest Generation for both Attestation and Appraisal.
      Uses the (as-yet-unverified) manifest environment union operation to merge manifests 
      generated for combined Attestation and Appraisal scenarios.        *)

Require Import Term_Defs_Core Manifest.

Require Import EqClass.

Require Import EnvironmentM JSON Stringifiable.

Require Import Manifest_Union Manifest_Generator.

Require Import List.
Import ListNotations.

Definition manifest_generator_plcTerm_list (ls:list (Term*Plc)) : list EnvironmentM := 
    List.map (fun '(t,p) => manifest_generator t p) ls.

Definition env_list_union (ls:list EnvironmentM) : EnvironmentM := 
    fold_right environment_union e_empty ls.

Definition mangen_plcTerm_list_union (ls:list (Term*Plc)) : EnvironmentM := 
    env_list_union (manifest_generator_plcTerm_list ls).

Definition manifest_generator_plcEvidenceT_list (comp_map : ASP_Compat_MapT) 
    (ls:list (EvidenceT*Plc)) : ResultT (list EnvironmentM) string := 
  result_map (fun '(et,p) => manifest_generator_app comp_map et p) ls.

Definition mangen_plcEvidenceT_list_union (comp_map : ASP_Compat_MapT) 
    (ls:list (EvidenceT*Plc)) : ResultT EnvironmentM string := 
  match (manifest_generator_plcEvidenceT_list comp_map ls) with
  | resultC ls' => resultC (env_list_union ls')
  | errC e => errC e
  end.

Definition EvidenceT_Plc_list := list (EvidenceT*Plc).
Open Scope string_scope.

Definition EvidenceT_Plc_list_to_JSON `{Jsonifiable EvidenceT} (ls: EvidenceT_Plc_list) : JSON := 
  JSON_Object [
    ("EvidenceT_Plc_list",
      (JSON_Array 
        (List.map 
          (fun '(et,p) => 
            JSON_Array [
              to_JSON et;
              JSON_String (to_string p)
            ]
          ) ls)
      )
    )].

Definition EvidenceT_Plc_list_from_JSON `{Jsonifiable EvidenceT, Jsonifiable ASP_Compat_MapT} (js : JSON) 
    : ResultT EvidenceT_Plc_list string :=
  match (JSON_get_Array "EvidenceT_Plc_list" js) with
  | resultC jsArr =>
    let res := result_map (fun js => 
      match js with
      | JSON_Array [jsEt; JSON_String jsP] =>
        match (from_JSON jsEt), (from_string jsP) with
        | resultC et,resultC p => resultC (et, p)
        | _, _ => errC "Error in parsing EvidenceT_Plc_list"
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

Global Instance Jsonifiable_EvidenceT_Plc_list `{Jsonifiable EvidenceT} : Jsonifiable EvidenceT_Plc_list.
eapply Build_Jsonifiable with 
  (to_JSON := EvidenceT_Plc_list_to_JSON)
  (from_JSON := EvidenceT_Plc_list_from_JSON).
unfold EvidenceT_Plc_list_to_JSON, EvidenceT_Plc_list_from_JSON;
induction a; simpl in *; intuition;
repeat (try break_match; simpl in *; subst; try congruence);
repeat rewrite canonical_jsonification in *; try congruence;
repeat find_injection; eauto.
Defined.

Definition Term_Plc_list := list (Term*Plc).

Definition Term_Plc_list_to_JSON `{Jsonifiable Term} (ls: Term_Plc_list) : JSON :=
  JSON_Object [
    ("Term_Plc_list",
      (JSON_Array 
        (List.map 
          (fun '(et,p) => 
            JSON_Array [ to_JSON et; JSON_String (to_string p) ]
          ) ls)
      )
    )].

Definition Term_Plc_list_from_JSON `{Jsonifiable Term} (js : JSON) 
    : ResultT Term_Plc_list string :=
  match (JSON_get_Array "Term_Plc_list" js) with
  | resultC jsArr =>
    let res := result_map (fun js => 
      match js with
      | JSON_Array [jsTerm; JSON_String jsP] =>
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
Close Scope string_scope.

Global Instance Jsonifiable_Term_Plc_list `{Jsonifiable Term} : Jsonifiable Term_Plc_list.
eapply Build_Jsonifiable with 
  (to_JSON := Term_Plc_list_to_JSON)
  (from_JSON := Term_Plc_list_from_JSON).
unfold Term_Plc_list_from_JSON, Term_Plc_list_to_JSON;
simpl in *.
induction a; simpl in *; intuition;
repeat (try break_match; simpl in *; subst; try congruence);
repeat rewrite canonical_jsonification in *; try congruence;
repeat find_injection; eauto.
Defined.

Definition end_to_end_mangen (comp_map : ASP_Compat_MapT) 
    (ls: EvidenceT_Plc_list) (ts: Term_Plc_list) 
    : ResultT EnvironmentM string := 
  let app_env := mangen_plcEvidenceT_list_union comp_map ls in
  let att_env := mangen_plcTerm_list_union ts in 
  match app_env with
  | resultC app_env => resultC (environment_union app_env 
      (Maps.map_map (fun m => add_compat_map_manifest m comp_map) att_env))
  | errC e => errC e
  end.

Definition manset_union_list{A : Type} `{HA : EqClass A} 
  (lss: manifest_set (manifest_set A)) : manifest_set A := 
    fold_right manset_union [] lss.

Definition end_to_end_mangen_final (comp_map : ASP_Compat_MapT) 
    (ls: EvidenceT_Plc_list) (ts: Term_Plc_list) 
    : ResultT (list Manifest) string :=
  match (end_to_end_mangen comp_map ls ts) with
  | resultC env => resultC (environment_to_manifest_list env)
  | errC e => errC e
  end.
