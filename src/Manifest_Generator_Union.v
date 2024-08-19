(*  (Mostly experimental) combination of Manifest Generation for both Attestation and Appraisal.
      Uses the (as-yet-unverified) manifest environment union operation to merge manifests 
      generated for combined Attestation and Appraisal scenarios.        *)

Require Import Term_Defs_Core Manifest.

Require Import EqClass.

Require Import EnvironmentM JSON Stringifiable.

Require Import Manifest_Union Manifest_Generator.

Require Import List.
Import ListNotations.

Open Scope string_scope.

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

Definition end_to_end_mangen (G : GlobalContext) (ts: Term_Plc_list) 
    : ResultT EnvironmentM string := 
  result_fold (fun '(t,p) => fun env =>
    manifest_generator G p t) e_empty ts.

