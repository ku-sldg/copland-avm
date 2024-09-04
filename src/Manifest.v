(* 
   Core definitions of the Manifest, AM_Library, and AM_Config datatypes.

   Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import ID_Type Term_Defs_Core Maps.
Require Export Manifest_Admits.

Require Import Manifest_Set.

Require Import List.
Import ListNotations.

(* ASP Locator JSON Admits *)
(* NOTE: Dropping this concept for now, it is viable, but does not have real use
Definition JSON_Local_ASP : string := "Local_ASP". 
Definition JSON_Remote_ASP : string := "Remote_ASP".

Inductive ASP_Locator :=
| Local_ASP : FS_Location -> ASP_Locator
| Remote_ASP : UUID -> ASP_Locator.

Global Instance jsonifiable_ASP_Locator : Jsonifiable ASP_Locator :=
  {
    to_JSON := (fun v => 
                  match v with
                  | Local_ASP loc => 
                      JSON_Object 
                        [(JSON_Local_ASP, (InJSON_String (to_string loc)))]
                  | Remote_ASP uuid => 
                      JSON_Object 
                        [(JSON_Remote_ASP, (InJSON_String (to_string uuid)))]
                  end);
    from_JSON := (fun js => 
                    match (JSON_get_string JSON_Local_ASP js) with
                    | resultC loc => 
                      match (from_string loc) with
                      | resultC loc' => resultC (Local_ASP loc')
                      | errC e => errC e
                      end
                    | errC e => 
                      match (JSON_get_string JSON_Remote_ASP js) with
                      | resultC uuid =>
                        match (from_string uuid) with
                        | resultC uuid' => resultC (Remote_ASP uuid')
                        | errC e => errC e
                        end
                      | errC e => errC e
                      end
                    end)
  }.
*)

Definition PolicyT := list (Plc * ASP_ID).

(** [Manifest] defines an attestation manger, a list of ASPs, and other
   * managers it is aware of (a single AM and its interconnections).
   *)
  Record Manifest := {
    asps              : manifest_set ASP_ID; 
    ASP_Mapping       : Map ASP_ID FS_Location;
    man_policy        : PolicyT  ;
    (* TO DO: Add privacy and selection policies to manifest? *)
  }.

  Definition empty_Manifest : Manifest :=
    Build_Manifest nil nil nil.

