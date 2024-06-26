(* 
   Core definitions of the Manifest, AM_Library, and AM_Config datatypes.

   Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import AbstractedTypes Term_Defs_Core Maps
  Term_Defs EqClass ErrorStMonad_Coq JSON.
Require Export Manifest_Admits.

Require Import Example_Phrases_Admits.

Require Import Manifest_Set String ErrorStringConstants.

Require Import List.
Import ListNotations.

(* ASP Locator JSON Admits *)
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

Inductive DispatcherErrors : Type :=
| Unavailable   : DispatcherErrors
| Runtime       : string -> DispatcherErrors.

Inductive CallBackErrors : Type := 
| messageLift   : string -> CallBackErrors.

Definition ASPCallback (ErrType : Type) : Type := 
  ASP_PARAMS -> RawEv -> ResultT RawEv ErrType.

Definition PubKeyCallback : Type := 
  Plc -> ResultT PublicKey DispatcherErrors.

Definition PlcCallback : Type := 
  Plc -> ResultT UUID DispatcherErrors.

Definition UUIDCallback : Type :=
  UUID -> ResultT Plc DispatcherErrors.

Definition PolicyT : Set :=  list (Plc * ASP_ID).

Definition empty_PolicyT : PolicyT := [].
  (* [(P0, attest_id)]. *)


(** [Manifest] defines an attestation manger, a list of ASPs, and other
   * managers it is aware of (a single AM and its interconnections).
   *)
  Record Manifest := {
    my_abstract_plc   : Plc ; 

    asps              : manifest_set ASP_ID; 
    appraisal_asps    : manifest_set (Plc * ASP_ID) ;
    uuidPlcs          : manifest_set Plc ;
    pubKeyPlcs        : manifest_set Plc ;
    targetPlcs        : manifest_set Plc ;
    policy            : PolicyT  ;
    (* TO DO: Add privacy and selection policies to manifest? *)
  }.

  Definition empty_Manifest : Manifest :=
    Build_Manifest 
      empty_Manifest_Plc 
      manifest_set_empty
      manifest_set_empty
      manifest_set_empty
      manifest_set_empty
      manifest_set_empty
      empty_PolicyT.

(** Representation of a system's environment/resources used to populate an 
    AM Config based on a Manifest. *)
  Record AM_Library := {
    (* NOTE: What is this and why is it necessary? *)
    UUID_AM_Clone : UUID ;

    (* Local Mappings *)
    Lib_ASPS            : MapC ASP_ID ASP_Locator ;
    Lib_Appraisal_ASPS  : MapC (Plc * ASP_ID) ASP_Locator ;
    Lib_Plcs            : MapC Plc UUID ;
    Lib_PubKeys         : MapC Plc PublicKey ;
  }.

Record AM_Config : Type := 
  mkAmConfig {
    absMan : Manifest ;
    am_clone_addr : UUID ;
    aspCb : (ASPCallback DispatcherErrors) ;
    app_aspCb : (ASPCallback DispatcherErrors) ;
    plcCb : PlcCallback ;
    pubKeyCb : PubKeyCallback ;
  }.

Definition empty_aspCb (ps:ASP_PARAMS) (rawev:RawEv) 
    : ResultT RawEv DispatcherErrors := 
  errC Unavailable.

  Definition empty_am_config : AM_Config :=
  mkAmConfig 
    empty_Manifest
    default_uuid
    empty_aspCb
    empty_aspCb
    (fun x => errC Unavailable)
    (fun x => errC Unavailable).

