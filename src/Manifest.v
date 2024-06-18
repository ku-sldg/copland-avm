(* 
   Core definitions of the Manifest, AM_Library, and AM_Config datatypes.

   Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import AbstractedTypes Term_Defs_Core Maps
  Term_Defs Manifest_Admits EqClass ErrorStMonad_Coq.

Require Import Example_Phrases_Admits.

Require Import Manifest_Set StringT ErrorStringConstants.

Require Import List.
Import ListNotations.

Inductive ASP_Locator :=
| Local_ASP : FS_Location -> ASP_Locator
| Remote_ASP : UUID -> ASP_Locator.

Inductive DispatcherErrors : Type :=
| Unavailable   : DispatcherErrors
| Runtime       : StringT -> DispatcherErrors.

Inductive CallBackErrors : Type := 
| messageLift   : StringT -> CallBackErrors.

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
    Lib_Plcs            : MapD Plc UUID ;
    Lib_PubKeys         : MapD Plc PublicKey ;
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

