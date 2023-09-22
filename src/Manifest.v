(* Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import AbstractedTypes Term_Defs_Core Maps String
  Term_Defs Manifest_Admits EqClass ErrorStMonad_Coq.

Require Import List.
Import ListNotations.

Inductive DispatcherErrors : Type :=
| Unavailable   : DispatcherErrors
| Runtime       : StringT -> DispatcherErrors.

Inductive CallBackErrors : Type := 
| messageLift   : StringT -> CallBackErrors.

Definition ASPCallback (ErrType : Type) : Type := 
  ASP_PARAMS -> Plc -> BS -> RawEv -> ResultT BS ErrType.

Definition PubKeyCallback : Type := 
  Plc -> ResultT PublicKey DispatcherErrors.

Definition PlcCallback : Type := 
  Plc -> ResultT UUID DispatcherErrors.

Definition UUIDCallback : Type :=
  UUID -> ResultT Plc DispatcherErrors.

(*
Definition PlcMap := MapC Plc Address.
*)


(** [Manifest] defines an attestation manger, a list of ASPs, and other
   * managers it is aware of (a single AM and its interconnections).
   *)
  Record Manifest := {
    my_abstract_plc   : Plc ; 

    asps              : list ASP_ID ;
    appraisal_asps    : list (Plc * ASP_ID) ;
    uuidPlcs          : list Plc ;
    pubKeyPlcs        : list Plc ;
    targetPlcs        : list Plc ;
    policy            : PolicyT  ;
    (* TO DO: Add privacy and selection policies to manifest? *)
  }.

  Definition empty_Manifest : Manifest :=
    Build_Manifest empty_Manifest_Plc [] [] [] [] [] empty_PolicyT.

(** Representation of a system's environment/resources used to populate a 
    ConcreteManifest based on an abstract Manifest. *)
  Record AM_Library := {
    ASPServer_Cb        : ASP_Address -> (ASPCallback CallBackErrors) ;
    PubKeyServer_Cb     : ASP_Address -> PubKeyCallback ;
    PlcServer_Cb        : ASP_Address -> PlcCallback ;
    UUIDServer_Cb       : ASP_Address -> UUIDCallback ;

    (* Server Addresses *)
    ASPServer_Addr    : ASP_Address ;
    PubKeyServer_Addr : ASP_Address ;
    PlcServer_Addr    : ASP_Address ;
    UUIDServer_Addr   : ASP_Address ;

    (* Local Mappings *)
    Local_ASPS        : MapC ASP_ID (ASPCallback CallBackErrors) ;
    Local_Appraisal_ASPS : MapC (Plc * ASP_ID) (ASPCallback CallBackErrors) ;

    Local_Plcs        : MapD Plc UUID ;
    Local_PubKeys     : MapD Plc PublicKey ;
  }.


  (*
 (* A ConcreteManifest is a refinement of Manifest with concrete parameters
    more suitable for extraction and deployment.  *)
  Record ConcreteManifest := {
    my_plc          : Plc ; 
    Concrete_policy : PolicyT;

    (* Local Mappings *)
    Concrete_ASPs         : list ASP_ID ;
    Concrete_Plcs         : list Plc ;
    Concrete_PubKeys      : list Plc ;
    Concrete_Targets      : list Plc ;

    (* Servers *)
    ASP_Server      : ASP_Address ;
    PubKey_Server   : ASP_Address ;
    Plc_Server      : ASP_Address ;
    UUID_Server     : ASP_Address ;
  }.


  Definition emptyConcreteMan : ConcreteManifest := {|
    my_plc := empty_Manifest_Plc; (* min_id_type; *)
    Concrete_policy := empty_PolicyT;
    Concrete_ASPs := nil;
    Concrete_Plcs := nil;
    Concrete_PubKeys := nil;
    Concrete_Targets := nil;
    ASP_Server := empty_ASP_Address;
    PubKey_Server := empty_ASP_Address;
    Plc_Server := empty_ASP_Address;
    UUID_Server := empty_ASP_Address;
  |}.

*)

Record AM_Config : Type := 
  mkAmConfig {
    absMan : Manifest ;
    aspCb : (ASPCallback DispatcherErrors) ;
    app_aspCb : (ASPCallback DispatcherErrors) ;
    plcCb : PlcCallback ;
    pubKeyCb : PubKeyCallback ;
    uuidCb : UUIDCallback ;
  }.

Definition empty_aspCb (ps:ASP_PARAMS) (p:Plc) (bs:BS) (rawev:RawEv) : ResultT BS DispatcherErrors := 
  errC Unavailable.

  Definition empty_am_config : AM_Config :=
  mkAmConfig 
    empty_Manifest
    empty_aspCb
    empty_aspCb
    (fun x => errC Unavailable)
    (fun x => errC Unavailable)
    (fun x => errC Unavailable).

