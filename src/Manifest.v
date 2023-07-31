(* Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import AbstractedTypes Term_Defs_Core Maps Term_Defs Manifest_Admits EqClass.

Require Import List.
Import ListNotations.

Definition CakeML_ASPCallback : Type := 
  ASP_PARAMS -> Plc -> BS -> RawEv -> BS.

Definition CakeML_PubKeyCallback : Type := 
  Plc -> PublicKey.

Definition CakeML_PlcCallback : Type := 
  Plc -> UUID.

Definition CakeML_uuidCallback : Type :=
  UUID -> Plc.

(*
Definition PlcMap := MapC Plc Address.
*)


(** [Manifest] defines an attestation manger, a list of ASPs, and other
   * managers it is aware of (a single AM and its interconnections).
   *)
  Record Manifest := {
    my_abstract_plc   : Plc ; 

    asps              : list ASP_ID ;
    uuidPlcs          : list Plc ;
    pubKeyPlcs        : list Plc ;
    policy            : PolicyT  ;
    (* TO DO: Add privacy and selection policies to manifest? *)
  }.

  Definition empty_Manifest : Manifest :=
    Build_Manifest empty_Manifest_Plc [] [] [] empty_PolicyT.

(** Representation of a system's environment/resources used to populate a 
    ConcreteManifest based on an abstract Manifest. *)
  Record AM_Library := {
    ASPServer_Cb        : ASP_Address -> CakeML_ASPCallback ;
    PubKeyServer_Cb     : ASP_Address -> CakeML_PubKeyCallback ;
    PlcServer_Cb        : ASP_Address -> CakeML_PlcCallback ;
    UUIDServer_Cb       : ASP_Address -> CakeML_uuidCallback ;

    (* Server Addresses *)
    ASPServer_Addr    : ASP_Address ;
    PubKeyServer_Addr : ASP_Address ;
    PlcServer_Addr    : ASP_Address ;
    UUIDServer_Addr   : ASP_Address ;

    (* Local Mappings *)
    Local_ASPS        : MapC ASP_ID CakeML_ASPCallback ;

    Local_Plcs        : MapD Plc UUID ;
    Local_PubKeys     : MapD Plc PublicKey ;
  }.

  
 (* A ConcreteManifest is a refinement of Manifest with concrete parameters
    more suitable for extraction and deployment.  *)
  Record ConcreteManifest := {
    my_plc          : Plc ; 

    (* Local Mappings *)
    Concrete_ASPs         : list ASP_ID ;
    Concrete_Plcs         : MapD Plc UUID ;
    Concrete_PubKeys      : MapD Plc PublicKey ;
(* 
    concrete_asps   : list ASP_ID ;
    concrete_plcs   : list Plc ;
    concrete_pubkeys: list PublicKey ; *)

    ASP_Server      : ASP_Address ;
    PubKey_Server   : ASP_Address ;
    Plc_Server      : ASP_Address ;
    UUID_Server     : ASP_Address ;
  }.



