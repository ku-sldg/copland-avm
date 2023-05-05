(* Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import Term_Defs_Core Maps Term_Defs Manifest_Admits.

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
    my_abstract_uuid  : UUID ;
    my_abstract_privkey : PrivateKey ;

    asps              : list ASP_ID ;
    knowsOf           : list Plc ;
    pubkeys           : list PublicKey ;
    policy            : PolicyT  ;
    (* TO DO: Add privacy and selection policies to manifest? *)

    (* Server Addresses *)
    ASPServer_Addr    : ASP_Address ;
    PubKeyServer_Addr : ASP_Address ;
    PlcServer_Addr    : ASP_Address ;
    UUIDServer_Addr   : ASP_Address ;

    (* Local Mappings *)
    Local_Plcs        : MapD Plc UUID ;
    Local_PubKeys     : MapD Plc PublicKey ;
  }.

(** Representation of a system's environment/resources used to populate a 
    ConcreteManifest based on an abstract Manifest. *)
  Record AM_Library := {
    Local_ASPS          : MapC ASP_ID CakeML_ASPCallback ;
    ASPServer_Cb        : ASP_Address -> CakeML_ASPCallback ;
    PubKeyServer_Cb     : ASP_Address -> CakeML_PubKeyCallback ;
    PlcServer_Cb        : ASP_Address -> CakeML_PlcCallback ;
    UUIDServer_Cb       : ASP_Address -> CakeML_uuidCallback ;
  }.

  
 (* A ConcreteManifest is a refinement of Manifest with concrete parameters
    more suitable for extraction and deployment.  *)
  Record ConcreteManifest := {
    my_plc          : Plc ; 

    my_uuid         : UUID ;
    my_private_key  : PrivateKey ;

    (* Local Mappings *)
    Concrete_Plcs        : MapD Plc UUID ;
    Concrete_PubKeys     : MapD Plc PublicKey ;
(* 
    concrete_asps   : list ASP_ID ;
    concrete_plcs   : list Plc ;
    concrete_pubkeys: list PublicKey ; *)

    ASP_Server      : ASP_Address ;
    PubKey_Server   : ASP_Address ;
    Plc_Server      : ASP_Address ;
    UUID_Server     : ASP_Address ;
  }.

  (* This function will be a dispatcher for either local ASPS to CakeMLCallback, or pass them off to the ASP_Server *)
  Definition generate_ASP_dispatcher (al : AM_Library) : ConcreteManifest -> CakeML_ASPCallback :=
    let local_asps_map := al.(Local_ASPS) in
    let asp_server_cb := al.(ASPServer_Cb) in
    fun (cman : ConcreteManifest) =>
      let asp_server_addr := cman.(ASP_Server) in
      fun (par : ASP_PARAMS) =>
        let (aspid, args, plc, targ) := par in
          (* check is the ASPID is a local, with a callback *)
          match (map_get local_asps_map aspid) with
          | Some cb => (cb par)
          | None => (asp_server_cb asp_server_addr par)
          end.

  (* This function will lookup for either local Plcs to UUID, or pass them off to the Plc Server *)
  Definition generate_Plc_dispatcher (al : AM_Library) : ConcreteManifest -> CakeML_PlcCallback :=
    let plc_server_cb := al.(PlcServer_Cb) in
    fun (cman : ConcreteManifest) =>
      let local_plc_map := cman.(Concrete_Plcs) in
      let plc_server_addr := cman.(Plc_Server) in
      fun (p : Plc) =>
        (* check is the plc "p" is local, with a reference *)
        match (map_get local_plc_map p) with
        | Some uuid => uuid
        | None => (plc_server_cb plc_server_addr p)
        end.
      
  (* This function will lookup the PubKey either locally Plc -> PublicKey or pass off to PubKeyServer *)
  Definition generate_PubKey_dispatcher (al : AM_Library) : ConcreteManifest -> CakeML_PubKeyCallback :=
    let pubkey_server_cb := al.(PubKeyServer_Cb) in
    fun (cman : ConcreteManifest) =>
      let local_pubkey_map := cman.(Concrete_PubKeys) in
      let pubkey_server_addr := cman.(PubKey_Server) in
      fun (p : Plc) =>
        (* check is the plc "p" is local, with a reference in the pubkey server mapping *)
        match (map_get local_pubkey_map p) with
        | Some key => key
        | None => (pubkey_server_cb pubkey_server_addr p)
        end.

  Definition generate_UUID_dispatcher (al : AM_Library) : ConcreteManifest -> CakeML_uuidCallback :=
    let uuid_server_cb := al.(UUIDServer_Cb) in
    fun (cman : ConcreteManifest) =>
      let local_plc_map := cman.(Concrete_Plcs) in
      let local_uuid_addr := cman.(UUID_Server) in
      fun (u : UUID) =>
        (* check if uuid "u" is local, else dispatch to callback *)
        match (mapD_get_key local_plc_map u) with
        | Some p => p
        | None => (uuid_server_cb local_uuid_addr u)
        end.


  (* This is a rough type signature for the "manifest compiler".  Still some details to be ironed out... *)
  Definition manifest_compiler (m : Manifest) (al : AM_Library) 
    : (ConcreteManifest * 
      (ConcreteManifest -> CakeML_ASPCallback) * 
      (ConcreteManifest -> CakeML_PlcCallback) * 
      (ConcreteManifest -> CakeML_PubKeyCallback) * 
      (ConcreteManifest -> CakeML_uuidCallback)) :=
  (* The output of this function is a Concrete manifest, and a 
  function that can be used like "check_asp_EXTD".
  This function will be used in extraction to either dispatch ASPs to the ASP server, or call a local callback *)
    let asp_cb := (generate_ASP_dispatcher al) in
    let plc_cb := (generate_Plc_dispatcher al) in
    let pubkey_cb := (generate_PubKey_dispatcher al) in
    let uuid_cb := (generate_UUID_dispatcher al) in
    let concrete_man := {|
      my_plc := m.(my_abstract_plc) ;

      my_uuid := m.(my_abstract_uuid) ;
      my_private_key := m.(my_abstract_privkey) ;

      Concrete_Plcs := m.(Local_Plcs) ;
      Concrete_PubKeys := m.(Local_PubKeys) ;

      ASP_Server := m.(ASPServer_Addr) ;
      PubKey_Server := m.(PubKeyServer_Addr);
      Plc_Server := m.(PlcServer_Addr) ;
      UUID_Server := m.(UUIDServer_Addr);
    |} in
      (concrete_man, asp_cb, plc_cb, pubkey_cb, uuid_cb).

