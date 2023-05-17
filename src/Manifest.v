(* Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import AbstractedTypes Term_Defs_Core Maps Term_Defs Manifest_Admits EqClass List.

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

  (* Reduces a MapC to only include elements that satisfy the condition "f" *)
  Fixpoint minify_mapC {A B : Type} `{HA : EqClass A} (m : MapC A B) (f : A -> bool) : (MapC A B) :=
    match m with
    | nil => nil
    | cons (k,v) tl => if (f k) then cons (k,v) (minify_mapC tl f) else minify_mapC tl f
    end.

  (* Reduces a MapD to only include elements that satisfy the condition "f" *)
  Fixpoint minify_mapD {A B : Type} `{HA : EqClass A} `{HB : EqClass B} (m : MapD A B) (f : A -> bool) : (MapD A B) :=
    match m with
    | nil => nil
    | cons (k,v) tl => if (f k) then cons (k,v) (minify_mapD tl f) else minify_mapD tl f
    end.

  (* This function will be a dispatcher for either local ASPS to CakeMLCallback, or pass them off to the ASP_Server *)
  Definition generate_ASP_dispatcher `{HID : EqClass ID_Type} (al : AM_Library) (am : Manifest)
      : ConcreteManifest -> CakeML_ASPCallback :=
    let local_asps_map := al.(Local_ASPS) in
    let abstract_asps := am.(asps) in
    let shrunk_map := 
      minify_mapC local_asps_map (fun x => if (in_dec (EqClass_impl_DecEq _) x abstract_asps) then true else false) in
    let asp_server_cb := al.(ASPServer_Cb) in
    fun (cman : ConcreteManifest) =>
      let asp_server_addr := cman.(ASP_Server) in
      fun (par : ASP_PARAMS) =>
        let (aspid, args, plc, targ) := par in
          (* check is the ASPID is a local, with a callback *)
          match (map_get shrunk_map aspid) with
          | Some cb => (cb par)
          | None => (asp_server_cb asp_server_addr par)
          end.

  (* This function will lookup for either local Plcs to UUID, or pass them off to the Plc Server *)
  Definition generate_Plc_dispatcher `{HID : EqClass ID_Type} (al : AM_Library) (am : Manifest) 
      : ConcreteManifest -> CakeML_PlcCallback :=
    let plc_server_cb := al.(PlcServer_Cb) in
    fun (cman : ConcreteManifest) =>
      let local_plc_map := cman.(Concrete_Plcs) in
      let abstract_plcs := am.(uuidPlcs) in
      let shrunk_map := 
        minify_mapD local_plc_map (fun x => if (in_dec (EqClass_impl_DecEq _) x abstract_plcs) then true else false) in
      let plc_server_addr := cman.(Plc_Server) in
      fun (p : Plc) =>
        (* check is the plc "p" is local, with a reference *)
        match (map_get shrunk_map p) with
        | Some uuid => uuid
        | None => (plc_server_cb plc_server_addr p)
        end.
      
  (* This function will lookup the PubKey either locally Plc -> PublicKey or pass off to PubKeyServer *)
  Definition generate_PubKey_dispatcher `{HID : EqClass ID_Type} (al : AM_Library) (am : Manifest) 
      : ConcreteManifest -> CakeML_PubKeyCallback :=
    let pubkey_server_cb := al.(PubKeyServer_Cb) in
    fun (cman : ConcreteManifest) =>
      let local_pubkey_map := cman.(Concrete_PubKeys) in
      let abstract_plcs := am.(pubKeyPlcs) in
      let shrunk_map := 
        minify_mapD local_pubkey_map (fun x => if (in_dec (EqClass_impl_DecEq _) x abstract_plcs) then true else false) in
      let pubkey_server_addr := cman.(PubKey_Server) in
      fun (p : Plc) =>
        (* check is the plc "p" is local, with a reference in the pubkey server mapping *)
        match (map_get shrunk_map p) with
        | Some key => key
        | None => (pubkey_server_cb pubkey_server_addr p)
        end.

  Definition generate_UUID_dispatcher `{HID : EqClass ID_Type} (al : AM_Library) (am : Manifest)  
      : ConcreteManifest -> CakeML_uuidCallback :=
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
    let asp_cb := (generate_ASP_dispatcher al m) in
    let plc_cb := (generate_Plc_dispatcher al m) in
    let pubkey_cb := (generate_PubKey_dispatcher al m) in
    let uuid_cb := (generate_UUID_dispatcher al m) in
    let concrete_man := {|
      my_plc := m.(my_abstract_plc) ;

      Concrete_Plcs := al.(Local_Plcs) ;
      Concrete_PubKeys := al.(Local_PubKeys) ;

      ASP_Server := al.(ASPServer_Addr) ;
      PubKey_Server := al.(PubKeyServer_Addr);
      Plc_Server := al.(PlcServer_Addr) ;
      UUID_Server := al.(UUIDServer_Addr);
    |} in
      (concrete_man, asp_cb, plc_cb, pubkey_cb, uuid_cb).

