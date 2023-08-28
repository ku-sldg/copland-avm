  
Require Import Maps AbstractedTypes EqClass Term_Defs_Core Manifest_Admits Manifest
  ErrorStMonad_Coq Term_Defs.
  

Require Import List.
Import ListNotations.
  
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
      : ConcreteManifest -> (CakeML_ASPCallback DispatcherErrors) :=
    let local_asps_map := al.(Local_ASPS) in
    let abstract_asps := am.(asps) in
    let shrunk_map : (MapC ASP_ID (CakeML_ASPCallback CallBackErrors)) := 
      minify_mapC local_asps_map (fun x => if (in_dec (EqClass_impl_DecEq _) x abstract_asps) then true else false) in
    let asp_server_cb := al.(ASPServer_Cb) in
    fun (cman : ConcreteManifest) =>
      let asp_server_addr := cman.(ASP_Server) in
      fun (par : ASP_PARAMS) (p : Plc) (bs : BS) (rawEv : RawEv) =>
        let (aspid, args, plc, targ) := par in
          (* check is the ASPID is a local, with a callback *)
          match (map_get shrunk_map aspid) with
          | Some cb => 
            match (cb par p bs rawEv) with
            | resultC r => resultC r
            | errC (messageLift msg) => (* TODO: Do something with msg *)
                errC Runtime
            end
          | None => errC Unavailable 
            (* (asp_server_cb asp_server_addr par) *)
          end.

  (* This function will be a dispatcher for either local ASPS to CakeMLCallback, or pass them off to the ASP_Server *)
  Definition generate_appraisal_ASP_dispatcher `{HID : EqClass ID_Type} (al : AM_Library) (am : Manifest)
      : ConcreteManifest -> (CakeML_ASPCallback DispatcherErrors) :=
    let local_app_asps_map := al.(Local_Appraisal_ASPS) in
    let abstract_app_asps := am.(appraisal_asps) in
    let shrunk_map : (MapC (Plc*ASP_ID) (CakeML_ASPCallback CallBackErrors)) := 
      minify_mapC local_app_asps_map (fun x => if (in_dec (EqClass_impl_DecEq _) x abstract_app_asps) then true else false) in
    let asp_server_cb := al.(ASPServer_Cb) in
    fun (cman : ConcreteManifest) =>
      let asp_server_addr := cman.(ASP_Server) in
      fun (par : ASP_PARAMS) (p : Plc) (bs : BS) (rawEv : RawEv) =>
        let (aspid, args, plc, targ) := par in
          (* check is the ASPID is a local, with a callback *)
          match (map_get shrunk_map (p,aspid)) with
          | Some cb => 
            match (cb par p bs rawEv) with
            | resultC r => resultC r
            | errC (messageLift msg) => (* TODO: Do something with msg *)
                errC Runtime
            end
          | None => errC Unavailable 
            (* (asp_server_cb asp_server_addr par) *)
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
        | Some uuid => resultC uuid
        | None => errC Unavailable
          (* (plc_server_cb plc_server_addr p) *)
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
        | Some key => resultC key
        | None => errC Unavailable
          (* (pubkey_server_cb pubkey_server_addr p) *)
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
        | Some p => resultC p
        | None => errC Unavailable
          (* (uuid_server_cb local_uuid_addr u) *)
        end.

  (* This is a rough type signature for the "manifest compiler".  Still some details to be ironed out... *)
  Definition manifest_compiler (m : Manifest) (al : AM_Library) : AM_Config :=
  (* The output of this function is a Concrete manifest, and a 
  function that can be used like "check_asp_EXTD".
  This function will be used in extraction to either dispatch ASPs to the ASP server, or call a local callback *)
  let cm := {|
      my_plc := m.(my_abstract_plc) ;

      Concrete_ASPs := m.(asps) ;
      Concrete_Plcs := al.(Local_Plcs) ;
      Concrete_PubKeys := al.(Local_PubKeys) ;
      Concrete_Targets := m.(targetPlcs) ;

      ASP_Server := al.(ASPServer_Addr) ;
      PubKey_Server := al.(PubKeyServer_Addr);
      Plc_Server := al.(PlcServer_Addr) ;
      UUID_Server := al.(UUIDServer_Addr);
    |} in
  {|
    concMan   := cm ;
    aspCb     := (generate_ASP_dispatcher al m) cm ;
    app_aspCb := (generate_appraisal_ASP_dispatcher al m) cm;
    plcCb     := (generate_Plc_dispatcher al m) cm ;
    pubKeyCb  := (generate_PubKey_dispatcher al m) cm ;
    uuidCb    := (generate_UUID_dispatcher al m) cm ;
  |}.