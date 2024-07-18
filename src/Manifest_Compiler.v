(* Implementation of the Manifest Compiler.
    Takes a Manifest + AM_Library to an AM_Config.  *)

Require Import Maps ID_Type EqClass Term_Defs_Core Manifest_Admits Manifest
  ErrorStMonad_Coq Term_Defs Interface_Types CvmJson_Interfaces Manifest_Set
  IO_Stubs.

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

Definition generate_ASP_dispatcher' (am : Manifest) (al : AM_Library) (aspBin : FS_Location) (par : ASP_PARAMS) (rawEv : RawEv) : ResultT RawEv DispatcherErrors :=
  let (aspid, args, targ_plc, targ) := par in
  let asps := am.(asps) in
  let asp_to_concrete_map := al.(Lib_ASPs) in
    (* check is the ASPID is available *) 
    if (in_dec_set aspid asps)
    then 
      match (map_get asp_to_concrete_map aspid) with
      | Some conc_asp_loc => 
          let asp_req := (mkASPRReq aspid args targ_plc targ rawEv) in
          let js_req := ASPRunRequest_to_JSON asp_req in
          let resp_res := make_JSON_FS_Location_Request aspBin conc_asp_loc js_req in
          match resp_res with
          | resultC js_resp =>
              match JSON_to_ASPRunResponse js_resp with
              | resultC r => 
                  let '(mkASPRResp succ bs) := r in
                  resultC bs
              | errC msg => errC (Runtime msg)
              end
          | errC msg => errC (Runtime msg)
          end
      | None => errC Unavailable
      end
    else errC Unavailable.

(* This function will be a dispatcher for either local ASPS to CakeMLCallback, or pass them off to the ASP_Server *)
Definition generate_ASP_dispatcher `{HID : EqClass ID_Type} (am : Manifest) (al : AM_Library) (aspBin : FS_Location) : (ASPCallback DispatcherErrors) :=
  (generate_ASP_dispatcher' am al aspBin). 

(* This function will lookup for either local Plcs to UUID, or pass them off to the Plc Server *)
Definition generate_Plc_dispatcher `{HID : EqClass ID_Type} (al : AM_Library) (am : Manifest) 
    : PlcCallback :=
  (* let plc_server_cb := al.(PlcServer_Cb) in *)
    let local_plc_map := al.(Lib_Plcs) in
    let abstract_plcs := am.(uuidPlcs) in
    let shrunk_map := 
      minify_mapD local_plc_map (fun x => if (in_dec_set x abstract_plcs) then true else false) in

    fun (p : Plc) =>
      (* check is the plc "p" is local, with a reference *)
      match (map_get shrunk_map p) with
      | Some uuid => resultC uuid
      | None => errC Unavailable
        (* (plc_server_cb plc_server_addr p) *)
      end.
    
(* This function will lookup the PubKey either locally Plc -> PublicKey or pass off to PubKeyServer *)
Definition generate_PubKey_dispatcher `{HID : EqClass ID_Type} (al : AM_Library) (am : Manifest) 
    : PubKeyCallback :=
  (* let pubkey_server_cb := al.(PubKeyServer_Cb) in *)
    let local_pubkey_map := al.(Lib_PubKeys) in
    let abstract_plcs := am.(pubKeyPlcs) in
    let shrunk_map := 
      minify_mapD local_pubkey_map (fun x => if (in_dec_set x abstract_plcs) then true else false) in

    fun (p : Plc) =>
      (* check is the plc "p" is local, with a reference in the pubkey server mapping *)
      match (map_get shrunk_map p) with
      | Some key => resultC key
      | None => errC Unavailable
        (* (pubkey_server_cb pubkey_server_addr p) *)
      end.

(* This is a rough type signature for the "manifest compiler".  Still some details to be ironed out... *)
Definition manifest_compiler (m : Manifest) (al : AM_Library) (aspBin : FS_Location) : AM_Config :=
(* The output of this function is an AM Config, and a 
function that can be used like "check_asp_EXTD".
This function will be used in extraction to either dispatch ASPs to the ASP server, or call a local callback *)
{|
  absMan   := m ;
  am_clone_addr := (UUID_AM_Clone al) ;
  ASP_to_APPR_ASP_Map := (ASP_Compat_Map al);
  aspCb     := (generate_ASP_dispatcher m al aspBin) ;
  plcCb     := (generate_Plc_dispatcher al m);
  pubKeyCb  := (generate_PubKey_dispatcher al m);
|}.