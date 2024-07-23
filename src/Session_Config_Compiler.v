Require Import Manifest Attestation_Session.
Require Import EqClass.
Require Import Term_Defs_Core ResultT ID_Type Manifest_Set Maps Interface.
Require Import IO_Stubs.

Definition generate_ASP_dispatcher' (am : Manifest) (ats : Attestation_Session) (aspBin : FS_Location) (par : ASP_PARAMS) (rawEv : RawEv) : ResultT RawEv DispatcherErrors :=
  let (aspid, args, targ_plc, targ) := par in
  let asps := am.(asps) in
  let asp_map := am.(ASP_Mapping) in
    (* check is the ASPID is available *) 
    if (in_dec_set aspid asps)
    then 
      match (map_get asp_map aspid) with
      | Some conc_asp_loc => 
          let asp_req := (mkASPRReq aspid args targ_plc targ rawEv) in
          let js_req := to_JSON asp_req in
          let resp_res := make_JSON_FS_Location_Request aspBin conc_asp_loc js_req in
          match resp_res with
          | resultC js_resp =>
              match from_JSON js_resp with
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
Definition generate_ASP_dispatcher `{HID : EqClass ID_Type} (am : Manifest) (al : Attestation_Session) (aspBin : FS_Location) 
    : (ASPCallback DispatcherErrors) :=
  (generate_ASP_dispatcher' am al aspBin). 

Definition session_config_compiler (m : Manifest) (aspBin : FS_Location) (ats : Attestation_Session) : Session_Config :=
{|
  session_plc := (Session_Plc ats) ;
  ASP_to_APPR_ASP_Map := (ASP_Compat_Map m);
  aspCb     := (generate_ASP_dispatcher m ats aspBin) ;
  plc_map     := (Plc_Mapping ats);
  pubkey_map  := (PubKey_Mapping ats);
  policy   := (man_policy m);
|}.

Definition session_config_decompiler (sc : Session_Config) : Attestation_Session :=
{|
  Session_Plc := (session_plc sc) ;
  Plc_Mapping := (plc_map sc) ;
  PubKey_Mapping := (pubkey_map sc) |}.