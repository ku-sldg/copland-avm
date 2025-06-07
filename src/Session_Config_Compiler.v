Require Import Manifest Attestation_Session AM_Manager.
Require Import Term_Defs_Core JSON_Core ID_Type Manifest_Set Maps Interface.
Require Import IO_Stubs ErrorStringConstants.

Definition FS_path_join (root:FS_Location) (rest:FS_Location) 
    : ResultT FS_Location string := 
  from_string ((to_string root) ++ "/" ++ (to_string rest)).

Definition generate_ASP_dispatcher' (am : Manifest) (ats : Attestation_Session) (aspBin : FS_Location) (par : ASP_PARAMS) (rawEv : RawEv) : ResultT RawEv DispatcherErrors :=
  let (aspid, args, targ_plc, targ) := par in
  let asps := am.(asps) in
  let asp_map := am.(ASP_Mapping) in
    (* check is the ASPID is available *) 
    if (in_dec_set aspid asps)
    then 
      let conc_asp_loc := 
          match (map_get aspid asp_map) with
          | Some conc_asp_loc => conc_asp_loc
          (* If we dont find a translation, assume its the same name*)
          | None => (aspid_to_fs_location aspid)
          end 
      in
        let asp_req := (mkASPRReq aspid args targ_plc targ rawEv) in
        let js_req := to_JSON asp_req in
        match (FS_path_join aspBin conc_asp_loc) with
        | errC e => errC (Runtime e)
        (* If we can join the path, then we can make the request *)
        | resultC bin_loc => 
          let resp_res := make_JSON_FS_Location_Request bin_loc js_req in
          (* If we get a response, then we can parse it *)
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
        end
    else errC Unavailable.

(* This function will be a dispatcher for either local ASPS to CakeMLCallback, or pass them off to the ASP_Server *)
Definition generate_ASP_dispatcher `{HID : EqClass ID_Type} (am : Manifest) (al : Attestation_Session) (aspBin : FS_Location) 
    : (ASPCallback DispatcherErrors) :=
  (generate_ASP_dispatcher' am al aspBin). 

  Definition generate_remote_dispatcher' (ats : Attestation_Session) 
      (commsBin : FS_Location) (pTo: Plc) (e : Evidence) (t:Term) 
      : ResultT Evidence DispatcherErrors := 
  (* There is assuredly a better way to do it than this *)
  let '(mkAtt_Sess my_plc plc_map pk_map G) := ats in
  (* We need  to update the Att Session to tell the next plc how
  they should be tagging their stuff (basically who they are
  in the protocol) *)
  let new_att_sess := (mkAtt_Sess pTo plc_map pk_map G) in
  match (map_get pTo plc_map) with 
  | Some uuid =>
      let remote_req := (mkPRReq new_att_sess my_plc e t) in
      let js_req := to_JSON remote_req in
      let comms_fsloc := commsBin in
      let resp_res := make_JSON_FS_Location_Request comms_fsloc js_req in
      match resp_res with
      | resultC js_resp =>
          match from_JSON js_resp with
          | resultC resp => 
              let '(mkPRResp success ev) := resp in
              if success 
              then resultC ev 
              else errC ((Runtime errStr_remote_am_failure))
          | errC msg => errC ((Runtime msg)) 
          end
      | errC msg => errC ((Runtime msg))
      end
  | None => errC (Unavailable)
  end.

Definition generate_remote_dispatcher `{HID : EqClass ID_Type} (ats : Attestation_Session) (commsBin : FS_Location) 
    : (RemoteCallback DispatcherErrors) :=
  (generate_remote_dispatcher' ats commsBin). 

Definition session_config_compiler (conf : AM_Manager_Config) (ats : Attestation_Session) : Session_Config :=
let '(mkAM_Man_Conf man aspBin commsBin myUUID) := conf in
{|
  session_plc := (Session_Plc ats) ;
  session_context := (ats_context ats) ;
  aspCb     := (generate_ASP_dispatcher man ats aspBin) ;
  remoteCb := (generate_remote_dispatcher ats commsBin) ;
  plc_map     := (Plc_Mapping ats);
  pubkey_map  := (PubKey_Mapping ats);
  policy   := (man_policy man);
|}.