(* Implementation of the Manifest Compiler.
    Takes a Manifest + AM_Library to an AM_Config.  *)

Require Import Maps AbstractedTypes EqClass Term_Defs_Core 
               Manifest_Admits Manifest
               ErrorStMonad_Coq Term_Defs.

Require Import Manifest_Set.
Require Import IO_Stubs.
  

Require Import List.
Import ListNotations.
  
  (* Reduces a MapC to only include elements that satisfy the condition "f" *)
  Fixpoint minify_mapC {A B : Type} `{HA : EqClass A} (m : MapC A B) (f : A -> bool) : (MapC A B) :=
    match m with
    | nil => nil
    | cons (k,v) tl => if (f k) then cons (k,v) (minify_mapC tl f) else minify_mapC tl f
    end.

    (*
  (* Reduces a MapD to only include elements that satisfy the condition "f" *)
  Fixpoint minify_mapD {A B : Type} `{HA : EqClass A} `{HB : EqClass B} (m : MapD A B) (f : A -> bool) : (MapD A B) :=
    match m with
    | nil => nil
    | cons (k,v) tl => if (f k) then cons (k,v) (minify_mapD tl f) else minify_mapD tl f
    end.
    *)

  Definition generate_ASP_dispatcher' (al : AM_Library) (am : Manifest) 
              (ps : ASP_PARAMS) (p:Plc) 
              (rawEv : RawEv) : ResultT BS DispatcherErrors :=
        let (aspid, _, _, _) := ps in
        let abstract_asps := am.(asps) in
        let local_asps_map := al.(Local_ASPS) in
        let shrunk_map : (MapC ASP_ID UUID) := 
        minify_mapC local_asps_map (fun x => if (in_dec_set x abstract_asps) then true else false) in
          (* check is the ASPID is a local, with a callback *)
          match (map_get shrunk_map aspid) with
          | Some uuid => 
            match (invoke_asp_uuid uuid ps rawEv) with
            | resultC r => resultC r
            | errC (messageLift msg) => 
                errC (Runtime msg)
            end
          | None => errC Unavailable 
          end.

  (* This function will be a dispatcher for either local ASPS to CakeMLCallback, or pass them off to the ASP_Server *)
  Definition generate_ASP_dispatcher `{HID : EqClass ID_Type} (al : AM_Library) (am : Manifest)
      : (ASPCallback DispatcherErrors) :=
          (generate_ASP_dispatcher' al am). 

  Definition generate_appraisal_ASP_dispatcher' (al : AM_Library) (am : Manifest) 
              (ps : ASP_PARAMS) (p : Plc) 
              (rawEv : RawEv) : ResultT BS DispatcherErrors :=
    let (aspid, _, _, _) := ps in
    let abstract_asps := am.(appraisal_asps) in
    let local_asps_map := al.(Local_Appraisal_ASPS) in
    let shrunk_map : (MapC (Plc*ASP_ID) UUID) :=  
    minify_mapC local_asps_map (fun x => if (in_dec_set x abstract_asps) then true else false) in
      (* check is the ASPID is a local, with a callback *)
      match (map_get shrunk_map (p,aspid)) with
        | Some uuid => 
          match (invoke_asp_uuid uuid ps rawEv) with
          | resultC r => resultC r
          | errC (messageLift msg) => errC (Runtime msg)
          end
        | None => errC Unavailable 
      end.

  Definition generate_appraisal_ASP_dispatcher `{HID : EqClass ID_Type} (al : AM_Library) (am : Manifest)
  : (ASPCallback DispatcherErrors) :=
  (generate_appraisal_ASP_dispatcher' al am). 


  (* This function will lookup for either local Plcs to UUID, or pass them off to the Plc Server *)
  Definition generate_Plc_dispatcher `{HID : EqClass ID_Type} (al : AM_Library) (am : Manifest) 
      : PlcCallback :=
      let local_plc_map := al.(Local_Plcs) in
      let abstract_plcs := am.(uuidPlcs) in
      let shrunk_map := 
        minify_mapC local_plc_map (fun x => if (in_dec_set x abstract_plcs) then true else false) in

      fun (p : Plc) =>
        (* check is the plc "p" is local, with a reference *)
        match (map_get shrunk_map p) with
        | Some uuid => resultC uuid
        | None => errC Unavailable
        end.
      
  (* This function will lookup the PubKey either locally Plc -> PublicKey or pass off to PubKeyServer *)
  Definition generate_PubKey_dispatcher `{HID : EqClass ID_Type} (al : AM_Library) (am : Manifest) 
      : PubKeyCallback :=
      let local_pubkey_map := al.(Local_PubKeys) in
      let abstract_plcs := am.(pubKeyPlcs) in
      let shrunk_map := 
        minify_mapC local_pubkey_map (fun x => if (in_dec_set x abstract_plcs) then true else false) in

      fun (p : Plc) =>
        (* check is the plc "p" is local, with a reference in the pubkey server mapping *)
        match (map_get shrunk_map p) with
        | Some key => resultC key
        | None => errC Unavailable
        end.

  (* This is the top-level definition for the "manifest compiler".  *)
  Definition manifest_compiler (m : Manifest) (al : AM_Library) : AM_Config :=
  {|
    absMan   := m ;
    am_clone_addr := (UUID_AM_Clone al);
    aspCb     := (generate_ASP_dispatcher al m);
    app_aspCb := (generate_appraisal_ASP_dispatcher al m);
    plcCb     := (generate_Plc_dispatcher al m);
    pubKeyCb  := (generate_PubKey_dispatcher al m);
  |}.