Require Import Term Example_Phrases_Demo Cvm_Run Manifest EqClass.

Require Import Impl_appraisal Appraisal_IO_Stubs IO_Stubs AM_Monad ErrorStMonad_Coq.

Require Import CvmJson_Admits Manifest_Generator Manifest_Compiler Maps.

Require Import ManCompSoundness Manifest_Admits Disclose ErrorStringConstants.

Require Import ManCompSoundness_Appraisal.

Require Import Auto StructTactics.


Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.



Definition fromSomeOption{A:Type} (default:A) (opt:option A): A :=
  match opt with
  | Some x => x
  | _ => default
  end.

Definition get_my_absman_generated (t:Term) (myPlc:Plc) : Manifest := 
  let env := manifest_generator t myPlc in 
  let maybe_absMan := map_get env myPlc in 
    fromSomeOption empty_Manifest maybe_absMan.



(*

Definition lib_supports_manifest (al : AM_Library) (am : Manifest) : Prop :=
  (forall (a : ASP_ID), In a am.(asps) -> exists cb, Maps.map_get al.(Local_ASPS) a = Some cb) /\
  (forall (up : Plc), In up am.(uuidPlcs) -> exists b, Maps.map_get al.(Local_Plcs) up = Some b) /\
  (forall (pkp : Plc), In pkp am.(pubKeyPlcs) -> exists b, Maps.map_get al.(Local_PubKeys) pkp = Some b) /\
  (forall (a : (Plc*ASP_ID)), In a am.(appraisal_asps) -> 
    exists cb, Maps.map_get al.(Local_Appraisal_ASPS) a = Some cb).


Lemma existsb_eq_iff_In: forall `{H : EqClass ID_Type} l a,
    existsb (eqb a) l = true <-> In a l.
Proof.


*)

(*
Check existsb.

existsb
	 : forall A : Type, (A -> bool) -> list A -> bool
*)

(*
Check forallb.
forallb
	 : forall A : Type, (A -> bool) -> list A -> bool
*)

Definition aspid_in_amlib_bool (al:AM_Library) (i:ASP_ID)  : bool := 
  match (Maps.map_get al.(Local_ASPS) i) with 
  | Some v => true 
  | None => false 
  end.

Definition uuid_plc_in_amlib_bool (al:AM_Library) (p:Plc)  : bool := 
  match (Maps.map_get al.(Local_Plcs) p) with 
  | Some v => true 
  | None => false 
  end.

Definition pubkey_plc_in_amlib_bool (al:AM_Library) (p:Plc)  : bool := 
  match (Maps.map_get al.(Local_PubKeys) p) with 
  | Some v => true 
  | None => false 
  end.

Definition appraisal_aspid_in_amlib_bool (al:AM_Library) (pr:Plc*ASP_ID)  : bool := 
  match (Maps.map_get al.(Local_Appraisal_ASPS) pr) with 
  | Some v => true 
  | None => false 
  end.


Definition lib_supports_aspids_bool (ls:list ASP_ID) (al:AM_Library) : bool := 
  forallb (aspid_in_amlib_bool al) ls.

Definition lib_supports_uuid_plcs_bool (ls:list Plc) (al:AM_Library) : bool := 
  forallb (uuid_plc_in_amlib_bool al) ls.

Definition lib_supports_pubkey_plcs_bool (ls:list Plc) (al:AM_Library) : bool := 
  forallb (pubkey_plc_in_amlib_bool al) ls.

Definition lib_supports_appraisal_aspids_bool (ls:list (Plc*ASP_ID)) (al:AM_Library) : bool := 
  forallb (appraisal_aspid_in_amlib_bool al) ls.

  Search (list bool -> bool).


Definition lib_supports_manifest_bool (al:AM_Library) (am:Manifest) : bool := 
  let aspid_list := am.(asps) in 
  let uuid_plcs_list := am.(uuidPlcs) in 
  let pubkey_plcs_list := am.(pubKeyPlcs) in 
  let appraisal_asps_list := am.(appraisal_asps) in 

  let aspid_list_bool := lib_supports_aspids_bool aspid_list al in 
  let uuid_plcs_list_bool := lib_supports_uuid_plcs_bool uuid_plcs_list al in 
  let pubkey_plcs_list_bool := lib_supports_pubkey_plcs_bool pubkey_plcs_list al in 
  let appraisal_aspids_list_bool := lib_supports_appraisal_aspids_bool appraisal_asps_list al in 

    andb (andb (andb aspid_list_bool uuid_plcs_list_bool) pubkey_plcs_list_bool) appraisal_aspids_list_bool.


Definition config_AM_if_lib_supported (t:Term) (myPlc:Plc) (amLib:AM_Library) : AM unit := 
    let absMan := get_my_absman_generated t myPlc in 
    let supportsB := lib_supports_manifest_bool amLib absMan in 
        if (supportsB) 
        then (
        let amConf := manifest_compiler absMan amLib in 
        put_amConfig amConf
        )
        else (
        am_failm (am_dispatch_error (Runtime errStr_lib_supports_man_check))
        ).
    
    
    Definition config_AM_if_lib_supported_app (et:Evidence) (amLib:AM_Library) : AM unit := 
    let absMan := manifest_generator_app et in 
    let supportsB := lib_supports_manifest_bool amLib absMan in 
        if (supportsB) 
        then (
        let amConf := manifest_compiler absMan amLib in 
        put_amConfig amConf
        )
        else (
        am_failm (am_dispatch_error (Runtime errStr_lib_supports_man_app_check))
        ).