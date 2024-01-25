(*  Helper definitions for AM Client and Server implementations.  *)

Require Import Term Example_Phrases_Demo Cvm_Run Manifest AbstractedTypes EqClass.

Require Import Impl_appraisal Appraisal_IO_Stubs IO_Stubs AM_Monad ErrorStMonad_Coq.

Require Import CvmJson_Admits Manifest_Generator Manifest_Compiler Maps Auto StructTactics.

Require Import ManCompSoundness Manifest_Admits Disclose ErrorStringConstants
    ManCompSoundness_Appraisal.

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


(* Helper lemma for proving equivalence of propositional vs boolean list membership.  
       TODO:  consider moving this somewhwere else? *)
Lemma existsb_eq_iff_In: forall `{H : EqClass ID_Type} l a,
  existsb (eqb a) l = true <-> In a l.
Proof.
    intros.
    split.
    -
      generalizeEverythingElse l.
      induction l; intros; simpl in *.
      +
        solve_by_inversion.
      +
        find_apply_lem_hyp Bool.orb_prop.
        destruct H0.
        ++
          left.
          symmetry.
          apply eqb_leibniz.
          eassumption.
        ++
          right.
          eauto.
    -
      generalizeEverythingElse l.
      induction l; intros; simpl in *.
      +
        solve_by_inversion.
      +
        destruct H0.
        ++
          subst.
          assert (eqb a0 a0 = true).
          {
            apply eqb_leibniz.
            auto.
          }
          find_rewrite.
          eauto.
        ++
          assert (existsb (eqb a0) l = true) by eauto.
          find_rewrite.
          simpl.
  
          apply Bool.orb_true_r.
  Qed.

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


Definition lib_omits_aspids (ls:manifest_set ASP_ID) (al:AM_Library) : manifest_set ASP_ID := 
  filter_manset (fun i => (negb (aspid_in_amlib_bool al i))) ls.

Definition lib_omits_uuid_plcs (ls:manifest_set Plc) (al:AM_Library) : manifest_set Plc := 
  filter_manset (fun p => (negb (uuid_plc_in_amlib_bool al p))) ls.

Definition lib_omits_pubkey_plcs (ls:manifest_set Plc) (al:AM_Library) : manifest_set Plc := 
  filter_manset (fun p => (negb (pubkey_plc_in_amlib_bool al p))) ls.

Definition lib_omits_appraisal_aspids (ls:manifest_set (Plc*ASP_ID)) (al:AM_Library) : manifest_set (Plc*ASP_ID) := 
  filter_manset (fun i => (negb (appraisal_aspid_in_amlib_bool al i))) ls.

Definition lib_omits_manifest (al:AM_Library) (am:Manifest) : Manifest := 
    let aspid_list := am.(asps) in 
    let uuid_plcs_list := am.(uuidPlcs) in 
    let pubkey_plcs_list := am.(pubKeyPlcs) in 
    let appraisal_asps_list := am.(appraisal_asps) in  

        Build_Manifest 
            am.(my_abstract_plc)
            (lib_omits_aspids aspid_list al)
            (lib_omits_appraisal_aspids appraisal_asps_list al)
            (lib_omits_uuid_plcs uuid_plcs_list al)
            (lib_omits_pubkey_plcs pubkey_plcs_list al)    
            manifest_set_empty 
            empty_PolicyT.

Definition manifest_none_omitted (m:Manifest) : bool := 
    match m with 
    | Build_Manifest _ asps app_asps uuids pubkeys _ _ => 
        (is_empty_manset asps) && 
        (is_empty_manset app_asps) &&
        (is_empty_manset uuids) &&
        (is_empty_manset pubkeys)
    end.


Definition lib_supports_manifest_bool (al:AM_Library) (am:Manifest) : bool := 
    manifest_none_omitted (lib_omits_manifest al am).

Definition config_AM_if_lib_supported (absMan:Manifest) (amLib:AM_Library) : AM unit := 
    let om := lib_omits_manifest amLib absMan in
    let supportsB := manifest_none_omitted om in 
        if (supportsB) 
        then (
            let amConf := manifest_compiler absMan amLib in 
                put_amConfig amConf
        )
        else (
            am_failm (am_dispatch_error (Runtime (pretty_print_manifest om)))
        ).