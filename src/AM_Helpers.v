(*  Helper definitions for AM Client and Server implementations.  *)

Require Import Term Cvm_Run Attestation_Session ID_Type EqClass.

Require Import Impl_appraisal Appraisal_IO_Stubs IO_Stubs AM_Monad ErrorStMonad_Coq.

Require Import Interface Maps Auto StructTactics.

Require Import Disclose ErrorStringConstants.

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.


Definition fromSomeOption{A:Type} (default:A) (opt:option A): A :=
  match opt with
  | Some x => x
  | _ => default
  end.

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
          apply eqb_eq.
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
            apply eqb_eq.
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

(* NOTE: All of this is deprecated now due to the 
Attestation Session being the identifier resolution method

Definition uuid_plc_in_amlib_bool (al:AM_Library) (p:Plc)  : bool := 
  match (Maps.map_get al.(Lib_Plcs) p) with 
  | Some v => true 
  | None => false 
  end.

Definition pubkey_plc_in_amlib_bool (al:AM_Library) (p:Plc)  : bool := 
  match (Maps.map_get al.(Lib_PubKeys) p) with 
  | Some v => true 
  | None => false 
  end.

Definition lib_omits_uuid_plcs (ls:manifest_set Plc) (al:AM_Library) : manifest_set Plc := 
  filter_manset (fun p => (negb (uuid_plc_in_amlib_bool al p))) ls.

Definition lib_omits_pubkey_plcs (ls:manifest_set Plc) (al:AM_Library) : manifest_set Plc := 
  filter_manset (fun p => (negb (pubkey_plc_in_amlib_bool al p))) ls.

Definition lib_omits_manifest (al:AM_Library) (am:Manifest) : Manifest := 
    let aspid_list := am.(asps) in 
    let uuid_plcs_list := am.(uuidPlcs) in 
    let pubkey_plcs_list := am.(pubKeyPlcs) in 

        Build_Manifest 
            am.(my_abstract_plc)
            aspid_list
            (lib_omits_uuid_plcs uuid_plcs_list al)
            (lib_omits_pubkey_plcs pubkey_plcs_list al)    
            manifest_set_empty 
            empty_PolicyT.

Definition manifest_none_omitted (m:Manifest) : bool := 
    match m with 
    | Build_Manifest _ asps uuids pubkeys _ _ => 
        (is_empty_manset asps) && 
        (is_empty_manset uuids) &&
        (is_empty_manset pubkeys)
    end.


Definition lib_supports_manifest_bool (al:AM_Library) (am:Manifest) : bool := 
    manifest_none_omitted (lib_omits_manifest al am).

Definition config_AM_if_lib_supported (absMan:Manifest) (amLib:AM_Library) (aspBin : FS_Location): AM unit := 
    let om := lib_omits_manifest amLib absMan in
    let supportsB := manifest_none_omitted om in 
        if (supportsB) 
        then (
            let amConf := manifest_compiler absMan amLib aspBin in 
                put_amConfig amConf
        )
        else (
            am_failm (am_dispatch_error (Runtime (pretty_print_manifest om)))
        ). *)