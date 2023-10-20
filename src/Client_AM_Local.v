Require Import Term Example_Phrases_Demo Cvm_Run Manifest EqClass.

Require Import Impl_appraisal Appraisal_IO_Stubs IO_Stubs AM_Monad ErrorStMonad_Coq.

Require Import CvmJson_Admits Manifest_Generator Manifest_Compiler Maps.

Require Import ManCompSoundness Manifest_Admits Disclose ErrorStringConstants.

Require Import ManCompSoundness_Appraisal.

Require Import Auto StructTactics.

Require Import AM_Helpers.


Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)

Definition gen_nonce_if_none_local (initEv:option EvC) : AM EvC :=
  match initEv with
      | Some (evc ebits et) => ret mt_evc
      | None =>
        let nonce_bits := gen_nonce_bits in
        nid <- am_newNonce nonce_bits ;;
        ret (evc [nonce_bits] (nn nid))
  end.

Definition gen_authEvC_if_some (ot:option Term) (myPlc:Plc) (init_evc:EvC) : AM EvC :=
  match ot with
  | Some auth_phrase =>
    let '(evc init_rawev_auth init_et_auth) := init_evc in
    let auth_rawev := am_sendReq auth_phrase myPlc mt_evc init_rawev_auth in
    let auth_et := eval auth_phrase myPlc init_et_auth in
      ret (evc auth_rawev auth_et)
  | None => ret (evc [] mt)
  end.

Definition am_appraise (t:Term) (toPlc:Plc) (init_et:Evidence) (cvm_ev:RawEv) : AM AppResultC :=
  (* let app_res := run_appraisal_client t pTo init_et cvm_ev in *)
  let expected_et := eval t toPlc init_et in
  app_res <- gen_appraise_AM expected_et cvm_ev ;;
  ret (app_res).



(*
Ltac unfold_libsupports_defs := 
  try (unfold 
        lib_supports_aspids_bool, 
        aspid_in_amlib_bool, 
        lib_supports_uuid_plcs_bool,
        uuid_plc_in_amlib_bool,
        lib_supports_pubkey_plcs_bool,
        pubkey_plc_in_amlib_bool,
        lib_supports_appraisal_aspids_bool,
        appraisal_aspid_in_amlib_bool in * ).
*)


Lemma lib_support_bool_iff_prop : forall amLib absMan,
(lib_supports_manifest_bool amLib absMan = true) <->
lib_supports_manifest amLib absMan.
Proof.

(*
  intros.
  split; intros.
  -
    unfold lib_supports_manifest_bool in *.
    unfold lib_supports_manifest in *.
    repeat rewrite Bool.andb_true_iff in *.
    destruct_conjs.

    repeat (
    split; intros;
        unfold_libsupports_defs;
        try rewrite forallb_forall in *;
        try find_apply_hyp_hyp;
        ff;
        eauto).

  -
  unfold lib_supports_manifest_bool in *.
  unfold lib_supports_manifest in *.
  repeat rewrite Bool.andb_true_iff in *.
  destruct_conjs.

  split; intros;

    repeat (
        repeat (split; intros);
        unfold_libsupports_defs;
        rewrite forallb_forall in *;
        intros;
        unfold_libsupports_defs;
        find_apply_hyp_hyp;
        ff;
        destruct_conjs;
        solve_by_inversion).
Qed.

*)

Admitted.



Definition run_cvm_local_am (t:Term) (myPlc:Plc) (ls:RawEv) : AM RawEv := 
  st <- get ;; 
  ret (run_cvm_rawEv t myPlc ls (amConfig st)).

Definition gen_authEvC_if_some_local (ot:option Term) (myPlc:Plc) (init_evc:EvC) (absMan:Manifest) (amLib:AM_Library) : AM EvC :=
  match ot with
  | Some auth_phrase =>
      let '(evc init_rawev_auth init_et_auth) := init_evc in

      config_AM_if_lib_supported (* auth_phrase myPlc *) absMan amLib ;; 
      resev <- run_cvm_local_am auth_phrase myPlc init_rawev_auth ;;
      let auth_et := eval auth_phrase myPlc init_et_auth in 
      ret (evc resev auth_et)
  | None => ret (evc [] mt)
  end.

Definition check_et_length (et:Evidence) (ls:RawEv) : AM unit := 
  if (eqb (et_size et) (length ls)) 
  then ret tt 
  else (am_failm (am_dispatch_error (Runtime errStr_et_size))).


Definition get_am_policy : AM PolicyT := 
  st <- get ;; 
  ret (policy (absMan (amConfig st))).

Definition check_disclosure_policy (t:Term) (p:Plc) (e:Evidence) : AM unit := 
  policy <- get_am_policy ;; 
  if (policy_list_not_disclosed t p e policy)
  then ret tt 
  else (am_failm (am_dispatch_error (Runtime errStr_disclosePolicy))).

Definition am_client_gen_local (t:Term) (myPlc:Plc) (initEvOpt:option EvC) 
    (* (authPhrase:option Term) *) (absMan:Manifest) (amLib:AM_Library) : AM AM_Result := 
  evcIn <- gen_nonce_if_none_local initEvOpt ;; 
  (* auth_evc <- gen_authEvC_if_some_local authPhrase myPlc mt_evc ;;  *)
  let '(evc init_ev init_et) := evcIn in 
  config_AM_if_lib_supported absMan amLib ;; 

  check_disclosure_policy t myPlc init_et ;;
  resev <- run_cvm_local_am t myPlc init_ev ;; 

  let expected_et := eval t myPlc init_et in 

  check_et_length expected_et resev ;;

  app_res <- gen_appraise_AM expected_et resev ;; 
  ret (am_appev app_res).

Require Import Auto.


Inductive no_nonces_pred : Evidence -> Prop := 
| mt_no_nonce : no_nonces_pred mt 
| uu_no_nonce : forall p fwd ps et', 
    no_nonces_pred et' -> 
    no_nonces_pred (uu p fwd ps et')
| ss_no_nonce : forall et1 et2,
    no_nonces_pred et1 -> 
    no_nonces_pred et2 -> 
    no_nonces_pred (ss et1 et2).

Lemma no_nonces'' : forall et ls,
  no_nonces_pred et -> 
  nonce_ids_et' et ls = ls.
Proof.
  induction et; intros; ff.
  -
    invc H.
    eauto.
  -
  invc H.
  erewrite IHet1; eauto.
Qed.


Lemma no_nonces_eval : forall t p et,
no_nonces_pred et -> 
no_nonces_pred (eval t p et).
Proof.
  induction t; intros; ff.
  -
    destruct a; ff.
    +
      econstructor.
    +
      destruct f; ff.
      ++
      econstructor.
      destruct s; ff.
      econstructor.
      ++
        econstructor.
        destruct s; ff.
        econstructor.
      ++
      econstructor.
      destruct s; ff.
      econstructor.
      ++
      econstructor.
      ++
      destruct s; ff.
      econstructor.
    +
      econstructor; eauto.
    +
    econstructor; eauto.
    +
    econstructor; eauto.
  -
    eauto.
  -
    eauto.
  -
    destruct s. 
    destruct s; destruct s0; ff.
    +
    econstructor; eauto.
    +
    econstructor; eauto.
    eapply IHt2.
    econstructor.
    +
    econstructor.
    eapply IHt1.
    econstructor.
    eauto.
    +
    econstructor.
    eapply IHt1.
    econstructor.

    eapply IHt2.
    econstructor.
  -
  destruct s. 
  destruct s; destruct s0; ff.
  +
  econstructor; eauto.
  +
  econstructor; eauto.
  eapply IHt2.
  econstructor.
  +
  econstructor.
  eapply IHt1.
  econstructor.
  eauto.
  +
  econstructor.
  eapply IHt1.
  econstructor.

  eapply IHt2.
  econstructor.
Qed.

Lemma no_nonces' : forall t p ls et,
no_nonces_pred et -> 
nonce_ids_et' (eval t p et) ls = ls.
Proof.
  induction t; intros; try (ff; congruence).
  -
    ff.
    unfold eval_asp in *.
    destruct a;
    ff; subst; try destruct s; ff;
    try eapply no_nonces''; eauto.

  -
    eauto.
  -
    ff.

    eapply IHt2.

    eapply no_nonces_eval; eauto.
  -
    ff.
    destruct s. 
    destruct s; destruct s0; ff.

    erewrite IHt1; eauto.

    erewrite IHt1; eauto.

    eapply IHt2.
    econstructor.

    erewrite IHt1; eauto.
    econstructor.

    erewrite IHt1; eauto.

    eapply IHt2.
    econstructor.
    econstructor.

  -

  ff.
  destruct s. 
  destruct s; destruct s0; ff.

  erewrite IHt1; eauto.

  erewrite IHt1; eauto.

  eapply IHt2.
  econstructor.

  erewrite IHt1; eauto.
  econstructor.

  erewrite IHt1; eauto.

  eapply IHt2.
  econstructor.
  econstructor.
Qed.

Lemma no_nonces : forall t p ,
nonce_ids_et (eval t p mt) = [].
Proof.
  intros.
  eapply no_nonces'.
  econstructor.
Qed.

Lemma nonce_ids_et_cumul : forall et ls nid,
  In nid ls -> 
  In nid (nonce_ids_et' et ls).
Proof.
  induction et; intros; ff; eauto.
Qed.

Lemma nid_in_gen : forall et ls nid ls',
  In nid (nonce_ids_et' et ls) -> 
  In nid ls \/ In nid (nonce_ids_et' et ls').
Proof.
  induction et; intros; ff.
  -
    door; ff.
  -
    eauto.
  -
    edestruct IHet2.
    eassumption.

    edestruct IHet1.
    eassumption.
    eauto.

    right.
    eapply nonce_ids_et_cumul.
    eassumption.

    eauto.
Qed.

Lemma nonce_ids_ss_decom : forall nid et1 et2 ls,
In nid (nonce_ids_et' et2 (nonce_ids_et' et1 ls)) -> 
In nid ls \/
In nid (nonce_ids_et' et1 []) \/ 
In nid (nonce_ids_et' et2 []).
Proof.
  intros.
  eapply nid_in_gen with (ls' := []) in H.
  door; eauto.

  eapply nid_in_gen with (ls':=[]) in H.
  door; eauto.
Qed.

Lemma nonce_ids_et_cumul_nil: forall nid et ls,
In nid (nonce_ids_et' et []) ->
In nid (nonce_ids_et' et ls).
Proof.
  induction et; intros; ff.
  -
    door; try solve_by_inversion.
  -
    eauto.
  -
    edestruct nonce_ids_ss_decom; eauto.

    solve_by_inversion.

    door.

    assert (In nid (nonce_ids_et' et1 ls)).
    apply IHet1.
    eassumption.

    eapply nonce_ids_et_cumul; eauto.
    eauto.
    Qed.

Lemma nid_nonce_ids_eval : forall t p et ls nid,
  In nid (nonce_ids_et' (eval t p et) ls) -> 
  In nid ls \/ In nid (nonce_ids_et' et []).
Proof.
  induction t; intros; ff.
  -
    destruct a; ff.
    + 
    eapply nid_in_gen; auto.
    +
      destruct f; ff; 
      destruct s; ff;
      eapply nid_in_gen; auto.
    +
    eapply nid_in_gen; auto.
    +
    eapply nid_in_gen; auto.
    +
    eapply nid_in_gen; auto.
  -
    eauto.
  -
    assert (
      In nid ls \/
      In nid (nonce_ids_et' (eval t1 p et) [])

    ).
    eauto.
    door.
    eauto.
    eapply IHt1.

    eapply nonce_ids_et_cumul_nil; eauto.

  -
    ff.
    destruct s.
    destruct s; destruct s0; ff.
    +

    assert (
      In nid (nonce_ids_et' (eval t1 p et) ls) \/ 
      In nid (nonce_ids_et' et [])

    ).
    eapply IHt2.
    apply H.

    door;
    eauto.

    +
    assert (
      In nid (nonce_ids_et' (eval t1 p et) ls) \/ 
      In nid (nonce_ids_et' mt [])

    ).
    eapply IHt2.
    apply H.

    door;
    eauto.

    solve_by_inversion.

    +
    assert (
      In nid (nonce_ids_et' (eval t1 p mt) ls) \/ 
      In nid (nonce_ids_et' et [])

    ).
    eapply IHt2.
    apply H.

    door;
    eauto.

    apply IHt1 in H0.
    door; eauto.
    solve_by_inversion.
    +
    assert (
      In nid (nonce_ids_et' (eval t1 p mt) ls) \/ 
      In nid (nonce_ids_et' mt [])

    ).
    eapply IHt2.
    apply H.

    door;
    eauto.

    apply IHt1 in H0.
    door; eauto.
    solve_by_inversion.

    ff.

  -

  ff.
  destruct s.
  destruct s; destruct s0; ff.
  +

  assert (
    In nid (nonce_ids_et' (eval t1 p et) ls) \/ 
    In nid (nonce_ids_et' et [])

  ).
  eapply IHt2.
  apply H.

  door;
  eauto.

  +
  assert (
    In nid (nonce_ids_et' (eval t1 p et) ls) \/ 
    In nid (nonce_ids_et' mt [])

  ).
  eapply IHt2.
  apply H.

  door;
  eauto.

  solve_by_inversion.

  +
  assert (
    In nid (nonce_ids_et' (eval t1 p mt) ls) \/ 
    In nid (nonce_ids_et' et [])

  ).
  eapply IHt2.
  apply H.

  door;
  eauto.

  apply IHt1 in H0.
  door; eauto.
  solve_by_inversion.
  +
  assert (
    In nid (nonce_ids_et' (eval t1 p mt) ls) \/ 
    In nid (nonce_ids_et' mt [])

  ).
  eapply IHt2.
  apply H.

  door;
  eauto.

  apply IHt1 in H0.
  door; eauto.
  solve_by_inversion.

  ff.
Qed.


Example client_gen_executable : forall t p initEvOpt amLib st, 

  lib_supports_manifest_bool amLib (get_my_absman_generated t p) = true -> 
(*
  lib_supports_manifest_bool amLib (manifest_generator_app (eval ))
*)

  (exists res st', 
  (am_client_gen_local t p initEvOpt (get_my_absman_generated t p) amLib) st = (resultC res, st')) \/ 

  (exists st' str, 
    (am_client_gen_local t p initEvOpt (get_my_absman_generated t p) amLib) st = (errC (am_dispatch_error (Runtime str)), st')
  ).
Proof.

(*

  intros.
  unfold am_client_gen_local.
  am_monad_unfold.
  repeat break_let.
  ff.
  -
  destruct initEvOpt; ff.
  -
    unfold config_AM_if_lib_supported in *.
    ff.
    (*
    find_rewrite.

    am_monad_unfold.

    solve_by_inversion.
    *)

  -
    unfold check_et_length in *.
    ff.
    unfold am_failm in *.
    ff. 
    right.
    eauto.

    (*

    

  -
    ff. 
    unfold check_et_length in *.
    ff.
    right.
    eauto.

    *)


  -
    unfold config_AM_if_lib_supported_app in *.

    ff.
    unfold am_failm in *.
    ff.

    right.
    eauto.

  -

    unfold config_AM_if_lib_supported_app in *.
    ff.

    rewrite lib_support_bool_iff_prop in *.


    assert (et_size (eval t p e0) = length (run_cvm_rawEv t p r1 (amConfig a1))).
    {
      unfold check_et_length in *.
      ff.
      Search (Nat.eqb _ _ = true -> _).
      apply EqNat.beq_nat_true_stt in Heqb0.
      eauto.
    }

    (*
    Theorem manifest_generator_compiler_soundness_app : forall et ls oldMan absMan amLib amConf,
  (* map_get (manifest_generator t tp) p = Some absMan -> *)
  manifest_generator_app' et oldMan = absMan ->
  lib_supports_manifest_app amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  et_size et = length ls ->
  forall st,

  st.(amConfig) = amConf ->

  has_nonces (nonce_ids_et et) (st.(am_nonceMap)) -> 

    ( 

    exists ec st',
         (gen_appraise_AM et ls) st = (resultC ec, st')) \/ 
    (exists st',
         (gen_appraise_AM et ls) st = (errC (dispatch_error Runtime), st')
    ).
Proof.
    
    *)

    Require Import ManCompSoundness_Appraisal.
    Check manifest_generator_compiler_soundness_app.

    Print get_my_absman_generated.

    pose (manifest_generator_compiler_soundness_app 
            (eval t p e0) 
            (run_cvm_rawEv t p r1 (amConfig a1))
            empty_Manifest
            (manifest_generator_app (eval t p e0))
            amLib 
            (manifest_compiler (manifest_generator_app (eval t p e0)) amLib)
            eq_refl Heqb eq_refl H0).

    specialize o with (st:= 
    {|
      am_nonceMap := am_nonceMap a5;
      am_nonceId := am_nonceId a5;
      amConfig := manifest_compiler (manifest_generator_app (eval t p e0)) amLib
    |}
    ).
    simpl in *.

    assert (
      manifest_compiler (manifest_generator_app (eval t p e0)) amLib =
    manifest_compiler (manifest_generator_app (eval t p e0)) amLib
    ) by reflexivity.

    apply o in H1.

    +
    door.
    ++
      find_rewrite.
      ff.
    ++
      find_rewrite.
      ff.
      right.
      eauto.

    +
      destruct initEvOpt.
      ff.

      rewrite no_nonces.
      cbv; intros; ff.


      unfold gen_nonce_if_none_local in *.
      am_monad_unfold.
      invc Heqp0.

      assert (a1 = a5).
      {
        unfold check_et_length in *.
        assert (
          Nat.eqb (et_size (eval t p (nn (am_nonceId st))))
            (length (run_cvm_rawEv t p [gen_nonce_bits] (amConfig a1))) = 
            true
        ).
        {
          Check EqNat.beq_nat_true_stt.
          Require Import PeanoNat.
          apply Nat.eqb_eq.
          eassumption.
        }
        ff.
      }
      subst.

      unfold config_AM_if_lib_supported in *.
      ff.

      unfold has_nonces.
      intros.

      assert (nid = (am_nonceId st)).
      {
        unfold nonce_ids_et in H1.

        apply nid_nonce_ids_eval in H1.

        door.
        solve_by_inversion.
        invc H1.
        reflexivity.
        solve_by_inversion.
      }
      subst.

      eexists.

      eapply mapC_get_works.

    -
    unfold config_AM_if_lib_supported_app in *.
    ff.

    rewrite lib_support_bool_iff_prop in *.


    assert (et_size (eval t p e0) = length (run_cvm_rawEv t p r1 (amConfig a1))).
    {
      unfold check_et_length in *.
      ff.
      apply Nat.eqb_eq.
      eassumption.
    }


    pose (manifest_generator_compiler_soundness_app 
            (eval t p e0) 
            (run_cvm_rawEv t p r1 (amConfig a1))
            empty_Manifest
            (manifest_generator_app (eval t p e0))
            amLib 
            (manifest_compiler (manifest_generator_app (eval t p e0)) amLib)
            eq_refl Heqb eq_refl H0).

    specialize o with (st:= 
    {|
      am_nonceMap := am_nonceMap a5;
      am_nonceId := am_nonceId a5;
      amConfig := manifest_compiler (manifest_generator_app (eval t p e0)) amLib
    |}
    ).
    simpl in *.

    assert (
      manifest_compiler (manifest_generator_app (eval t p e0)) amLib =
    manifest_compiler (manifest_generator_app (eval t p e0)) amLib
    ) by reflexivity.

    apply o in H1.

    +
    door.
    ++
      find_rewrite.
      left.
      eauto.
    ++
      find_rewrite.
      ff.

    +
      destruct initEvOpt.
      ff.

      rewrite no_nonces.
      cbv; intros; ff.


      unfold gen_nonce_if_none_local in *.
      am_monad_unfold.
      invc Heqp0.

      assert (a1 = a5).
      {
        unfold check_et_length in *.
        assert (
          Nat.eqb (et_size (eval t p (nn (am_nonceId st))))
            (length (run_cvm_rawEv t p [gen_nonce_bits] (amConfig a1))) = 
            true
        ).
        {
          Check EqNat.beq_nat_true_stt.
          Require Import PeanoNat.
          apply Nat.eqb_eq.
          eassumption.
        }
        ff.
      }
      subst.

      unfold config_AM_if_lib_supported in *.
      ff.

      unfold has_nonces.
      intros.

      assert (nid = (am_nonceId st)).
      {
        unfold nonce_ids_et in H1.

        apply nid_nonce_ids_eval in H1.

        door.
        solve_by_inversion.
        invc H1.
        reflexivity.
        solve_by_inversion.
      }
      subst.

      eexists.

      eapply mapC_get_works.
Qed.


*)

Abort.







(*

evcIn <- gen_nonce_if_none initEvOpt ;;
auth_evc <- gen_authEvC_if_some authPhrase myPlc mt_evc  ;;
let '(evc init_ev init_et) := evcIn in
let resev := am_sendReq t pTo auth_evc init_ev in 
match app_bool with
| true =>  
  app_res <- am_appraise t pTo init_et resev ;; 
  ret (am_appev app_res)
| false => ret (am_rawev resev)
end.

*)