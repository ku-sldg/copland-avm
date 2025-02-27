(*  Implementation of a top-level Client (initiator) thread for Client AMs in
      end-to-end Copland Attestation + Appraisal protocols.  *)
Require Import String.

Require Import Term EqClass.

Require Import IO_Stubs AM_Monad ErrorStMonad_Coq.

Require Import Maps Attestation_Session Interface.

Require Import ErrorStringConstants Manifest_Admits.

Require Import AM_Helpers AppraisalSummary.

Import ListNotations ErrNotation.

Import ResultNotation.

Definition am_sendReq (att_sess : Attestation_Session) (req_plc : Plc) 
    (e : Evidence) (t:Term) (toPlc : Plc) : ResultT RawEv string :=
  let req := (mkPRReq att_sess req_plc e t) in 
  let m :=  Plc_Mapping att_sess in 
    match (map_get toPlc m) with 
    | None => errC errStr_remote_am_failure (* TODO: better errStr here *)
    | Some uuid =>  

      let js := to_JSON req in
      let resp_res := make_JSON_Network_Request uuid js in 
      match resp_res with 
      | errC msg => errC msg
      | resultC js_res => 
          match from_JSON js_res with
          | errC msg => errC msg
          | resultC res =>
            let '(mkPRResp success (evc ev _)) := res in
            if success then resultC ev else errC errStr_remote_am_failure
          end
      end
    end.

Definition am_client_app_summary (att_sess : Attestation_Session) (req_plc : Plc) 
(e : Evidence) (t:Term) (toPlc : Plc) : ResultT AppraisalSummary string :=
  match (am_sendReq att_sess req_plc e t toPlc) with 
  | errC msg => errC msg 
  | resultC rawev => 
      let glob_ctx := (ats_context att_sess) in 
      match e with 
      | evc _ et => 
        et' <- eval glob_ctx toPlc et t ;;
        do_AppraisalSummary et' rawev glob_ctx cds_RawEvJudgement
      end
  end.

(*

Definition am_sendReq_app (uuid : UUID) (att_sess : Attestation_Session) (t:Term) (p:Plc) (e:EvidenceT) (ev:RawEv) : 
    ResultT AppResultC string :=
  let req := (mkPAReq att_sess t p e ev) in
  let js := to_JSON req in
  let resp_res := make_JSON_Network_Request uuid js in
  match resp_res with
  | resultC js_res =>
    match from_JSON js_res with
    | errC msg => errC msg
    | resultC res =>
      let '(mkPAResp success result) := res in
      if success then resultC result else errC errStr_remote_am_failure
    end
  | errC msg => errC msg
  end.

Definition gen_nonce_if_none_local (initEv:option Evidence) : AM Evidence :=
  match initEv with
  | Some (evc ebits et) => err_ret mt_evc
  | None =>
    let nonce_bits := gen_nonce_bits in
    nid <- am_newNonce nonce_bits ;;
    err_ret (evc [nonce_bits] (nonce_evt nid))
  end.

Definition run_appraisal_client (att_sess : Attestation_Session) (t:Term) (p:Plc) (et:EvidenceT) (re:RawEv) 
  (addr:UUID) : ResultT AppResultC string :=
  let expected_et := eval t p et in 
  am_sendReq_app addr att_sess t p et re.
  (*
  let comp := gen_appraise_AM expected_et re in
  run_am_app_comp comp mtc_app.
  *)

Definition run_demo_client_AM (t:Term) (top_plc:Plc) (att_plc:Plc) (et:EvidenceT) (att_sess : Attestation_Session)
  (re:RawEv) (attester_addr:UUID) (appraiser_addr:UUID) : ResultT AppResultC string :=
    let att_result := am_sendReq top_plc att_sess t attester_addr re in 
    match att_result with 
    | errC msg => errC msg 
    | resultC att_rawev => 
        run_appraisal_client att_sess t att_plc et att_rawev appraiser_addr
    end.

Definition check_et_length (et:EvidenceT) (ls:RawEv) : AM unit := 
if (eqb (et_size et) (length ls)) 
then err_ret tt 
else (am_failm (am_dispatch_error (Runtime errStr_et_size))).

Definition am_appraise (att_sess : Attestation_Session) (t:Term) (toPlc:Plc) (init_et:EvidenceT) (cvm_ev:RawEv) (apprUUID : UUID) (local_appraisal:bool) : AM AppResultC :=
  let expected_et := eval t toPlc init_et in
  check_et_length expected_et cvm_ev ;;

  app_res <- 
    (match local_appraisal with 
    | true => 
       let expected_et := eval t toPlc init_et in
        gen_appraise_AM expected_et cvm_ev 
    | false => 
      match run_appraisal_client att_sess t toPlc init_et cvm_ev apprUUID with
      | errC msg => am_failm (am_dispatch_error (Runtime msg))
      | resultC res => err_ret res
      end
    end) ;;
  (*
  let expected_et := eval t toPlc init_et in
  app_res <- gen_appraise_AM expected_et cvm_ev ;; *)
  err_ret (app_res).




*)





(*
  resev <- run_cvm_local_am t myPlc init_ev ;; 

  let expected_et := eval t myPlc init_et in 

  check_et_length expected_et resev ;;

  app_res <- gen_appraise_AM expected_et resev ;; 
  ret (am_appev app_res).

*)



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


(*
Lemma lib_support_bool_iff_prop : forall amLib absMan,
(lib_supports_manifest_bool amLib absMan = true) <->
lib_supports_manifest amLib absMan.
Proof.
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
Admitted.
*)

(* Definition run_cvm_local_am (t:Term) (ls:RawEv) : AM RawEv := 
  st <- get ;; 
  match (run_cvm_w_config t ls (amConfig st)) with
  | resultC cvm_st => ret (get_bits (st_ev cvm_st))
  | errC e => am_failm (cvm_error e)
  end. *)

(* Definition gen_authEvidence_if_some_local (ot:option Term) (myPlc:Plc) (init_evc:Evidence) (absMan:Manifest) (amLib:AM_Library) (aspBin : FS_Location) : AM Evidence :=
  match ot with
  | Some auth_phrase =>
      let '(evc init_rawev_auth init_et_auth) := init_evc in

      config_AM_if_lib_supported absMan amLib aspBin ;; 
      resev <- run_cvm_local_am auth_phrase init_rawev_auth ;;
      let auth_et := eval auth_phrase myPlc init_et_auth in 
      ret (evc resev auth_et)
  | None => ret (evc [] mt_evt)
  end.

Definition get_am_policy : AM PolicyT := 
  st <- get ;; 
  ret (policy (absMan (amConfig st))).

Definition check_disclosure_policy (t:Term) (p:Plc) (e:EvidenceT) : AM unit := 
  policy <- get_am_policy ;; 
  if (policy_list_not_disclosed t p e policy)
  then ret tt 
  else (am_failm (am_dispatch_error (Runtime errStr_disclosePolicy))).
*)

(* Definition am_client_gen_local (t:Term) (myPlc:Plc) (initEvOpt:option Evidence) 
    (absMan:Manifest) (amLib:AM_Library) (aspBin : FS_Location) : AM AM_Result := 
  evcIn <- gen_nonce_if_none_local initEvOpt ;; 
  (* auth_evc <- gen_authEvidence_if_some_local authPhrase myPlc mt_evc ;;  *)
  let '(evc init_ev init_et) := evcIn in 
  config_AM_if_lib_supported absMan amLib aspBin ;; 

  check_disclosure_policy t myPlc init_et ;;
  resev <- run_cvm_local_am t init_ev ;;  *)

  (*
  let expected_et := eval t myPlc init_et in 
  check_et_length expected_et resev ;;
  app_res <- gen_appraise_AM expected_et resev ;; 

  (*

  (t:Term) (toPlc:Plc) (init_et:EvidenceT) (cvm_ev:RawEv) : AM AppResultC :=
  
  *)

  app_res <- am_appraise t myPlc init_et resev (is_local_appraisal amLib) ;;


  ret (am_appev app_res).
*)





(*

Fixpoint nonce_ids_et' (et:EvidenceT) (ls:list N_ID) : list N_ID :=
  match et with
  | mt_evt=> ls
  | nonce_evt nid => nid :: ls 
  | split_evt et1 et2 => (nonce_ids_et' et2 (nonce_ids_et' et1 ls))
  | asp_evt _ _ _ et' => nonce_ids_et' et' ls
  end.

Definition nonce_ids_et (et:EvidenceT) : list N_ID :=
  nonce_ids_et' et [].



Inductive no_nonces_pred : EvidenceT -> Prop := 
| mt_no_nonce : no_nonces_pred mt_evt
| uu_no_nonce : forall p fwd ps et', 
    no_nonces_pred et' -> 
    no_nonces_pred (asp_evt p fwd ps et')
| ss_no_nonce : forall et1 et2,
    no_nonces_pred et1 -> 
    no_nonces_pred et2 -> 
    no_nonces_pred (split_evt et1 et2).

Lemma no_nonces'' : forall et ls,
  no_nonces_pred et -> 
  nonce_ids_et' et ls = ls.
Proof.
  induction et; intros; ffa.
  erewrite IHet1; ff.
Qed.


Lemma no_nonces_eval : forall t p et,
no_nonces_pred et -> 
no_nonces_pred (eval t p et).
Proof.
  induction t; intros; ffa.
  - destruct a; ffa using (econstructor).
    simpl in *; ff; try econstructor; simpl in *;
    destruct s; ff; econstructor.
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
  - ff.
    unfold eval_asp in *.
    destruct a;
    ff; subst; try destruct s; ff;
    try eapply no_nonces''; eauto.

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
nonce_ids_et (eval t p mt_evt) = [].
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
  induction et; intros; ffa;
  simpl in *.
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
  induction et; intros; ffa using intuition.
  -
    edestruct nonce_ids_ss_decom; ffa.

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
  - destruct a; ffa; try eapply nid_in_gen; auto;
    destruct s; ffa; eapply nonce_ids_et_cumul; eauto.
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
      In nid (nonce_ids_et' mt_evt[])

    ).
    eapply IHt2.
    apply H.

    door;
    eauto.

    solve_by_inversion.

    +
    assert (
      In nid (nonce_ids_et' (eval t1 p mt_evt) ls) \/ 
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
      In nid (nonce_ids_et' (eval t1 p mt_evt) ls) \/ 
      In nid (nonce_ids_et' mt_evt[])

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
    In nid (nonce_ids_et' mt_evt[])

  ).
  eapply IHt2.
  apply H.

  door;
  eauto.

  solve_by_inversion.

  +
  assert (
    In nid (nonce_ids_et' (eval t1 p mt_evt) ls) \/ 
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
    In nid (nonce_ids_et' (eval t1 p mt_evt) ls) \/ 
    In nid (nonce_ids_et' mt_evt[])

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

*)