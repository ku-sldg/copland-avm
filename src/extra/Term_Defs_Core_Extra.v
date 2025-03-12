

Require Import Lia.

Lemma EvidenceT_double_ind (P : EvidenceT -> Prop) 
    (f_mt : P mt_evt) 

    (f_nonce : forall n : N_ID, P (nonce_evt n))

    (f_asp_mt : forall p a, P (asp_evt p a mt_evt))
    (f_aps_nonce : forall p a n, P (asp_evt p a (nonce_evt n)))
    (f_asp_asp : forall (e : EvidenceT), P e -> 
      forall p p' a a', P (asp_evt p a (asp_evt p' a' e)))
    (f_asp_left : forall p a e, P (left_evt e) -> P (asp_evt p a (left_evt e)))
    (f_asp_right : forall p a e, P (right_evt e) -> P (asp_evt p a (right_evt e)))
    (f_asp_split : forall p a e1 e2, P e1 -> P e2 -> P (asp_evt p a (split_evt e1 e2)))

    (f_left_mt : P (left_evt mt_evt))
    (f_left_nonce : forall n : N_ID, P (left_evt (nonce_evt n)))
    (f_left_asp_mt : forall p a, P (left_evt (asp_evt p a mt_evt)))
    (f_left_asp_nonce : forall p a n, P (left_evt (asp_evt p a (nonce_evt n))))
    (f_left_asp_asp : forall e, P (left_evt e) -> 
      forall p a p' a', P (left_evt (asp_evt p a (asp_evt p' a' e))))
    (f_left_asp_left : forall e, P (left_evt e) -> 
      forall p a, P (left_evt (asp_evt p a (left_evt e))))
    (f_left_asp_right : forall e, P (right_evt e) -> 
      forall p a, P (left_evt (asp_evt p a (right_evt e))))
    (f_left_asp_split : forall e1 e2, P e1 -> P e2 -> 
      forall p a, P (left_evt (asp_evt p a (split_evt e1 e2))))
    (f_left_left : forall e : EvidenceT, P (left_evt e) -> P (left_evt (left_evt e)))
    (f_left_right : forall e : EvidenceT, P (right_evt e) -> P (left_evt (right_evt e)))
    (f_left_split : forall e1 e2 : EvidenceT, 
      P e1 -> 
      P (left_evt (split_evt e1 e2)))

    (f_right_mt : P (right_evt mt_evt))
    (f_right_nonce : forall n : N_ID, P (right_evt (nonce_evt n)))
    (f_right_asp_mt : forall p a, P (right_evt (asp_evt p a mt_evt)))
    (f_right_asp_nonce : forall p a n, P (right_evt (asp_evt p a (nonce_evt n))))
    (f_right_asp_asp : forall e, P (right_evt e) -> 
      forall p a p' a', P (right_evt (asp_evt p a (asp_evt p' a' e))))
    (f_right_asp_left : forall e, P (left_evt e) -> 
      forall p a, P (right_evt (asp_evt p a (left_evt e))))
    (f_right_asp_right : forall e, P (right_evt e) -> 
      forall p a, P (right_evt (asp_evt p a (right_evt e))))
    (f_right_asp_split : forall e1 e2, P e1 -> P e2 -> 
      forall p a, P (right_evt (asp_evt p a (split_evt e1 e2))))
    (f_right_left : forall e : EvidenceT, P e -> P (right_evt (left_evt e)))
    (f_right_right : forall e : EvidenceT, P e -> P (right_evt (right_evt e)))
    (f_right_split : forall e1 e2 : EvidenceT, 
      P e2 -> 
      P (right_evt (split_evt e1 e2)))

    (f_split : forall e : EvidenceT, P e -> 
      forall e0 : EvidenceT, P e0 -> P (split_evt e e0)) 
    : forall e, P e.
  assert (well_founded (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2)). {
    simpl in *.
    eapply Wf_nat.well_founded_ltof.
  }
  assert (forall x : EvidenceT, (forall y : EvidenceT, (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2) y x -> P y) -> P x). {
    destruct x; simpl in *; eauto; intros F.
    - destruct x; eauto.
      eapply f_asp_split; eapply F; simpl in *; eauto; lia.
    - destruct x; eauto.
      * destruct x; eauto.
        (* ** eapply f_left_asp_asp; eapply F; simpl in *; eauto; lia. *)
        (* ** eapply f_left_asp_left; eapply F; simpl in *; eauto; lia. *)
        (* ** eapply f_left_asp_right; eapply F; simpl in *; eauto; lia. *)
        ** eapply f_left_asp_split; eapply F; simpl in *; eauto; lia.
      * eapply f_left_split; eapply F; eauto; simpl in *; lia.
    - destruct x; eauto.
      * destruct x; eauto.
        (* ** eapply f_right_asp_asp; eapply F; simpl in *; eauto; lia. *)
        (* ** eapply f_right_asp_left; eapply F; simpl in *; eauto; lia. *)
        (* ** eapply f_right_asp_right; eapply F; simpl in *; eauto; lia. *)
        ** eapply f_right_asp_split; eapply F; simpl in *; eauto; lia.
      * eapply f_right_split; eapply F; eauto; simpl in *; lia.
    - eapply f_split; eapply F; simpl in *; eauto; lia.
  }
  eapply well_founded_ind; eauto.
Qed.

Lemma EvidenceT_double_ind_2 (P : EvidenceT -> Prop) 
    (f_mt : P mt_evt) 

    (f_nonce : forall n : N_ID, P (nonce_evt n))

    (* (f_asp_mt : forall p a, P (asp_evt p a mt_evt))
    (f_aps_nonce : forall p a n, P (asp_evt p a (nonce_evt n)))
    (f_asp_asp : forall (e : EvidenceT), P e -> 
      forall p p' a a', P (asp_evt p a (asp_evt p' a' e)))
    (f_asp_left : forall p a e, P (left_evt e) -> P (asp_evt p a (left_evt e)))
    (f_asp_right : forall p a e, P (right_evt e) -> P (asp_evt p a (right_evt e))) 
    (f_asp_split : forall p a e1 e2, P e1 -> P e2 -> P (asp_evt p a (split_evt e1 e2))) *)
    (f_asp : forall p a e, P e -> P (asp_evt p a e))

    (f_left_mt : P (left_evt mt_evt))
    (f_left_nonce : forall n : N_ID, P (left_evt (nonce_evt n)))
    (f_left_asp : forall p a e, P (asp_evt p a e) -> P (left_evt (asp_evt p a e)))
    (f_left_left : forall e : EvidenceT, P (left_evt e) -> P (left_evt (left_evt e)))
    (f_left_right : forall e : EvidenceT, P (right_evt e) -> P (left_evt (right_evt e)))
    (f_left_split : forall e1 e2 : EvidenceT, 
      P e1 -> 
      P (left_evt (split_evt e1 e2)))

    (f_right_mt : P (right_evt mt_evt))
    (f_right_nonce : forall n : N_ID, P (right_evt (nonce_evt n)))
    (f_right_asp : forall p a e, P (asp_evt p a e) -> P (right_evt (asp_evt p a e)))
    (f_right_left : forall e : EvidenceT, P e -> P (right_evt (left_evt e)))
    (f_right_right : forall e : EvidenceT, P e -> P (right_evt (right_evt e)))
    (f_right_split : forall e1 e2 : EvidenceT, 
      P e2 -> 
      P (right_evt (split_evt e1 e2)))

    (f_split : forall e : EvidenceT, P e -> 
      forall e0 : EvidenceT, P e0 -> P (split_evt e e0)) 
    : forall e, P e.
  assert (well_founded (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2)). {
    simpl in *.
    eapply Wf_nat.well_founded_ltof.
  }
  assert (forall x : EvidenceT, (forall y : EvidenceT, (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2) y x -> P y) -> P x). {
    destruct x; simpl in *; eauto; intros F.
    - destruct x; eauto.
      eapply f_left_split; eapply F; eauto; simpl in *; lia.
    - destruct x; eauto.
      eapply f_right_split; eapply F; eauto; simpl in *; lia.
    - eapply f_split; eapply F; simpl in *; eauto; lia.
  }
  eapply well_founded_ind; eauto.
Qed.

Lemma EvidenceT_triple_ind (P : EvidenceT -> Prop) 
    (f_mt : P mt_evt) 

    (f_nonce : forall n : N_ID, P (nonce_evt n))

    (f_asp_mt : forall p a, P (asp_evt p a mt_evt))
    (f_aps_nonce : forall p a n, P (asp_evt p a (nonce_evt n)))

    (f_asp_asp_mt : forall p p' a a', P (asp_evt p a (asp_evt p' a' mt_evt)))
    (f_asp_asp_nonce : forall n,
      forall p p' a a', P (asp_evt p a (asp_evt p' a' (nonce_evt n))))
    (f_asp_asp_asp : forall e, P e -> 
      forall p a p' a' p'' a'', 
        P (asp_evt p a (asp_evt p' a' (asp_evt p'' a'' e))))
    (f_asp_asp_left : forall p a p' a' e, P (left_evt e) -> 
      P (asp_evt p a (asp_evt p' a' (left_evt e))))
    (f_asp_asp_right : forall p a p' a' e, P (right_evt e) ->
      P (asp_evt p a (asp_evt p' a' (right_evt e))))
    (f_asp_asp_split : forall p a p' a' e1 e2, P e1 -> P e2 -> 
      P (asp_evt p a (asp_evt p' a' (split_evt e1 e2))))

    (f_asp_left : forall p a e, P (left_evt e) -> P (asp_evt p a (left_evt e)))
    (f_asp_right : forall p a e, P (right_evt e) -> P (asp_evt p a (right_evt e)))
    (f_asp_split : forall p a e1 e2, P e1 -> P e2 -> P (asp_evt p a (split_evt e1 e2)))

    (f_left_mt : P (left_evt mt_evt))
    (f_left_nonce : forall n : N_ID, P (left_evt (nonce_evt n)))
    (f_left_asp_mt : forall p a, P (left_evt (asp_evt p a mt_evt)))
    (f_left_asp_nonce : forall p a n, P (left_evt (asp_evt p a (nonce_evt n))))
    (f_left_asp_asp : forall e, P (left_evt e) -> 
      forall p a p' a', P (left_evt (asp_evt p a (asp_evt p' a' e))))
    (f_left_asp_left : forall e, P (left_evt e) -> 
      forall p a, P (left_evt (asp_evt p a (left_evt e))))
    (f_left_asp_right : forall e, P (right_evt e) -> 
      forall p a, P (left_evt (asp_evt p a (right_evt e))))
    (f_left_asp_split : forall e1 e2, P e1 -> P e2 -> 
      forall p a, P (left_evt (asp_evt p a (split_evt e1 e2))))
    (f_left_left : forall e : EvidenceT, P (left_evt e) -> P (left_evt (left_evt e)))
    (f_left_right : forall e : EvidenceT, P (right_evt e) -> P (left_evt (right_evt e)))
    (f_left_split : forall e1 e2 : EvidenceT, 
      P e1 -> 
      P (left_evt (split_evt e1 e2)))

    (f_right_mt : P (right_evt mt_evt))
    (f_right_nonce : forall n : N_ID, P (right_evt (nonce_evt n)))
    (f_right_asp_mt : forall p a, P (right_evt (asp_evt p a mt_evt)))
    (f_right_asp_nonce : forall p a n, P (right_evt (asp_evt p a (nonce_evt n))))
    (f_right_asp_asp : forall e, P (right_evt e) -> 
      forall p a p' a', P (right_evt (asp_evt p a (asp_evt p' a' e))))
    (f_right_asp_left : forall e, P (left_evt e) -> 
      forall p a, P (right_evt (asp_evt p a (left_evt e))))
    (f_right_asp_right : forall e, P (right_evt e) -> 
      forall p a, P (right_evt (asp_evt p a (right_evt e))))
    (f_right_asp_split : forall e1 e2, P e1 -> P e2 -> 
      forall p a, P (right_evt (asp_evt p a (split_evt e1 e2))))
    (f_right_left : forall e : EvidenceT, P e -> P (right_evt (left_evt e)))
    (f_right_right : forall e : EvidenceT, P e -> P (right_evt (right_evt e)))
    (f_right_split : forall e1 e2 : EvidenceT, 
      P e2 -> 
      P (right_evt (split_evt e1 e2)))

    (f_split : forall e : EvidenceT, P e -> 
      forall e0 : EvidenceT, P e0 -> P (split_evt e e0)) 
    : forall e, P e.
  assert (well_founded (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2)). {
    simpl in *.
    eapply Wf_nat.well_founded_ltof.
  }
  assert (forall x : EvidenceT, (forall y : EvidenceT, (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2) y x -> P y) -> P x). {
    destruct x; simpl in *; eauto; intros F; eauto.
    - destruct x; eauto.
      * destruct x; eauto.
        ** eapply f_asp_asp_asp; eapply F; simpl in *; eauto; lia.
        ** eapply f_asp_asp_split; eapply F; simpl in *; eauto; lia.
      * eapply f_asp_split; eapply F; simpl in *; eauto; lia.
    - destruct x; eauto.
      * destruct x; eauto.
        (* ** eapply f_left_asp_asp; eapply F; simpl in *; eauto; lia. *)
        (* ** eapply f_left_asp_left; eapply F; simpl in *; eauto; lia. *)
        (* ** eapply f_left_asp_right; eapply F; simpl in *; eauto; lia. *)
        ** eapply f_left_asp_split; eapply F; simpl in *; eauto; lia.
      * eapply f_left_split; eapply F; eauto; simpl in *; lia.
    - destruct x; eauto.
      * destruct x; eauto.
        (* ** eapply f_right_asp_asp; eapply F; simpl in *; eauto; lia. *)
        (* ** eapply f_right_asp_left; eapply F; simpl in *; eauto; lia. *)
        (* ** eapply f_right_asp_right; eapply F; simpl in *; eauto; lia. *)
        ** eapply f_right_asp_split; eapply F; simpl in *; eauto; lia.
      * eapply f_right_split; eapply F; eauto; simpl in *; lia.
    - eapply f_split; eapply F; simpl in *; eauto; lia.
  }
  eapply well_founded_ind; eauto.
Qed.

Module Test_Unwrap_Wrap.
  Definition X : ASP_ID. Admitted.
  Definition X' : ASP_ID. Admitted.
  Definition Y : ASP_ID. Admitted.
  Definition Y' : ASP_ID. Admitted.
  Axiom XX' : X <> X'.
  Axiom XY : X <> Y.
  Axiom XY' : X <> Y'.
  Axiom YY' : Y <> Y'.
  Axiom X'Y' : X' <> Y'.
  Axiom X'Y : X' <> Y.
  Ltac use_neqs :=
    pose proof XX';
    pose proof XY;
    pose proof XY';
    pose proof YY';
    pose proof X'Y';
    pose proof X'Y;
    try (exfalso; eauto; fail).

  Definition P1 : Plc. Admitted.
  Definition P2 : Plc. Admitted.
  Definition T_PLC : Plc. Admitted.
  Definition TARG : TARG_ID. Admitted.

  Definition G : GlobalContext := Build_GlobalContext 
    [(X, ev_arrow WRAP InAll (OutN 1)); (Y, ev_arrow WRAP InAll (OutN 1));
      (X', ev_arrow UNWRAP InAll OutUnwrap); (Y', ev_arrow UNWRAP InAll OutUnwrap)] 
    [(X, X'); (Y, Y')].
  
  Ltac str_rew :=
    repeat rewrite String.eqb_eq in *;
    repeat rewrite String.eqb_refl in *;
    subst_max;
    repeat rewrite String.eqb_neq in *;
    try lazymatch goal with
    | H : true = false |- _ => inversion H
    end.

  Example test_get_evidence_under_unwrap_wrap_1 : forall v,
    apply_to_evidence_below G (fun e => e) [Trail_UNWRAP X'] 
      (asp_evt P1 (asp_paramsC X nil T_PLC TARG) v) = resultC v.
  Proof.
    ff; str_rew.
    destruct v; simpl in *; eauto.
  Qed.

  Example test_get_evidence_under_unwrap_wrap_2 : forall v,
    apply_to_evidence_below G (fun e => e) [Trail_UNWRAP X'; Trail_UNWRAP Y'] 
      (asp_evt P1 (asp_paramsC X nil T_PLC TARG) (
        asp_evt P2 (asp_paramsC Y nil T_PLC TARG) v)) = resultC v.
  Proof.
    ff; str_rew.
    destruct v; simpl in *; eauto.
    destruct v; simpl in *; eauto.
    use_neqs.
  Qed.
  
  Example test_get_evidence_under_unwrap_wrap_3 : forall v,
    apply_to_evidence_below G (fun e => e) [Trail_UNWRAP X'] 
      (asp_evt P1 (asp_paramsC X nil T_PLC TARG) (
        asp_evt P2 (asp_paramsC Y nil T_PLC TARG) v)) 
    = resultC (asp_evt P2 (asp_paramsC Y nil T_PLC TARG) v).
  Proof.
    ff; str_rew.
  Qed.

  Example test_get_evidence_under_unwrap_wrap_4 : forall v,
    apply_to_evidence_below G (fun e => e) [Trail_UNWRAP X'] 
      ( asp_evt P2 (asp_paramsC Y' nil T_PLC TARG) 
        (asp_evt P2 (asp_paramsC Y nil T_PLC TARG) 
        (asp_evt P1 (asp_paramsC X nil T_PLC TARG) v)))
    = resultC v.
  Proof.
    ff.
    all: str_rew.
    all: use_neqs.
    destruct v; simpl in *; eauto.
  Qed.

  Example test_get_evidence_under_unwrap_wrap_5 : forall v,
    apply_to_evidence_below G (fun e => e) [Trail_UNWRAP X'; Trail_UNWRAP Y'] 
      (asp_evt P1 (asp_paramsC X nil T_PLC TARG) (
        left_evt (split_evt (asp_evt P2 (asp_paramsC Y nil T_PLC TARG) v) mt_evt))) 
    = resultC v.
  Proof.
    ff; str_rew.
    destruct v; simpl in *; eauto.
    destruct v; simpl in *; eauto.
    use_neqs.
  Qed.

  Example test_get_evidence_under_unwrap_wrap_6 : forall v,
    apply_to_evidence_below G (fun e => e) [Trail_UNWRAP X'; Trail_UNWRAP Y'] 
      (asp_evt P1 (asp_paramsC X nil T_PLC TARG) (
        right_evt (split_evt mt_evt (asp_evt P2 (asp_paramsC Y nil T_PLC TARG) v)))) 
    = resultC v.
  Proof.
    ff; str_rew.
    destruct v; simpl in *; eauto.
    destruct v; simpl in *; eauto.
    use_neqs.
  Qed.
End Test_Unwrap_Wrap.