Require Import Term_Defs Term StAM Maps ConcreteEvidence OptMonad Auto.

(* Require Import Impl_appraisal (*MonadAM*). *)

Require Import AutoApp StructTactics.

Require Import List.
Import ListNotations.

Require Import Lia Coq.Program.Tactics.

Definition peel_bs (ls:EvBits) : option (BS * EvBits) :=
  match ls with
  | bs :: ls' => Some (bs, ls')
  | _ => None
  end.

Lemma peel_fact': forall e x y H,
    length e = S x ->
    peel_bs e = Some (y, H) ->
    length H = x.
Proof.
  intros.
  destruct e;
    ff; eauto.
Defined.

Lemma peel_fact: forall e x y H et,
    length e = S x ->
    peel_bs e = Some (y, H) ->
    et_size et = x ->
    wf_ec (evc H et).
Proof.
  intros.
  econstructor.
  eapply peel_fact'; eauto.
  lia.
Defined.


Fixpoint encodeEv (e:EvidenceC) : EvBits :=
  match e with
  | mtc => []
  | nnc _ bs => [bs]
  | uuc _ _ _ _ bs e' =>
    bs :: (encodeEv e')
  | ggc _ bs e' =>
    bs :: (encodeEv e')
  | hhc _ bs _ =>
    [bs]
  | ssc e1 e2 =>
    (encodeEv e1) ++ (encodeEv e2)
  | ppc e1 e2 =>
    (encodeEv e1) ++ (encodeEv e2)
  end.

Fixpoint reconstruct_ev' (ls:EvBits) (et:Evidence) : option EvidenceC :=
  match et with
  | mt => (* Some mtc *)
    match ls with
    | [] => Some mtc
    | _ => None
    end 
  | uu i args tpl tid et' =>
    '(bs, ls') <- peel_bs ls ;;
    x <- reconstruct_ev' ls' et' ;;
    Some (uuc i args tpl tid bs x)
  | gg p et' =>
    '(bs, ls') <- peel_bs ls ;;
    x <- reconstruct_ev' ls' et' ;;
    Some (ggc p bs x)
  | hh p et' =>
    '(bs, ls') <- peel_bs ls ;;
     match ls' with
    | [] => Some (hhc p bs et')
    | _ => None
    end 
   
  | nn i =>
    '(bs, ls') <- peel_bs ls ;;
     match ls' with
    | [] => Some (nnc i bs)
    | _ => None
    end 
    
  | ss et1 et2 =>
    e1 <- reconstruct_ev' (firstn (et_size et1) ls) et1 ;;
    e2 <- reconstruct_ev' (skipn (et_size et1) ls) et2 ;;
    Some (ssc e1 e2)
  | pp et1 et2 =>
    e1 <- reconstruct_ev' (firstn (et_size et1) ls) et1 ;;
    e2 <- reconstruct_ev' (skipn (et_size et1) ls) et2 ;;
    Some (ppc e1 e2)  
  end.

Definition reconstruct_ev (e:EvC) : option EvidenceC :=
  match e with
  | evc ls et => reconstruct_ev' ls et
  end.

Definition checkASP (i:ASP_ID) (args:list Arg) (tpl:Plc) (tid:Plc) (bs:BS) : BS.
Admitted.

Definition checkSigBits (ls:EvBits) (p:Plc) (sig:BS) : BS.
Admitted.

Definition checkSig (e:EvidenceC) (p:Plc) (sig:BS) : BS :=
  checkSigBits (encodeEv e) p sig.

Definition checkHash (e:Evidence) (p:Plc) (hash:BS) : BS.
Admitted.

Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p i args tpl tid, evidenceEvent (umeas n p i args tpl tid).

Definition measEvent (t:AnnoTerm) (p:Plc) (e:Evidence) (ev:Ev) : Prop :=
  events t p e ev /\ evidenceEvent ev.

Inductive sigEventP: Ev -> Prop :=
| sev: forall n p e, sigEventP (sign n p e).

Definition sigEvent (t:AnnoTerm) (p:Plc) (e:Evidence) (ev:Ev) : Prop :=
  events t p e ev /\ sigEventP ev.

Inductive appEvent_EvidenceC : Ev -> EvidenceC -> Prop :=
| aeuc: forall i args tpl tid e e' n p,
    EvSub (uuc i args tpl tid (checkASP i args tpl tid n) e') e ->
    appEvent_EvidenceC (umeas n p i args tpl tid) e
| ahuc: forall i args tpl tid e' et n p pi bs e,
    EvSubT (uu i args tpl tid  e') et ->
    EvSub (hhc pi (checkHash et pi bs) et) e ->
    appEvent_EvidenceC (umeas n p i args tpl tid) e.

Inductive appEvent_Sig_EvidenceC: Ev -> EvidenceC -> Prop :=
| asigc: forall n p sig e e' e'',
    EvSub (ggc p (checkSig e' p sig) e'') e ->
    appEvent_Sig_EvidenceC (sign n p (et_fun e')) e.

Definition none_none_term (t:AnnoTerm): Prop :=
  (exists t1 t2 r,
      t = abseq r (NONE,NONE) t1 t2)
  \/
  (exists t1 t2 r,
      t = abpar r (NONE,NONE) t1 t2).

Definition not_none_none (t:AnnoTerm) :=
  forall t',
    none_none_term t'  -> 
    ~ (term_sub t' t).

Definition hash_sig_term (t:AnnoTerm): Prop :=
  exists r r1 r2 t1 t2,
  t = alseq r t1 t2 /\
  term_sub (aasp r1 SIG) t1 /\
  term_sub (aasp r2 HSH) t2.

Definition not_hash_sig_term (t:AnnoTerm) :=
  forall t',
    hash_sig_term t'  -> 
    ~ (term_sub t' t).

Definition hash_sig_ev (e:EvidenceC): Prop :=
  exists p p' bs et et',
    e = hhc p bs et /\ 
    EvSubT (gg p' et') et.

Definition not_hash_sig_ev (e:EvidenceC) :=
  forall e',
    hash_sig_ev e' ->
    ~ (EvSub e' e).

Definition gg_sub (e:EvidenceC) :=
  exists p bs e'' e', e' = ggc p bs e'' /\
                 EvSub e' e.

Definition hsh_subt (t:AnnoTerm) :=
  exists r, term_sub (aasp r HSH) t.

Definition not_hash_sig_term_ev (t:AnnoTerm) (e:EvidenceC): Prop :=
  not_hash_sig_term t /\
  not_hash_sig_ev e /\
  ((gg_sub e) -> ~ (hsh_subt t)).

Ltac measEventFacts :=
  match goal with
  | [H: measEvent _ _ _ _ |- _] => invc H
  end.

Ltac evEventFacts :=
  match goal with
  | [H: evidenceEvent _ |- _] => invc H
  end.

Ltac invEvents :=
  match goal with
  | [H: events _ _ _ _  |- _] => invc H
  end.

Lemma inv_recon_mt: forall ls et,
    Some mtc = reconstruct_ev' ls et ->
    et = mt.
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
Defined.

Ltac do_inv_recon_mt :=
  match goal with
  | [H: Some mtc = reconstruct_ev' _ ?et

     |- _] =>
    assert_new_proof_by (et = mt) ltac:(eapply inv_recon_mt; apply H)
  end;
  subst.

Lemma inv_recon_nn: forall ls et n n0,
    Some (nnc n n0) = reconstruct_ev' ls et ->
    et = nn n.
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
Defined.

Ltac do_inv_recon_nn :=
  match goal with
  | [H: Some (nnc ?n _) = reconstruct_ev' _ ?et

     |- _] =>
    assert_new_proof_by (et = nn n) ltac:(eapply inv_recon_nn; apply H)
  end;
  subst.

Lemma inv_recon_uu: forall ls et n l n0 n1 n2 ec,
    Some (uuc n l n0 n1 n2 ec) = reconstruct_ev' ls et  ->
    (exists et', et = uu n l n0 n1 et').
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
  eauto.
Defined.

Ltac do_inv_recon_uu :=
  match goal with
  | [H: Some (uuc ?n ?l ?n0 ?n1 _ _) = reconstruct_ev' _ ?et

     |- _] =>
    assert_new_proof_by (exists et', et = uu n l n0 n1 et')
                        ltac:(eapply inv_recon_uu; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_gg: forall ls et n n0 ec,
    Some (ggc n n0 ec) = reconstruct_ev' ls et ->
    (exists et', et = gg n et').
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
  eauto.
Defined.

Ltac do_inv_recon_gg :=
  match goal with
  | [H: Some (ggc ?n _ _) = reconstruct_ev' _ ?et

     |- _] =>
    assert_new_proof_by (exists et', et = gg n et')
                        ltac:(eapply inv_recon_gg; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_hh: forall ls et n n0 et',
    Some (hhc n n0 et') = reconstruct_ev' ls et  ->
    (et = hh n et' ).
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
Defined.

Ltac do_inv_recon_hh :=
  match goal with
  | [H: Some (hhc ?n _ ?et') = reconstruct_ev' _ ?et

     |- _] =>
    assert_new_proof_by (et = hh n et')
                        ltac:(eapply inv_recon_hh; apply H)
  end;
  subst.

Lemma inv_recon_ss: forall ls et ec1 ec2,
    Some (ssc ec1 ec2) = reconstruct_ev' ls et ->
    (exists et1 et2, et = ss et1 et2).
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
  eauto.
Defined.

Ltac do_inv_recon_ss :=
  match goal with
  | [H: Some (ssc _ _) = reconstruct_ev' _ ?et

     |- _] =>
    assert_new_proof_by (exists et1 et2, et = ss et1 et2)
                        ltac:(eapply inv_recon_ss; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_pp: forall ls et ec1 ec2,
    Some (ppc ec1 ec2) = reconstruct_ev' ls et ->
    (exists et1 et2, et = pp et1 et2).
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
  eauto.
Defined.

Ltac do_inv_recon_pp :=
  match goal with
  | [H: Some (ppc _ _) = reconstruct_ev' _ ?et

     |- _] =>
    assert_new_proof_by (exists et1 et2, et = pp et1 et2)
                        ltac:(eapply inv_recon_pp; apply H)
  end;
  destruct_conjs;
  subst.

Ltac do_inv_recon :=
  try do_inv_recon_mt;
  try do_inv_recon_nn;
  try do_inv_recon_uu;
  try do_inv_recon_gg;
  try do_inv_recon_hh;
  try do_inv_recon_ss;
  try do_inv_recon_pp.

Lemma firstn_long: forall (e:list BS) x,
    length e >= x ->
    length (firstn x e) = x.
Proof.
  intros.
  eapply firstn_length_le.
  lia.
Defined.

Lemma skipn_long: forall (e:list BS) x y,
    length e = x + y ->
    length (skipn x e) = y.
Proof.
  intros.
  assert (length (skipn x e) = length e - x).
  { eapply skipn_length. }
  lia.
Defined.

Lemma recon_encodeEv : forall ls et ec,
    wf_ec (evc ls et) -> 
    reconstruct_ev' ls et = Some ec ->
    ls = encodeEv ec.
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros.
  -
    ff.
    assert (et = mt).
    {
      eapply inv_recon_mt; eauto.
    }
    subst.
    invc H.
    ff.
    destruct ls; try solve_by_inversion.
  (* TODO: exclude mt case? *)
  -
    ff.
    assert (et = nn n).
    {
      eapply inv_recon_nn; eauto.
    }
    subst.
    repeat ff.
    destruct ls; try solve_by_inversion.

    (*
    invc H.
    ff.
    assert (e = []).
    destruct e; try solve_by_inversion.
    ff. *)
  -
    ff.
    assert (exists et', et = uu n l n0 n1 et').
    {
      eapply inv_recon_uu; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H.
    ff.
    edestruct IHec with (ls := e).
    2: {
      eassumption.
    }
    econstructor.
    destruct ls; try solve_by_inversion.
    unfold peel_bs in *.
    ff.
  -
    ff.
    assert (exists et', et = gg n et').
    {
      eapply inv_recon_gg; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H.
    ff.
    edestruct IHec with (ls := e).
    2: {
      eassumption.
    }
    econstructor.
    destruct ls; try solve_by_inversion.
    unfold peel_bs in *.
    ff.
  -
    ff.
    assert (et = hh n e).
    {
      eapply inv_recon_hh; eauto.
    }
    subst.
    repeat ff.
    invc H.
    ff.
    destruct ls; try solve_by_inversion.
  -
    ff.
    assert (exists et1 et2, et = ss et1 et2).
    {
      eapply inv_recon_ss; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H.
    ff.

    assert ((firstn (et_size H1) ls) = encodeEv ec1).
    { eapply IHec1 with (et:= H1).
      econstructor.
      eapply firstn_long.
      lia.
      eassumption.
    }

    assert ((skipn (et_size H1) ls) = encodeEv ec2).
    {
      eapply IHec2 with (et := H2).
      econstructor.
      eapply skipn_long.
      lia.
      eassumption.
    }
    jkjke'.
    jkjke'.
    rewrite firstn_skipn.
    tauto.
    -
      ff.
    assert (exists et1 et2, et = pp et1 et2).
    {
      eapply inv_recon_pp; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H.
    ff.

    assert ((firstn (et_size H1) ls) = encodeEv ec1).
    { eapply IHec1 with (et:= H1).
      econstructor.
      eapply firstn_long.
      lia.
      eassumption.
    }

    assert ((skipn (et_size H1) ls) = encodeEv ec2).
    {
      eapply IHec2 with (et := H2).
      econstructor.
      eapply skipn_long.
      lia.
      eassumption.
    }
    jkjke'.
    jkjke'.
    rewrite firstn_skipn.
    tauto.
Defined.

Lemma wf_recon: forall e et ec,
    reconstruct_ev' e et = Some ec ->
    wf_ec (evc e et).
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros.
  -
    assert (et = mt).
    eapply inv_recon_mt; eauto.
    subst.
    repeat ff.
    econstructor.
    tauto.
  -
    assert (et = nn n) by (eapply inv_recon_nn; eauto).
    subst.
    repeat ff.
    econstructor.
    ff.
    destruct e; try solve_by_inversion.
  -
    assert (exists et', et = uu n l n0 n1 et').
    { eapply inv_recon_uu; eauto. }
    destruct_conjs.
    subst.
    repeat ff.
    assert (wf_ec (evc e0 H0)) by eauto.
    econstructor.
    ff.
    invc H.
    destruct e; try solve_by_inversion.
    ff.
    lia.
  -
    assert (exists et', et = gg n et').
    { eapply inv_recon_gg; eauto. }
    destruct_conjs.
    subst.
    repeat ff.
    assert (wf_ec (evc e0 H0)) by eauto.
    econstructor.
    ff.
    invc H.
    destruct e; try solve_by_inversion.
    ff.
    lia.
  -
    assert (et = hh n e).
    { eapply inv_recon_hh; eauto.
    }
    subst.
    repeat ff.
    
    
    econstructor.
    ff.
    destruct e0; try solve_by_inversion.
  -
    assert (exists et1 et2, et = ss et1 et2).
    { eapply inv_recon_ss; eauto. }
    destruct_conjs.
    subst.
    repeat ff.

    assert (wf_ec (evc (firstn (et_size H0) e) H0)) by eauto.

    assert (wf_ec (evc (skipn (et_size H0) e) H1)) by eauto.

    invc H; invc H2.
    econstructor.
    ff.
    rewrite <- H4.
    rewrite <- H3.
    assert (e = (firstn (et_size H0) e) ++ (skipn (et_size H0) e)).
    
    { rewrite firstn_skipn.
      tauto.
    }
    rewrite H at 1.
    eapply app_length.
  -
    assert (exists et1 et2, et = pp et1 et2).
    { eapply inv_recon_pp; eauto. }
    destruct_conjs.
    subst.
    repeat ff.

    assert (wf_ec (evc (firstn (et_size H0) e) H0)) by eauto.

    assert (wf_ec (evc (skipn (et_size H0) e) H1)) by eauto.

    invc H; invc H2.
    econstructor.
    ff.
    rewrite <- H4.
    rewrite <- H3.
    assert (e = (firstn (et_size H0) e) ++ (skipn (et_size H0) e)).
    
    { rewrite firstn_skipn.
      tauto.
    }
    rewrite H at 1.
    eapply app_length.
Defined.
