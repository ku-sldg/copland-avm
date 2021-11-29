Require Import Term_Defs Term ConcreteEvidence OptMonad Auto More_lists Appraisal_Evidence VmSemantics IO_Stubs AutoPrim AutoApp Evidence_Bundlers.

(* Require Import Impl_appraisal (*MonadAM*). *)

Require Import StructTactics.

Require Import List.
Import ListNotations.

Require Import Lia Coq.Program.Tactics.

Definition checkASP (params:ASP_PARAMS) (bs:BS) : option BS.
Admitted.

Definition checkASPF (params:ASP_PARAMS) (bs:BS) : BS :=
  fromSome default_bs (checkASP params bs).

Definition checkSigBits (ls:RawEv) (p:Plc) (sig:BS) : option BS.
Admitted.

Definition checkSigBitsF (ls:RawEv) (p:Plc) (sig:BS) : BS :=
  fromSome default_bs (checkSigBits ls p sig).

Definition checkNonce (nid:nat) (val:BS) : option BS.
Admitted.

Definition checkNonceF (nid:nat) (val:BS) : BS :=
  fromSome default_bs (checkNonce nid val).

Definition checkSig (e:EvidenceC) (p:Plc) (sig:BS) : option BS :=
  checkSigBits (encodeEv e) p sig.

Definition checkSigF (e:EvidenceC) (p:Plc) (sig:BS) : BS :=
  fromSome default_bs (checkSig e p sig).

Fixpoint checkHash (e:Evidence) (p:Plc) (hash:BS) : option BS :=
  match e with
  | gg _ _ => None
  | mt => ret default_bs (* TODO: implement reconstruct_hash and ignore mt *)
  | nn _ => ret default_bs (* TODO: reconstruct_hash will grab nonce value here *)
  | uu _  _ e' => checkHash e' p hash
  | hh _ e' => checkHash e' p hash
  | ss e1 e2 =>
    res1 <- checkHash e1 p hash ;;
    res2 <- checkHash e2 p hash ;;
    ret default_bs
  | pp e1 e2 =>
    res1 <- checkHash e1 p hash ;;
    res2 <- checkHash e2 p hash ;;
    ret default_bs
  end.

Definition checkHashF (e:Evidence) (p:Plc) (hash:BS) : BS :=
  fromSome default_bs (checkHash e p hash).

Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p ps e, evidenceEvent (umeas n p ps e).

Definition measEvent (t:AnnoTerm) (p:Plc) (e:Evidence) (ev:Ev) : Prop :=
  events t p e ev /\ evidenceEvent ev.

Inductive sigEventP: Ev -> Prop :=
| sev: forall n p e, sigEventP (sign n p e).

Definition sigEvent (t:AnnoTerm) (p:Plc) (e:Evidence) (ev:Ev) : Prop :=
  events t p e ev /\ sigEventP ev.

Inductive appEvent_EvidenceC : Ev -> EvidenceC -> Prop :=
| aeuc: forall e e' e'' n p params,
    (*let params := (asp_paramsC i args tpl tid) in *)
    EvSub (uuc params p
               (checkASPF params
                          (do_asp params (encodeEv e') p n)) e'') e ->
    appEvent_EvidenceC (umeas n p params (et_fun e')) e
| ahuc: forall ps e' et n p pi bs e,
    EvSubT (uu ps p e') et ->
    EvSub (hhc pi (checkHashF et pi bs) et) e ->
    appEvent_EvidenceC (umeas n p ps e') e.

(*
Inductive appEvent_Sig_EvidenceC: Ev -> EvidenceC -> Prop :=
| asigc: forall n p e e' e'' ee,
    EvSub (ggc p (checkSigF e' p (do_sig ee p n)) e'') e ->
    appEvent_Sig_EvidenceC (sign n p (et_fun e')) e.
 *)

(*
Inductive signs_meas: AnnoTerm -> Event_ID -> BS -> Prop :=
| sm_asp: forall t t1 t2 et1 et2 et2' x mpl id l tpl tid n p q r,
    events t1 p et1 (umeas x mpl id l tpl tid) ->
    events t2 p et2 (sign n q et2') ->
    term_sub (alseq r t1 t2) t ->
    signs_meas t n (do_asp (asp_paramsC id l tpl tid) mpl x).

Definition signs_all_meas (t:AnnoTerm) (x:Event_ID) (bits:list BS) :=
  forall (v:BS),
  signs_meas t x v ->
  In v bits.

Inductive appEvent_Sig_EvidenceC': AnnoTerm -> Ev -> EvidenceC -> Prop :=
| asigc: forall t n p e e'' bits et,
    (*let e' := (evc bits et) in *)
    signs_all_meas t n bits ->
    EvSub (ggc p (checkSigBitsF bits p (do_sig (encodeEvBits (evc bits et)) p n)) e'') e ->
    appEvent_Sig_EvidenceC' t (sign n p et) e.
*)

Inductive appEvent_Sig_EvidenceC: Ev -> EvidenceC -> Prop :=
| asigc: forall n p e e'' bits et,
    (*let e' := (evc bits et) in *)
    EvSub (ggc p (checkSigBitsF bits p (do_sig (encodeEvBits (evc bits et)) p n)) e'') e ->
    appEvent_Sig_EvidenceC (sign n p et) e.

Definition none_none_term (t:Term): Prop :=
  (exists t1 t2,
      t = bseq (NONE,NONE) t1 t2)
  \/
  (exists t1 t2,
      t = bpar (NONE,NONE) t1 t2).

Definition not_none_none (t:Term) :=
  forall t',
    none_none_term t'  -> 
    ~ (term_sub t' t).

Inductive reaches_HSH : Term -> Prop :=
| rh_hsh: reaches_HSH (asp (HSH))
| rh_aatt: forall p t,
    reaches_HSH t ->
    reaches_HSH (att p t)
| rh_lseql: forall t1 t2,
    reaches_HSH t1 ->
    reaches_HSH (lseq t1 t2)
| rh_lseqr: forall t1 t2,
    reaches_HSH t2 ->
    reaches_HSH (lseq t1 t2)
| rh_bseql: forall sp2 t1 t2,
    reaches_HSH t1 ->
    reaches_HSH (bseq (ALL,sp2) t1 t2)
| rh_bseqr: forall sp1 t1 t2,
    reaches_HSH t2 ->
    reaches_HSH (bseq (sp1,ALL) t1 t2)
| rh_bparl: forall sp2 t1 t2,
    reaches_HSH t1 ->
    reaches_HSH (bpar (ALL,sp2) t1 t2)
| rh_bparr: forall sp1 t1 t2,
    reaches_HSH t2 ->
    reaches_HSH (bpar (sp1,ALL) t1 t2).
Hint Constructors reaches_HSH : core.

Definition hash_sig_term (t:Term): Prop :=
  exists t1 t2,
  t = lseq t1 t2 /\
  term_sub (asp SIG) t1 /\
  reaches_HSH t2.
  (*
  term_sub (aasp r2 HSH) t2. *)

Definition not_hash_sig_term (t:Term) :=
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

Definition hsh_subt (t:Term) :=
  term_sub (asp HSH) t.

Definition not_hash_sig_term_ev (t:Term) (e:EvidenceC): Prop :=
  not_hash_sig_term t /\
  not_hash_sig_ev e /\
  ((gg_sub e) -> ~ (reaches_HSH t)).

Lemma nhse_uuc: forall params n2 n3 e,
    not_hash_sig_ev (uuc params n2 n3 e) ->
    not_hash_sig_ev e.
Proof.
  intros.
  unfold not_hash_sig_ev in *.
  intros.
  unfold not in *; intros.
  eapply H.
  eassumption.
  econstructor.
  eassumption.
Defined.

Ltac do_nhse_uuc:=
  match goal with
  | [H: not_hash_sig_ev (uuc _ _ _ ?e)
     |- _] =>
    assert_new_proof_by (not_hash_sig_ev e) ltac:(eapply nhse_uuc; apply H)
  end.

Lemma nhse_ggc: forall n n0 e,
    not_hash_sig_ev (ggc n n0 e) ->
    not_hash_sig_ev e.
Proof.
  intros.
  unfold not_hash_sig_ev in *.    
  unfold not in *; intros.
  eapply H.
  eassumption.
  econstructor.
  eassumption.
Defined.

Ltac do_nhse_ggc:=
  match goal with
  | [H: not_hash_sig_ev (ggc _ _ ?e)
     |- _] =>
    assert_new_proof_by (not_hash_sig_ev e) ltac:(eapply nhse_ggc; apply H)
  end.

Lemma nhse_hhc: forall n n0 e x y,
    not_hash_sig_ev (hhc n n0 e) ->
    ~ (EvSubT (gg x y) e).
Proof.
  intros.
  unfold not_hash_sig_ev in *.    
  unfold not in *; intros.
  eapply H.
  econstructor.
  repeat eexists.
  eassumption.
  econstructor.
Defined.

Lemma nhse_hhc': forall n n0 n1 e x y,
    not_hash_sig_ev (hhc n n0 e) ->
    EvSubT (gg x y) (hh n1 e) ->
    False.
Proof.
  intros.
  eapply nhse_hhc.
  eassumption.
  invc H0.
  eassumption.
Defined.

Ltac do_nhse_hhc_contra:=
  match goal with
  | [H: not_hash_sig_ev (hhc _ _ ?e),
        H2: EvSubT (gg _ _) (hh _ ?e)
     |- _] =>
    assert_new_proof_by (False) ltac:(eapply nhse_hhc'; [apply H | apply H2])
  end;
  solve_by_inversion.

Lemma nhse_ssc: forall e1 e2,
    not_hash_sig_ev (ssc e1 e2) ->
    not_hash_sig_ev e1 /\ not_hash_sig_ev e2.
Proof.
  intros.
  unfold not_hash_sig_ev in *.
  unfold not in *; intros.
  split; intros.
  -
    eapply H.
    eassumption.
    econstructor.
    eassumption.
  -
    eapply H.
    eassumption.
    apply ssSubr.
    eassumption.
Defined.

Ltac do_nhse_ssc:=
  match goal with
  | [H: not_hash_sig_ev (ssc ?e1 ?e2)
     |- _] =>
    assert_new_proof_by (not_hash_sig_ev e1 /\
                         not_hash_sig_ev e2) ltac:(eapply nhse_ssc; apply H)
  end; destruct_conjs.


Lemma nhse_ppc: forall e1 e2,
    not_hash_sig_ev (ppc e1 e2) ->
    not_hash_sig_ev e1 /\ not_hash_sig_ev e2.
Proof.
  intros.
  unfold not_hash_sig_ev in *.
  unfold not in *; intros.
  split; intros.
  -
    eapply H.
    eassumption.
    econstructor.
    eassumption.
  -
    eapply H.
    eassumption.
    apply ppSubr.
    eassumption.
Defined.

Ltac do_nhse_ppc:=
  match goal with
  | [H: not_hash_sig_ev (ppc ?e1 ?e2)
     |- _] =>
    assert_new_proof_by (not_hash_sig_ev e1 /\
                         not_hash_sig_ev e2) ltac:(eapply nhse_ppc; apply H)
  end; destruct_conjs.

Ltac do_nhse :=
  try do_nhse_uuc;
  try do_nhse_hhc_contra;
  try do_nhse_ggc;
  try do_nhse_ssc;
  try do_nhse_ppc.

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

Lemma recon_encodeEv : forall ls et ec,
    wf_ec (evc ls et) -> 
    reconstruct_evP (evc ls et) ec ->
    ls = encodeEv ec.
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros.
  -
    ff.
    do_inv_recon.
    inv_wfec.
    destruct ls; try solve_by_inversion.
  (* TODO: exclude mt case? *)
  -
    ff.
    do_inv_recon.
    tauto.
  -
    ff.
    do_inv_recon.
    do_recon_inv.
    inv_wfec.
    repeat ff.

    edestruct IHec.
    2: {
      eassumption.
      
    }
    econstructor.
    eassumption.
    tauto.
  -
    ff.
    do_inv_recon.
    do_recon_inv.
    inv_wfec.
    repeat ff.
    edestruct IHec.
    2: {
      eassumption.
    }

    econstructor.
    eassumption.
    tauto.
  -
    ff.
    do_inv_recon.
    tauto.  
  -
    ff.
    do_inv_recon.

    do_recon_inv.

    inv_wfec.
    ff.
    
    jkjke'.
    jkjke'.
    rewrite firstn_skipn.
    tauto.

    econstructor.
    eapply firstn_long. lia.

    econstructor.
    eapply skipn_long. lia.

  -
    ff.
    do_inv_recon.
    do_recon_inv.
    inv_wfec.
    ff.
    
    jkjke'.
    jkjke'.
    rewrite firstn_skipn.
    tauto.

    econstructor.
    eapply firstn_long. lia.

    econstructor.
    eapply skipn_long. lia.
Defined.

Lemma wf_recon: forall e et ec,
    reconstruct_evP (evc e et) ec ->
    wf_ec (evc e et).
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros.
  -
    do_inv_recon.
    invc H.
    repeat ff.
    econstructor.
    tauto.
  -
    do_inv_recon.
    econstructor.
    tauto.
  -
    do_inv_recon.
    do_recon_inv.
    assert (wf_ec (evc H0 H1)) by eauto.
    inv_wfec.
    econstructor.
    ff.
    lia.
  -
    do_inv_recon.
    do_recon_inv.
    assert (wf_ec (evc H0 H1)) by eauto.
    inv_wfec. 
    econstructor.
    ff.
    lia.

  -
    do_inv_recon.
    econstructor.
    tauto.
  -
    do_inv_recon.
    do_recon_inv.

    assert (wf_ec (evc (firstn (et_size H0) e) H0)) as HH.
    {
      eapply IHec1.
      eassumption.
    }
    
    assert (wf_ec (evc (skipn (et_size H0) e) H1)) as HH'.
    {
      eapply IHec2.
      econstructor.
      ff.
    }
    inv_wfec.
    
    econstructor.
    ff.

    rewrite <- H6.
    rewrite <- H5.

    assert (e = (firstn (et_size H0) e) ++ (skipn (et_size H0) e)) as HH.
    
    { rewrite firstn_skipn.
      tauto.
    }
    rewrite HH at 1.
    eapply app_length.

  -
    do_inv_recon.
    do_recon_inv.

    assert (wf_ec (evc (firstn (et_size H0) e) H0)) as HH.
    {
      eapply IHec1.
      eassumption.
    }
    
    assert (wf_ec (evc (skipn (et_size H0) e) H1)) as HH'.
    {
      eapply IHec2.
      econstructor.
      ff.
    }
    inv_wfec.
    
    econstructor.
    ff.

    rewrite <- H6.
    rewrite <- H5.

    assert (e = (firstn (et_size H0) e) ++ (skipn (et_size H0) e)) as HH.
    
    { rewrite firstn_skipn.
      tauto.
    }
    rewrite HH at 1.
    eapply app_length.
Defined.
