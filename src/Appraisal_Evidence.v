(* Definitions, properties, and associated automation related to 
    Appraisal and EvidenceT examination/reconstruction.

    Also included:  properties about CVM internal EvidenceT and Event handling.  
    TODO:  This file has become quite bloated.  May need to refactor/decompose.  *)

Require Import ConcreteEvidenceT AutoApp Defs StructTactics OptMonad_Coq Anno_Term_Defs Cvm_Impl Cvm_St ResultT Axioms_Io Attestation_Session External_Facts Helpers_CvmSemantics Cvm_Monad More_lists Auto.

Require Import List.
Import ListNotations OptNotation.

Require Import Lia Coq.Program.Tactics.

Definition peel_bs (ls:RawEv) : Opt (BS * RawEv) :=
  match ls with
  | bs :: ls' => opt_ret (bs, ls')
  | _ => opt_failm
  end.

Fixpoint peel_n (n : nat) (ls : RawEv) : Opt (RawEv * RawEv) :=
  match n with
  | 0 => opt_ret ([], ls)
  | S n' =>
      match ls with
      | [] => opt_failm
      | x :: ls' =>
          '(ls1, ls2) <- peel_n n' ls' ;;
          opt_ret (x :: ls1, ls2)
      end
  end.

Lemma firstn_long: forall (e:list BS) x,
    length e >= x ->
    length (firstn x e) = x.
Proof.
  intros.
  eapply firstn_length_le.
  lia.
Qed.

Lemma skipn_long: forall (e:list BS) x y,
    length e = x + y ->
    length (skipn x e) = y.
Proof.
  intros.
  assert (length (skipn x e) = length e - x).
  { eapply skipn_length. }
  lia.
Qed.

Lemma peel_fact': forall e x y H,
    length e = S x ->
    peel_bs e = Some (y, H) ->
    length H = x.
Proof.
  intros.
  destruct e;
    ff; eauto.
Qed.

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
Qed.

Fixpoint encodeEv (e:EvidenceTC) : RawEv :=
  match e with
  | mtc => []
  | nnc _ bs => [bs]
  | ggc _ _ rawev e' => rawev ++ (encodeEv e')
  | hhc _ _ bs _ => [bs]
  | eec _ _ bs _ => [bs]
  | kkc _ _ _ => []
  | kpc _ _ e' => encodeEv e'
  | ssc e1 e2 => (encodeEv e1) ++ (encodeEv e2)
  end.

Fixpoint reconstruct_ev' (ls:RawEv) (et:EvidenceT) : Opt EvidenceTC :=
  match et with
  | mt_evt=> 
    match ls with
    | [] => Some mtc
    | _ => None
    end
  | asp_evt p fwd ps et' =>
    match fwd with
    | (EXTD n) => 
      '(rawEv, ls') <- peel_n n ls ;;
      x <- reconstruct_ev' ls' et' ;;
      Some (ggc p ps rawEv x)
    | COMP =>
      '(bs, ls') <- peel_bs ls ;;
      match ls' with
      | [] => Some (hhc p ps bs et')
      | _ => None
      end
    | ENCR =>
      '(bs, ls') <- peel_bs ls ;;
      match ls' with
      | [] => Some (eec p ps bs et')
      | _ => None
      end
    | KILL =>
      match ls with
      | [] => Some (kkc p ps et')
      | _ => None
      end
    | KEEP =>
      x <- reconstruct_ev' ls et' ;;
      Some (kpc p ps x)
    end
  | nonce_evt i =>
    '(bs, ls') <- peel_bs ls ;;
     match ls' with
    | [] => Some (nnc i bs)
    | _ => None
    end 
  | split_evt et1 et2 =>
    e1 <- reconstruct_ev' (firstn (et_size et1) ls) et1 ;;
    e2 <- reconstruct_ev' (skipn (et_size et1) ls) et2 ;;
    Some (ssc e1 e2)
  end.

Definition reconstruct_ev (e:EvC) : Opt EvidenceTC :=
  match e with
  | evc ls et => reconstruct_ev' ls et
  end.

Inductive reconstruct_evP: EvC -> EvidenceTC -> Prop :=
| reconstruct_evC: forall e ee,
    Some ee = reconstruct_ev e ->
    reconstruct_evP e ee.


Lemma inv_recon_mt_evt: forall ls et,
    reconstruct_evP (evc ls et) mtc ->
    (et = mt_evt).
Proof.
  intros.
  invc H.
  destruct et;
    repeat ff;
    try (unfold opt_bind in *);
         repeat ff;
         try solve_by_inversion.
Qed.

Ltac do_inv_recon_mt_evt:=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) mtc

     |- _] =>
    assert_new_proof_by (et = mt_evt) ltac:(eapply inv_recon_mt_evt; apply H)
  end;
  subst.

Lemma inv_recon_mt_evt': forall ls e,
    reconstruct_evP (evc ls mt_evt) e ->
    e = mtc.
Proof.
  intros.
  invc H.
  repeat ff; try solve_by_inversion; eauto.
Qed.

Ltac do_inv_recon_mt_evt' :=
  match goal with
  | [H: reconstruct_evP (evc _ mt_evt) ?e

     |- _] =>
    assert_new_proof_by (e = mtc) ltac:(eapply inv_recon_mt_evt'; apply H)
  end;
  subst.


Lemma inv_recon_nn: forall ls et n n0,
    reconstruct_evP (evc ls et) (nnc n n0) ->
    ((et = nonce_evt n /\ ls = [n0])).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold opt_bind in *); repeat ff; destruct ls; try solve_by_inversion.                              
Qed.

Ltac do_inv_recon_nonce_evt :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (nnc ?n ?nval)

     |- _] =>
    assert_new_proof_by (et = nonce_evt n /\ ls = [nval] ) ltac:(eapply inv_recon_nn; apply H)
  end;
  destruct_conjs;
  subst.

Lemma peel_n_spec : forall n ls ls1 ls2,
  peel_n n ls = Some (ls1, ls2) ->
  ls = ls1 ++ ls2 /\ length ls1 = n.
Proof.
  induction n; intuition; repeat ff; subst;
  unfold opt_ret, opt_bind in *; repeat ff; eauto.
  - eapply IHn in Heqo; intuition; subst; eauto. 
  - eapply IHn in Heqo; intuition; subst; eauto. 
Qed.

Lemma inv_recon_gg: forall p ps ls et n ec,
    reconstruct_evP (evc ls et) (ggc p ps n ec) ->
    (exists ls' et', et = asp_evt p (EXTD (length n)) ps et' /\
                ls = n ++ ls') .
Proof.
  intuition; invc H.
  generalizeEverythingElse et.
  destruct et; repeat ff; intuition; 
  try (unfold opt_bind, opt_ret in *); 
  repeat ff; try solve_by_inversion.
  eapply peel_n_spec in Heqo; intuition; subst; eauto.
Qed.

Ltac do_inv_recon_gg :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (ggc ?p ?ps ?n _)

     |- _] =>
    assert_new_proof_by ((exists ls' et', et = asp_evt p (EXTD (length n)) ps et' /\
                                    ls = n ++ ls') )
                        ltac:(eapply inv_recon_gg; apply H)
  | H : peel_n _ _ = Some _ |- _ => 
      apply peel_n_spec in H; intuition; subst; eauto;
      find_apply_lem_hyp app_inv_head_iff; subst; eauto
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_hh: forall p ps ls et n et',
    reconstruct_evP (evc ls et) (hhc p ps n et') ->
    ((et = asp_evt p COMP ps et' ) /\ ls = [n]).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold opt_bind in *); repeat ff; destruct ls; try solve_by_inversion.
Qed.

Ltac do_inv_recon_hh :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (hhc ?p ?ps ?hval ?et')

     |- _] =>
    assert_new_proof_by ((et = asp_evt p COMP ps et' /\ ls = [hval]))
                        ltac:(eapply inv_recon_hh; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_ee: forall p ps ls et n ec',
    reconstruct_evP (evc ls et) (eec p ps n ec') ->
    (exists et', et = asp_evt p ENCR ps et' /\ ls = [n]).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold opt_bind in *); 
  repeat ff; destruct ls; try solve_by_inversion;
  repeat eexists; ff.
Qed.

Ltac do_inv_recon_ee :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (eec ?p ?ps ?hval (*_*) _)

     |- _] =>
    assert_new_proof_by ( (exists et', et = asp_evt p ENCR ps et' /\ ls = [hval]) )
                        ltac:(eapply inv_recon_ee; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_ss: forall ls et ec1 ec2,
    reconstruct_evP (evc ls et) (ssc ec1 ec2) ->
    (exists et1 et2, et = split_evt et1 et2).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold opt_bind in *); 
  repeat ff; try solve_by_inversion;
  eauto.
Qed.

Ltac do_inv_recon_split_evt :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) (ssc _ _)

     |- _] =>
    assert_new_proof_by ((exists et1 et2, et = split_evt et1 et2) )
                        ltac:(eapply inv_recon_ss; apply H)
  end;
  destruct_conjs;
  subst.


Ltac do_inv_recon :=
  try do_inv_recon_mt_evt;
  try do_inv_recon_mt_evt';
  try do_inv_recon_nn;
  try do_inv_recon_gg;
  try do_inv_recon_hh;
  try do_inv_recon_ee;
  try do_inv_recon_ss.

Lemma recon_inv_gg: forall sig ls p ps et e,
    reconstruct_evP
      (evc (sig ++ ls) (asp_evt p (EXTD (length sig)) ps et))
      (ggc p ps sig e) ->
    reconstruct_evP (evc ls et) e.
Proof.
  intros.
  invc H.
  repeat ff; try (unfold opt_bind in *); repeat ff;
  econstructor.
  find_apply_lem_hyp peel_n_spec; intuition;
  find_apply_lem_hyp app_inv_head_iff; subst; eauto.
Qed.

Ltac do_recon_inv_gg :=
  match goal with
  | [H: reconstruct_evP
          (evc (_ :: ?ls) (asp_evt _ _ _ ?et))
          (ggc _ _ _ ?e)
     |- _] =>
    assert_new_proof_by (reconstruct_evP (evc ls et) e) ltac:(eapply recon_inv_gg; apply H)
  | H : peel_n _ _ = Some _ |- _ => 
      apply peel_n_spec in H; intuition; subst; eauto;
      find_apply_lem_hyp app_inv_head_iff; subst; eauto
  end.

Lemma recon_inv_ss: forall ls H1 H2 ec1 ec2,
    reconstruct_evP (evc ls (split_evt H1 H2)) (ssc ec1 ec2) ->
    reconstruct_evP (evc (firstn (et_size H1) ls) H1) ec1 /\
    reconstruct_evP (evc (skipn (et_size H1) ls) H2)  ec2.
Proof.
  intros.
  invc H.
  repeat ff; try (unfold opt_bind in *); repeat ff;
  split;
    econstructor;
    try 
      symmetry; eassumption.
Qed.

Ltac do_recon_inv_split_evt :=
  match goal with
  | [H: reconstruct_evP
          (evc ?ls (split_evt ?H1 ?H2))
          (ssc ?ec1 ?ec2) _
     |- _] =>
    assert_new_proof_by
      (reconstruct_evP (evc (firstn (et_size H1) ls) H1) ec1 /\
       reconstruct_evP (evc (skipn (et_size H1) ls) H2)  ec2)
      ltac:(eapply recon_inv_ss; apply H)
  end; destruct_conjs.

Ltac do_recon_inv :=
  try do_recon_inv_gg;
  try do_recon_inv_ss.


Lemma wrap_reconP: forall ec e,
    reconstruct_ev ec = Some e ->
    reconstruct_evP ec e.
Proof.
  intros.
  econstructor.
  congruence.
Qed.

Lemma fold_recev: forall e0 e1,
    reconstruct_ev' e0 e1 = reconstruct_ev (evc e0 e1).
Proof.
  ffa.
Qed.

Ltac do_wrap_reconP :=
  repeat
  match goal with
  | [H: reconstruct_ev ?ec = Some ?e
     |- _] =>
    apply wrap_reconP in H
  end.

Ltac do_rewrap_reconP :=
  match goal with
  | [H: reconstruct_evP (evc _ (?cc _)) _
     |- _] =>
    invc H;
    ffa;
    try rewrite fold_recev in *;
    do_wrap_reconP
  end.

Lemma etfun_reconstruct: forall e e0 e1,
    reconstruct_evP (evc e0 e1) e ->
    e1 = et_fun e.
Proof.
  intros.
  generalizeEverythingElse e1.
  induction e1; intros e e0 H.
  - (* mt_evtcase *)
    invc H.
    ff.
  - (* nonce_evt case *)
    invc H.
    repeat ff; try (unfold opt_bind in * ); repeat ff.
  
  - (* asp_evt case *)
    destruct f; ffa.
    + (* COMP case *)
      invc H.
      repeat ff; try (unfold opt_bind in * ); repeat ff.
    + (* ENCR case *)
      
      invc H.
      unfold reconstruct_ev in *.
      unfold reconstruct_ev' in *.
      unfold opt_bind in *.
      repeat ff; try (unfold opt_bind in * ); repeat ff.
           
    + (* EXTD case *)
      invc H.
      ff.
      repeat ff; try (unfold opt_bind in * ); repeat ff.
      assert (e1 = et_fun e2 ).
      {
      eapply IHe1.
      econstructor.
      ff.
      }
      find_apply_lem_hyp peel_n_spec; intuition; subst; eauto.
    + (* KILL case *)
      invc H.
      unfold reconstruct_ev in *.
      ff.
    + (* KEEP case *)
      invc H.
      unfold reconstruct_ev in *.
      ff.
      repeat ff; try (unfold opt_bind in * ); repeat ff.
      assert (e1 = et_fun e2).
      { eapply IHe1.
        econstructor.
        unfold reconstruct_ev.
        symmetry.
        eassumption.
      }
      subst.
      tauto.
  - (* split_evt case *)
    invc H.
    ff.
    repeat ff; try (unfold opt_bind in * ); repeat ff.
    assert (e1_1 = et_fun e1).
    {
      eapply IHe1_1.
      econstructor.
      symmetry.
      eassumption.
    }
    assert (e1_2 = et_fun e2).
    {
      eapply IHe1_2.
      econstructor.
      symmetry.
      eassumption.
    }
    congruence.
Qed.

Lemma wfec_split: forall e s,
    wf_ec e ->
    wf_ec (splitEv_l s e) /\ wf_ec (splitEv_r s e).
Proof.
  intros.
  split;
    destruct s; ff; try unfold mt_evc; ff;
      econstructor; ff.
Qed.

Ltac do_wfec_split :=
  match goal with
  | [H: context[splitEv_l ?s ?e],
        H2: context[splitEv_r ?s ?e],
            H3: wf_ec ?e
     |- _] =>
    
    assert_new_proof_by
      (wf_ec (splitEv_l s e) /\ wf_ec (splitEv_r s e))
      ltac: (eapply wfec_split; apply H3)
  end; destruct_conjs.


(* Lemma:  Encoding an EvC bundle gives you the bits used 
   to (re)construct it. *)
Lemma recon_encodeEv: forall bits et ec,
    reconstruct_evP (evc bits et) ec ->
    encodeEv ec = bits.
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros; ffa.
  -
    dd.
    do_inv_recon.
    invc H.
    repeat ff.
    (*
    invc H.
    repeat ff. *)
  - (* nnc case *)
    do_inv_recon.
    ff.
  - (* ggc case *)
    do_inv_recon.
    ff.
    invc H.
    repeat ff.
    unfold opt_bind in *.
    ff.
    find_apply_lem_hyp peel_n_spec; intuition; subst;
    find_apply_lem_hyp app_inv_head_iff; subst.
    assert (reconstruct_evP (evc r1 H1) e).
    {
      econstructor; eauto.
    }
    find_apply_hyp_hyp; subst; eauto.
  - (* hhc case *)
    do_inv_recon.
    ff.
  - (* eec case *)
    
    do_inv_recon.
    ff.

  - (* kkc case *)
    do_inv_recon.
    ff.
    invc H.
    ff.
    unfold reconstruct_ev' in *.
    ff.
    unfold opt_bind in *.
    ff.
    rewrite fold_recev in *.
    unfold reconstruct_ev in *.
    unfold reconstruct_ev' in *.
    destruct et; try solve_by_inversion;
    ffa using (unfold opt_bind in *).


  - (* kpc case *)
    ff.

    assert (exists et', et = asp_evt p KEEP a et').
    {
      destruct et; try solve_by_inversion;
      invc H; ffa using (unfold opt_bind in *).
    }
    
    destruct_conjs.
    subst.

    invc H; ffa using (unfold opt_bind in *).
    eapply IHec.
    econstructor.
    ff.
    
  - (* ssc case *)
    do_inv_recon.
    ff.
    invc H.
    ff.
    unfold opt_bind in *.
    ff.
    rewrite fold_recev in *.
    do_wrap_reconP.
    
    
    assert (encodeEv e =  (firstn (et_size H0) bits)) by eauto.
    assert (encodeEv e0 = (skipn (et_size H0) bits)) by eauto.

    assert (bits = firstn (et_size H0) bits ++ skipn (et_size H0) bits).
    {
      symmetry.
      eapply firstn_skipn.
    }
    rewrite H3 at 1.
    congruence.
Qed.

Lemma wfec_recon: forall (ee:EvC) (ec:EvidenceTC),
    reconstruct_evP ee ec ->
    wf_ec ee.
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros; destruct ee.
  - (* mtc case *)
    do_inv_recon.
    dd.
    invc H.
    dd.
    ff.
    econstructor. tauto.
  - (* nnc case *)
    do_inv_recon.
    invc H.
    dd.
    econstructor; tauto.
  - (* ggc case *)
    do_inv_recon.
    invc H.
    dd.
    ff.
    unfold opt_bind in *.
    ff.
    do_inv_recon.
    assert (wf_ec (evc r1 H1)).
    {
      apply IHec.
      econstructor.
      eauto.
    }
    econstructor.
    dd.
    invc H.
    rewrite app_length.
    lia.

  - (* hhc case *)
    do_inv_recon.
    invc H.
    econstructor.
    simpl in *.
    dd.
    econstructor; tauto.
  - (* eec case *)
    do_inv_recon.
    invc H.
    dd.
    econstructor; tauto.

  - (* kkc case *)
    invc H.
    unfold reconstruct_ev in *.
    unfold reconstruct_ev' in *.
    destruct e0; try solve_by_inversion.
    ff.
    unfold opt_bind in *. ff.
    unfold opt_bind in *. ff.
    econstructor.
    ff.
    unfold opt_bind in *. ff.
  - (* kpc case *)
    invc H.
    destruct e; try solve_by_inversion.
    +
      ff.
    +
      ff.
      repeat ff; try (unfold opt_bind in * ); repeat ff.
    +
      repeat ff; try (unfold opt_bind in * ); repeat ff.
      assert (wf_ec (evc r e)).
      {
        eapply IHec. econstructor.
        symmetry. eassumption. }
      econstructor.
      ff.
    +
      ff.
      repeat ff; try (unfold opt_bind in * ); repeat ff.
   
  -
    do_inv_recon.
    invc H.
    dd.
    ff.
    unfold opt_bind in *.
    
    ff.

    assert (wf_ec (evc (firstn (et_size H0) r) H0)).
    {
      apply IHec1.
      econstructor.
      eauto.
    }
    assert (wf_ec (evc (skipn (et_size H0) r) H1)).
    {
      apply IHec2.
      econstructor.
      eauto.
    }
    
    econstructor.
    dd.
    invc H.
    invc H2.
    rewrite <- H4.
    rewrite <- H3.
    assert (r = firstn (et_size H0) r ++ skipn (et_size H0) r).
    {
      symmetry.
      eapply firstn_skipn.
    }
    rewrite H at 1.
    eapply app_length.
Qed.

Lemma reconP_determ: forall ec e e',
    reconstruct_evP ec e ->
    reconstruct_evP ec e' ->
    e = e'.
Proof.
  intros.
  invc H; invc H0.
  repeat jkjke'.
  ff.
Qed.

Ltac do_reconP_determ :=
  repeat 
  match goal with
  | [H: reconstruct_evP ?ec ?e,
        H2: reconstruct_evP ?ec ?e2
     |- _] =>
    assert_new_proof_by (e = e2)
                        ltac:(eapply reconP_determ; [apply H | apply H2]);
    clear H2
  end; subst.



Ltac inv_wfec :=
  repeat
    match goal with
    | [H: wf_ec _ |-  _ ] => invc H
    end.

(** * If a raw EvidenceT sequence is non-empty, we can grab a first element. *)
Lemma some_recons' : forall e x,
    length e = S x ->
    exists bs ls', peel_bs e = Some (bs, ls').
Proof.
  intros.
  destruct e;
    ff; eauto.
Qed.

Ltac do_some_recons' :=
  match goal with
  | [H: length ?e = S _ |- _ ] =>
    edestruct some_recons'; [apply H | idtac]
                              
  end; destruct_conjs; jkjke.

Ltac do_rcih :=
  match goal with
  | [H: context[reconstruct_ev' _ _]
               

     |- context[reconstruct_ev' ?e' ?et] ] =>
    assert_new_proof_by
      (exists x, Some x = reconstruct_ev' e' et)
      ltac:(eapply H with (r:=e'); (* TODO:  make r lesplit_evt one-off *)
            try (eapply peel_fact; eauto; tauto);
            try (econstructor; first [eapply firstn_long | eapply skipn_long]; try eauto; try lia))      
  end.

Lemma peel_n_none_spec : forall n ls,
  peel_n n ls = None ->
  length ls < n.
Proof.
  induction n; intuition; simpl in *;
  repeat ff; try lia;
  unfold opt_ret, opt_bind in *; repeat ff; eauto.
  eapply IHn in Heqo.
  lia.
Qed.

(** * Lemma:  well-formed EvC bundles can be successfully reconstructed to a Typed Concrete EvidenceT (EvidenceTC) value. *)
Lemma some_recons : forall (e:EvC),
    wf_ec e ->
    exists (ee:EvidenceTC), Some ee = reconstruct_ev e.
Proof.
  intros.
  destruct e.
  generalizeEverythingElse e.
  induction e; intros.
  - inv_wfec; ff.

  - (* nonce_evt case *)
    ffa using (unfold opt_bind in * );
    inv_wfec; destruct r.

  - (* asp_evt case *)

    destruct f.
    
    + (* COMP case *)

      inv_wfec.
      ff.
      repeat ff;
    (unfold opt_bind in * );
    repeat ff; eauto.

      ++
       ff.
       assert (exists v, r = [v]).
       {
         destruct r; ff.
         destruct r; ff. }
       destruct_conjs. subst.
       ff.
      ++
       assert (exists v, r = [v]).
       {
         destruct r; ff. }
       destruct_conjs. subst.
       ff.
    + (* ENCR case *)

      inv_wfec.
      ff.
      repeat ff;
    (unfold opt_bind in * );
    repeat ff; eauto.
      ++
         ff.
       assert (exists v, r = [v]).
       {
         destruct r; ff.
         destruct r; ff. }
       destruct_conjs. subst.
       ff.
      ++
       assert (exists v, r = [v]).
       {
         destruct r; ff. }
       destruct_conjs. subst.
       ff.
    + (* EXTD case *)
      inv_wfec.
      ff.
      unfold opt_bind in * ;
        repeat ff; eauto;
        subst; eauto;
        try do_inv_recon.
      ++
        find_apply_lem_hyp peel_n_spec; intuition; subst; eauto.
        rewrite app_length in *;
        intuition.
        assert (length r1 = et_size e). lia.
        assert (wf_ec (evc r1 e)).
        {
          econstructor; eauto.
        }
        assert (exists ee, Some ee = reconstruct_ev' r1 e).
        {
          invc H.
          eapply IHe.
         econstructor. eassumption. }
        
        destruct_conjs; congruence.
      ++ assert (r = []). {
          eapply peel_n_none_spec in Heqo; lia. }
       subst; simpl in *; destruct n; simpl in *; try lia;
       unfold opt_ret in *; congruence.
    + (* KILL case *)
      inv_wfec; ff.
    + (* KEEP case *)
      inv_wfec.
      simpl in H1.
      ffa using (unfold opt_bind in *).

    assert (exists ee, Some ee = reconstruct_ev' r e).
    { eapply IHe.
      econstructor.
      eassumption.
    }
    ffa.
  - (* split_evt case *)
    assert (wf_ec (evc (firstn (et_size e1) r) e1)).
    {
      inv_wfec; econstructor;
      simpl in *;
      eapply firstn_length_le; lia.
    }
    assert (wf_ec (evc (skipn (et_size e1) r) e2)).
    {
      inv_wfec; econstructor;
      simpl in *.
      rewrite skipn_length; lia.
    }
    ffa using (try break_exists; unfold opt_bind in *).
Qed.

Lemma some_reconsP : forall e,
    wf_ec e ->
    exists ee, reconstruct_evP e ee.
Proof.
  intros.
  edestruct some_recons.
  eassumption.
  eexists.
  econstructor.
  eassumption.
Qed.

Ltac do_somerecons :=
  repeat
    match goal with
    | [H: wf_ec ?e
       |- _ ] =>
      assert_new_proof_by
        (exists x, reconstruct_evP e x)
        ltac:(eapply some_reconsP; apply H)     
    end; destruct_conjs.

Definition spc_ev (sp:SP) (e:EvidenceTC) : EvidenceTC :=
  match sp with
  | ALL => e
  | NONE => mtc
  end.

(*
TODO: try this again after appraisal lemmas settled 
*)
Definition do_asp_nofail (ps:ASP_PARAMS) (ev:RawEv) (p:Plc) (x:Event_ID): BS.
Admitted. (* TODO:  fill this in with some sort of callback + default value? *)

Definition do_asp_EXTD_nofail (ps:ASP_PARAMS) (n : nat) (ev:RawEv) (p:Plc) (x:Event_ID): RawEv.
Admitted. (* TODO:  fill this in with some sort of callback + default value? *)

(* This may seem a bit un-intuitive, but its a matter of 
  the new returned RawEv will be of length 'n'
*)
Axiom do_asp_EXTD_nofail_length_spec : forall ps n ev p x,
    length (do_asp_EXTD_nofail ps n ev p x) = n.

Definition cvm_EvidenceT_denote_asp (a:ASP) (p:Plc) (e:EvidenceTC) (x:Event_ID): EvidenceTC :=
  match a with
  | NULL => mtc
  | CPY => e
  | ASPC sp fwd params =>
    match fwd with
    | COMP => hhc p params
                 (do_asp_nofail params (encodeEv (spc_ev sp e)) p x)
                 (sp_ev sp (et_fun e))
    | (EXTD n) => ggc p params
                 (do_asp_EXTD_nofail params n (encodeEv (spc_ev sp e)) p x)
                 (spc_ev sp e)
    | ENCR => eec p params
                 (do_asp_nofail params (encodeEv (spc_ev sp e)) p x)
                 (sp_ev sp (et_fun e))
    | KEEP => (spc_ev sp e)
    | KILL => mtc (* kkc p params (sp_ev sp (et_fun e)) *)
    end
  | SIG => ggc p sig_params
              (do_asp_EXTD_nofail sig_params 1 (encodeEv e) p x)
              e
  | HSH => hhc p hsh_params
              (do_asp_nofail hsh_params (encodeEv e) p x)
              (et_fun e)
  | ENC q => eec p (enc_params q)
                (do_asp_nofail (enc_params q) (encodeEv e) p x)
                (et_fun e)
  end.


(** * Denotation function of a Typed Concrete EvidenceT value from an annotated term, initial place, initial EvidenceT *)
Fixpoint cvm_EvidenceT_denote (t:AnnoTerm) (p:Plc) (ec:EvidenceTC) : EvidenceTC :=
  match t with
  | aasp (i,_) x => cvm_EvidenceT_denote_asp x p ec i
  | aatt _ q x => cvm_EvidenceT_denote x q ec
  | alseq _ t1 t2 => cvm_EvidenceT_denote t2 p (cvm_EvidenceT_denote t1 p ec)
  | abseq _ s t1 t2 => ssc (cvm_EvidenceT_denote t1 p ((splitEvl s ec)))
                         (cvm_EvidenceT_denote t2 p ((splitEvr s ec)))
  | abpar _ s t1 t2 => ssc (cvm_EvidenceT_denote t1 p ((splitEvl s ec)))
                         (cvm_EvidenceT_denote t2 p ((splitEvr s ec)))
  end.

Set Warnings "-notation-overridden".
Set Warnings "+notation-overridden".


(** * Assert an arbitrary (remote) CVM execution.  
      Uses uninterpreted functions for "simulated" CVM EvidenceT and events. *)
Ltac do_assert_remote t e i ac :=
  assert (
      build_cvm t
                      {| st_ev := e; st_trace := []; st_evid := i; st_config := ac |} =
      (resultC tt,
       {| st_ev := cvm_EvidenceT_core t (session_plc ac) e;
          st_trace := cvm_events_core t (session_plc ac) (get_et e);
          st_evid :=  (i + event_id_span t); 
          st_config := ac
       |})
    ) by (eapply build_cvm_external).


(**  * Event ID spans same for a term and its corresponding core term. *)
Lemma event_id_spans_same : forall t,
    event_id_span' t = event_id_span (copland_compile t).
Proof.
  intros.
  induction t; ff.
  -
    destruct a; ff; try tauto.
Qed.


(** * Lemma:  CVM increases event IDs according to event_id_span' denotation. *)
Lemma cvm_spans: forall t pt e tr i e' tr' i' ac ac',
    term_to_coreP t pt ->
    build_cvmP
      pt
      {| st_ev := e;
         st_trace := tr;
         st_evid := i;
         st_config := ac |}
      (resultC tt)
      {|
        st_ev := e';
        st_trace := tr';
        st_evid := i';
        st_config := ac'
      |} ->
    i' = i + event_id_span' t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    wrap_ccp_anno.

  
 (*   (* This is more automated, but slower *)
    try (
        destruct a;
        try destruct a;
        ff; tauto);
    try (
        repeat find_apply_hyp_hyp;
        lia).
Qed.
  *)
   
  - (* asp case *)
    destruct a;
      try destruct a;
      ffa; try tauto;
      try (wrap_ccp_anno; ff).
  
  - (* at case *)
    ffa using (cvm_monad_unfold; try lia).

  - (* lseq case *)
    wrap_ccp_anno.

    destruct r; ffa.
    destruct u; ffa.



    assert (st_evid0 = i + event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (i' = st_evid0 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    lia.
  -
    destruct s0; destruct s1.
    +
      wrap_ccp_anno.
      try destruct r; ff; 
      try destruct r3; ff;
      try destruct r0; ff;
      try destruct u; ff;
      try destruct u0; ff.


      assert (st_evid1 = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (st_evid = st_evid1 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    subst.
    lia.
    +
      wrap_ccp_anno.
      try destruct r; ff; 
      try destruct r3; ff;
      try destruct r0; ff;
      try destruct u; ff;
      try destruct u0; ff.

      assert (st_evid1 = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (st_evid = st_evid1 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    subst.
    lia.
    +
      wrap_ccp_anno.
      try destruct r; ff; 
      try destruct r3; ff;
      try destruct r0; ff;
      try destruct u; ff;
      try destruct u0; ff.

      assert (st_evid1 = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (st_evid = st_evid1 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    subst.
    lia.
    +
      wrap_ccp_anno.
      try destruct r; ff; 
      try destruct r3; ff;
      try destruct r0; ff;
      try destruct u; ff;
      try destruct u0; ff.

      assert (st_evid1 = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (st_evid = st_evid1 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    subst.
    lia.
  - (* bpar case *)
    destruct s0; destruct s1.
    +
      wrap_ccp_anno.
      try destruct r; ff;
      try destruct r3; ff;
      try destruct u; ff;
      try destruct u0; ff.

      assert (st_evid = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (event_id_span' t2 = event_id_span (copland_compile t2)).
    {
      eapply event_id_spans_same.
    }
    lia.
    +
      wrap_ccp_anno.
      try destruct r; ff;
      try destruct r3; ff;
      try destruct u; ff;
      try destruct u0; ff.

      assert (st_evid = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (event_id_span' t2 = event_id_span (copland_compile t2)).
    {
      eapply event_id_spans_same.
    }
    lia.
    +
      wrap_ccp_anno.
      try destruct r; ff;
      try destruct r3; ff;
      try destruct u; ff;
      try destruct u0; ff.

      assert (st_evid = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (event_id_span' t2 = event_id_span (copland_compile t2)).
    {
      eapply event_id_spans_same.
    }
    lia.
    +
      wrap_ccp_anno.
      try destruct r; ff;
      try destruct r3; ff;
      try destruct u; ff;
      try destruct u0; ff.

      assert (st_evid = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (event_id_span' t2 = event_id_span (copland_compile t2)).
    {
      eapply event_id_spans_same.
    }
    
    lia.
Qed.

(** * CVM event ID span same as annotated term range *)
Lemma span_cvm: forall atp t annt i j e e' tr tr' i' ac ac',
    build_cvmP
      atp
      {| st_ev := e;
         st_trace := tr;
         st_evid := i;
         st_config := ac |} 
      (resultC tt)
      {| st_ev := e';
         st_trace := tr';
         st_evid := i';
         st_config := ac' |} ->
    
    term_to_coreP t atp -> 
    anno t i = (j, annt) ->
    j = i'.
Proof.
  intros.
  assert (j = i + event_id_span' t).
  {
    assert (j - i = event_id_span' t).
    {
      symmetry.
      eapply span_range.
      eauto.
    }
    rewrite <- H2.
    assert (j > i).
    {
      eapply anno_mono; eauto.
    }
    lia.
  }
  subst.
  symmetry.
  eapply cvm_spans; eauto.
Qed.


(** * Propositional version of span_cvm *)
Lemma anno_span_cvm: forall t pt annt i i' e e' tr tr' st_evid1 ac ac',
    anno t i = (i', annt) ->
    term_to_coreP t pt ->
    build_cvmP pt
                     {|
                       st_ev := e ;
                       st_trace := tr ;
                       st_evid := i;
                       st_config := ac
                     |} (resultC tt)
                     {|
                       st_ev := e';
                       st_trace := tr';
                       st_evid := st_evid1;
                       st_config := ac'
                     |} ->
    i' = st_evid1.
Proof.
  intros.
  invc H.
  eapply span_cvm; eauto.
Qed.


Lemma wfec_firstn: forall e0 e1 e2,
    wf_ec (evc e0 e1) ->
    firstn (et_size e1) (e0 ++ e2) = e0.
Proof.
  intros.
  inv_wfec.
  jkjke'.
  eapply firstn_append.
Qed.

Ltac do_wfec_firstn :=
  match goal with
  | [H: context[(firstn (et_size ?e1) (?e0 ++ ?e2))],
        H2: wf_ec (evc ?e0 ?e1)

     |- _] =>
    
    assert_new_proof_by
      (firstn (et_size e1) (e0 ++ e2) = e0)
      ltac: (eapply wfec_firstn; apply H2)
  end.

Lemma wfec_skipn: forall e0 e1 e2,
    wf_ec (evc e0 e1) ->
    skipn (et_size e1) (e0 ++ e2) = e2.
Proof.
  intros.
  inv_wfec.
  jkjke'.
  eapply More_lists.skipn_append.
Qed.

Ltac do_wfec_skipn :=
  match goal with
  | [H: context[(skipn (et_size ?e1) (?e0 ++ ?e2))],
        H2: wf_ec (evc ?e0 ?e1)

     |- _] =>
    
    assert_new_proof_by
      (skipn (et_size e1) (e0 ++ e2) = e2)
      ltac: (eapply wfec_skipn; apply H2)
  end.

Ltac clear_skipn_firstn :=
  match goal with
  | [H: firstn _ _ = _,
        H2: skipn _ _ = _ |- _]
    => rewrite H in *; clear H;
      rewrite H2 in *; clear H2
  end.


(** * Axiom:  assume parallel CVM threads preserve well-formednesplit_evt of EvC bundles *)
Axiom wf_ec_preserved_par: forall e l t2 p,
    wf_ec e ->
    wf_ec (parallel_vm_thread l t2 p e).

Axiom wf_ec_preserved_remote: forall t ev1,
    wf_ec ev1 -> 
    forall p rawEv ac,
      do_remote t p ev1 ac = resultC rawEv ->
      wf_ec (evc rawEv (eval t p (get_et ev1))).

(** * Lemma:  CVM execution preserves well-formednesplit_evt of EvC bundles 
      (EvidenceT Type of sufficient length for raw EvidenceT). *)
Lemma wf_ec_preserved_by_cvm : forall e e' t1 tr tr' i i' ac ac' res,
    wf_ec e ->
    build_cvmP t1
                {| st_ev := e; st_trace := tr; st_evid := i;
                    st_config := ac |}
                (res)
                {| st_ev := e'; st_trace := tr'; st_evid := i';
                    st_config := ac' |} ->
    wf_ec (e').
Proof.
  intros.
  generalizeEverythingElse t1.
  induction t1; intros.
  - (* asp case *)
    rewrite <- ccp_iff_cc in *;
    simpl in *; cvm_monad_unfold; simpl in *.
    ff; try (econstructor; simpl in *; eauto; fail).
    econstructor.
    rewrite app_length;
    rewrite EqClass.nat_eqb_eq in *; subst;
    ff.
    
  - (* at case *)
    invc H0; repeat cvm_monad_unfold; ffa;
    eapply wf_ec_preserved_remote; eauto.
  - (* lseq case *)
    wrap_ccp.
    ff; eauto.
  - (* bseq case *)
    wrap_ccp; ffa.
    inv_wfec; econstructor;
    rewrite app_length; ffa.

  - (* bpar case *)
    wrap_ccp; ffa; cbn; ffa.
    assert (wf_ec (evc r0 e1)).
    {
      rewrite <- Heqe1.
      eapply wf_ec_preserved_par; ffa.
    }
    econstructor; inv_wfec; 
    rewrite app_length; ffa.
Qed.

Ltac do_wfec_preserved :=
  repeat
    match goal with
    | [(*H: well_formed_r ?t, *)
        H2: wf_ec ?stev,
        H3: build_cvmP ?t
            {| st_ev := ?stev; st_trace := _; st_evid := _; st_config := _ |}
            (resultC tt)
            {| st_ev := ?stev'; st_trace := _; st_evid := _; st_config := _ |}
       |- _ ] =>
      assert_new_proof_by (wf_ec stev')
                          ltac:(eapply wf_ec_preserved_by_cvm; [(*apply H |*) apply H2 | apply H3])
                                 
    end.


Axiom ev_cvm_mtc: forall ct p e loc,
    parallel_vm_thread loc ct p mt_evc = parallel_vm_thread loc (lseqc (aspc CLEAR) ct) p e.


(** * Lemma:  EvidenceT Type denotation respects EvidenceT reference semantics  *)
Lemma cvm_ev_denote_evtype: forall annt p e,
    (*(exists n n', anno t n = (n',annt)) -> *)
    et_fun (cvm_EvidenceT_denote annt p e) = (aeval annt p (et_fun e)).
Proof.
  intros.
  generalizeEverythingElse annt.
  induction annt; intros.
  -
    dd.
    destruct a; simpl in *; eauto; repeat ff; subst; simpl in *;
    try rewrite do_asp_EXTD_nofail_length_spec; simpl in *; eauto;
    unfold spc_ev, sp_ev; repeat ff.
  -
    dd.
    eauto.
  -
    dd.
    assert (et_fun (cvm_EvidenceT_denote annt1 p e) = aeval annt1 p (et_fun e)) by eauto.
    repeat jkjke.
  - dd.
    jkjke.
    jkjke.
    destruct s; destruct s; destruct s0; eauto.
  - dd.
    jkjke.
    jkjke.
    destruct s; destruct s; destruct s0; eauto.
Qed.


(** * Lemma:  CVM execution always succeeds *)
Lemma exists_some_cc: forall t st,
    exists st' res,
      build_cvm t st = (res, st').
Proof.
  intros.
  destruct (build_cvm t st) eqn:ee.
  subst.
  eauto.
Qed.

Ltac do_exists_some_cc t st :=
    assert_new_proof_by
      (exists st' res, build_cvm t st = (res, st') )
      ltac:(eapply exists_some_cc);
    destruct_conjs.

(** * Helper Lemma stating: CVM traces are "cumulative" (or monotonic).  
      Traces are only ever extended--prefixes are maintained. *)
Lemma st_trace_cumul'' : forall t m k e v_full v_suffix res i ac,
    build_cvmP t
      {| st_ev := e; st_trace := m ++ k; st_evid := i; st_config := ac |}
      (res) v_full ->
    
    build_cvmP t
      {| st_ev := e; st_trace := k; st_evid := i; st_config := ac |}
      res v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  induction t; intros.
  - (* asp case *)
    (* NOTE: This got really ugly, unfortunately it is quite complex *)
    wrap_ccp.
    match goal with
    | A : ASP_Core |- _ => destruct A
    end; simpl in *; eauto.
    * unfold nullEv in *; cvm_monad_unfold; ff; rewrite app_assoc; eauto.
    * ff. 
    * ff; rewrite app_assoc; eauto. 
    * simpl in *; 
      destruct (aspCb ac a (get_bits e)); simpl in *; eauto;
      repeat find_injection; try rewrite app_assoc; eauto;
      destruct e;
      repeat (match goal with
      | F : FWD |- _ => destruct f
      | R : ResultT _ _ |- _ => destruct R
      | R' : RawEv |- _ => destruct R'
      end; simpl in *; eauto;
        repeat find_injection;
        try rewrite app_assoc; eauto;
        try congruence);
      try (destruct r1; simpl in *; repeat find_injection; eauto;
        try congruence; rewrite app_assoc; eauto);
      try (destruct n; simpl in *; repeat find_injection; 
        try congruence; try rewrite app_assoc; eauto;
        destruct (Nat.eqb (length r1) n); simpl in *;
        repeat find_injection; eauto;
        try congruence; try rewrite app_assoc; eauto
        ).
  - (* at case *)
    invc H; invc H0;
    repeat cvm_monad_unfold; ffa using (try rewrite app_assoc; eauto).

  - (* alseq case *)
    repeat ff.
    wrap_ccp_dohi.
    ff.
    +
    repeat ff; eauto.
    ff. eauto.
    cumul_ih.
    dd.
    repeat do_st_trace.
    repeat find_rw_in_goal.
    eauto.
    +
    wrap_ccp_dohi.
    repeat ff; eauto.
    ff. eauto.
    assert (resultC tt = errC c). 
    {
      rewrite <- ccp_iff_cc in *.
      eapply cvm_errors_deterministic; eauto.
    }
    solve_by_inversion.
    +
    wrap_ccp_dohi.
    repeat ff; eauto.
    ff. eauto.
    assert (resultC tt = errC c). 
    {
      symmetry.
      rewrite <- ccp_iff_cc in *.
      eapply cvm_errors_deterministic.
      apply Heqp1.
      eassumption.
    }
    solve_by_inversion.

    +
    wrap_ccp_dohi.
    ff.

    cumul_ih.
    dd.
    repeat do_st_trace.
    repeat find_rw_in_goal.
    eauto.

  - (* bseq case *)
    wrap_ccp_dohi.
    ff.

    +
    repeat rewrite <- app_assoc in *.
    cumul_ih.
    dd.
    cumul_ih.
    dd.
    intuition.
    +
      assert (errC c0 = resultC u).
      {
        wrap_ccp_dohi; ff. 
        rewrite <- ccp_iff_cc in *.
        eapply cvm_errors_deterministic.
        eapply Heqp5.
        eassumption.
      }
    solve_by_inversion.
    +
    assert (errC c = resultC u).
      {
        wrap_ccp_dohi. ff.
        rewrite <- ccp_iff_cc in *.
        eapply cvm_errors_deterministic; eauto.
      }
    solve_by_inversion.
    +
    assert (errC c0 = resultC u).
      {
        wrap_ccp_dohi. ff.
        rewrite <- ccp_iff_cc in *.
        eapply cvm_errors_deterministic;
        ffa.
      }
    solve_by_inversion.
    +
    repeat rewrite <- app_assoc in *.
    cumul_ih.
    dd.
    cumul_ih.
    dd.
    intuition.
    +
    assert (errC c = resultC u0).
      {
        wrap_ccp_dohi. ff.
        rewrite <- ccp_iff_cc in *.
        eapply cvm_errors_deterministic; eauto.
      }
    solve_by_inversion.
    +
    assert (errC c = resultC u).
      {
        wrap_ccp_dohi. ff.
        rewrite <- ccp_iff_cc in *.
        eapply cvm_errors_deterministic.
        eapply Heqp8. eauto.
      }
    solve_by_inversion.
    +
    assert (errC c = resultC tt).
      {
        wrap_ccp_dohi. ff.
        rewrite <- ccp_iff_cc in *.
        eapply cvm_errors_deterministic.
        eapply Heqp8. eauto.
      }
    solve_by_inversion.
    +
    repeat rewrite <- app_assoc in *.
    wrap_ccp_dohi.
    cumul_ih.
    dd.
    cumul_ih.
    dd.
    intuition.
    +
    repeat rewrite <- app_assoc in *.
    wrap_ccp_dohi.
    cumul_ih.
    dd.
    cumul_ih.
    dd.
    auto with *.

  - (* bpar base *)
  wrap_ccp_dohi.
  ff.

  +
  repeat rewrite <- app_assoc in *.
  cumul_ih.
  dd.
  cumul_ih.
  dd.
  intuition.
  +
  wrap_ccp_dohi.
  repeat rewrite <- app_assoc in *.
  cumul_ih.
  dd.
  cumul_ih.
  dd.
  auto with *.
Qed.

(** * Instance of st_trace_cumul'' where k=[] *)
Lemma st_trace_cumul' : forall t m e v_full v_suffix res i ac,
    build_cvmP t
      {| st_ev := e; st_trace := m; st_evid := i; st_config := ac |}
      (res) v_full ->
    
    build_cvmP t
      {| st_ev := e; st_trace := []; st_evid := i; st_config := ac |}
      res v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  intros.
  eapply st_trace_cumul''; eauto.
  repeat rewrite app_nil_r.
  eauto.
Qed.


(** * Lemma stating: CVM traces are "cumulative" (or monotonic).  
      Traces are only ever extended--prefixes are maintained. 
      TODO:  rename to st_trace_cumul 
*) 
Lemma suffix_prop : forall t e e' tr tr' i i' ac ac' res,
    build_cvmP t
           {| st_ev := e;
              st_trace := tr;
              st_evid := i; st_config := ac |}
           (res)
           {|
             st_ev := e';
             st_trace := tr';
             st_evid := i'; st_config := ac' |} ->
    exists l, tr' = tr ++ l.
Proof.
  intros.

  do_exists_some_cc t {| st_ev := e; st_trace := []; st_evid := i; st_config := ac |}.
  wrap_ccp.
  (*

  rewrite ccp_iff_cc in *. *)

  repeat do_st_trace_assumps.
  repeat find_rw_in_goal.
  eexists.

  erewrite st_trace_cumul''.
  3: {
    eassumption.
  }
  simpl.
  tauto.
  rewrite app_nil_r.
  ff.
  destruct H1; destruct res; ff.
  +
    assert (c = c0).
    {
      edestruct cvm_errors_deterministic; ffa.
      invc H2; ffa.
      invc H; ffa.
      simpl in *; ffa.
    }
    subst.
    eassumption.
  +
  assert (errC c = resultC tt).
  {
    wrap_ccp_dohi. ff.
    invc H2. invc H.
    edestruct cvm_errors_deterministic.
    apply H0.
    apply H1.
    ff.
  }
solve_by_inversion.
  +
  assert (errC c = resultC tt).
  {
    wrap_ccp_dohi. ff.
    invc H2. invc H.
    edestruct cvm_errors_deterministic.
    apply H0.
    apply H1.
    ff.
  }
solve_by_inversion.
  +
    wrap_ccp_dohi.
    eassumption.
Qed.

Ltac do_suffix name :=
  match goal with
  | [H': build_cvmP ?t
         {| st_ev := _; st_trace := ?tr; st_evid := _; st_config := _ |}
         (_)
         {| st_ev := _; st_trace := ?tr'; st_evid := _; st_config := _ |}
         (*H2: well_formed_r ?t*) |- _] =>
    fail_if_in_hyps_type (exists l, tr' = tr ++ l);
    assert (exists l, tr' = tr ++ l) as name by (eapply suffix_prop; [apply H'])
  end.

(** * Structural Lemma:   Decomposes the CVM trace for the lseq phrase into the appending of the two traces
      computed by its subterms, where each subterm starts from the empty trace.

      Useful for leveraging induction hypotheses in the lseq case of induction that require empty traces in the 
      initial CVM state. *)
Lemma alseq_decomp : forall t1' t2' e e'' tr i i'' ac ac'',
    build_cvmP
      (lseqc t1' t2')
      {| st_ev := e;
         st_trace := [];
         st_evid := i; st_config := ac |}
      (resultC tt)
      {| st_ev := e'';
         st_trace := tr;
         st_evid := i''; st_config := ac'' |} ->

    exists e' tr' i' ac',
      build_cvmP
        t1'
        {| st_ev := e;
           st_trace := [];
           st_evid := i; st_config := ac |}
        (resultC  tt)
        {| st_ev := e';
           st_trace := tr';
           st_evid := i'; st_config := ac' |} /\
      exists tr'',
        build_cvmP
          t2'
          {| st_ev := e';
             st_trace := [];
             st_evid := i'; st_config := ac' |}
          (resultC tt)
          {| st_ev := e'';
             st_trace := tr'';
             st_evid := i''; st_config := ac'' |} /\
        tr = tr' ++ tr''.     
Proof.
  intros.
  wrap_ccp_dohi.
  repeat ff.
  wrap_ccp_dohi.
  
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.

  split.
  - rewrite <- ccp_iff_cc in *.
    eassumption.
  -
    do_exists_some_cc t2' {| st_ev := st_ev0; st_trace := []; st_evid := st_evid0; st_config := st_config0 |}.
    vmsts.
    repeat ff.
    destruct H0; ff.
    +
    assert (errC c = resultC tt).
    {
      wrap_ccp_dohi. ff.
      rewrite <- ccp_iff_cc in *.
      eapply cvm_errors_deterministic; eauto.
    }
  solve_by_inversion.
    +
    ff.

    eexists.

    wrap_ccp_dohi.

    split.
    ++
      eassumption.
    ++
      repeat do_st_trace.
      repeat find_rw_in_goal.
      eapply st_trace_cumul'; 
        eassumption.
Qed.


(** Structural convenience lemma:  reconfigures CVM execution to use an empty initial trace *)
Lemma restl : forall t e e' x tr i i' ac ac' res,
    build_cvmP t
      {| st_ev := e; st_trace := x; st_evid := i; st_config := ac|}
      (res)
      {| st_ev := e'; st_trace := x ++ tr; st_evid := i'; st_config := ac' |} ->

    build_cvmP t
      {| st_ev := e; st_trace := []; st_evid := i; st_config := ac |}
      (res)
      {| st_ev := e'; st_trace := tr; st_evid := i'; st_config := ac' |}.
Proof.
  intros.

  do_exists_some_cc t  {| st_ev := e; st_trace := []; st_evid := i; st_config := ac |}.
  wrap_ccp_dohi.

  assert (res = H1).
  {
    wrap_ccp_dohi.
    eapply cvm_errors_deterministic.
    invc H.
    apply H0.
    invc H2.
    eassumption.
  }
  subst.

  assert (st_trace = tr).
  {
    do_st_trace.
    rewrite H0; clear H0.
    assert (tr = st_trace).
    {
      assert (Cvm_St.st_trace {| st_ev := st_ev; st_trace := x ++ tr; st_evid := st_evid; st_config := st_config|} =
              x ++ Cvm_St.st_trace {| st_ev := st_ev; st_trace := st_trace; st_evid := st_evid; st_config := st_config |}).
      {
        eapply st_trace_cumul'; eauto.
        wrap_ccp_dohi.
        eassumption.
      }
      simpl in *.
      eapply app_inv_head; eauto.
    }
    jkjke.
  }

  wrap_ccp_dohi.
  congruence.
Qed.

Ltac do_restl :=
  match goal with
  | [H: build_cvmP ?t
        {| st_ev := ?e; st_trace := ?tr; st_evid := ?i; st_config := ?ac |}
        ?res
        {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_evid := ?i'; st_config := ?ac' |}
        (*H2: well_formed_r ?t*) |- _] =>
    assert_new_proof_by
      (build_cvmP t
        {| st_ev := e; st_trace := []; st_evid := i; st_config := ac|}
        ?res
        {| st_ev := e'; st_trace := x; st_evid := i'; st_config := ac' |})
      ltac:(eapply restl; [apply H])
  end.

(** * Lemma:  EvidenceT semantics same for annotated and un-annotated terms *)
Lemma eval_aeval': forall t1 p et,
    eval (unanno t1) p et = aeval t1 p et.
Proof.
  induction t1; intros;
    repeat ff;
    repeat jkjke.
Qed.

Axiom cvm_EvidenceT_correct_type : forall t p e e',
  cvm_EvidenceT t p e = e' -> 
  get_et e' = eval t p (get_et e).


(** * Lemma:  parallel CVM threads preserve the reference EvidenceT Type semantics (eval). *)
Lemma par_EvidenceT_r: forall l p bits bits' et et' t2,
    parallel_vm_thread l (copland_compile t2) p (evc bits et) = evc bits' et' ->
    et' = eval t2 p et.
Proof.
  intros.
  rewrite par_EvidenceT in H.
  assert (get_et (evc bits' et') = eval t2 p (get_et (evc bits et))).
  {
    eapply cvm_EvidenceT_correct_type; eauto.
  }
  ff.
Qed.
         
(** * Axiom about "simulated" parallel semantics of CVM execution:
      Executing a "CLEAR" before a term is the same as executing that term with mt_evtinitial EvidenceT.
      TODO:  can we use existing axioms to prove this? *)
Axiom par_EvidenceT_clear: forall l p bits et t2,
    parallel_vm_thread l (lseqc (aspc CLEAR) t2) p (evc bits et) =
    parallel_vm_thread l t2 p mt_evc.

Lemma doRemote_session'_sc_immut : forall t st st' res p ev,
    doRemote_session' t p ev st = (res, st') ->
    st_config st = st_config st'.
Proof.
  unfold doRemote_session'.
  intuition.
  cvm_monad_unfold.
  ff.
Qed.

Lemma build_cvm_sc_immut : forall t st st' res,
    build_cvm t st = (res, st') ->
    st_config st = st_config st'.
Proof.
  induction t; simpl in *; intuition; eauto; ffa using cvm_monad_unfold.
Qed.

Lemma build_cvmP_sc_immut : forall t st st' res,
    build_cvmP t st res st' ->
    st_config st = st_config st'.
Proof.
  setoid_rewrite <- ccp_iff_cc.
  eapply build_cvm_sc_immut.
Qed.

(** * Main Lemma:  CVM execution maintains the EvidenceT Type reference semantics (eval) for 
      its internal EvidenceT bundle. *)
Lemma cvm_refines_lts_EvidenceT' : forall t tr tr' bits bits' et et' i i' ac ac',
    build_cvmP (copland_compile t)
        (mk_st (evc bits et) tr i ac)
        (resultC tt)
        (mk_st (evc bits' et') tr' i' ac') ->
    et' = (Term_Defs.eval t (session_plc ac) et).
Proof.
  intuition.
  eapply build_cvmP_sc_immut in H as H'.
  simpl in *; subst.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    rewrite <- ccp_iff_cc in *.
    ffa.  
    destruct a; (try dd; eauto); ffa using cvm_monad_unfold.
      

  - (* at case *)
    rewrite <- ccp_iff_cc in *.
    dd.
    repeat ffa.

  - (* alseq case *)
    do_suffix blah.
    destruct_conjs.
    subst.

    edestruct alseq_decomp.
    eapply restl.
    eassumption.
    fold copland_compile in *.
    destruct_conjs.
    repeat match goal with
    | x : EvC |- _ =>
      destruct x
    | H : build_cvmP (copland_compile t1) _ _ _ |- _ =>
      let AC := fresh "AC" in
      let Ho := fresh "Ho" in
      eapply build_cvmP_sc_immut in H as AC;
      simpl in *; try rewrite AC in *; clear AC;
      eapply IHt1 in H as Ho;
      simpl in *; subst; clear H
    | H2 : build_cvmP (copland_compile t2) _ _ _ |- _ =>
      let AC := fresh "AC" in
      let Ho := fresh "Ho" in
      eapply build_cvmP_sc_immut in H2 as AC;
      simpl in *; try rewrite AC in *; clear AC;
      eapply IHt2 in H2 as Ho;
      simpl in *; subst; clear H2
    end; eauto.
    
  - (* abseq case *)
    simpl in *; repeat ff; subst;
    wrap_ccp; cbn in *; repeat ff; cbn in *;
    repeat match goal with
    | x : EvC |- _ =>
      destruct x
    | u : unit |- _ =>
      destruct u
    | H : build_cvmP (copland_compile t1) _ _ _ |- _ =>
      let AC := fresh "AC" in
      let Ho := fresh "Ho" in
      eapply build_cvmP_sc_immut in H as AC;
      simpl in *; try rewrite AC in *; clear AC;
      eapply IHt1 in H as Ho;
      simpl in *; subst; clear H
    | H2 : build_cvmP (copland_compile t2) _ _ _ |- _ =>
      let AC := fresh "AC" in
      let Ho := fresh "Ho" in
      eapply build_cvmP_sc_immut in H2 as AC;
      simpl in *; try rewrite AC in *; clear AC;
      eapply IHt2 in H2 as Ho;
      simpl in *; subst; clear H2
    end; eauto.

   - (* abpar case *)

    destruct s; repeat ffa;
    wrap_ccp; cbn in *; repeat ff; cbn in *;
    repeat (ffa; match goal with
    | u : unit |- _ =>
      destruct u
    end).
    +
      assert (e0 = eval t2 (session_plc ac') et).
      {
        eapply par_EvidenceT_r; eauto.
      }
      ffa.
      
    +
      find_apply_hyp_hyp.

      assert (e0 = eval t2 (session_plc ac') mt_evt).
      {
        rewrite par_EvidenceT_clear in *.
        eapply par_EvidenceT_r; eauto.
      }
      congruence.
    +
      wrap_ccp.
      ffa.
      assert (e0 = eval t2 (session_plc ac') et).
      {
        eapply par_EvidenceT_r; eauto.
      }
      congruence.
    +
      wrap_ccp.
      ffa.
      assert (e0 = eval t2 (session_plc ac') mt_evt).
      {
        rewrite par_EvidenceT_clear in *.

        eapply par_EvidenceT_r; eauto.
      }
      congruence.
Qed.

(** * Propositional version of CVM EvidenceT Type preservation. *)
Lemma cvm_refines_lts_EvidenceT :
  forall t t' tr tr' bits bits' et et' i i' ac ac',
    term_to_coreP t t' ->
    build_cvmP t'
      (mk_st (evc bits et) tr i ac)
      (resultC tt)
      (mk_st (evc bits' et') tr' i' ac') ->
    et' = (Term_Defs.eval t (session_plc ac) et).
Proof.
  intros.
  invc H.
  eapply cvm_refines_lts_EvidenceT'.
  eauto.
Qed.


(** BEGIN Deprecated parallel annotated term stuff *)

(*
Lemma anno_parP_redo: forall t pt loc loc',
    anno_par_list' t loc = Some (loc', pt) ->
    anno_parP pt t.
Proof.
  intros.
  econstructor.
  eexists.
  jkjke.
Qed.

(*
Lemma anno_parPloc_redo: forall t pt loc loc',
    anno_par t loc = (loc', pt) ->
    anno_parPloc pt t loc.
Proof.
  intros.
  econstructor.
  jkjke.
Qed.
 *)
Lemma anno_parPloc_redo: forall t pt loc loc',
    anno_par_list' t loc = Some (loc', pt) ->
    anno_parPloc pt t loc.
Proof.
  intros.
  econstructor.
  jkjke.
Qed.

 *)

(*

Ltac do_annopar_redo :=
  match goal with
  | [H: anno_par ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parP_redo in H
  end.

Ltac do_annopar_loc_redo :=
  match goal with
  | [H: anno_par ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parPloc_redo in H
  end.
 *)


(*

Ltac do_annopar_redo :=
  match goal with
  | [H: anno_par_list' ?t ?loc = Some (_,?pt)
     |- _ ] =>
    eapply anno_parP_redo in H
  end.

Ltac do_annopar_loc_redo :=
  match goal with
  | [H: anno_par_list' ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parPloc_redo in H
  end.



Ltac inv_annoparP :=
  match goal with
  | [H: anno_parP _ _ (* ?t (?c _) *)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.

Ltac inv_annoparPloc :=
  match goal with
  | [H: anno_parPloc _ _ _(*?t (?c _) _ *)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.
 *)


(*
Ltac wrap_annopar :=
  inv_annoparP;
  dd;
  repeat do_annopar_redo.

Ltac wrap_annoparloc :=
  inv_annoparPloc;
  dd;
  repeat do_annopar_loc_redo.
 *)


(** END Deprecated parallel annotated term stuff *)
