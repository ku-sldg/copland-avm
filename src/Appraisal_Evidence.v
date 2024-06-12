(* Definitions, properties, and associated automation related to 
    Appraisal and Evidence examination/reconstruction.

    Also included:  properties about CVM internal Evidence and Event handling.  
    TODO:  This file has become quite bloated.  May need to refactor/decompose.  *)

Require Import ConcreteEvidence AutoApp Auto Helpers_CvmSemantics Term_Defs Anno_Term_Defs Cvm_St Cvm_Impl Defs StructTactics OptMonad_Coq IO_Stubs Evidence_Bundlers Axioms_Io External_Facts.

Require Import List.
Import ListNotations.

Require Import Lia Coq.Program.Tactics.


Definition peel_bs (ls:RawEv) : Opt (BS * RawEv) :=
  match ls with
  | bs :: ls' => OptMonad_Coq.ret (bs, ls')
  | _ => OptMonad_Coq.failm
  end.

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

Fixpoint encodeEv (e:EvidenceC) : RawEv :=
  match e with
  | mtc => []
  | nnc _ bs => [bs]
  | ggc _ _ bs e' => bs :: (encodeEv e')
  | hhc _ _ bs _ => [bs]
  | eec _ _ bs _ => [bs]
  | kkc _ _ _ => []
  | kpc _ _ e' => encodeEv e'
  | ssc e1 e2 => (encodeEv e1) ++ (encodeEv e2)
  end.

Fixpoint reconstruct_ev' (ls:RawEv) (et:Evidence) : Opt EvidenceC :=
  match et with
  | mt => 
    match ls with
    | [] => Some mtc
    | _ => None
    end
  | uu p fwd ps et' =>
    match fwd with
    | EXTD => 
      '(bs, ls') <- peel_bs ls ;;
      x <- reconstruct_ev' ls' et' ;;
      Some (ggc p ps bs x)
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
  end.

Definition reconstruct_ev (e:EvC) : Opt EvidenceC :=
  match e with
  | evc ls et => reconstruct_ev' ls et
  end.

Inductive reconstruct_evP: EvC -> EvidenceC -> Prop :=
| reconstruct_evC: forall e ee,
    Some ee = reconstruct_ev e ->
    reconstruct_evP e ee.


Lemma inv_recon_mt: forall ls et,
    reconstruct_evP (evc ls et) mtc ->
    (et = mt).
Proof.
  intros.
  invc H.
  destruct et;
    repeat ff;
    try (unfold OptMonad_Coq.bind in *);
         repeat ff;
         try solve_by_inversion.
                    
         -
           eauto.
                                   
Defined.

Ltac do_inv_recon_mt :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) mtc

     |- _] =>
    assert_new_proof_by (et = mt) ltac:(eapply inv_recon_mt; apply H)
  end;
  subst.

Lemma inv_recon_mt': forall ls e,
    reconstruct_evP (evc ls mt) e ->
    e = mtc.
Proof.
  intros.
  invc H.
  repeat ff; try solve_by_inversion; eauto.
Defined.

Ltac do_inv_recon_mt' :=
  match goal with
  | [H: reconstruct_evP (evc _ mt) ?e

     |- _] =>
    assert_new_proof_by (e = mtc) ltac:(eapply inv_recon_mt'; apply H)
  end;
  subst.


Lemma inv_recon_nn: forall ls et n n0,
    reconstruct_evP (evc ls et) (nnc n n0) ->
    ((et = nn n /\ ls = [n0])).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; destruct ls; try solve_by_inversion.                              
Defined.

Ltac do_inv_recon_nn :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (nnc ?n ?nval)

     |- _] =>
    assert_new_proof_by (et = nn n /\ ls = [nval] ) ltac:(eapply inv_recon_nn; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_gg: forall p ps ls et n ec,
    reconstruct_evP (evc ls et) (ggc p ps n ec) ->
    (exists ls' et', et = uu p EXTD ps et' /\
                ls = n :: ls') .
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; try solve_by_inversion.
                               -
                                 repeat eexists.
                                 destruct ls; ff.                         
Defined.

Ltac do_inv_recon_gg :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (ggc ?p ?ps ?n _)

     |- _] =>
    assert_new_proof_by ((exists ls' et', et = uu p EXTD ps et' /\
                                    ls = n :: ls') )
                        ltac:(eapply inv_recon_gg; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_hh: forall p ps ls et n et',
    reconstruct_evP (evc ls et) (hhc p ps n et') ->
    ((et = uu p COMP ps et' ) /\ ls = [n]).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; destruct ls; try solve_by_inversion.
Defined.

Ltac do_inv_recon_hh :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (hhc ?p ?ps ?hval ?et')

     |- _] =>
    assert_new_proof_by ((et = uu p COMP ps et' /\ ls = [hval]))
                        ltac:(eapply inv_recon_hh; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_ee: forall p ps ls et n ec',
    reconstruct_evP (evc ls et) (eec p ps n ec') ->
    (exists et', et = uu p ENCR ps et' /\ ls = [n]).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); 
  repeat ff; destruct ls; try solve_by_inversion;
  repeat eexists; ff.
Defined.

Ltac do_inv_recon_ee :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (eec ?p ?ps ?hval (*_*) _)

     |- _] =>
    assert_new_proof_by ( (exists et', et = uu p ENCR ps et' /\ ls = [hval]) )
                        ltac:(eapply inv_recon_ee; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_ss: forall ls et ec1 ec2,
    reconstruct_evP (evc ls et) (ssc ec1 ec2) ->
    (exists et1 et2, et = ss et1 et2).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); 
  repeat ff; try solve_by_inversion;
  eauto.
Defined.

Ltac do_inv_recon_ss :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) (ssc _ _)

     |- _] =>
    assert_new_proof_by ((exists et1 et2, et = ss et1 et2) )
                        ltac:(eapply inv_recon_ss; apply H)
  end;
  destruct_conjs;
  subst.


Ltac do_inv_recon :=
  try do_inv_recon_mt;
  try do_inv_recon_mt';
  try do_inv_recon_nn;
  try do_inv_recon_gg;
  try do_inv_recon_hh;
  try do_inv_recon_ee;
  try do_inv_recon_ss.

Lemma recon_inv_gg: forall sig ls p ps et e,
    reconstruct_evP
      (evc (sig :: ls) (uu p EXTD ps et))
      (ggc p ps sig e) ->
    reconstruct_evP (evc ls et) e.
Proof.
  intros.
  invc H.
  repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff;
  econstructor.
  symmetry.
  tauto.
Defined.

Ltac do_recon_inv_gg :=
  match goal with
  | [H: reconstruct_evP
          (evc (_ :: ?ls) (uu _ _ _ ?et))
          (ggc _ _ _ ?e)
     |- _] =>
    assert_new_proof_by (reconstruct_evP (evc ls et) e) ltac:(eapply recon_inv_gg; apply H)
  end.

Lemma recon_inv_ss: forall ls H1 H2 ec1 ec2,
    reconstruct_evP (evc ls (ss H1 H2)) (ssc ec1 ec2) ->
    reconstruct_evP (evc (firstn (et_size H1) ls) H1) ec1 /\
    reconstruct_evP (evc (skipn (et_size H1) ls) H2)  ec2.
Proof.
  intros.
  invc H.
  repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff;
  split;
    econstructor;
    try 
      symmetry; eassumption.
Qed.

Ltac do_recon_inv_ss :=
  match goal with
  | [H: reconstruct_evP
          (evc ?ls (ss ?H1 ?H2))
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
Defined.

Lemma fold_recev: forall e0 e1,
    reconstruct_ev' e0 e1 = reconstruct_ev (evc e0 e1).
Proof.
  ff.
  tauto.
Defined.

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
    repeat Auto.ff;
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
  - (* mt case *)
    invc H.
    ff.
    tauto.
  - (* nn case *)
    invc H.
    repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
  
  - (* uu case *)
    destruct f; ff.
    + (* COMP case *)
      invc H.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
    + (* ENCR case *)
      
      invc H.
      unfold reconstruct_ev in *.
      unfold reconstruct_ev' in *.
      unfold OptMonad_Coq.bind in *.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
           
    + (* EXTD case *)
      invc H.
      ff.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
      assert (e1 = et_fun e2 ).
      {
      eapply IHe1.
      econstructor.
      ff.
      }
      congruence.
    + (* KILL case *)
      invc H.
      unfold reconstruct_ev in *.
      ff.
    + (* KEEP case *)
      invc H.
      unfold reconstruct_ev in *.
      ff.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
      assert (e1 = et_fun e2).
      { eapply IHe1.
        econstructor.
        unfold reconstruct_ev.
        symmetry.
        eassumption.
      }
      subst.
      tauto.
  - (* ss case *)
    invc H.
    ff.
    repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
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
Defined.

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
  induction ec; intros.
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
    unfold OptMonad_Coq.bind in *.
    ff.
    assert (reconstruct_evP (evc H0 H1) e).
    {
      econstructor; eauto.
    }
    assert (encodeEv e = H0) by eauto.
    congruence.
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
    unfold OptMonad_Coq.bind in *.
    ff.
    rewrite fold_recev in *.
    unfold reconstruct_ev in *.
    unfold reconstruct_ev' in *.
    destruct et; try solve_by_inversion.
    ff.
    unfold OptMonad_Coq.bind in *.
    ff.
    unfold OptMonad_Coq.bind in *.
    ff.
    unfold OptMonad_Coq.bind in *.
    ff.


  - (* kpc case *)
    ff.

    assert (exists et', et = uu p KEEP a et').
    {
      destruct et; try solve_by_inversion.
      +
        invc H.
        ff.
      +
        invc H.
        ff.
        repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
      +
        invc H.
        ff.
        repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
        repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
        repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
        repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
        eexists.
        tauto.
      +
        invc H.
        ff.
        repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
    }
    
    destruct_conjs.
    subst.

    invc H.
    ff.
    repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
    eapply IHec.
    econstructor.
    ff.
    
  - (* ssc case *)
    do_inv_recon.
    ff.
    invc H.
    ff.
    unfold OptMonad_Coq.bind in *.
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

Lemma recon_encodeEv_Raw: forall ec bits et,
    reconstruct_evP (evc bits et) ec ->
    encodeEvRaw (encodeEv ec) = encodeEvBits (evc bits et).
Proof.
  intros.
  unfold encodeEvBits.
  erewrite recon_encodeEv.
  tauto.
  eauto.
Defined.

Lemma wfec_recon: forall (ee:EvC) (ec:EvidenceC),
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
    unfold OptMonad_Coq.bind in *.
    ff.
    assert (wf_ec (evc H0 H1)).
    {
      apply IHec.
      econstructor.
      eauto.
    }
    econstructor.
    dd.
    invc H.
    lia.

  - (* hhc case *)
    do_inv_recon.
    invc H.
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
    unfold OptMonad_Coq.bind in *. ff.
    unfold OptMonad_Coq.bind in *. ff.
    econstructor.
    ff.
    unfold OptMonad_Coq.bind in *. ff.
  - (* kpc case *)
    invc H.
    destruct e; try solve_by_inversion.
    +
      ff.
    +
      ff.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
    +
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
      assert (wf_ec (evc r e)).
      {
        eapply IHec. econstructor.
        symmetry. eassumption. }
      econstructor.
      ff.
    +
      ff.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
   
  -
    do_inv_recon.
    invc H.
    dd.
    ff.
    unfold OptMonad_Coq.bind in *.
    
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
Defined.

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

(** * If a raw evidence sequence is non-empty, we can grab a first element. *)
Lemma some_recons' : forall e x,
    length e = S x ->
    exists bs ls', peel_bs e = Some (bs, ls').
Proof.
  intros.
  destruct e;
    ff; eauto.
Defined.

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
      ltac:(eapply H with (r:=e'); (* TODO:  make r less one-off *)
            try (eapply peel_fact; eauto; tauto);
            try (econstructor; first [eapply firstn_long | eapply skipn_long]; try eauto; try lia))      
  end.

(** * Lemma:  well-formed EvC bundles can be successfully reconstructed to a Typed Concrete Evidence (EvidenceC) value. *)
Lemma some_recons : forall (e:EvC),
    wf_ec e ->
    exists (ee:EvidenceC), Some ee = reconstruct_ev e.
Proof.
  intros.
  destruct e.
  generalizeEverythingElse e.
  induction e; intros.
  -
  try (repeat ff; eauto; tauto).
    try
      ( inv_wfec; ff;
        do_some_recons');
    try (
        repeat do_rcih;
        destruct_conjs;
        repeat jkjke');
    try ( inv_wfec; ff;
          repeat do_rcih;
          destruct_conjs;
          repeat jkjke';
          repeat ff; eauto).

  - (* nn case *)
    repeat ff.
    (unfold OptMonad_Coq.bind in * ).
     repeat ff.
     +
     eauto.
     +
       inv_wfec.
       ff.
       destruct r; try solve_by_inversion.
       ff.
       unfold OptMonad_Coq.ret in *.
       repeat ff.
       

     +
       destruct r; try solve_by_inversion.
       ff.
       invc H.
       ff.

  - (* uu case *)

    destruct f.
    
    + (* COMP case *)

      inv_wfec.
      ff.
      repeat ff;
    (unfold OptMonad_Coq.bind in * );
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
    (unfold OptMonad_Coq.bind in * );
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
      unfold OptMonad_Coq.bind in * ;
        repeat ff; eauto.
      ++
        assert (wf_ec (evc r0 e)).
        {
          eapply peel_fact.
          eassumption.
          eassumption.
          tauto.
        }
       
          
          
        assert (exists ee, Some ee = reconstruct_ev' r0 e).
        {
          invc H.
          eapply IHe.
         econstructor. eassumption. }
        destruct_conjs.
        ff.
      ++
         inv_wfec.
       ff.
       assert (r = []).
       {
         destruct r; ff.
       }
       subst.
       ff.
    + (* KILL case *)
      inv_wfec.
      ff.
      eauto.
    + (* KEEP case *)
      inv_wfec.
      simpl in H1.
      ff.

    repeat ff;
    (unfold OptMonad_Coq.bind in * );
    repeat ff; eauto.
    assert (exists ee, Some ee = reconstruct_ev' r e).
    { eapply IHe.
      econstructor.
      eassumption.
    }
    destruct_conjs.
    congruence.
     - (* ss case *)
       try (ff; eauto; tauto).
       inv_wfec; ff.
    do_rcih.
    do_rcih.
    destruct_conjs.
    jkjke'.
    jkjke'.
    ff.
    eauto.
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
Defined.

Ltac do_somerecons :=
  repeat
    match goal with
    | [H: wf_ec ?e
       |- _ ] =>
      assert_new_proof_by
        (exists x, reconstruct_evP e x)
        ltac:(eapply some_reconsP; apply H)     
    end; destruct_conjs.

Definition spc_ev (sp:SP) (e:EvidenceC) : EvidenceC :=
  match sp with
  | ALL => e
  | NONE => mtc
  end.

(*
TODO: try this again after appraisal lemmas settled 
*)

Definition do_asp_nofail (ps:ASP_PARAMS) (ev:RawEv) (p:Plc) (x:Event_ID): BS.
Admitted. (* TODO:  fill this in with some sort of callback + default value? *)

Definition cvm_evidence_denote_asp (a:ASP) (p:Plc) (e:EvidenceC) (x:Event_ID): EvidenceC :=
  match a with
  | NULL => mtc
  | CPY => e
  | ASPC sp fwd params =>
    match fwd with
    | COMP => hhc p params
                 (do_asp_nofail params (encodeEv (spc_ev sp e)) p x)
                 (sp_ev sp (et_fun e))
    | EXTD => ggc p params
                 (do_asp_nofail params (encodeEv (spc_ev sp e)) p x)
                 (spc_ev sp e)
    | ENCR => eec p params
                 (do_asp_nofail params (encodeEv (spc_ev sp e)) p x)
                 (sp_ev sp (et_fun e))
    | KEEP => (spc_ev sp e)
    | KILL => mtc (* kkc p params (sp_ev sp (et_fun e)) *)
    end
  | SIG => ggc p sig_params
              (do_asp_nofail sig_params (encodeEv e) p x)
              e
  | HSH => hhc p hsh_params
              (do_asp_nofail hsh_params (encodeEv e) p x)
              (et_fun e)
  | ENC q => eec p (enc_params q)
                (do_asp_nofail (enc_params q) (encodeEv e) p x)
                (et_fun e)
  end.


(** * Denotation function of a Typed Concrete Evidence value from an annotated term, initial place, initial evidence *)
Fixpoint cvm_evidence_denote (t:AnnoTerm) (p:Plc) (ec:EvidenceC) : EvidenceC :=
  match t with
  | aasp (i,_) x => cvm_evidence_denote_asp x p ec i
  | aatt _ q x => cvm_evidence_denote x q ec
  | alseq _ t1 t2 => cvm_evidence_denote t2 p (cvm_evidence_denote t1 p ec)
  | abseq _ s t1 t2 => ssc (cvm_evidence_denote t1 p ((splitEvl s ec)))
                         (cvm_evidence_denote t2 p ((splitEvr s ec)))
  | abpar _ s t1 t2 => ssc (cvm_evidence_denote t1 p ((splitEvl s ec)))
                         (cvm_evidence_denote t2 p ((splitEvr s ec)))
  end.

Set Warnings "-notation-overridden".
Require Import Cvm_Monad.
Set Warnings "+notation-overridden".


(** * Assert an arbitrary (remote) CVM execution.  
      Uses uninterpreted functions for "simulated" CVM evidence and events. *)
Ltac do_assert_remote t e p i ac :=
  assert (
      build_cvm t
                      {| st_ev := e; st_trace := []; st_pl := p; st_evid := i; st_AM_config := ac |} =
      (resultC tt,
       {| st_ev := cvm_evidence_core t p e;
          st_trace := cvm_events_core t p (get_et e);
          st_pl := p; 
          st_evid :=  (i + event_id_span t); 
          st_AM_config := ac
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
Lemma cvm_spans: forall t pt e tr p i e' tr' p' i' ac ac',
    term_to_coreP t pt ->
    build_cvmP
      pt
      {| st_ev := e;
         st_trace := tr;
         st_pl := p;
         st_evid := i;
         st_AM_config := ac |}
      (resultC tt)
      {|
        st_ev := e';
        st_trace := tr';
        st_pl := p';
        st_evid := i';
        st_AM_config := ac'
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
Defined.
  *)
   
  - (* asp case *)
    destruct a;
      try destruct a;
      ff; try tauto;
      try (wrap_ccp_anno; ff).
  
  - (* at case *)
  repeat ff;
  unfold doRemote_session' in *;
  repeat Auto.ff.
  lia.

  - (* lseq case *)
    wrap_ccp_anno.

    destruct r; ff.
    destruct u; ff.



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
Lemma span_cvm: forall atp t annt i j e e' tr tr' p p' i' ac ac',
    build_cvmP
      atp
      {| st_ev := e;
         st_trace := tr;
         st_pl := p;
         st_evid := i;
         st_AM_config := ac |} 
      (resultC tt)
      {| st_ev := e';
         st_trace := tr';
         st_pl := p';
         st_evid := i';
         st_AM_config := ac' |} ->
    
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
Defined.


(** * Propositional version of span_cvm *)
Lemma anno_span_cvm: forall t pt annt i i' e e' p p' tr tr' st_evid1 ac ac',
    annoP_indexed annt t i i' ->
    term_to_coreP t pt ->
    build_cvmP pt
                     {|
                       st_ev := e ;
                       st_trace := tr ;
                       st_pl := p;
                       st_evid := i;
                       st_AM_config := ac
                     |} (resultC tt)
                     {|
                       st_ev := e';
                       st_trace := tr';
                       st_pl := p';
                       st_evid := st_evid1;
                       st_AM_config := ac'
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
  eapply More_lists.firstn_append.
Defined.

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
Defined.

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


(** * Axiom:  assume parallel CVM threads preserve well-formedness of EvC bundles *)
Axiom wf_ec_preserved_par: forall e l t2 p,
    wf_ec e ->
    wf_ec (parallel_vm_thread l t2 p e).

Lemma check_cvm_policy_preserves_plc : forall t p evt st1 u st1',
  check_cvm_policy t p evt st1 = (resultC u, st1') ->
  st_pl st1 = st_pl st1'.
Proof.
  induction t; simpl in *; intuition; eauto; ff.
Qed.

Lemma check_cvm_policy_preserves_amConf : forall t p evt st1 u st1',
  check_cvm_policy t p evt st1 = (resultC u, st1') ->
  st_AM_config st1 = st_AM_config st1'.
Proof.
  induction t; simpl in *; intuition; eauto; ff.
Qed.

Lemma doRemote_session'_plc_immut : forall t1 pto e st1 res st2,
  doRemote_session' t1 pto e st1 = (res, st2) ->
  st_pl st1 = st_pl st2.
Proof.
  unfold doRemote_session'; intuition; monad_unfold;
  simpl in *; repeat ff.
Qed.

Lemma build_cvmP_plc_immut : forall t1 st1 st2 res,
  build_cvmP t1 st1 res st2 ->
  st_pl st1 = st_pl st2.
Proof.
  intuition.
  rewrite <- ccp_iff_cc in H.
  generalizeEverythingElse t1.
  induction t1; simpl in *; intuition; eauto; ff.
  - monad_unfold; destruct a; ff.
  - repeat (monad_unfold; simpl in *; intuition; eauto; ff);
    eapply doRemote_session'_plc_immut in Heqp0; eauto.
  - repeat (monad_unfold; simpl in *; intuition; eauto; ff).
    eapply IHt1_1 in Heqp; find_rewrite.
    eapply IHt1_2 in Heqp0; find_rewrite.
    eauto.
  - repeat (monad_unfold; simpl in *; intuition; eauto; ff).
    * eapply IHt1_1 in Heqp; eauto.
    * eapply IHt1_1 in Heqp; simpl in *; subst.
      eapply IHt1_2 in Heqp4; simpl in *; eauto.
      find_rewrite; eauto.
    * eapply IHt1_1 in Heqp; simpl in *; subst.
      eapply IHt1_2 in Heqp4; simpl in *; eauto.
      find_rewrite; eauto.
  - repeat (monad_unfold; simpl in *; intuition; eauto; ff).
    * eapply IHt1_1 in Heqp; eauto.
    * subst; simpl in *. 
      eapply IHt1_1 in Heqp; eauto.
Qed.

(** * Lemma:  CVM execution preserves well-formedness of EvC bundles 
      (Evidence Type of sufficient length for raw evidence). *)
Lemma wf_ec_preserved_by_cvm : forall e e' t1 tr tr' p p' i i' ac ac' res,
    wf_ec e ->
    build_cvmP t1
                {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i;
                    st_AM_config := ac |}
                (res)
                {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i';
                    st_AM_config := ac' |} ->
    wf_ec (e').
Proof.
  intros.
  eapply build_cvmP_plc_immut in H0 as HP; simpl in *; subst.
  generalizeEverythingElse t1.
  induction t1; intros.
  - (* asp case *)
    rewrite <- ccp_iff_cc in *.
    destruct a; (* asp *)
      try destruct a; (* asp params *)
      ff;
      inv_wfec;
      try (
          econstructor;
          ff;
          try tauto;
          try congruence).
    +
      destruct f; 
        repeat Auto.ff;
        try (econstructor; eauto).

        ff.
    
  - (* at case *)
    wrap_ccp.
    repeat Auto.ff.
    (* unfold do_remote in *. *)
    repeat ff;
    unfold doRemote_session' in *;
    repeat ff.
    monad_unfold.
    repeat ff.
    unfold doRemote_session' in *;
    repeat ff.
    repeat monad_unfold.
    (* invc Heqr0. *)
    unfold do_remote in *.
    break_match; eauto.
    break_match; subst; eauto.
    ff.
    break_match; eauto.
    break_match; eauto.
    break_match; eauto.
    break_match; eauto.
    ff.
    ff.
    break_match; eauto.
    ff.
    break_match; eauto; [ | ff].
    repeat find_injection.
    break_match; subst; eauto; try congruence.
    simpl in *.
    break_match; subst; eauto.
    break_match; subst; eauto; try congruence.
    find_injection.
    eapply check_cvm_policy_preserves_amConf in Heqp1 as AMC.
    eapply check_cvm_policy_preserves_plc in Heqp1 as PLC.
    simpl in *; subst.
    eapply wf_ec_preserved_remote; eauto.
    assert (p = my_abstract_plc (absMan ac')). {
      clear Heqo Heqr2.

    }
    Search check_cvm_policy.
    eapply Heqo.
    repeat find_injection.
    break_match; subst; eauto.
    
    ff.
     
    repeat ff.
    eapply (wf_ec_preserved_remote u0); eauto.
    simpl in *.
    cbv.
    repeat ff.
    eapply wf_ec_preserved_remote; eauto.

  - (* lseq case *)
    wrap_ccp.
    ff; eauto.
  - (* bseq case *)
    wrap_ccp.

    ff; eauto.

    (* do_wfec_split. *)

    find_apply_hyp_hyp.
    find_apply_hyp_hyp.
    econstructor.
    dd.
    inv_wfec.
    repeat jkjke'.
    eapply app_length.

  - (* bpar case *)
    wrap_ccp.
    ff; eauto.

    (* do_wfec_split. *)

    find_apply_hyp_hyp.

      inv_wfec;
      ff;
      econstructor;
      dd;
      repeat jkjke'.

    erewrite app_length.

    assert (wf_ec (evc r1 e1)).
    {
      rewrite <- Heqe1.
      eapply wf_ec_preserved_par.
      econstructor; eassumption.
    }

    solve_by_inversion.
Qed.

Ltac do_wfec_preserved :=
  repeat
    match goal with
    | [(*H: well_formed_r ?t, *)
          H2: wf_ec ?stev,
              H3: build_cvmP ?t
                                   {| st_ev := ?stev; st_trace := _; st_pl := _; st_evid := _ |}
                                   (resultC tt)
                                   {| st_ev := ?stev'; st_trace := _; st_pl := _; st_evid := _ |}
       |- _ ] =>
      assert_new_proof_by (wf_ec stev')
                          ltac:(eapply wf_ec_preserved_by_cvm; [(*apply H |*) apply H2 | apply H3])
                                 
    end.


Axiom ev_cvm_mtc: forall ct p e loc,
    parallel_vm_thread loc ct p mt_evc = parallel_vm_thread loc (lseqc (aspc CLEAR) ct) p e.


(** * Lemma:  Evidence Type denotation respects evidence reference semantics  *)
Lemma cvm_ev_denote_evtype: forall annt p e,
    (*annoP annt t -> *)
    et_fun (cvm_evidence_denote annt p e) = (aeval annt p (et_fun e)).
Proof.
  intros.
  generalizeEverythingElse annt.
  induction annt; intros.
  -
    dd.
    destruct a; dd;
      try eauto.
    +
      destruct f; ff.
      destruct s; ff.
      destruct s; ff.
  -
    dd.
    eauto.
  -
    dd.
    assert (et_fun (cvm_evidence_denote annt1 p e) = aeval annt1 p (et_fun e)) by eauto.
    repeat jkjke.
  -
    dd.
    jkjke.
    jkjke.
    destruct s; destruct s; destruct s0; eauto.
  -
    dd.
    jkjke.
    jkjke.
    destruct s; destruct s; destruct s0; eauto.
Defined.


(** * Lemma:  CVM execution always succeeds *)
Lemma exists_some_cc: forall t st,
    exists st' res,
      build_cvm t st = (res, st').
Proof.
  intros.
  destruct (build_cvm t st) eqn:ee.
  subst.
  eauto.
Defined.

Ltac do_exists_some_cc t st :=
    assert_new_proof_by
      (exists st' res, build_cvm t st = (res, st') )
      ltac:(eapply exists_some_cc);
    destruct_conjs.



(** * Helper Lemma stating: CVM traces are "cumulative" (or monotonic).  
      Traces are only ever extended--prefixes are maintained. *)
Lemma st_trace_cumul'' : forall t m k e p v_full v_suffix res i ac,
    build_cvmP t
               {| st_ev := e; st_trace := m ++ k; st_pl := p; st_evid := i;
                       st_AM_config := ac |}
               (res) v_full ->
    
    build_cvmP t
                     {| st_ev := e; st_trace := k; st_pl := p; st_evid := i;
                       st_AM_config := ac |}
                     res v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  induction t; intros.
  - (* asp case *)
    wrap_ccp.
    ff; eauto; auto with *.
  - (* at case *)
    wrap_ccp.
    repeat Auto.ff.


    unfold doRemote_session' in *;
    repeat Auto.ff; 
    repeat rewrite app_assoc;
    eauto.

    unfold doRemote_session' in *;
    repeat Auto.ff; 
    repeat rewrite app_assoc;
    eauto.

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
      eapply cvm_errors_deterministic.
      apply Heqp2.
      eassumption.
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
      apply Heqp2.
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
        wrap_ccp_dohi. ff.
        invc Heqp6. invc Heqp11.
        edestruct cvm_errors_deterministic.
        apply H0.
        apply H.
        ff.

      }
    solve_by_inversion.
    +
    assert (errC c = resultC u).
      {
        wrap_ccp_dohi. ff.
        invc Heqp0. invc Heqp7.
        edestruct cvm_errors_deterministic.
        apply H0.
        apply H.
        ff.

      }
    solve_by_inversion.
    +
    assert (errC c1 = resultC u).
      {
        wrap_ccp_dohi. ff.
        invc Heqp6. invc Heqp11.
        edestruct cvm_errors_deterministic.
        apply H0.
        apply H.
        ff.

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
        invc Heqp0. invc Heqp7.
        edestruct cvm_errors_deterministic.
        apply H0.
        apply H.
        ff.
      }
    solve_by_inversion.
    +
    assert (errC c = resultC u).
      {
        wrap_ccp_dohi. ff.
        invc Heqp0. invc Heqp7.
        edestruct cvm_errors_deterministic.
        apply H0.
        apply H.
        ff.
      }
    solve_by_inversion.
    +
    assert (errC c = resultC tt).
      {
        wrap_ccp_dohi. ff.
        invc Heqp0. invc Heqp7.
        edestruct cvm_errors_deterministic.
        apply H0.
        apply H.
        ff.

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
Lemma st_trace_cumul' : forall t m e p v_full v_suffix res i ac,
    build_cvmP t
               {| st_ev := e; st_trace := m; st_pl := p; st_evid := i; st_AM_config := ac |}
               (res) v_full ->
    
    build_cvmP t
                     {| st_ev := e; st_trace := []; st_pl := p; st_evid := i; st_AM_config := ac |}
                     res v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  intros.
  eapply st_trace_cumul''; eauto.
  repeat rewrite app_nil_r.
  eauto.
Defined.


(** * Lemma stating: CVM traces are "cumulative" (or monotonic).  
      Traces are only ever extended--prefixes are maintained. 
      TODO:  rename to st_trace_cumul 
*) 
Lemma suffix_prop : forall t e e' tr tr' p p' i i' ac ac' res,
    build_cvmP t
           {| st_ev := e;
              st_trace := tr;
              st_pl := p;
              st_evid := i; st_AM_config := ac |}
           (res)
           {|
             st_ev := e';
             st_trace := tr';
             st_pl := p';
             st_evid := i'; st_AM_config := ac' |} ->
    exists l, tr' = tr ++ l.
Proof.
  intros.

  do_exists_some_cc t {| st_ev := e; st_trace := []; st_pl := p; st_evid := i; st_AM_config := ac |}.
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
      edestruct cvm_errors_deterministic.
      invc H2.
      invc H.
      apply H1.
      invc H2.
      apply H0.
      ff.

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
         {| st_ev := _; st_trace := ?tr; st_pl := _; st_evid := _ |}
         (_)
         {| st_ev := _; st_trace := ?tr'; st_pl := _; st_evid := _ |}
         (*H2: well_formed_r ?t*) |- _] =>
    assert_new_proof_as_by
      (exists l, tr' = tr ++ l)
      ltac:(eapply suffix_prop; [apply H'])
             name
  end.

(** * Structural Lemma:   Decomposes the CVM trace for the lseq phrase into the appending of the two traces
      computed by its subterms, where each subterm starts from the empty trace.

      Useful for leveraging induction hypotheses in the lseq case of induction that require empty traces in the 
      initial CVM state. *)
Lemma alseq_decomp : forall t1' t2' e e'' p p'' tr i i'' ac ac'',
    build_cvmP
      (lseqc t1' t2')
      {| st_ev := e;
         st_trace := [];
         st_pl := p;
         st_evid := i; st_AM_config := ac |}
      (resultC tt)
      {| st_ev := e'';
         st_trace := tr;
         st_pl := p'';
         st_evid := i''; st_AM_config := ac'' |} ->

    exists e' tr' p' i' ac',
      build_cvmP
        t1'
        {| st_ev := e;
           st_trace := [];
           st_pl := p;
           st_evid := i; st_AM_config := ac |}
        (resultC  tt)
        {| st_ev := e';
           st_trace := tr';
           st_pl := p';
           st_evid := i'; st_AM_config := ac' |} /\
      exists tr'',
        build_cvmP
          t2'
          {| st_ev := e';
             st_trace := [];
             st_pl := p';
             st_evid := i'; st_AM_config := ac' |}
          (resultC tt)
          {| st_ev := e'';
             st_trace := tr'';
             st_pl := p'';
             st_evid := i''; st_AM_config := ac'' |} /\
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
  -
    eassumption.
  -
    do_exists_some_cc t2' {| st_ev := st_ev0; st_trace := []; st_pl := st_pl0; st_evid := st_evid0; st_AM_config := st_AM_config0 |}.
    vmsts.
    repeat ff.
    destruct H0; ff.
    +
    assert (errC c = resultC tt).
    {
      wrap_ccp_dohi. ff.
      invc H1. invc Heqp1.
      edestruct cvm_errors_deterministic.
      apply H.
      apply H0.
      ff.
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
Lemma restl : forall t e e' x tr p p' i i' ac ac' res,
    build_cvmP t
                     {| st_ev := e; st_trace := x; st_pl := p; st_evid := i; st_AM_config := ac|}
                     (res)
                     {| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_evid := i'; st_AM_config := ac' |} ->

    build_cvmP t
                     {| st_ev := e; st_trace := []; st_pl := p; st_evid := i; st_AM_config := ac |}
                     (res)
                     {| st_ev := e'; st_trace := tr; st_pl := p'; st_evid := i'; st_AM_config := ac' |}.
Proof.
  intros.

  do_exists_some_cc t  {| st_ev := e; st_trace := []; st_pl := p; st_evid := i; st_AM_config := ac |}.
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
      assert (Cvm_St.st_trace {| st_ev := st_ev; st_trace := x ++ tr; st_pl := st_pl; st_evid := st_evid; st_AM_config := st_AM_config|} =
              x ++ Cvm_St.st_trace {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl; st_evid := st_evid; st_AM_config := st_AM_config |}).
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
Defined.

Ltac do_restl :=
  match goal with
  | [H: build_cvmP ?t
        {| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_evid := ?i; st_AM_config := ?ac |}
        ?res
        {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_pl := ?p'; st_evid := ?i'; st_AM_config := ?ac' |}
        (*H2: well_formed_r ?t*) |- _] =>
    assert_new_proof_by
      (build_cvmP t
                        {| st_ev := e; st_trace := []; st_pl := p; st_evid := i; st_AM_config := ac|}
                        ?res
                        {| st_ev := e'; st_trace := x; st_pl := p'; st_evid := i'; st_AM_config := ac' |})
      ltac:(eapply restl; [apply H])
  end.




(** * Lemma:  evidence semantics same for annotated and un-annotated terms *)
Lemma eval_aeval': forall t1 p et,
    eval (unanno t1) p et = aeval t1 p et.
Proof.
  induction t1; intros;
    repeat ff;
    repeat jkjke.
Defined.




Axiom cvm_evidence_correct_type : forall t p e e',
  cvm_evidence t p e = e' -> 
  get_et e' = eval t p (get_et e).


(** * Lemma:  parallel CVM threads preserve the reference Evidence Type semantics (eval). *)
Lemma par_evidence_r: forall l p bits bits' et et' t2,
    parallel_vm_thread l (copland_compile t2) p (evc bits et) = evc bits' et' ->
    et' = eval t2 p et.
Proof.
  intros.
  rewrite par_evidence in H.
  assert (get_et (evc bits' et') = eval t2 p (get_et (evc bits et))).
  {
    eapply cvm_evidence_correct_type; eauto.
  }
  ff.
Qed.
         
(** * Axiom about "simulated" parallel semantics of CVM execution:
      Executing a "CLEAR" before a term is the same as executing that term with mt initial evidence.
      TODO:  can we use existing axioms to prove this? *)
Axiom par_evidence_clear: forall l p bits et t2,
    parallel_vm_thread l (lseqc (aspc CLEAR) t2) p (evc bits et) =
    parallel_vm_thread l t2 p mt_evc.

(** * Main Lemma:  CVM execution maintains the Evidence Type reference semantics (eval) for 
      its internal evidence bundle. *)
Lemma cvm_refines_lts_evidence' : forall t tr tr' bits bits' et et' p p' i i' ac ac',
    build_cvmP (copland_compile t)
                     (mk_st (evc bits et) tr p i ac)
                     (resultC tt)
                     (mk_st (evc bits' et') tr' p' i' ac') ->
    et' = (Term_Defs.eval t p et).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    rewrite <- ccp_iff_cc in *.

    Auto.ff.
    destruct a;
      (try dd; eauto); try (repeat Auto.ff).

      

  - (* at case *)
    rewrite <- ccp_iff_cc in *.
    dd.
    repeat Auto.ff.
    unfold doRemote_session' in *; 
    repeat Auto.ff.

  - (* alseq case *)
    do_suffix blah.
    destruct_conjs.
    subst.

    edestruct alseq_decomp.
    eapply restl.
    eassumption.
    destruct_conjs.

    wrap_ccp.
    
    destruct x.
    repeat jkjke'.
    
  - (* abseq case *)
    wrap_ccp.



    destruct s0; destruct s1; Auto.ff; 
      wrap_ccp;
      repeat Auto.ff;
      repeat find_apply_hyp_hyp; try congruence.
      
   - (* abpar case *)

    destruct s; repeat Auto.ff.

    +
      wrap_ccp.
      Auto.ff.
      find_apply_hyp_hyp.

      assert (e0 = eval t2 p' et).
      {
        eapply par_evidence_r.
        eassumption.
      }
      congruence.
      
    +
      wrap_ccp.
      Auto.ff.
      find_apply_hyp_hyp.

      assert (e0 = eval t2 p' mt).
      {
        rewrite par_evidence_clear in *.
        eapply par_evidence_r.
        eassumption.
      }
      
      congruence.
    +
      wrap_ccp.
      Auto.ff.
      find_apply_hyp_hyp.

      assert (e0 = eval t2 p' et).
      {
        eapply par_evidence_r.
        eassumption.
      }
      congruence.
    +
      wrap_ccp.
      Auto.ff.
      find_apply_hyp_hyp.

      assert (e0 = eval t2 p' mt).
      {
        rewrite par_evidence_clear in *.

        eapply par_evidence_r.
        eassumption.
      }
      congruence.
Qed.

(** * Propositional version of CVM Evidence Type preservation. *)
Lemma cvm_refines_lts_evidence :
  forall t t' tr tr' bits bits' et et' p p' i i' ac ac',
    term_to_coreP t t' ->
    build_cvmP t'
                     (mk_st (evc bits et) tr p i ac)
                     (resultC tt)
                     (mk_st (evc bits' et') tr' p' i' ac') ->
    et' = (Term_Defs.eval t p et).
Proof.
  intros.
  invc H.
  eapply cvm_refines_lts_evidence'.
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
Defined.

(*
Lemma anno_parPloc_redo: forall t pt loc loc',
    anno_par t loc = (loc', pt) ->
    anno_parPloc pt t loc.
Proof.
  intros.
  econstructor.
  jkjke.
Defined.
 *)
Lemma anno_parPloc_redo: forall t pt loc loc',
    anno_par_list' t loc = Some (loc', pt) ->
    anno_parPloc pt t loc.
Proof.
  intros.
  econstructor.
  jkjke.
Defined.

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
