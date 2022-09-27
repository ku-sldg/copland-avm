Require Import ConcreteEvidence AutoApp Auto Helpers_CvmSemantics Term_Defs Anno_Term_Defs Cvm_St Cvm_Impl Defs StructTactics OptMonad_Coq IO_Stubs Evidence_Bundlers. (* Cvm_Monad. *)

Require Import List.
Import ListNotations.

Require Import Lia Coq.Program.Tactics.



Inductive AppResultC: Set :=
| mtc_app: AppResultC
| nnc_app: N_ID -> BS -> AppResultC
| ggc_app: Plc -> ASP_PARAMS -> BS -> AppResultC -> AppResultC
| hhc_app: Plc -> ASP_PARAMS -> BS -> AppResultC -> (* Evidence -> *) AppResultC
| eec_app: Plc -> ASP_PARAMS -> BS -> AppResultC ->(* Evidence -> *) AppResultC
| ssc_app: AppResultC -> AppResultC -> AppResultC.



Definition peel_bs (ls:RawEv) : Opt (BS * RawEv) :=
  match ls with
  | bs :: ls' => ret (bs, ls')
  | _ => failm
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
  (* | kkc _ _ _ => [] *)
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
      | [] => Some mtc
      | _ => None
      end
    | KEEP => None
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
    (et = mt \/ exists p ps et', et = uu p KILL ps et').
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
         -
           eauto.
           (*
           
                      right.
                      eauto. *)
                                 
Defined.

Ltac do_inv_recon_mt :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) mtc

     |- _] =>
    assert_new_proof_by (et = mt \/ exists p ps et', et = uu p KILL ps et') ltac:(eapply inv_recon_mt; apply H)
  end;
  door;
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
    et = nn n /\ ls = [n0].
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; destruct ls; try solve_by_inversion.
Defined.

Ltac do_inv_recon_nn :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (nnc ?n ?nval)

     |- _] =>
    assert_new_proof_by (et = nn n /\ ls = [nval]) ltac:(eapply inv_recon_nn; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_gg: forall p ps ls et n ec,
    reconstruct_evP (evc ls et) (ggc p ps n ec) ->
    (exists ls' et', et = uu p EXTD ps et' /\
                ls = n :: ls').
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; try solve_by_inversion.

  repeat eexists.
  destruct ls; ff.
Defined.

Ltac do_inv_recon_gg :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (ggc ?p ?ps ?n _)

     |- _] =>
    assert_new_proof_by (exists ls' et', et = uu p EXTD ps et' /\
                                    ls = n :: ls')
                        ltac:(eapply inv_recon_gg; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_hh: forall p ps ls et n et',
    reconstruct_evP (evc ls et) (hhc p ps n et') ->
    (et = uu p COMP ps et' ) /\ ls = [n].
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; destruct ls; try solve_by_inversion.
Defined.

Ltac do_inv_recon_hh :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (hhc ?p ?ps ?hval ?et')

     |- _] =>
    assert_new_proof_by (et = uu p COMP ps et' /\ ls = [hval])
                        ltac:(eapply inv_recon_hh; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_ee: forall p ps ls et (*et'*) n ec',
    reconstruct_evP (evc ls et) (eec p ps n (*et'*) ec') ->
    (* (exists et', et = uu p ENCR ps et' ) /\ ls = [n]. *)
    (exists et', et = uu p ENCR ps et' /\ ls = [n]).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; destruct ls; try solve_by_inversion.
                               -
                               ff.
                               repeat eexists.
                               ff.
                               
Defined.

Ltac do_inv_recon_ee :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (eec ?p ?ps ?hval (*_*) _)

     |- _] =>
    assert_new_proof_by (exists et', et = uu p ENCR ps et' /\ ls = [hval])
                        ltac:(eapply inv_recon_ee; apply H)
  end;
  destruct_conjs;
  subst.

(*
Lemma inv_recon_kk: forall p ps ls et et',
    reconstruct_evP (evc ls et) (kkc p ps et') ->
    (et = uu p KILL ps et' ) /\ ls = [].
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff; destruct ls; try solve_by_inversion.
Defined.

Ltac do_inv_recon_kk :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (kkc ?p ?ps ?et')

     |- _] =>
    assert_new_proof_by (et = uu p KILL ps et' /\ ls = [])
                        ltac:(eapply inv_recon_kk; apply H)
  end;
  destruct_conjs;
  subst.
*)

Lemma inv_recon_ss: forall ls et ec1 ec2,
    reconstruct_evP (evc ls et) (ssc ec1 ec2) ->
    (exists et1 et2, et = ss et1 et2).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; try solve_by_inversion.
  eauto.
Defined.

Ltac do_inv_recon_ss :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) (ssc _ _)

     |- _] =>
    assert_new_proof_by (exists et1 et2, et = ss et1 et2)
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
  (* try do_inv_recon_kk; *)
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
          (ssc ?ec1 ?ec2)
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
    repeat ff;
    try rewrite fold_recev in *;
    do_wrap_reconP
  end.


(*
TODO: try this again after appraisal lemmas settled 
*)

Lemma etfun_reconstruct: forall e e0 e1,
    reconstruct_evP (evc e0 e1) e ->
    e1 = et_fun e.
Proof.
  intros.
  generalizeEverythingElse e1.

  (*
  induction e1; intros e e0 H;
    do_inv_recon;
    ff.
  -
    invc H.
    repeat ff;
      try (unfold OptMonad_Coq.bind in * );
           repeat ff.
  -
    invc H;
      ff;
      try (unfold OptMonad_Coq.bind in * );
      destruct f;    try (unfold OptMonad_Coq.bind in * );
      try (ff; tauto).
    +
      ff.
      assert (e1 = et_fun e2).
      eapply IHe1.
      econstructor; eauto.
      subst.
      tauto.
    +
      ff.
      
      
      
      
      
      eauto.
      tauto.
    ff.
    repeat ff;
      try (unfold OptMonad_Coq.bind in * );
           repeat ff.
           +
             assert (e1 = et_fun e2).
             eapply IHe1.
             econstructor; eauto.
             subst.
             tauto.
           +

             Locate et_fun.
             Locate reconstruct_ev.
             
 *)
             
             
                      
   


  
  induction e1; intros e e0 H;
    try (
    do_inv_recon;
    ff;
    invc H;
    repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff;
    rewrite fold_recev in *;
    do_wrap_reconP;
    repeat jkjke).
  -
    destruct f; ff.
    + (* COMP case *)
      invc H.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
    + (* ENCR case *)
      (*
      Print et_fun.
      Print do_inv_recon_ee.
      Print do_inv_recon_ee.
      Locate reconstruct_ev.
       *)
      
      invc H.
      unfold reconstruct_ev in *.
      unfold reconstruct_ev' in *.
      unfold OptMonad_Coq.bind in *.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
    + (* EXTD case *)
      invc H.
      ff.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
      assert (e1 = et_fun e2).
      eapply IHe1.
      econstructor.
      ff.
      congruence.
    + (* KILL case *)
      invc H.
      Print et_fun.
      ff.
      ff.
      

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
    invc H.
    repeat ff.
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

    (*
  -
    do_inv_recon.
    ff. 
     *)
    
    
    
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
  -
    do_inv_recon.
    dd.
    invc H.
    dd.
    ff.
    econstructor. tauto.
    invc H.
    repeat ff.
    econstructor. tauto.
  -
    do_inv_recon.
    invc H.
    dd.
    econstructor; tauto.
  -
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

  -
    do_inv_recon.
    invc H.
    dd.
    econstructor; tauto.
  -
    do_inv_recon.
    invc H.
    dd.
    econstructor; tauto.
    (*
  -
    do_inv_recon.
    invc H.
    econstructor; tauto.   
     *)
    
    
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








(*


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

  -
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


    
     -
       
       
       
    repeat ff;
    (unfold OptMonad_Coq.bind in * );
     repeat ff; eauto.
     +
       inv_wfec.
       ff.
       assert (exists v, r = [v]).
       {
         destruct r; ff.
         destruct r; ff. }
       destruct_conjs. subst.
       ff.
     +
       inv_wfec.
       assert (r = []).
       {
         destruct r; ff. }
       subst.
       ff.
     +
       inv_wfec.
       ff.
       assert (exists v, r = [v]).
       { destruct r; ff.
       destruct r; ff. }
       destruct_conjs.
       subst.
       ff.
     +
       inv_wfec.
       ff.
       assert (exists v, r = [v]).
       { destruct r; ff. }
       destruct_conjs.
       subst.
       ff.
     +
       inv_wfec.
       ff.
       destruct r; ff.
       unfold OptMonad_Coq.ret in *.
       ff.
       assert (exists ee, Some ee = reconstruct_ev' r0 e).
       { eapply IHe.
         econstructor. eassumption. }
       destruct_conjs.
       rewrite <- H1 in *.
       solve_by_inversion.
     +
       inv_wfec.
       ff.
       assert (r = []).
       {
         destruct r; ff.
       }
       subst.
       ff.
     +
       inv_wfec.
       ff.
       
       
       
       
       
      (* 
       
       
     
     +
       inv_wfec.
       ff.
       eapply peel_fact.
     eauto.
     +
       inv_wfec.
       assert (wf_ec (evc r0 e)).
       {
         eapply peel_fact; eauto.
       }
       ff.
     +
       destruct r; try solve_by_inversion.
       ff.
       invc H.
       ff.

         -
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
       *)
     +
       inv_wfec.
       ff.
       edestruct IHe.
       econstructor.
       eassumption.
       asdf
       
       
         
       
    
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
*)

Definition spc_ev (sp:SP) (e:EvidenceC) : EvidenceC :=
  match sp with
  | ALL => e
  | NONE => mtc
  end.

(*
TODO: try this again after appraisal lemmas settled 
*)

Definition cvm_evidence_denote_asp (a:ASP) (p:Plc) (e:EvidenceC) (x:Event_ID): EvidenceC :=
  match a with
  | NULL => mtc
  | CPY => e
  | ASPC sp fwd params =>
    match fwd with
    | COMP => hhc p params (do_asp params (encodeEv (spc_ev sp e)) p x) (sp_ev sp (et_fun e))
    | EXTD => ggc p params (do_asp params (encodeEv (spc_ev sp e)) p x) (spc_ev sp e)
    | ENCR => eec p params (do_asp params (encodeEv (spc_ev sp e)) p x) (sp_ev sp (et_fun e)) (* (spc_ev sp e) (sp_ev sp (et_fun e)) *)
    | KEEP => e
    | KILL => mtc (* kkc p params (sp_ev sp (et_fun e)) *)
    end
  | SIG => ggc p sig_params (do_asp sig_params (encodeEv e) p x) e
  | HSH => hhc p hsh_params (do_asp hsh_params (encodeEv e) p x) (et_fun e)
  | ENC q => eec p (enc_params q) (do_asp (enc_params q) (encodeEv e) p x) (et_fun e) (* e *) (* (et_fun e) *)
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

(*
TODO: try this lemma again after getting appraisal Lemmas settled 
*)


(** * Lemma:  relating reconstructed CVM EvC bundles via the EvidenceC evidence denotation. *)
Lemma cvm_raw_evidence_denote_fact :
  forall t annt t' tr tr' bits bits' et et' p p' i i' ec ec',
    build_cvmP t
                     (mk_st (evc bits et) tr p i)
                     (Some tt)
                     (mk_st (evc bits' et') tr' p' i') ->
    term_to_coreP t' t ->
    annoP_indexed annt t' i i' ->

    reconstruct_evP (evc bits et) ec ->
    reconstruct_evP (evc bits' et') ec' ->

    cvm_evidence_denote annt p ec = ec'.
Proof.
  intros.
  generalizeEverythingElse t'.
  induction t'; intros.
  -
    wrap_ccp_anno.
    
    destruct a; wrap_ccp_anno.
    + (* NULL case *)
      ff.
      invc H3.
      dd.
      tauto.   
    + (* CPY case *)
      dd.
      eapply reconP_determ; eauto.

    +
      ff.
      ++ (* COMP case *)
        wrap_ccp_anno.
        invc H3.
        ff.
        assert (bits = encodeEv ec).
        {
          symmetry.
          invc H2.
          eapply recon_encodeEv.
          econstructor.
          eassumption.
        }
        subst.

        assert (et_fun ec = et).
      {
        symmetry.
        eapply etfun_reconstruct.
        eassumption.
      }
      congruence.
      ++
        wrap_ccp_anno.
        invc H3.
        ff.
      ++
        wrap_ccp_anno.
        invc H3.
        ff.
         assert (bits = encodeEv ec).
        {
          symmetry.
          invc H2.
          eapply recon_encodeEv.
          econstructor.
          eassumption.
        }
        subst.

        assert (et_fun ec = et).
      {
        symmetry.
        eapply etfun_reconstruct.
        eassumption.
      }
      congruence.

      ++
        wrap_ccp_anno.
        invc H3.
        ff.
        
      ++
        wrap_ccp_anno.
        invc H3.
        ff.
        invc H2.
        ff.
        jkjke'.
        ff.
        assert (bits = encodeEv ec).
        {
          symmetry.
          eapply recon_encodeEv.
          econstructor.
          eassumption.
        }
        subst.
        tauto.
      ++
        wrap_ccp_anno.
        invc H3.
        ff.
      ++
        wrap_ccp_anno.
        invc H3.
        ff.
        assert (et_fun ec = et).
        {
          symmetry.
        eapply etfun_reconstruct.
        eassumption.
        }
        congruence.
      ++
        wrap_ccp_anno.
        invc H3.
        ff.
        
        
        
    +
      dd.
      invc H3; invc H2.
      dd.
      jkjke'.
      dd.
      Search (encodeEv _ = _).
      rewrite recon_encodeEv with (bits:=bits) (et:=et).
      tauto.
      econstructor; eassumption.

    +
      wrap_ccp.
      invc H3; invc H2.
      dd.
      assert (et_fun ec = et).
      {
        symmetry.
        eapply etfun_reconstruct.
        econstructor.
        eassumption.
      }

      rewrite recon_encodeEv  with (bits:=bits) (et:=et).
      congruence.
      econstructor; eassumption.
    +
      wrap_ccp.
      invc H3; invc H2.
      dd.
      assert (et_fun ec = et).
      {
        symmetry.
        eapply etfun_reconstruct.
        econstructor.
        eassumption.
      }

      rewrite recon_encodeEv  with (bits:=bits) (et:=et).
      congruence.
      econstructor; eassumption.
      

  -
    wrap_ccp_anno.
    ff.
    wrap_ccp_anno.

    do_assert_remote (copland_compile t') (evc bits et) p (S i).

    assert (evc bits' et' = cvm_evidence_core (copland_compile t') p (evc bits et)). {

      rewrite at_evidence in *.
      unfold cvm_evidence in *.
      rewrite H5.
      tauto.
    }

    eapply IHt'.
    econstructor.
    rewrite <- H7 in H4.
    eassumption.
    econstructor; eauto.
    assert (n = (S i + event_id_span (copland_compile t'))).
    {
      wrap_ccp_anno.
      eapply anno_span_cvm.
      eassumption.
      2: { eassumption. }
      econstructor; eauto.
    }
    subst.
    eassumption.
    eassumption.
    eassumption.

  - (* lseq case *)
    wrap_ccp_anno.
    ff.
    wrap_ccp_anno.
    ff.

    assert (n = st_evid0).
    {
      eapply anno_span_cvm.
      eassumption.
      2: { eassumption. }
      econstructor; eauto.
    }
    
    dd.

    destruct st_ev0.

    assert (wf_ec (evc bits et)).
    {
      eapply wfec_recon; eauto.
    }

    do_wfec_preserved.

    do_somerecons.
    
    assert ((cvm_evidence_denote a p ec) = H8).
    {
      eapply IHt'1.
      
      eassumption.
      econstructor; eauto.
      eassumption.

      eassumption.
      eassumption.
    }
    
    subst.
    eapply IHt'2.
    apply Heqp1.
    econstructor; eauto.
    eassumption.
    eauto.
    eauto.
    
  - (* bseq case *)
    wrap_ccp_anno;
      ff;
      wrap_ccp_anno.
    
    +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      assert (reconstruct_evP (evc r e) e1).
      {
        econstructor.
        ff.
      }

    assert (reconstruct_evP (evc r0 e0) e2).
    {
      econstructor.
      ff.
    }

    assert (i + 1 = S i) as H9 by lia.
    rewrite H9 in *; clear H9.

    assert (n = st_evid1).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp2. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a st_pl1 ec = e1).
    {
      eapply IHt'1.
      apply Heqp2.
      econstructor; eauto.
      

      eassumption.
      eassumption.
      eassumption.
    }

     assert (cvm_evidence_denote a0 st_pl1 ec = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      eassumption.
      eassumption.
    }
    
      
    dd.
    congruence.
    +
            do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      assert (reconstruct_evP (evc r e) e1).
      {
        econstructor.
        ff.
      }

    assert (reconstruct_evP (evc r0 e0) e2).
    {
      econstructor.
      ff.
    }

    assert (i + 1 = S i) as H9 by lia.
    rewrite H9 in *; clear H9.

    assert (n = st_evid1).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp2. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a st_pl1 ec = e1).
    {
      eapply IHt'1.
      apply Heqp2.
      econstructor; eauto.
      

      eassumption.
      eassumption.
      eassumption.
    }

     assert (cvm_evidence_denote a0 st_pl1 mtc = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      econstructor. ff.
      eassumption.
    }
    
      
    dd.
    congruence.


    +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec mt_evc).
      {
        econstructor.
        ff.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      assert (reconstruct_evP (evc r e) e1).
      {
        econstructor.
        ff.
      }

    assert (reconstruct_evP (evc r0 e0) e2).
    {
      econstructor.
      ff.
    }

    assert (i + 1 = S i) as H9 by lia.
    rewrite H9 in *; clear H9.

    assert (n = st_evid1).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp8. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a st_pl1 mtc = e1).
    {
      eapply IHt'1.
      apply Heqp8.
      econstructor; eauto.
      

      eassumption.
      econstructor; eauto.
      eassumption.
    }

     assert (cvm_evidence_denote a0 st_pl1 ec = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      econstructor. ff.
      eassumption.
    }
    
      
    dd.
    congruence.
    


        +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec mt_evc).
      {
        econstructor.
        ff.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      assert (reconstruct_evP (evc r e) e1).
      {
        econstructor.
        ff.
      }

    assert (reconstruct_evP (evc r0 e0) e2).
    {
      econstructor.
      ff.
    }

    assert (i + 1 = S i) as H9 by lia.
    rewrite H9 in *; clear H9.

    assert (n = st_evid1).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp9. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a st_pl1 mtc = e1).
    {
      eapply IHt'1.
      apply Heqp9.
      econstructor; eauto.
      

      eassumption.
      econstructor; eauto.
      eassumption.
    }

     assert (cvm_evidence_denote a0 st_pl1 mtc = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      econstructor. ff.
      eassumption.
    }
    
      
    dd.
    congruence.



  - (* bpar case *)
    wrap_ccp_anno;
      ff;
      wrap_ccp_anno.
    
    +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      assert (reconstruct_evP (evc r e) e1).
      {
        econstructor.
        ff.
      }

    assert (reconstruct_evP (evc r0 e0) e2).
    {
      econstructor.
      ff.
    }

    assert (i + 1 = S i) as H9 by lia.
    rewrite H9 in *; clear H9.

    assert (n = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp2. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a p ec = e1).
    {
      eapply IHt'1.
      apply Heqp2.
      econstructor; eauto.
      

      eassumption.
      eassumption.
      eassumption.
    }

    do_assert_remote (copland_compile t'2) (evc bits et) p (st_evid).

    wrap_ccp_anno.

    rewrite par_evidence in *.

    unfold cvm_evidence in *.
    rewrite Heqe0 in *.

    assert (cvm_evidence_denote a0 p ec = e2).
    {
      eapply IHt'2.
      apply H9.
      econstructor; eauto.
      assert (n0 = st_evid + event_id_span (copland_compile t'2)).
      {
        eapply anno_span_cvm.
        apply Heqp1.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      eassumption.
      eassumption.
    }
    
      
    dd.
    congruence.


    +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      assert (reconstruct_evP (evc r e) e1).
      {
        econstructor.
        ff.
      }

    assert (reconstruct_evP (evc r0 e0) e2).
    {
      econstructor.
      ff.
    }

    assert (i + 1 = S i) as H9 by lia.
    rewrite H9 in *; clear H9.

    assert (n = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp2. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a p ec = e1).
    {
      eapply IHt'1.
      apply Heqp2.
      econstructor; eauto.
      

      eassumption.
      eassumption.
      eassumption.
    }

     do_assert_remote (copland_compile t'2) mt_evc p (st_evid).

    wrap_ccp_anno.

    rewrite <- ev_cvm_mtc in *.

    rewrite par_evidence in *.

    unfold cvm_evidence in *.
    rewrite Heqe0 in *.


     assert (cvm_evidence_denote a0 p mtc = e2).
    {
      eapply IHt'2.
      apply H9.
      econstructor; eauto.
      assert (n0 = st_evid + event_id_span (copland_compile t'2)).
      {
        eapply anno_span_cvm.
        apply Heqp1.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      econstructor; eauto.
      eassumption.
    }
    
      
    dd.
    congruence.


    +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec mt_evc).
      {
        econstructor.
        ff.
      }

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      assert (reconstruct_evP (evc r e) e1).
      {
        econstructor.
        ff.
      }

    assert (reconstruct_evP (evc r0 e0) e2).
    {
      econstructor.
      ff.
    }

    assert (i + 1 = S i) as H9 by lia.
    rewrite H9 in *; clear H9.

    assert (n = st_evid).
      {
        eapply anno_span_cvm.
        apply Heqp0.
        2: { 
             apply Heqp3. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a p mtc = e1).
    {
      eapply IHt'1.
      apply Heqp3.
      econstructor; eauto.
      

      eassumption.
      econstructor; eauto.
      eassumption.
    }

     do_assert_remote (copland_compile t'2) (evc bits et) p (st_evid).

    wrap_ccp_anno.

    rewrite par_evidence in *.

    unfold cvm_evidence in *.
    rewrite Heqe0 in *.


     assert (cvm_evidence_denote a0 p ec = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid + event_id_span (copland_compile t'2)).
      {
        eapply anno_span_cvm.
        apply Heqp1.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      eassumption.
      eassumption.
    }
    
      
    dd.
    congruence.



        +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec mt_evc).
      {
        econstructor.
        ff.
      }

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      assert (reconstruct_evP (evc r e) e1).
      {
        econstructor.
        ff.
      }

    assert (reconstruct_evP (evc r0 e0) e2).
    {
      econstructor.
      ff.
    }

    assert (i + 1 = S i) as H9 by lia.
    rewrite H9 in *; clear H9.

    assert (n = st_evid).
      {
        eapply anno_span_cvm.
        apply Heqp0.
        2: { 
             apply Heqp3. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a p mtc = e1).
    {
      eapply IHt'1.
      apply Heqp3.
      econstructor; eauto.
      

      eassumption.
      econstructor; eauto.
      eassumption.
    }

     do_assert_remote (copland_compile t'2) mt_evc p (st_evid).

    wrap_ccp_anno.

    rewrite <- ev_cvm_mtc in *.

    rewrite par_evidence in *.

    unfold cvm_evidence in *.
    rewrite Heqe0 in *.


     assert (cvm_evidence_denote a0 p mtc = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid + event_id_span (copland_compile t'2)).
      {
        eapply anno_span_cvm.
        apply Heqp1.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      econstructor; eauto.
      eassumption.
    }
    
      
    dd.
    congruence.
Qed.

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
*)



































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
