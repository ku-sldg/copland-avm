Require Import GenStMonad MonadVM MonadAM ConcreteEvidence.
Require Import StAM VM_IO_Axioms Maps VmSemantics Event_system Term_system.

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.


Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p i args, evidenceEvent (umeas n p i args)
(*| sev: forall n p, evidenceEvent (sign n p)
| hev: forall n p, evidenceEvent (hash n p)*) .

(*
Definition measEvent (t:AnnoTerm) (p:Plc) (ev:Ev) : Prop :=
  let es := ev_sys t p in
  ev_in ev es /\ evidenceEvent ev.
 *)

Definition measEvent (t:AnnoTerm) (p:Plc) (ev:Ev) : Prop :=
  events t p ev /\ evidenceEvent ev.

Check bound_to.

Inductive appEvent : Ev -> AM_St -> Ev -> Prop :=
| aeu : forall p q i i' n m args nmap nid amap,
    bound_to amap (p,i) i' ->
    appEvent (umeas n p i args) (mkAM_St nmap nid amap) (umeas m q i' (args ++ [n])).

Definition am_get_app_asp (p:Plc) (i:ASP_ID) : AM ASP_ID :=
  m <- gets st_aspmap ;;
  let maybeId := map_get m (p,i) in
  match maybeId with
  | Some i' => ret i'
  | None => failm
  end.

Fixpoint gen_appraisal_comp (e:EvidenceC) (et:Evidence) : AM (VM unit) :=
  match e with
  | mtc =>
    match et with
    | mt => ret (ret tt)
    | _ => failm
    end   
  | uuc i bs e' =>
    match et with 
    | uu i_t args_t p e'_t =>
      app_id <- am_get_app_asp p i_t ;;
      let c1 :=
          e <- invokeUSM 0 app_id p (args_t ++ [bs]) ;;  (* TODO: is bogus event id ok here? *)
          put_ev e in
      c2 <- gen_appraisal_comp e' e'_t ;;
      ret (c1 ;; c2)
    | _ => failm
    end
  | ggc bs e' =>
    match et with
    | gg p e'_t =>
      ret (ret tt)
    | _ => failm
    end
  | hhc bs e' =>
    match et with
    | hh p e'_t =>
      ret (ret tt)
    | _ => failm
    end
  | nnc nid bs e' =>
    match et with
    | nn nid_t e'_t =>
      ret (ret tt)
    | _ => failm
    end
  | ssc e1 e2 =>
    match et with
    | ss e1_t e2_t => 
      c1 <- gen_appraisal_comp e1 e1_t ;;
          c2 <- gen_appraisal_comp e2 e2_t ;;
          ret (c1 ;; c2)
    | _ => failm
    end
  | ppc e1 e2 =>
    match et with
    | pp e1_t e2_t => 
      c1 <- gen_appraisal_comp e1 e1_t ;;
          c2 <- gen_appraisal_comp e2 e2_t ;;
          ret (c1 ;; c2)
    | _ => failm
    end
  end.

Check build_comp.
Check runSt.
Check run_vm.
Check eval.

(*
Definition run_vm_fresh (t:AnnoTerm) :=
  run_vm t empty_vmst.
Check run_vm_fresh.


Definition run_vm_fresh_t (t:Term) :=
  run_vm (annotated t) empty_vmst.
Check run_vm_fresh_t.
*)

Definition build_app_comp (t: AnnoTerm) (p:Plc) (st:vm_st) : AM (VM unit) :=
  let vm_res_st := run_vm t st in
  let evc := st_ev vm_res_st in
  let evt := eval (unanno t) p mt in
  app_comp <- gen_appraisal_comp evc evt ;;
  ret (app_comp).

Definition build_app_comp_t (t:Term) (p:Plc) (st:vm_st) : AM (VM unit) :=
  build_app_comp (annotated t) p st.

Definition exec_app_comp (t: AnnoTerm) (p:Plc) (st:vm_st) : AM vm_st :=
  app_comp <- build_app_comp t p st ;;
  let app_res := runSt empty_vmst app_comp in
  ret ((snd (app_res))).

Definition exec_app_comp_t (t: Term) (p:Plc) (p':nat) (st:vm_st) : AM vm_st :=
  exec_app_comp (snd (anno t p')) p st.

Definition run_app_comp_ev (t: AnnoTerm) (p:Plc) (st:vm_st) : AM EvidenceC :=
  app_st <- exec_app_comp t p st ;;
  ret (st_ev app_st).

Definition run_app_comp_ev_t (t: Term) (p:Plc) (st:vm_st) : AM EvidenceC :=
  run_app_comp_ev (annotated t) p st.
  

(*
Definition at1 := (asp (ASPC 11 [])).
Definition at2 := (asp (ASPC 22 [])).
Definition aterm := bseq (NONE,NONE) at1 at2.


Definition aterm_ev_comp := run_app_comp_ev_t aterm 0.

Definition ast :=
  mkAM_St [] 0 [((0,11),34); ((0,22),45)].

Definition aterm_res : ((option EvidenceC) * AM_St) := runSt ast aterm_ev_comp.
Compute aterm_res.

Definition aterm_st : AM vm_st := exec_app_comp_t aterm 0 0.
Compute (runSt ast aterm_st).

Definition aet := eval aterm 0 mt.
Compute aet.

Definition evc_st := (run_vm_fresh_t aterm).
Compute evc_st.
Definition evc := st_ev evc_st.
Compute evc.
*)

Definition fromOpt{A:Type} (o:option A) (a:A) : A :=
  match o with
  | Some t => t
  | None => a
  end.

Inductive evMapped : Evidence -> asp_map -> Prop :=
| evMappedMt : forall m, evMapped mt m
| evMappedU : forall p i args e' m,
    evMapped e' m -> 
    (exists j, bound_to m (p,i) j) -> 
    evMapped (uu i args p e') m
| evMappedG : forall e' m p,
    evMapped e' m ->
    evMapped (gg p e') m
| evMappedH : forall e' m p,
    evMapped e' m ->
    evMapped (hh p e') m
| evMappedN : forall e' m nid,
    evMapped e' m ->
    evMapped (nn nid e') m
| evMappedS : forall e1 e2 m,
    evMapped e1 m ->
    evMapped e2 m ->
    evMapped (ss e1 e2) m
| evMappedP : forall e1 e2 m,
    evMapped e1 m ->
    evMapped e2 m ->
    evMapped (pp e1 e2) m.


(*
Definition allMapped (t:AnnoTerm) (p:Plc) (st: AM_St) : Prop :=
  forall aspmap n q i l ,
    measEvent t p (umeas n q i l) -> (* TODO: generalize once measEvent is richer *)
    aspmap = st_aspmap st ->
    exists j,
      bound_to aspmap (q,i) j.
*)

Lemma atgentrace : forall t p e n v1 v a b am_nonceMap am_nonceId st_aspmap ev,
    gen_appraisal_comp
      (st_ev (snd (build_comp (annotated t) empty_vmst))) (eval t p e)
      {| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} = (Some v1, a) ->
    gen_appraisal_comp
      (st_ev (snd (build_comp (annotated (att n t)) empty_vmst))) (eval (att n t) p e)
      {| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} = (Some v, b) ->
    In ev (st_trace (snd (v1 empty_vmst))) ->
    In ev (st_trace (snd (v empty_vmst))).
Proof.
Admitted.

Lemma fifi : forall t p e n v a b am_nonceMap am_nonceId st_aspmap,
    gen_appraisal_comp
      (st_ev (snd (build_comp (annotated t) empty_vmst))) (eval t p e)
      {| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} = (Some v, a) ->
    gen_appraisal_comp
      (st_ev (snd (build_comp (annotated (att n t)) empty_vmst))) (eval t n mt)
      {| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} = (None, b) ->
    False.
Proof.
Admitted.



Lemma measEventAt' : forall t n p q ev,
    measEvent (snd (anno (att n t) q)) p ev ->
    measEvent (snd (anno t (S q))) n ev.
Proof.

  induction t; intros.
  - inv H.
    invc H1.
    destruct a;
      try (inv H; inv H1; solve_by_inversion).
    +
      simpl in *.
      invc H0.
      invc H6.
      invc H.
      invc H0.
      simpl.
      econstructor.
      eauto.
      eauto.
  -
    simpl in *.
    repeat break_let.
    simpl in *.
    repeat find_inversion.
    simpl in *.
    invc H.
    invc H1.
    repeat find_inversion.
    invc H0.
    invc H5.
    econstructor.
    +
    econstructor.
    assumption.
    +
      econstructor.
  - simpl in *.
    repeat break_let.
    simpl in *.
    repeat find_inversion.
    simpl in *.
    invc H.
    invc H1.
    repeat find_inversion.
    invc H0.
    invc H5.
    econstructor.
    econstructor.
    eassumption.
    econstructor.
    econstructor.
    apply evtslseqr.
    assumption.
    econstructor.
  - simpl in *.
    repeat break_let.
    simpl in *.
    repeat find_inversion.
    simpl in *.
    invc H.
    invc H1.
    repeat find_inversion.
    invc H0.
    invc H5.
    econstructor.
    econstructor.
    eassumption.
    econstructor.
    econstructor.
    apply evtsbseqr.
    assumption.
    econstructor.
  - simpl in *.
    repeat break_let.
    simpl in *.
    repeat find_inversion.
    simpl in *.
    invc H.
    invc H1.
    repeat find_inversion.
    invc H0.
    invc H5.
    econstructor.
    econstructor.
    eassumption.
    econstructor.
    econstructor.
    apply evtsbparr.
    assumption.
    econstructor.
Defined.

(*
Lemma measEventAt : forall t n p ev,
    measEvent (annotated (att n t)) p ev ->
    measEvent (annotated t) n ev.
Proof.
  intros.
  eapply measEventAt'.
  eapply measEventAt'; eauto.
Defined.
*)


Lemma announ' : forall t p,
    unanno (snd (anno t p)) = t.
Proof.
  induction t; intros; unfold annotated; simpl.
  -
    auto.
  - repeat break_let. simpl.
    edestruct IHt with (p:=(S p)).
    rewrite Heqp0.
    simpl.
    reflexivity.
  - repeat break_let.
    simpl.
    edestruct IHt1 with (p:=p).
    rewrite Heqp0. simpl.
    edestruct IHt2 with (p:=n).
    rewrite Heqp1. simpl. eauto.
  - repeat break_let.
    simpl.
    edestruct IHt1 with (p:=S p).
    rewrite Heqp0. simpl.
    edestruct IHt2 with (p:=n).
    rewrite Heqp1. simpl. eauto.
  - repeat break_let.
    simpl.
    edestruct IHt1 with (p:=S p).
    rewrite Heqp0. simpl.
    edestruct IHt2 with (p:=n).
    rewrite Heqp1. simpl. eauto.
Defined.

Lemma announ : forall t,
    unanno (annotated t) = t.
Proof.
  intros.
  eapply announ'; eauto.
Defined.

Lemma allMappedAt : forall r n a p st,
    allMapped (aatt r n a) p st ->
    allMapped a n st.
Proof.
  intros.
  unfold allMapped.
  intros; subst.
  invc H0.
  unfold allMapped in H.
  assert (measEvent a n (umeas n0 q i l)).
  econstructor; eauto.

  edestruct H.
  econstructor.
  econstructor.
  eassumption.
  econstructor.
  reflexivity.
  eauto.
Defined.

Check exec_app_comp_t.
Check runSt.

Require Import MonadVMFacts.
Check Term.eval.
Check gen_appraisal_comp.

Lemma app_some' : forall t t' p' e' tr p'' o a_st (app_comp:AM (VM unit)) app_comp_res,
  t = snd (anno t' p') ->
  build_comp t {| st_ev:=mtc; st_trace:=[]; st_pl:=0; st_store:=[]|} =
  (Some tt, {| st_ev:=e'; st_trace:=tr; st_pl:=p''; st_store:=o|}) ->
  allMapped t 0 a_st ->
  app_comp = gen_appraisal_comp e' (Term.eval t' 0 mt) ->
  app_comp_res = runSt a_st app_comp ->
  exists st, (fst app_comp_res = (Some st)).
Proof.
  intros.
  assert (Ev_Shape e' (Term.eval t' 0 mt)).
  eapply multi_ev_eval; eauto.
  rewrite H.
  Check announ'.
  rewrite announ'.
  reflexivity.
Admitted.

Lemma app_some'' : forall t t' p p' p'' tr o e e' et (app_comp: AM (VM unit)) app_comp_res a_st,
    t = snd (anno t' p') ->
    build_comp t {| st_ev:=e; st_trace:=[]; st_pl:=p; st_store:=[]|} =
    (Some tt, {| st_ev:=e'; st_trace:=tr; st_pl:=p''; st_store:=o|}) ->
    allMapped t p a_st ->
    Ev_Shape e et ->
    app_comp = gen_appraisal_comp e' (eval t' p et) ->
    app_comp_res = runSt a_st app_comp ->
    (*Ev_Shape e' (eval t' p mt) -> *)
    exists st, (fst app_comp_res = (Some st)).
Proof.
  intros.
  assert (Ev_Shape e' (eval t' p et)).
  eapply multi_ev_eval; eauto.
  rewrite H.
  erewrite announ'.
  reflexivity.
  generalize dependent t.
  generalize dependent p'.
  generalize dependent app_comp.
  generalize dependent app_comp_res.
  generalize dependent a_st.
  generalize dependent o.
  generalize dependent p''.
  generalize dependent tr.
  generalize dependent p.
  generalize dependent e'.
  generalize dependent e.
  generalize dependent et.
  induction t'; intros; subst.
  -
    cbn in *.
    repeat break_let.
    monad_unfold.
    destruct a; simpl in *;
      repeat find_inversion.
    +
      cbn.
      eexists. eauto.
    + cbn.
      monad_unfold.
      edestruct H1.
      econstructor.
      econstructor.
      reflexivity.
      econstructor.
      reflexivity.
      inv H.
      cbn.
      repeat break_let.
      repeat find_inversion.
      rewrite H0 in *.
      monad_unfold.
      repeat find_inversion.
      simpl in *.
      eexists.
      eauto.
    +
      cbn.
      eexists.
      eauto.
    + cbn.
      eexists.
      eauto.
  -
    cbn in *.
    repeat break_let.
    simpl in *.
    Check allMappedAt.
    assert (allMapped a n a_st).
    {
      eapply allMappedAt; eauto.
    }
    
    edestruct IHt'.
    eassumption.
    reflexivity.
    reflexivity.
    reflexivity.
    monad_unfold.
    repeat break_let.
    unfold get_store_at in *.
    monad_unfold.
    dohtac.
    repeat find_inversion.
    rewrite Heqp0.
    simpl.
    Check build_comp_at.
    apply build_comp_at.
    rewrite Heqp0.
    simpl.
    eassumption.

    rewrite H2.
    eexists.
    eauto.
  -
    Check alseq_decomp.
    cbn in *.
    repeat break_let.
    unfold snd in *.
    Check alseq_decomp.
    edestruct alseq_decomp with (r:=(p',n0)).
    cbn.
    repeat break_let.
    simpl.
    repeat find_inversion.
    rewrite Heqp0 in Heqp2.
    repeat find_inversion.
    rewrite Heqp1 in *.
    repeat find_inversion.
    reflexivity.
    eassumption.
    destruct_conjs.
    edestruct IHt'2.
    eassumption.

    eapply IHt'2.
    2 : {
      reflexivity.
    }
    2: { 
    
    
    
    
    
      
      
      
      
      

Lemma app_some'' : forall t t' p p' p'' tr o e' (app_comp: AM (VM unit)) app_comp_res a_st,
    t = snd (anno t' p') ->
    build_comp t {| st_ev:=mtc; st_trace:=[]; st_pl:=p; st_store:=[]|} =
    (Some tt, {| st_ev:=e'; st_trace:=tr; st_pl:=p''; st_store:=o|}) ->
    allMapped t p a_st ->
    app_comp = gen_appraisal_comp e' (eval t' p mt) ->
    app_comp_res = runSt a_st app_comp ->
    (*Ev_Shape e' (eval t' p mt) -> *)
    exists st, (fst app_comp_res = (Some st)).
Proof.
  intros.
  assert (Ev_Shape e' (eval t' p mt)).
  eapply multi_ev_eval; eauto.
  rewrite H.
  erewrite announ'.
  reflexivity.
  generalize dependent t.
  generalize dependent p'.
  generalize dependent app_comp.
  generalize dependent app_comp_res.
  generalize dependent a_st.
  generalize dependent o.
  generalize dependent p''.
  generalize dependent tr.
  (*
  generalize dependent t'.
  generalize dependent p. *)
  induction H4; intros; subst.
  -
    cbv.
    eauto.
  -
    edestruct IHEv_Shape.
    reflexivity.
    reflexivity.
    reflexivity.
    admit.
    eassumption.
    
 
    unfold runSt in H.
    repeat break_let.
    simpl in *.
    subst.
    unfold runSt in *.
    monad_unfold.
    repeat break_let.
    assert (a_st = a).
    { admit. }
    rewrite H2 in *. clear H2.
    subst.
    rewrite Heqp0 in *. clear Heqp0.
    simpl in *.
    repeat find_inversion.
    subst.
    cbn in *.
    repeat break_let.
    repeat find_inversion.
    edestruct H1.
    econstructor.
    admit.
    econstructor.
    reflexivity.
    inv H.
    rewrite H2 in *.
    monad_unfold.
    repeat find_inversion.
    eexists.
    simpl.
    eauto.
  -
    cbv.
    eexists.
    eauto.
  - cbv.
    eexists.
    eauto.
  - cbv.
    eexists.
    eauto.
  -
    edestruct IHEv_Shape1.
    reflexivity.
    reflexivity.
    reflexivity.
    admit.
    eassumption.
    edestruct IHEv_Shape2.
    reflexivity.
    reflexivity.
    reflexivity.
    admit.
    eassumption.
    unfold runSt.
    cbn.
    monad_unfold.
    unfold runSt in *.
    destruct (gen_appraisal_comp e1 e1t a_st) eqn:aa.
    simpl in *.
    destruct (gen_appraisal_comp e2 e2t a_st) eqn:bb.
    simpl in *.
    subst.
    repeat break_let.
    destruct a_st.
    destruct a.
    destruct a1.
    simpl.
    destruct a2.
    simpl in *.
    cbn in *.
    break_match.
    repeat find_inversion.
    eexists.
    eauto.
    repeat find_inversion.
    assert ({| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} =
            {| am_nonceMap := am_nonceMap0; am_nonceId := am_nonceId0; st_aspmap := st_aspmap0 |}).
    {
      admit.
    }
    rewrite H in *.
    congruence.
  -
    
    
    
    
    
    
      



    
    repeat break_match.
    +
      repeat find_inversion.
      eexists.
      simpl.
      eauto.
    + repeat find_inversion.
      destruct a_st.
      destruct a.
      simpl in *.
      assert (
          {| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} =
          {| am_nonceMap := am_nonceMap0; am_nonceId := am_nonceId0; st_aspmap := st_aspmap0 |}
        ).
      {
        admit.
      }
      rewrite H1 in *. clear H1.
      rewrite Heqp0 in *.
      solve_by_inversion.
    +
      assert (a = a_st).
      {
        admit.
      }
      rewrite H1 in *. clear H1.
      rewrite Heqp0 in *.
      simpl in *.
      
      repeat find_inversion.
      subst.

      destruct a_st.
      destruct a.

       assert (
          {| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} =
          {| am_nonceMap := am_nonceMap0; am_nonceId := am_nonceId0; st_aspmap := st_aspmap0 |}
        ).
      {
        admit.
      }
      rewrite H1 in *. clear H1.
      rewrite Heqp0 in *. clear Heqp0.
      simpl in *.
      repeat find_inversion.
      
      
      
      
      unfold gen_appraisal_comp in H
      edestruct H0.
      econstructor.
      econstructor.
      
    


    
    rewrite Heqp0 in *.
    
    inv H3.
    destruct t';
      try destruct a;
      try (cbv; eauto; tauto).
  -

    inv H3.
    destruct t';
      try destruct a;
      try (simpl in *; eauto; solve_by_inversion).
    + simpl in *.
      inv H5.
      monad_unfold.
      edestruct H0.
      econstructor.
      econstructor.
      reflexivity.
      econstructor.
      reflexivity.
      inv H.
      unfold am_get_app_asp.
      monad_unfold.
      repeat break_let.
      unfold runSt.
      monad_unfold.
      repeat break_let.
      rewrite H2 in *.
      repeat find_inversion.
      repeat break_let.
      repeat find_inversion.
      inv H1.
      unfold gen_appraisal_comp in *.
      monad_unfold.
      repeat find_inversion.
      eexists.
      eauto.
    +



      
      simpl in *.
      repeat break_let.
      simpl in *.
      edestruct allMappedAt.
      apply H0.
      econstructor.
      inv H3.
      subst.
      repeat find_inversion.
      simpl in H3.
      
      rewrite <- H5 in *.
      invc H3.
      invc H7.
      unfold gen_appraisal_comp.
      monad_unfold.
      repeat break_let.
      simpl in *.
      unfold runSt.
      clear H2.
      edestruct H0.
      simpl.
      econstructor.
      econstructor.
      admit.
      econstructor.
      reflexivity.
      inv H.
      unfold am_get_app_asp.
      monad_unfold.
      rewrite H2.
      repeat break_let.
      
      econstructor.
      rewrite H7 in *.
      
      
      
    simpl in H5.
      
    subst.
    unfold gen_appraisal_comp.
    monad_unfold.
    unfold runSt.
    edestruct H0.
    
    simpl in H.
    cbv.
    eexists.
    eauto.
    + inv H.
    + inv H.
    + inv H.
    + inv H.
      destruct t'.
      destruct a.
      simpl in H.
      cbv.
      eauto.
      inv H2.
      inv H2.
      inv H2.
      inv H2.
      cbv.
      eauto.
      inv H2.
      cbv.
      eauto.
      cbv.
      eauto.
      cbv.
      eauto.
    + cbv.
      eauto.
    + cbv.
      eauto.
    +
      
      
      


          
      
      
      
      
    cbv.
    eexists.
    eauto.
  -
    subst.
    unfold gen_appraisal_comp.
    monad_unfold.
    unfold runSt.
    eapply IHEv_Shape.
    reflexivity.
    unfold gen_appraisal_comp at 1.
    monad_unfold.
    unfold runSt.
    unfold am_get_app_asp.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    cbv
    
    
  -
    
  induction t; intros.
  -
    destruct a.
    +
      annogo.
      inv H3.
      cbv.
      eexists.
      eauto.
    + annogo.
      inv H3.
      cbn.
      monad_unfold.
      edestruct H0.
      econstructor.
      econstructor.
      reflexivity.
      econstructor.
      reflexivity.
      inv H1.
      unfold am_get_app_asp.
      monad_unfold.
      repeat break_let.
      rewrite H2 in *.
      repeat find_inversion.
      repeat break_let.
      repeat find_inversion.
      inv H4.
      cbn in *.
      monad_unfold.
      repeat find_inversion.
      simpl in *.
      cbn.
      monad_unfold.
      eexists.
      eauto.
    +
       annogo.
      inv H3.
      cbv.
      eexists.
      eauto.
    +
       annogo.
      inv H3.
      cbv.
      eexists.
      eauto.
  -
    destruct r.
    Check afff.
    assert (exists t'' n', t = snd (anno t'' n')).
    {
      eapply afff.
      exact 0.
      symmetry.
      eassumption.
    }
      
    destruct_conjs.
    simpl.
    subst.

    edestruct allMappedAt.
   ++
     apply H0.
   ++
     

    edestruct IHt.
    eassumption.
    
    
      
      
      
      
      cbv.
      eexists.
      eauto.
      
      
    
  
Admitted.


Lemma app_some : forall t t' p' (vm_st':vm_st) (app_comp: AM vm_st) app_comp_res a_st,
    t = snd (anno t' p') ->
    build_comp t empty_vmst = (Some tt, vm_st') ->
    allMapped t 0 a_st ->
    app_comp = exec_app_comp_t t' 0 p' empty_vmst ->
    app_comp_res = runSt a_st app_comp ->
    exists st, (fst app_comp_res = (Some st)).
Proof.
  intros.
  vmsts.
  unfold empty_vmst in *.
  edestruct app_some'' with (t:=t) (t':=t') (p':=p') (e':=st_ev).
  eassumption.
  eassumption.
  reflexivity.
  reflexivity.
  eapply multi_ev_eval.
  eassumption.
  apply H0.
  econstructor.
  rewrite H.
  erewrite announ'.
  reflexivity.
  subst.
  unfold exec_app_comp_t.
  unfold exec_app_comp.
  monad_unfold.
  unfold build_app_comp.
  monad_unfold.
  unfold runSt.
  unfold run_vm.
  monad_unfold.
  rewrite H0.
  simpl.
  erewrite announ'.
  unfold runSt in *.
  repeat break_match; try solve_by_inversion.
  repeat find_inversion.
  eexists.
  simpl.
  eauto.
Defined.




                                
  

Lemma app_some : forall t t' p p' vm_st' app_comp app_comp_res a_st,
    t = snd (anno t' p') ->
    build_comp t empty_vmst = (Some tt, vm_st') ->
    allMapped t p a_st ->
    app_comp = exec_app_comp_t t' p p' empty_vmst ->
    app_comp_res = runSt a_st app_comp ->
    exists st, (fst app_comp_res = (Some st)).
Proof.
  induction t; intros; subst.
  -

    destruct a.
    + unfold exec_app_comp_t.
      unfold exec_app_comp.
      monad_unfold.
      monad_unfold.
      repeat break_let.
      simpl in *.
      repeat find_inversion.
      unfold runSt.
      rewrite <- H.
      simpl.
      cbn.
      unfold build_app_comp.
      monad_unfold.



      repeat break_match; try solve_by_inversion.
      eexists.
      simpl.
      reflexivity.
      repeat find_inversion.
      unfold empty_vmst in *.
      repeat find_inversion.
      unfold gen_appraisal_comp in *.
      monad_unfold.
      solve_by_inversion.
    +
      vmsts.
      simpl in *.
      monad_unfold.
      repeat find_inversion.
      unfold runSt.
      cbn.
      unfold exec_app_comp_t.
      unfold exec_app_comp.
      monad_unfold.
      unfold build_app_comp.
      monad_unfold.
      monad_unfold.
      unfold allMapped in H1.
      repeat break_match; try solve_by_inversion.
      repeat break_let.
      repeat find_inversion.
      unfold runSt.
      repeat break_let.
      eexists. simpl.
      eauto.
      repeat find_inversion.
      rewrite <- H in *.
      simpl in Heqp1.
      monad_unfold.
      edestruct H1.
      econstructor.
      econstructor.
      reflexivity.
      econstructor.
      reflexivity.
      inv H0.
      unfold am_get_app_asp in *.
      monad_unfold.
      repeat break_let.
      rewrite H2 in *.
      repeat break_match;
        try solve_by_inversion.
      ++
        repeat break_let.
        cbn in *.
        repeat find_inversion.
      ++
        repeat find_inversion.
        clear H0.
        unfold empty_vmst in *.
        repeat find_inversion.
        unfold gen_appraisal_comp in *.
        monad_unfold.
        solve_by_inversion.
      ++
        repeat find_inversion.
    +
      vmsts.
      unfold empty_vmst in *.
      simpl in *.
      monad_unfold.
      repeat find_inversion.
      unfold runSt.
      repeat break_let.
      simpl in *.
      cbn.
      repeat find_inversion.
      unfold exec_app_comp_t.
      rewrite <- H in *.
      cbn.
      eexists.
      reflexivity.
    +
       vmsts.
      unfold empty_vmst in *.
      simpl in *.
      monad_unfold.
      repeat find_inversion.
      unfold runSt.
      repeat break_let.
      simpl in *.
      cbn.
      repeat find_inversion.
      unfold exec_app_comp_t.
      rewrite <- H in *.
      cbn.
      eexists.
      reflexivity.
  -
    unfold exec_app_comp_t.
    unfold exec_app_comp.
    Lemma build_at : forall r n t st st',
      build_comp (aatt r n t) st = (Some tt,st') ->
      build_comp t st = (Some tt, st').
    Proof.
    Admitted.
    
    assert (build_comp t empty_vmst = (Some tt, vm_st')).
    eapply build_at; eauto.
    
    rewrite <- H.
    monad_unfold.
    monad_unfold.
    repeat break_let.
    vmsts.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    dohtac.
    repeat find_inversion.
    unfold runSt.
    repeat break_let.
    repeat break_match.
    repeat find_inversion.
    ++ simpl. eauto.
    ++ repeat find_inversion.


       destruct afff with (t':=t') (r:=n0) (s:=n1) (x:=n) (t:=t) (n0:=p').
       exact p'.
       symmetry.
       eassumption.
       destruct_conjs.
       edestruct IHt.
       eassumption.
       eassumption.
       eapply allMappedAt; eauto.
       reflexivity.
       reflexivity.
       Print build_app_comp.
       unfold build_app_comp in *.
       monad_unfold.
       unfold run_vm in Heqp0.
       monad_unfold.
       monad_unfold.
       repeat break_let.
       unfold get_store_at in *.
       monad_unfold.
       dohtac.
       repeat find_inversion.
       simpl in *.
       repeat break_match; try solve_by_inversion.
       repeat find_inversion.
       unfold exec_app_comp_t in *.
       unfold exec_app_comp in *.
       monad_unfold.
       rewrite H2 in *.
       repeat break_match; try solve_by_inversion.
       rewrite <- H2 in *.
       unfold build_app_comp in *.
       monad_unfold.
       unfold runSt in *.

       assert ((toRemote (unanno (snd (anno x H0))) st_ev) =
               (StVM.st_ev
                  (run_vm (snd (anno x H0))
                     {|
                     st_ev := st_ev;
                     st_trace := st_trace1;
                     st_pl := st_pl;
                     st_store := st_store0 |}))).
       {
         admit. (* TODO: axiom? *)
       }
       rewrite H3 in *.
       unfold run_vm in *.
       monad_unfold.
       rewrite H2 in *.
       simpl in *.
       rewrite Heqp1 in *.
       solve_by_inversion.
  -
    destruct vm_st'.
    unfold empty_vmst in *.
    assert (Ev_Shape st_ev (Term.eval (unanno (alseq r t1 t2)) 0 mt)).
    eapply multi_ev_eval.
    eassumption.
    eassumption.
    econstructor.
    reflexivity.
    inv H2
    
      

       
               
       
      
    unfold snd in *.
    assert (exists vvss, (build_comp a empty_vmst) = (Some tt, vvss)).
    {
      admit.
    }
    destruct_conjs.
    
    cbn in *.
    repeat break_let.
    monad_unfold.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    dohtac.
    repeat find_inversion.
    break_match.
    +
      repeat break_let.
      simpl.
      eauto.

      (*
      subst.
      unfold build_app_comp in *.
      monad_unfold.
      simpl in *.
      cbn in *.
      unfold run_vm_fresh in *.
      cbn in *.
      unfold run_vm in *.
      monad_unfold.
      monad_unfold.
      repeat break_let.
      unfold get_store_at in *.
      monad_unfold.
      repeat break_let.
      dohtac.
      repeat find_inversion.
      simpl in *.
      destruct o; try solve_by_inversion.
      repeat find_inversion.
      edestruct IHt.
      rewrite Heqp0.
      eassumption.
      rewrite Heqp0.
      eapply allMappedAt; eauto.
      reflexivity.
      reflexivity.
      unfold exec_app_comp_t in *.
      unfold exec_app_comp in *.
      monad_unfold.
      rewrite Heqp0 in *.
      simpl in *.
      unfold runSt in *.
      Print gen_appraisal_comp.
      Print build_app_comp.
      unfold build_app_comp in *.
      monad_unfold.
      assert (
          (toRemote (unanno a) n mtc) =
          (st_ev (run_vm_fresh a))).
      {
        admit.
      }
      rewrite <- H3 in *.
      rewrite Heqp2 in *.
      repeat find_inversion.
      simpl in *.
      rewrite Heqp8 in *.
      simpl in *.
      eexists.
      reflexivity. *)
    +
      unfold build_app_comp in *.
      monad_unfold.
      unfold run_vm_fresh in *.
      cbn in *.
      unfold run_vm in *.
      monad_unfold.
      monad_unfold.
      repeat break_let.
      unfold get_store_at in *.
      monad_unfold.
      dohtac.
      repeat find_inversion.
      simpl in *.
      destruct o0; try solve_by_inversion.
      repeat find_inversion.
      edestruct IHt.
      rewrite Heqp0.
      eassumption.
      rewrite Heqp0.
      eapply allMappedAt; eauto.
      reflexivity.
      reflexivity.
      unfold exec_app_comp_t in *.
      unfold exec_app_comp in *.
      monad_unfold.
      unfold runSt in *.
      rewrite Heqp0 in *.
      simpl in *.
      unfold build_app_comp in *.
      monad_unfold.

      assert ((toRemote (unanno a) n mtc) =
              (st_ev (run_vm_fresh a))).
      {
        admit.
      }
      rewrite <- H3 in *.
      rewrite Heqp2 in *.
      simpl in *.
      congruence.
  -
    destruct ((snd (anno (lseq t1 t2) p'))) eqn:hi;
      try (inv hi;
           repeat break_let;
           simpl in *;
           solve_by_inversion).




    unfold empty_vmst in *.
    vmsts.
    edestruct alseq_decomp; eauto.
    destruct_conjs.
    repeat break_let.

    unfold exec_app_comp_t.
    unfold exec_app_comp.
    monad_unfold.
    unfold runSt.
    repeat break_let.
    simpl in *.

    destruct o; try solve_by_inversion.
    repeat find_inversion.
    rewrite Heqp6 in *.
    repeat find_inversion.

    destruct o1.
    + admit.
    +
      

    assert ((allMapped (alseq (p', n0) a1 a2) p a_st) -> False).
    admit.
    tauto.
















    
    repeat find_inversion.
    unfold build_app_comp in *.
    monad_unfold.
    unfold run_vm_fresh in *.
    unfold run_vm in *.
    monad_unfold.
    simpl in *.
    monad_unfold.
    unfold empty_vmst in *.
    rewrite Heqp2 in *.
    monad_unfold.
    simpl in *.
    repeat break_let.
    simpl in *.
    simpl in *.
    repeat break_let.
    simpl in *.
    rewrite Heqp6 in *.
    repeat find_inversion.
    repeat break_let.

    repeat break_match;
      try solve_by_inversion.
    +
      repeat find_inversion.
      destruct v0.
      simpl.
      eexists. eauto.
    +
      repeat find_inversion.
      destruct v.
      simpl in *.
      destruct o0.
      dunit.
      repeat find_inversion.
      
      eapply fals.
      rewrite Heqp6. reflexivity.
      
      

    unfold gen_appraisal_comp in *
                                 




    
    rewrite <- Heqp6 in *.

    assert ( (let (_, y) := anno t2 p' in y) =  (let (_, y) := anno t2 p' in y)
    
      
      
      
      unfold 
      
      
      unfold gen_appraisal_comp in *
      eapply IHt.
      unfold gen_appraisal_comp in *
      
    
    
    
    
      
    
    
  

Lemma app_correct :
  forall t app_comp app_comp_res app_comp_st tr_app_comp ev p p' a_st st',

    build_comp (snd (anno t p')) empty_vmst = (Some tt, st') ->
    app_comp = exec_app_comp_t t p p'  (* AM vm_st *) ->
    app_comp_res = runSt a_st app_comp (* ((option vm_st) * AM_St) *)  -> 
    app_comp_st = fromOpt (fst app_comp_res) empty_vmst (* vm_st *)  ->
    tr_app_comp = st_trace app_comp_st ->
                      
    measEvent (snd (anno t p')) p ev ->
    allMapped (snd (anno t p')) p a_st ->
    exists ev', In ev' tr_app_comp /\ appEvent ev a_st ev'.
Proof.
  induction t; intros; subst.
  -
    destruct a;
      try (invc H4;
           invc H1;
           solve_by_inversion).
    +
      inv H4.
      inv H1.
      inv H0.
      simpl in *.
      repeat find_inversion.
         
      simpl in *.
      monad_unfold.
      unfold allMapped in *.
      edestruct H5.
      eassumption.
      reflexivity.
      unfold am_get_app_asp.
      inv H2.
      unfold exec_app_comp_t.
      unfold exec_app_comp.
      unfold build_app_comp.
      monad_unfold.
      monad_unfold.
      unfold runSt.
      unfold am_get_app_asp.
      monad_unfold.
      repeat break_let.
      rewrite H3 in *.
      simpl in *.
      repeat find_inversion.
      simpl in *.
      Print appEvent.
      eexists.
      split.
      eauto.
      destruct a.
      Print appEvent.
      econstructor.
      eauto.
  -
    inv H4.
    inv H1.
    cbn in *.
    repeat break_let.
    unfold snd in *.
    assert ((build_comp a empty_vmst) = (Some tt, st')).
    {
      admit.
    }
    
    simpl in *.
    inv H0.

    assert (allMapped a n a_st).
    eapply allMappedAt; eauto.
        
    unfold allMapped in H5.
    edestruct H5.
    eassumption.
    reflexivity.
    inv H6.
    
    edestruct IHt.
    rewrite Heqp1.
    eassumption.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    eapply measEventAt'.
    assert ((aatt (p',S n1) n a) = (snd (anno (att n t) p'))) as HH.
    {
      cbn. repeat break_let.
      simpl.
      congruence.
    }
    rewrite <- HH. clear HH.
    eassumption.
    rewrite Heqp1.
    simpl.
    eassumption.

    exists x0.
    unfold exec_app_comp_t in *.
    unfold exec_app_comp in *.
    monad_unfold.
    rewrite Heqp1 in *.
    simpl in *.
    unfold runSt in *.
    simpl in *.
    repeat break_let.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    dohtac.
    repeat find_inversion.
    repeat break_match; try solve_by_inversion.
    +
      repeat find_inversion.
      simpl in *.
      repeat find_inversion.
      cbn in *.
      unfold build_app_comp in *.
      monad_unfold.
      cbn in *.

      unfold run_vm_fresh in *.
      unfold run_vm in Heqp7.
      unfold execSt in Heqp7.
      cbn in Heqp7.
      repeat break_let.
      repeat find_inversion.
      monad_unfold.
      repeat find_inversion.
      unfold get_store_at in *.
      monad_unfold.
      repeat break_let.
      dohtac.
      repeat find_inversion.
      simpl in *.
      assert ((st_ev (run_vm a empty_vmst)) = (toRemote (unanno a) n mtc)).
      {
        admit. (* TODO: make this an axiom? *)
      }
      rewrite H in *.
      subst.
      rewrite Heqp6 in *.
      repeat find_inversion.
      repeat break_match; try solve_by_inversion.
      repeat find_inversion.
      eassumption.
    + simpl in *.
      tauto.
    + simpl in *.
      repeat find_inversion.
      unfold build_app_comp in *.
      monad_unfold.
      unfold run_vm_fresh in *.
      cbn in *.
      unfold run_vm in Heqp7.
      monad_unfold.
      monad_unfold.
      repeat break_let.
      repeat find_inversion.
      simpl in *.
      unfold get_store_at in *. monad_unfold. repeat break_let.
      dohtac.
      repeat find_inversion.
      simpl in *.

       assert ((st_ev (run_vm a empty_vmst)) = (toRemote (unanno a) n mtc)).
      {
        admit. (* TODO: make this an axiom? *)
      }
      rewrite H in *.
      rewrite Heqp9 in *.
      repeat find_inversion.
      repeat break_match; solve_by_inversion.
  -
    invc H4.
    invc H1.
    invc H0; repeat break_let; simpl in *; try solve_by_inversion; invc H1.
    +
    unfold exec_app_comp_t.
    unfold exec_app_comp.
    monad_unfold.
    simpl in *.
    repeat break_let.
    unfold snd in *.
    (*build_comp (alseq (p', n3) a1 a2) empty_vmst = (Some tt, st')*)
    Print build_app_comp.
    unfold runSt.
    unfold build_app_comp.
    monad_unfold.
    unfold run_vm_fresh.
    unfold run_vm.
    unfold execSt.
    cbn.
    rewrite H.
    simpl in *.
    unfold runSt.
    simpl in *.
    repeat break_match; try solve_by_inversion; repeat find_inversion.
    ++
      simpl in *.
      unfold build_app_comp in *.
      monad_unfold.
      repeat find_inversion.
      unfold run_vm_fresh in *.
      unfold run_vm in *.
      monad_unfold.
      monad_unfold.
      simpl in *.
      repeat break_match; try solve_by_inversion.
      +++ repeat find_inversion.
          simpl in *.
          repeat find_inversion.
          edestruct IHt1; try reflexivity.
          rewrite Heqp2.
          simpl.
          dunit.
          eassumption.
          econstructor.
          rewrite Heqp2.
          eassumption.
          simpl.
          econstructor.
          simpl.
          rewrite Heqp2.
          Lemma allMappedL : forall r t1 t2 p st,
            allMapped (alseq r t1 t2) p st ->
            allMapped t1 p st.
          Proof.
          Admitted.

          eapply allMappedL; eauto.
          exists x.
          dunit.
          destruct_conjs.
          unfold exec_app_comp_t in *.
          unfold exec_app_comp in *.
          monad_unfold.
          unfold runSt in *.
          rewrite Heqp2 in *.
          simpl in *.
          repeat break_match; try solve_by_inversion.
          simpl in *.
          repeat find_inversion.
          destruct o; try solve_by_inversion.
          repeat find_inversion.
          admit.
    ++
      admit.
    +
      repeat break_let; simpl in *.
      repeat find_inversion.
      admit.
  -
    
      
      
      +++ repeat find_inversion.
          simpl in *.
          
          unfold gen_appraisal_comp in *
    
    invc H0.
    
      
      
      
      
      


















    
    unfold allMapped.
    intros; subst.
      
    unfold anno in Heqp1
    cbn in H3.
    break_let.
    simpl in H3.
    inv H3.
    inv H2.
    cbn in H.
    break_let.
    simpl in H.
    clear H2.
    clear H0.
    

    Check measEventAt'.
    unfold annotated.
    Check measEventAt'.
    cbn in H4.
    break_let.
    simpl in H4.
    eapply measEventAt'.
    cbn.
    break_let.
    eassumption.

    
    cbn in H4.
    repeat break_let.
    simpl in H4.
    simpl.
    
    repeat find_inversion.
    unfold allMapped in H4.
    inv H0.
    edestruct H4.
    apply H3.
    reflexivity.

    unfold allMapped.
    intros.
    subst.
    cbn in H3.
    break_let.
    simpl in H3.

    exists x.
    
    admit.
    inv H1
    apply H1.
    eassumption.
    intros.
    subst.
    

    

    



    eapply measEventAt.
    eassumption.
    destruct_conjs.
    monad_unfold.
    unfold exec_app_comp_t.
    unfold exec_app_comp.
    monad_unfold.
    unfold runSt.
    break_match.
    destruct o.
    +
      simpl.
      destruct ast.
      monad_unfold.
      unfold runSt in *.
      unfold exec_app_comp_t in *.
      unfold exec_app_comp in *.
      monad_unfold.
      cbn in *.
      repeat break_let.
      simpl in *.
      unfold build_app_comp in Heqp.
      monad_unfold.
      unfold run_vm_fresh in Heqp.
      monad_unfold.
      unfold run_vm in Heqp.
      monad_unfold.
      monad_unfold.
      repeat break_let.
      repeat find_inversion.
      simpl in *.

      Require Import MonadVMFacts.
      vmsts.
      simpl in *.
      unfold get_store_at in *.
      monad_unfold.
      repeat break_let.
      dohtac.
      repeat find_inversion.
      repeat break_match;
        repeat find_inversion.
      ++  vmsts.
          vmsts.
          inv H2.
          unfold build_app_comp in *.
          monad_unfold.
          unfold run_vm_fresh in Heqp0.
          unfold run_vm in *.
          monad_unfold.
          Print unanno.



          rewrite announ in *.

          Print build_comp.
          repeat break_match;
            try solve_by_inversion.
          repeat find_inversion.

          unfold runSt in *.



          exists (umeas m q i' (args ++ [n0])).
          split.

          eapply atgentrace.
          apply Heqp2.
          apply Heqp1.
          eassumption.
          eauto.
      ++
        unfold build_app_comp in *.
        monad_unfold.
        repeat break_match;
          try solve_by_inversion.
    +
      inv H3.
      inv H2.
      simpl.
      unfold allMapped in *.
      edestruct H4 with (st:=ast).
      eassumption.
      reflexivity.
      repeat find_inversion.
      unfold runSt in *.
      monad_unfold.
      unfold exec_app_comp_t in *.
      unfold exec_app_comp in *.
      monad_unfold.
      repeat break_match;
        try solve_by_inversion.
      simpl in *.
      unfold build_app_comp in *.
      monad_unfold.
      repeat break_match;
        try solve_by_inversion.
      ++ rewrite announ in *.
         repeat find_inversion.
         unfold run_vm_fresh in *.
         unfold run_vm in *.
         monad_unfold.
         destruct ast.
         simpl in *.



         exfalso.
         eapply fifi; eauto.
      
             
  - 
    
          
          
              
              
   (*           
              
              unfold annotated in *.
              rewrite <- IHt.
              unfold anno in Heqp
              
              simpl.
              
            intros.
            unfold annotated.
            induction 
            -
              unfold anno. simpl. reflexivity.
            - simpl. repeat break_let. simpl. unfold unanno
              
          Admitted.
          

            
          unfold gen_appraisal_comp in *
          inv H.
          invc H7.
          invc H7.
          invc H8.
          +++
            unfold runSt in H1.
            unfold build_app_comp in *.
            monad_unfold.

            destruct v.
              simpl. vmsts.
              simpl.
              unfold gen_appraisal_comp in Heqp2.

            
          unfold gen_appraisal_comp in Heqp2
    
    
      
           
 
         unfold bind.
         unfold run_vm_fresh.
         unfold run_vm.
         unfold execSt.
         unfold eval.
         unfold annotated.
         unfold anno.
         simpl.
         unfold bind.
         unfold am_get_app_asp.
         unfold bind.
         unfold gets.
         unfold bind.
         unfold runSt.
         unfold get.
         repeat break_let.
         repeat find_inversion.
         repeat break_match.
                     
         monad_unfold.
         unfold build_app_comp.
         monad_unfold.
         monad_unfold.
         unfold am_get_app_asp.
         monad_unfold.
         repeat break_let.
         unfold map_get
         














      
      unfold runSt.
      simpl in *.
      repeat break_let.
      simpl in *.
      inv H1.
      rewrite H2 in *.
      invc Heqp0.
      invc Heqp.
      simpl.
      eexists.
      split.
      right. left. eauto.
      destruct a.
      econstructor.
      simpl in *.
      assumption.
    + invc H7.
      invc H.
      invc H0.
    + invc H7.
      invc H.
      invc H0.
  -
    inv H7.
    Print measEvent.
    inv H0.
    monad_unfold.
    destruct empty_vmst.
    simpl in *.
    monad_unfold.
    unfold runSt.
    monad_unfold.

    edestruct IHaterm0; eauto.
    econstructor.
    Lemma hfhf : forall x n t p,
      ev_in x (ev_sys (annotated (att n t)) p) ->
      ev_in x (ev_sys (annotated t) p).
    Proof.
    Admitted.
    eapply hfhf; eauto.
    econstructor.

    (*
    Lemma jfjf : forall n p t st,
      allMapped (annotated (att n t)) p st ->
      allMapped (annotated t) p st.
    Proof.
    Admitted.

    eapply jfjf; eauto. *)
    destruct_conjs.
    inv H2.

    exists (umeas m q i' (args ++ [n0])).
    split.
    unfold runSt in *.

    Lemma jhjh : forall x t p n t_st init_st init_st',
       In x
         (StVM.st_trace
            (snd
               (build_comp
                  (annotated
                     (fromOpt
                        (fst
                           (gen_appraisal_term
                              (StVM.st_ev
                                 (run_vm (annotated t)
                                    t_st))
                              (eval t p mt)
                              init_st)) 
                        (asp CPY)))
                  init_st'))) ->
       In x
         (StVM.st_trace
            (snd
               (build_comp
                  (annotated
                     (fromOpt
                        (fst
                           (gen_appraisal_term
                              (StVM.st_ev
                                 (run_vm (annotated (att n t))
                                    t_st))
                              (eval t n mt)
                              init_st)) 
                        (asp CPY)))
                  init_st'))).
    Proof.
    Admitted.

    eapply jhjh; eauto.
    eauto.
  - inv H7.
    inv H0.
    edestruct IHaterm0_1; eauto.
    admit.

*)
  
  
  

