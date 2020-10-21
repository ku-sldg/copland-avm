Require Import GenStMonad MonadVM MonadAM ConcreteEvidence MonadVMFacts.
Require Import StAM VM_IO_Axioms Maps VmSemantics Event_system Term_system.

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.


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
      c1 <- gen_appraisal_comp e' e'_t ;;
      ret (c1)
    | _ => failm
    end
  | hhc bs e' =>
    match et with
    | hh p e'_t =>
      c1 <- gen_appraisal_comp e' e'_t ;;
      ret (c1)
    | _ => failm
    end
  | nnc nid bs e' =>
    match et with
    | nn nid_t e'_t =>
      c1 <- gen_appraisal_comp e' e'_t ;;
      ret (c1)
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

Definition build_app_comp (t: AnnoTerm) (*(p:Plc)*) (st:vm_st) (et:Evidence) : AM (VM unit) :=
  let vm_res_st := run_vm t st in
  let evc := st_ev vm_res_st in
  let evt := eval (unanno t) (st_pl st) et in
  app_comp <- gen_appraisal_comp evc evt ;;
  ret (app_comp).

Definition build_app_comp_t (t:Term) (*(p:Plc)*) (st:vm_st) (et:Evidence) : AM (VM unit) :=
  build_app_comp (annotated t) st et.

Definition exec_app_comp (t: AnnoTerm) (*(p:Plc)*) (st:vm_st) (et:Evidence) : AM vm_st :=
  app_comp <- build_app_comp t st et ;;
  let app_res := runSt empty_vmst app_comp in
  ret ((snd (app_res))).

Definition exec_app_comp_t (t: Term) (*(p:Plc)*) (p':nat) (st:vm_st) (et:Evidence) : AM vm_st :=
  exec_app_comp (snd (anno t p')) st et.

Definition run_app_comp_ev (t: AnnoTerm) (*(p:Plc)*) (st:vm_st) (et:Evidence) : AM EvidenceC :=
  app_st <- exec_app_comp t st et ;;
  ret (st_ev app_st).

Definition run_app_comp_ev_t (t: Term) (*(p:Plc)*) (st:vm_st) (et:Evidence) : AM EvidenceC :=
  run_app_comp_ev (annotated t) st et.
  

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

Inductive allMapped : AnnoTerm -> Plc -> AM_St -> Evidence -> Prop :=
| allMapped_cpy : forall r p st e m,
    m = st_aspmap st ->
    evMapped e m ->
    allMapped (aasp r (CPY)) p st e
| allMapped_asp : forall m st p i r args e,
    m = st_aspmap st ->
    evMapped e m ->
    (exists j, bound_to m (p,i) j) ->
    allMapped (aasp r (ASPC i args)) p st e
| allMapped_sig : forall r p st m e,
    m = st_aspmap st ->
    evMapped e m ->
    allMapped (aasp r (SIG)) p st e
| allMapped_hsh : forall r p st m e,
    m = st_aspmap st ->
    evMapped e m ->
    allMapped (aasp r (HSH)) p st e
| allMapped_at : forall t' p q r st e m,
    m = st_aspmap st ->
    (*evMapped e m -> *) (* TODO: need this? *)
    allMapped t' q st e ->
    allMapped (aatt r q t') p st e
| allMapped_lseq : forall t1 t2 p st r m e,
    m = st_aspmap st ->
    (* evMapped e m -> *)  (* TODO: need this? *)
    allMapped t1 p st e ->
    allMapped t2 p st (eval (unanno t1) p e) ->
    allMapped (alseq r t1 t2) p st e
| allMapped_bseq_nn : forall t1 t2 p st e r,
    allMapped t1 p st mt ->
    allMapped t2 p st mt ->
    allMapped (abseq r (NONE,NONE) t1 t2) p st e
| allMapped_bseq_na : forall t1 t2 p st e r,
    allMapped t1 p st mt ->
    allMapped t2 p st e ->
    allMapped (abseq r (NONE,ALL) t1 t2) p st e
| allMapped_bseq_an : forall t1 t2 p st e r,
    allMapped t1 p st e ->
    allMapped t2 p st mt ->
    allMapped (abseq r (ALL,NONE) t1 t2) p st e
| allMapped_bseq_aa : forall t1 t2 p st e r,
    allMapped t1 p st e ->
    allMapped t2 p st e ->
    allMapped (abseq r (ALL,ALL) t1 t2) p st e
| allMapped_bpar_nn : forall t1 t2 p st e r,
    allMapped t1 p st mt ->
    allMapped t2 p st mt ->
    allMapped (abpar r (NONE,NONE) t1 t2) p st e
| allMapped_bpar_na : forall t1 t2 p st e r,
    allMapped t1 p st mt ->
    allMapped t2 p st e ->
    allMapped (abpar r (NONE,ALL) t1 t2) p st e
| allMapped_bpar_an : forall t1 t2 p st e r,
    allMapped t1 p st e ->
    allMapped t2 p st mt ->
    allMapped (abpar r (ALL,NONE) t1 t2) p st e
| allMapped_bpar_aa : forall t1 t2 p st e r,
    allMapped t1 p st e ->
    allMapped t2 p st e ->
    allMapped (abpar r (ALL,ALL) t1 t2) p st e.



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

Lemma allMappedAt : forall r n a p st e,
    allMapped (aatt r n a) p st e ->
    allMapped a n st e.
Proof.
  intros.
  inv H.
  eauto.
Defined.

Lemma evshape_et : forall e et st,
    Ev_Shape e et ->
    evMapped et (st_aspmap st) ->
    exists res, gen_appraisal_comp e et st = (Some res, st).
Proof.
  induction e; intros.
  -
    inv H.
    cbv.
    eauto.
  -
    inv H.
    cbn.
    monad_unfold.
    cbn.
    repeat break_let.
    invc H0.
    destruct_conjs.
    invc H0.
    rewrite H1 in *.
    monad_unfold.
    repeat find_inversion.
    repeat break_let.
    edestruct IHe.
    apply H5.
    eassumption.
    rewrite H0 in *.
    repeat find_inversion.
    eauto.
  -
    inv H.
    cbn.
    monad_unfold.
    edestruct IHe.
    eassumption.
    inv H0.
    eassumption.
    rewrite H1.
    eauto.
  -
    inv H.
    cbn.
    monad_unfold.
    eauto.
    edestruct IHe.
    eassumption.
    inv H0.
    eassumption.
    rewrite H1.
    eauto.
  -
    inv H.
    cbn.
    monad_unfold.
    eauto.
    edestruct IHe.
    eassumption.
    inv H0.
    eassumption.
    rewrite H1.
    eauto.
  -
    cbn.
    invc H.
    invc H0.
    monad_unfold.
    edestruct IHe1.
    apply H3.
    eassumption.
    rewrite H in *.
    repeat break_let.
    edestruct IHe2.
    apply H5.
    eassumption.
    rewrite H0 in *.
    repeat find_inversion.
    eauto.
  -
    cbn.
    invc H.
    invc H0.
    monad_unfold.
    edestruct IHe1.
    apply H3.
    eassumption.
    rewrite H in *.
    repeat break_let.
    edestruct IHe2.
    apply H5.
    eassumption.
    rewrite H0 in *.
    repeat find_inversion.
    eauto.
Defined.

Lemma gen_const : forall e et a o a',
    gen_appraisal_comp e et a = (o,a') ->
    a = a'.
Proof.
  induction e; intros;
    cbn in *;
    destruct et;
    try (monad_unfold; cbn in *; repeat break_match;
         repeat (find_inversion; monad_unfold);
         try (assert (a = a0) by eauto);
         subst; eauto; tauto).
Defined.

Lemma app_some'' : forall t t' p p' p'' tr tr' o o' e' e et (app_comp: AM (VM unit)) app_comp_res (*app_comp' app_comp_res'*) a_st,
    t = snd (anno t' p') ->
    build_comp t {| st_ev:=e; st_trace:=tr; st_pl:=p; st_store:=o|} =
    (Some tt, {| st_ev:=e'; st_trace:=tr'; st_pl:=p''; st_store:=o'|}) ->
    Ev_Shape e et ->  (* TODO: maybe don't need this *)
    allMapped t p a_st et ->
    app_comp = gen_appraisal_comp e' (eval t' p et) ->
    app_comp_res = runSt a_st app_comp ->
    exists st, (fst app_comp_res = (Some st)).
Proof.
  intros.
  subst.
  simpl in *.
  repeat find_inversion.
  subst.
  Check trace_irrel_ev'.
  Check restl'.
  Check restl'_2.
  Check suffix_prop.
  assert (exists l, tr' = tr ++ l).
  {
    eapply suffix_prop.

    reflexivity.
    eassumption.
  }
  destruct_conjs.
  rewrite H3 in H0.
  (*
  assert (Ev_Shape e' (eval t' p et)). (* TODO: maybe dont' need this *)
  eapply multi_ev_eval; eauto.
  eapply restl'_2.
  reflexivity.
  eassumption. 
  

  
  erewrite announ'.
  reflexivity. *)
  rewrite <- H3 in *.
  clear H3.
  clear H.
  (*erewrite announ' in *. *)
  generalizeEverythingElse t'.

  induction t'; intros; subst.

  Ltac df :=
    repeat (
    cbn in *;
    repeat break_let;
    repeat (monad_unfold; cbn in *; find_inversion);
    monad_unfold).
  
  -
    df.
    destruct a; simpl in *;
      repeat find_inversion;
      subst.

    +
      cbn in *.
      Ltac allMappedFacts :=
        match goal with
        | [H: allMapped (aasp _ _) _ _ _ |- _] => invc H
        | [H: allMapped (aatt _ _ _) _ _ _ |- _] => invc H
        | [H: allMapped (alseq _ _ _) _ _ _ |- _] => invc H
        end.
      allMappedFacts.
     
      inv H1.
      ++
        df; eauto.
      ++
        df.
        Ltac evMappedFacts :=
          match goal with
          | [H: evMapped (uu _ _ _ _) _ |- _] => invc H
          | [H: evMapped (gg _ _) _ |- _] => invc H
          | [H: evMapped (hh _ _) _ |- _] => invc H
          | [H: evMapped (nn _ _) _ |- _] => invc H
          | [H: evMapped (ss _ _) _ |- _] => invc H
          | [H: evMapped (pp _ _) _ |- _] => invc H 
          end.
        
        evMappedFacts.
        destruct_conjs.
        Ltac debound :=
          match goal with
          | [H: bound_to _ _ _ |- _] => invc H
          end.
        
        debound.
        Ltac subst' :=
          match goal with
          | [H: ?A = _,
                H2: context[?A] |- _] =>
            rewrite H in *; clear H
          end.

        subst'.

        (*
        Ltac map_get_subst :=
          match goal with
          | [H: map_get ?A ?B = _,
                H2: context[map_get ?A ?B] |- _] =>
            rewrite H in *; clear H
          end.
         *)
        
        (* map_get_subst. *)
            

         df.
         (*
        vmsts.
        repeat df.
        repeat find_inversion.
        monad_unfold.
        repeat find_inversion.
        repeat break_let.
        repeat find_inversion.
        vmsts. *)

         Ltac gen_st_const :=
           let tac := (eapply gen_const; eauto) in
           repeat (
           match goal with
           | [H: gen_appraisal_comp ?e ?et ?A = (?o,?B) |- _] =>
             assert_new_proof_by (A = B) tac
                                 (*
             destruct gen_const with (e:=ee) (et:=?et) (a:=?A) (a':=?B) (o:=?o);
             try eassumption *)
           end);
           subst.

         Ltac evShapeFacts :=
           match goal with
           | [H: Ev_Shape (uuc _ _ _) _ |- _] => invc H
           end.
         
         gen_st_const.
         
         evShapeFacts.

         edestruct evshape_et;
           eauto.

         subst'.
         

         
         df.
         eauto.

      ++
        df.
        (*
        cbn in *.
        monad_unfold.
        repeat find_inversion. *)
        evMappedFacts.
        edestruct evshape_et; eauto.
        (*
        eauto.
        inv H3.
        eauto.
         *)
        subst'.
        df.
        eauto.
      ++
        df.

        evMappedFacts.
        edestruct evshape_et; eauto.

        subst'.
        df.
        eauto.

      ++
        df.

        evMappedFacts.
        edestruct evshape_et; eauto.

        subst'.
        df.
        eauto.

      ++
        df.

        evMappedFacts.

        Check evshape_et.
        Ltac do_evshape :=
          let tac := edestruct evshape_et; eauto in
          match goal with
          | [H: Ev_Shape ?e ?et,
                H2: evMapped ?et (st_aspmap ?a) |- _] =>
            assert_new_proof_by 
              (exists (res: VM unit), gen_appraisal_comp e et a = (Some res, a))
              tac ;
            clear H; clear H2
          end;
          destruct_conjs.
         
          
      

       
        repeat (do_evshape).

        gen_st_const.
        repeat subst'.
        df.
        eauto.

      ++
                df.

        evMappedFacts.


         
          
      

       
        repeat (do_evshape).

        gen_st_const.
        repeat subst'.
        df.
        eauto.
    +
      df.
      allMappedFacts.
      destruct_conjs.
      try (debound;
           subst').
      df.

      edestruct evshape_et; eauto.
      subst'.
      df.
      eauto.
    +
      df.
      allMappedFacts.
      destruct_conjs.
      try (debound;
           subst').
      df.

      edestruct evshape_et; eauto.
      subst'.
      df.
      eauto.

    +
            df.
      allMappedFacts.
      destruct_conjs.
      try (debound;
           subst').
      df.

      edestruct evshape_et; eauto.
      subst'.
      df.
      eauto.

  -

    (*
    cbn in *.
    repeat break_let.
    simpl in *.
   
    monad_unfold.
    cbn in *. *)
    df.
    dohtac.

    df.
    allMappedFacts.

    eapply IHt'.
    (*
    eassumption.
    apply H4.
     *)
    jkjke.
    

    simpl. 
    eapply build_comp_at.
    eassumption.
    simpl.
    jkjke.

  -
    Check alseq_decomp.

    (*
    assert (a_st = a).
    {
      eapply gen_const; eauto.
    }
     *)
    
    subst.
    cbn in *.
    repeat break_let.
    
    unfold snd in *.
    
    assert (alseq (p', n0) a a0 = snd (anno (lseq t'1 t'2) p')) as H.
      {
        cbn.
        repeat break_let.
        simpl.
        repeat find_inversion.
        subst'.
        df.
        eauto.
      } 
    
    assert (exists l, tr' = tr ++ l).
    {
      eapply suffix_prop.
      reflexivity.

      rewrite <- H.
      eassumption.
    }
    destruct_conjs.

    Check alseq_decomp.
    edestruct alseq_decomp with (r:=(p',n0)).
    cbn.
    repeat break_let.
    simpl.
    repeat find_inversion.
    rewrite Heqp0 in Heqp2.
    df.
    rewrite Heqp1 in *.
    df.
    reflexivity.

    rewrite H4 in *.
    eapply restl'_2.

    
(*
    rewrite H5 in *. 
    eapply restl'_2. *)
    eassumption.
    eassumption.
    clear H.
    
    
    destruct_conjs.
    

    destruct (gen_appraisal_comp x (eval t'1 p et) a_st) eqn:hi.

    repeat gen_st_const.


    destruct IHt'1 with (a_st:=a1) (tr':=H5) (et:=et) (e:=e) (e':=x) (p:=p) (tr:=nil (A:=Ev)) (p'':=H) (o':=H6) (o:=o) (p':=p').

    (*
    destruct IHt'1 with (a:=a) (a_st:=a) (tr':=H6) (o0:=o1) (et:=et) (e:=e) (e':=x) (p:=p) (tr:=nil (A:=Ev)) (p'':=p'') (o':=H7) (o:=o) (p':=p'). *)

    Print allMapped.
    jkjke.

    eassumption.
    unfold runSt in *.

    (*


    assert (a = a2).
    {
      eapply gen_const; eauto.
    }
    congruence. *)

    rewrite Heqp0.
    (*
    
    assert (H = p'').
    {
      symmetry.
      erewrite <- pl_immut in *.
      rewrite H10.
      simpl.
      reflexivity.
    }
    subst.
    eassumption.

    rewrite Heqp0.
    inv H2.
    assert (a = a2).
    {
      eapply gen_const; eauto.
    }
    subst.
    eassumption. *)

    allMappedFacts.
    eassumption.
    

    subst.
    eapply IHt'2 with (e:=x) (p':=n).
    jkjke.
        assert (p = H).
    {
      symmetry.
      erewrite <- pl_immut in *.
      jkjke.
    }
    subst.
    
    eassumption.

    eapply multi_ev_eval.
    reflexivity.

    rewrite Heqp0.
    simpl.
    eassumption.
    eassumption.
    rewrite announ'.
    reflexivity.

    jkjke.

    allMappedFacts.
   
    assert (unanno a = t'1).
    erewrite <- announ'.
    rewrite Heqp0.
    simpl.
    reflexivity.
    subst.
    eassumption.
    
    
  -

    assert (a = a_st).
    {
      symmetry.
      eapply gen_const; eauto.
    }
    subst.
    cbn in *.
    repeat break_let.
    
    unfold snd in *.
    (*
    assert (abseq (p', (S n0)) s a a0 = snd (anno (bseq s t'1 t'2) p')).
      {
        cbn.
        repeat break_let.
        simpl.
        repeat find_inversion.
        subst.
        repeat find_inversion.
      
        rewrite Heqp3 in *.
        repeat find_inversion.
        reflexivity.
      }
     *)
    cbn in *.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    (*
      inversion Heqp6.
      rewrite H10 in *. clear H10.
      rewrite H11 in *. clear H11.

      repeat find_inversion. *)
    simpl in *.
    (*
      rewrite Heqp3 in *.
      repeat find_inversion. *)
    destruct o5; try solve_by_inversion.
    repeat find_inversion.
    destruct o9; try solve_by_inversion.
    repeat find_inversion.
    
    simpl in *.
    cbn in *.
    monad_unfold.
    
    vmsts.

    simpl in *.
    invc H2.
    +
      cbn in *.
      repeat dunit.
      vmsts.
      simpl in *.
      unfold runSt in *.

      destruct (gen_appraisal_comp st_ev0 (eval t'1  p mt) a_st) eqn:ghi.
      destruct (gen_appraisal_comp st_ev  (eval t'2  p mt) a_st) eqn:hhi.
      
      edestruct IHt'1.
      eapply mtt.
      symmetry.
      eassumption.
      rewrite Heqp0.
      eassumption.
      rewrite Heqp0.
      eassumption.        
      subst.
      
      
      repeat break_let.
      repeat find_inversion.

      edestruct IHt'2.
      eapply mtt.
      symmetry.
      eassumption.
      rewrite Heqp1.

      assert (p = st_pl0).
      {
        symmetry.
        erewrite <- pl_immut in *.
        rewrite Heqp6.
        simpl.
        reflexivity.
      }
      subst.
      eassumption.
      rewrite Heqp1.
      eassumption.

      assert (a1 = a3).
      {
        symmetry.
        eapply gen_const; eauto.
      }
      subst.
      rewrite hhi in *.
      repeat find_inversion.
      eauto.

    +
      cbn in *.
      repeat dunit.
      vmsts.
      simpl in *.
      unfold runSt in *.

      destruct (gen_appraisal_comp st_ev0 (eval t'1  p mt) a_st) eqn:ghi.
      destruct (gen_appraisal_comp st_ev  (eval t'2  p et) a_st) eqn:hhi.
      
      edestruct IHt'1.
      eapply mtt.
      symmetry.
      eassumption.
      rewrite Heqp0.
      eassumption.
      rewrite Heqp0.
      eassumption.
      
      subst.
      
      repeat break_let.
      repeat find_inversion.

      edestruct IHt'2.
      apply H1.
      symmetry.
      eassumption.
      rewrite Heqp1.

      assert (p = st_pl0).
      {
        symmetry.
        erewrite <- pl_immut in *.
        rewrite Heqp6.
        simpl.
        reflexivity.
      }
      subst.
      eassumption.
      rewrite Heqp1.
      eassumption.

      assert (a1 = a3).
      {
        symmetry.
        eapply gen_const; eauto.
      }
      subst.
      rewrite hhi in *.
      repeat find_inversion.
      eauto.
    +
      cbn in *.
      repeat dunit.
      vmsts.
      simpl in *.
      unfold runSt in *.

      destruct (gen_appraisal_comp st_ev0 (eval t'1  p et) a_st) eqn:ghi.
      destruct (gen_appraisal_comp st_ev  (eval t'2  p mt) a_st) eqn:hhi.
      
      edestruct IHt'1.
      apply H1.
      symmetry.
      eassumption.
      rewrite Heqp0.
      eassumption.
      rewrite Heqp0.
      eassumption.
      
      subst.
      
      repeat break_let.
      repeat find_inversion.

      edestruct IHt'2.
      apply mtt.
      symmetry.
      eassumption.
      rewrite Heqp1.

      assert (p = st_pl0).
      {
        symmetry.
        erewrite <- pl_immut in *.
        rewrite Heqp6.
        simpl.
        reflexivity.
      }
      subst.
      eassumption.
      rewrite Heqp1.
      eassumption.

      assert (a1 = a3).
      {
        symmetry.
        eapply gen_const; eauto.
      }
      subst.
      rewrite hhi in *.
      repeat find_inversion.
      eauto.
    +
      cbn in *.
      repeat dunit.
      vmsts.
      simpl in *.
      unfold runSt in *.

      destruct (gen_appraisal_comp st_ev0 (eval t'1  p et) a_st) eqn:ghi.
      destruct (gen_appraisal_comp st_ev  (eval t'2  p et) a_st) eqn:hhi.
      
      edestruct IHt'1.
      apply H1.
      symmetry.
      eassumption.
      rewrite Heqp0.
      eassumption.
      rewrite Heqp0.
      eassumption.
      
      subst.
      
      repeat break_let.
      repeat find_inversion.

      edestruct IHt'2.
      apply H1.
      symmetry.
      eassumption.
      rewrite Heqp1.

      assert (p = st_pl0).
      {
        symmetry.
        erewrite <- pl_immut in *.
        rewrite Heqp6.
        simpl.
        reflexivity.
      }
      subst.
      eassumption.
      rewrite Heqp1.
      eassumption.

      assert (a1 = a3).
      {
        symmetry.
        eapply gen_const; eauto.
      }
      subst.
      rewrite hhi in *.
      repeat find_inversion.
      eauto.
  -
    assert (a = a_st).
    {
      symmetry.
      eapply gen_const; eauto.
    }
    subst.
    cbn in *.
    repeat break_let.
    
    
    unfold snd in *.
    (*
    assert (abseq (p', (S n0)) s a a0 = snd (anno (bseq s t'1 t'2) p')).
      {
        cbn.
        repeat break_let.
        simpl.
        repeat find_inversion.
        subst.
        repeat find_inversion.
      
        rewrite Heqp3 in *.
        repeat find_inversion.
        reflexivity.
      }
     *)
    



    cbn in *.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    simpl in *.

    destruct o5; try solve_by_inversion.
    repeat find_inversion.
    repeat break_let.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    assert (PeanoNat.Nat.eqb (fst (range a)) (fst (range a0)) = false).
    {
      assert (
          exists r b,
            abpar r b a a0 = snd(anno (bpar (s0,s1) t'1 t'2) p')).
      {
        eexists.
        eexists.
        cbn.
        repeat break_let.
        simpl.
        repeat find_inversion.
        rewrite Heqp8 in *.
        repeat find_inversion.
        reflexivity.
      }
      destruct_conjs.
      eapply h; eauto.
    }
    rewrite H in *.
    dohtac.
    repeat find_inversion.
    repeat break_let.
    simpl in *.
    dohtac.
    repeat find_inversion.
    
    
    simpl in *.
    cbn in *.
    monad_unfold.
    
    vmsts.
    simpl in *.
    invc H2.
    +
      cbn in *.
      repeat dunit.
      vmsts.
      simpl in *.
      unfold runSt in *.

      destruct (gen_appraisal_comp (parallel_att_vm_thread a  mtc) (eval t'1  p'' mt) a_st) eqn:ghi.
      destruct (gen_appraisal_comp (parallel_att_vm_thread a0 mtc) (eval t'2  p'' mt) a_st) eqn:hhi.
      
      edestruct IHt'1.
      eapply mtt.
      symmetry.
      eassumption.
      rewrite Heqp0.
      eapply build_comp_par.
      
      rewrite Heqp0.
      eassumption.
      
      subst.
      
      repeat break_let.
      repeat find_inversion.

      edestruct IHt'2.
      apply mtt.
      symmetry.
      eassumption.
      rewrite Heqp1.
      apply build_comp_par.
      rewrite Heqp1.
      eassumption.
      

      assert (a1 = a3).
      {
        symmetry.
        eapply gen_const; eauto.
      }
      
      
      subst.
      rewrite hhi in *.
      repeat find_inversion.
      eauto.

    +
      cbn in *.
      repeat dunit.
      vmsts.
      simpl in *.
      unfold runSt in *.

      destruct (gen_appraisal_comp (parallel_att_vm_thread a  mtc) (eval t'1  p'' mt) a_st) eqn:ghi.
      destruct (gen_appraisal_comp (parallel_att_vm_thread a0 e) (eval t'2  p'' et) a_st) eqn:hhi.
      
      edestruct IHt'1.
      eapply mtt.
      symmetry.
      eassumption.
      rewrite Heqp0.
      eapply build_comp_par.
      
      rewrite Heqp0.
      eassumption.
      
      subst.
      
      repeat break_let.
      repeat find_inversion.

      edestruct IHt'2.
      apply H1.
      symmetry.
      eassumption.
      rewrite Heqp1.
      apply build_comp_par.
      rewrite Heqp1.
      eassumption.
      

      assert (a1 = a3).
      {
        symmetry.
        eapply gen_const; eauto.
      }
      
      
      subst.
      rewrite hhi in *.
      repeat find_inversion.
      eauto.
    +
      cbn in *.
      repeat dunit.
      vmsts.
      simpl in *.
      unfold runSt in *.

      destruct (gen_appraisal_comp (parallel_att_vm_thread a  e) (eval t'1  p'' et) a_st) eqn:ghi.
      destruct (gen_appraisal_comp (parallel_att_vm_thread a0 mtc) (eval t'2  p'' mt) a_st) eqn:hhi.
      
      edestruct IHt'1.
      apply H1.
      symmetry.
      eassumption.
      rewrite Heqp0.
      eapply build_comp_par.
      
      rewrite Heqp0.
      eassumption.
      
      subst.
      
      repeat break_let.
      repeat find_inversion.

      edestruct IHt'2.
      apply mtt.
      symmetry.
      eassumption.
      rewrite Heqp1.
      apply build_comp_par.
      rewrite Heqp1.
      eassumption.
      
      assert (a1 = a3).
      {
        symmetry.
        eapply gen_const; eauto.
      }
      
      
      subst.
      rewrite hhi in *.
      repeat find_inversion.
      eauto.
    +
      cbn in *.
      repeat dunit.
      vmsts.
      simpl in *.
      unfold runSt in *.

      destruct (gen_appraisal_comp (parallel_att_vm_thread a e) (eval t'1  p'' et) a_st) eqn:ghi.
      destruct (gen_appraisal_comp (parallel_att_vm_thread a0 e) (eval t'2  p'' et) a_st) eqn:hhi.
      
      edestruct IHt'1.
      apply H1.
      symmetry.
      eassumption.
      rewrite Heqp0.
      eapply build_comp_par.
      
      rewrite Heqp0.
      eassumption.
      
      subst.
      
      repeat break_let.
      repeat find_inversion.

      edestruct IHt'2.
      apply H1.
      symmetry.
      eassumption.
      rewrite Heqp1.
      apply build_comp_par.
      rewrite Heqp1.
      eassumption.
      

      assert (a1 = a3).
      {
        symmetry.
        eapply gen_const; eauto.
      }
          
      subst.
      rewrite hhi in *.
      repeat find_inversion.
      eauto.
      Unshelve.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
Defined.

(*
Lemma app_some'' : forall t t' p p' p'' tr tr' o o' e' e et (app_comp: AM (VM unit)) app_comp_res (*app_comp' app_comp_res'*) a_st,
    t = snd (anno t' p') ->
    build_comp t {| st_ev:=e; st_trace:=tr; st_pl:=p; st_store:=o|} =
    (Some tt, {| st_ev:=e'; st_trace:=tr'; st_pl:=p''; st_store:=o'|}) ->
    Ev_Shape e et ->  (* TODO: maybe don't need this *)
    allMapped t p a_st et ->
    app_comp = gen_appraisal_comp e' (eval t' p et) ->
    app_comp_res = runSt a_st app_comp ->
    exists st, (fst app_comp_res = (Some st)).
 *)

Print gen_appraisal_comp.
Print exec_app_comp_t.
Print exec_app_comp.
Check gen_appraisal_comp.
Check runSt.

Definition run_appraisal_ev' (t:AnnoTerm) (p:Plc) (e:Evidence) (evc:EvidenceC) : AM vm_st :=
  let evt := eval (unanno t) p e in
  app_comp <- gen_appraisal_comp evc evt ;; (* AM (VM unit) *)
  let (_, res) := runSt empty_vmst app_comp in  (* ( option () * vm_st ) *)
  ret res.

Definition run_appraisal_ev (t:AnnoTerm) (p:Plc) (e:Evidence)
           (evc:EvidenceC) (a_st:AM_St) : (option vm_st) :=
  let app_comp := run_appraisal_ev' t p e evc in
  let (o,_) := runSt a_st app_comp in
  o.

Definition run_appraisal (t:AnnoTerm) (v_st:vm_st) (et:Evidence) (a_st:AM_St) : (option vm_st) :=
  let app_comp := exec_app_comp t v_st et in
  fst (runSt a_st app_comp).

Lemma app_some : forall t t' p' res a_st v_st v_st' e e' et p,
    t = snd (anno t' p') ->
    build_comp t v_st = (Some tt, v_st') ->
    e = st_ev v_st ->
    p  = st_pl v_st ->
    e' = st_ev v_st' ->
    Ev_Shape e et ->
    allMapped t p a_st et ->
    res = run_appraisal_ev t p et e' a_st ->
    (*res = run_appraisal t v_st et a_st -> *)
    exists (st:vm_st), res = Some st.
Proof.
  intros.
  vmsts.
  simpl in *.
  edestruct app_some'';
    try (subst; eassumption);
    try reflexivity.
  subst.
  unfold run_appraisal_ev.
  unfold run_appraisal_ev'.
  monad_unfold.
  unfold runSt in *.
  rewrite announ' in *.
  repeat break_let.
  simpl in *.
  subst.
  repeat break_let.
  repeat find_inversion.
  eauto.
Defined.


(*
Lemma app_somee : forall t t' p' (app_comp: AM vm_st) app_comp_res a_st e e' tr tr' p p'' o o' et,
    t = snd (anno t' p') ->
    build_comp t {| st_ev:=e; st_trace:=tr; st_pl:=p; st_store:=o|} =
    (Some tt, {| st_ev:=e'; st_trace:=tr'; st_pl:=p''; st_store:=o'|}) ->
    Ev_Shape e et ->
    allMapped t p a_st et ->
    app_comp = exec_app_comp_t t' 0 p' empty_vmst ->
    app_comp_res = runSt a_st app_comp ->
    exists st, (fst app_comp_res = (Some st)).
Proof.
  Print exec_app_comp_t.
  Print exec_app_comp.
  intros.
  vmsts.
  unfold empty_vmst in *.
  edestruct app_some'' with (t:=t) (t':=t') (p':=p') (e':=e').
  eassumption.
  eassumption.
  eassumption.
  
  eassumption.
  reflexivity.
  reflexivity.
  subst.
  unfold exec_app_comp_t.
  unfold exec_app_comp.
  monad_unfold.
  unfold runSt in *.
  unfold build_app_comp.
  monad_unfold.
  unfold run_vm.
  monad_unfold.
  rewrite announ'.
  simpl in *.
  Check evshape_et.
  
  Lemma eval_evshape : forall t' p',
      Ev_Shape
      (st_ev
       (snd
          (build_comp (snd (anno t' p'))
                      {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |})))
      (eval t' 0 mt).
  Proof.
  Admitted.
  
  edestruct evshape_et with (et:= (eval t' 0 mt)) (e:=(st_ev
               (snd
                  (build_comp (snd (anno t' p'))
                              {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |})))).
  eapply eval_evshape; eauto.
  admit.
  admit.
  rewrite H.
  simpl.
  eauto.
    



  
  eapply multi_ev_eval.
  reflexivity.
  rewrite H0.
  simpl in *.
  rewrite announ'.
  destruct ((gen_appraisal_comp st_ev (eval t' 0 mt) a_st)) eqn:hi.
  simpl in *.
  subst.
  simpl.
  eauto.
Defined.
*)



(*
    Lemma build_at : forall r n t st st',
      build_comp (aatt r n t) st = (Some tt,st') ->
      build_comp t st = (Some tt, st').
    Proof.
    Admitted.
*)








(*
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
 *)

Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p i args, evidenceEvent (umeas n p i args)
(*| sev: forall n p, evidenceEvent (sign n p)
| hev: forall n p, evidenceEvent (hash n p)*) .


Definition measEvent (t:AnnoTerm) (p:Plc) (ev:Ev) : Prop :=
  events t p ev /\ evidenceEvent ev.

Inductive appEvent : Ev -> AM_St -> Ev -> Prop :=
| aeu : forall p q i i' n n' m args st,
    m = st_aspmap st ->
    bound_to m (p,i) i' ->
    appEvent (umeas n p i args) st (umeas n' q i' (args ++ [n])).
    
Print exec_app_comp_t.
Print exec_app_comp.
Print build_app_comp.
Print allMapped.

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
  unfold annotated in *.
  Check measEventAt'.
  eapply measEventAt'.
  split
  unfold annotated in *.
  eapply measEventAt'.
  eapply measEventAt'; eauto.
Defined.
 *)


(*
Lemma app_correct' :
  forall t t' p' app_comp app_comp_res app_comp_st tr_app_comp ev a_st vm_st' e tr p o et,

    t = snd (anno t' p') ->
    build_comp t {| st_ev:=e; st_trace:=tr; st_pl:=p; st_store:=o|} = (Some tt, vm_st') ->
    app_comp = exec_app_comp_t t' p' {| st_ev:=e; st_trace:=tr; st_pl:=p; st_store:=o|} et  (* AM vm_st *) ->
    Ev_Shape e et ->
    app_comp_res = runSt a_st app_comp (* ((option vm_st) * AM_St) *)  -> 
    app_comp_st = fromOpt (fst app_comp_res) empty_vmst (* vm_st *)  ->
    tr_app_comp = st_trace app_comp_st ->
    allMapped t p a_st et ->                    
    measEvent t p ev ->

    exists ev', In ev' tr_app_comp /\ appEvent ev a_st ev'.
 *)


Lemma trace_cumul : forall e st st' v tr tr' p p' o o' e' o0 ev evt,
    gen_appraisal_comp ev evt st = (Some v, st') ->
    v    {| st_ev := e;  st_trace := tr;  st_pl := p;  st_store := o |} =
    (o0, {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o'|}) ->
    exists tr'', tr' = tr ++ tr''.
Proof.
Admitted.

Lemma gen_ev_shape : forall ev evt st st' v,
    gen_appraisal_comp ev evt st = (Some v, st') ->
    Ev_Shape ev evt.
Proof.
  induction ev; destruct evt; intros;
    try (econstructor; eauto; tauto);
    try (cbn in *; monad_unfold; solve_by_inversion).
  -
    econstructor.
    cbn in *.
    monad_unfold.
    cbn in *.
    repeat break_let.
    repeat find_inversion.
    repeat break_match;
      try solve_by_inversion.
    repeat find_inversion.
    monad_unfold.
    repeat find_inversion.
    eauto.
    repeat find_inversion.
  -
    econstructor.
    cbn in *.
    monad_unfold.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    eauto.
  -
    econstructor.
    cbn in *.
    monad_unfold.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    eauto.
  -
    
    econstructor.
    cbn in *.
    monad_unfold.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    eauto.
  -
    econstructor.
    cbn in *.
    monad_unfold.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    eauto.
    repeat find_inversion.

    cbn in *.
    monad_unfold.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    eauto.
    repeat find_inversion.
  -
    econstructor.
    cbn in *.
    monad_unfold.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    eauto.
    repeat find_inversion.

    cbn in *.
    monad_unfold.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    eauto.
    repeat find_inversion.
Defined.


Lemma app_correct' :
  forall t t' p' v_st v_st' app_comp_res_opt app_comp_res_st tr_app ev a_st e e' p et,

    t = snd (anno t' p') ->
    build_comp t v_st = (Some tt, v_st') ->
    e = st_ev v_st ->
    p = st_pl v_st ->
    e' = st_ev v_st' ->
    Ev_Shape e et ->
    app_comp_res_opt = run_appraisal_ev t p et e' a_st ->
    app_comp_res_st = fromOpt app_comp_res_opt empty_vmst ->
    tr_app = st_trace app_comp_res_st ->
    allMapped t p a_st et ->
    measEvent t p ev ->
    exists ev', In ev' tr_app /\ appEvent ev a_st ev'.
Proof.
  intros.
  edestruct app_some; try eassumption.
  subst.
  rewrite H10.
  cbn.
  unfold run_appraisal_ev in *.
  unfold run_appraisal_ev' in *.
  unfold runSt in *.
  monad_unfold.
  repeat break_let.
  repeat find_inversion.
  subst.
  repeat break_match; try solve_by_inversion.
  repeat find_inversion.
  rewrite announ' in *.
  simpl in *.
  unfold empty_vmst in *.
  vmsts.
  simpl in *.
  repeat find_inversion.

  (*
  assert (snd (runSt empty_vmst v) = x).
  congruence.
  clear H8.
  rewrite H. *)
  generalizeEverythingElse t'.
  

  induction t'; intros.
  -
    cbn in *.
    repeat break_let.
    repeat find_inversion.
    destruct a.
    (*
      monad_unfold;
      repeat find_inversion;
      monad_unfold;
      repeat find_inversion. *)
    +
      repeat (monad_unfold; repeat find_inversion).
      
      cbn in *.
      inv H9.
      inv H0.
      inv H.
    +
      cbn in *.
      repeat break_let.
      repeat find_inversion.
      monad_unfold.
      monad_unfold.
      repeat find_inversion.
      cbn in *.
      repeat break_let.
      destruct o;
        try solve_by_inversion.
      repeat break_let.
      repeat find_inversion.
      destruct o0;
        try solve_by_inversion.
      repeat find_inversion.
      repeat break_let.
      repeat find_inversion.
      simpl in *.
      invc H9.
      invc H.
      invc H0.
      invc H8.
      destruct_conjs.
      inv H.
      cbn in *.
      rewrite H0 in *.
      monad_unfold.
      repeat find_inversion.
      repeat break_let.
      repeat find_inversion.
      (*
      destruct o1;
        try solve_by_inversion.
      repeat find_inversion. *)
      unfold runSt.
      repeat find_inversion.
      repeat break_let.
      simpl in *.
      repeat find_inversion.
      vmsts.
      repeat find_inversion.
      unfold empty_vmst in *.
      repeat find_inversion.
      simpl in *.
      exists (umeas 0 st_pl0 n0 (l ++ [p'])).
      split.



      edestruct trace_cumul.
      eassumption.
      eassumption.
      subst.
      econstructor.
      reflexivity.
      econstructor.
      reflexivity.
      eassumption.


      (*
    +





      edestruct trace_cumul.
      eassumption.
      eassumption.
      subst.
      econstructor.
      reflexivity. *)
    +
      repeat (monad_unfold; repeat find_inversion).
      
          cbn in *.
          inv H9.
          inv H.
          inv H0.
    +
      repeat (monad_unfold; repeat find_inversion).
      
          cbn in *.
          inv H9.
          inv H.
          inv H0.
  -
    cbn in *.
    repeat break_let.
    monad_unfold.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    unfold run_vm in *.
    unfold get_store_at in *.
    monad_unfold.
    dohtac.
    repeat find_inversion.
    monad_unfold.
    cbn in *.
    monad_unfold.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    dohtac.
    repeat find_inversion.
    simpl in *.

    invc H8.
    invc H9.

    invc H;
      try solve_by_inversion.
    

    edestruct IHt'.
    apply build_comp_at.
    eassumption.
    
    rewrite Heqp.
    simpl.
    eassumption.
    rewrite Heqp.
    simpl.
    econstructor; eauto.
    rewrite Heqp.
    simpl.
    eassumption.
    eassumption.
    eauto.
  -
    cbn in *.

    repeat break_let.
    simpl in *.
    monad_unfold.
    repeat break_match;
      try solve_by_inversion.
    repeat find_inversion.
    unfold run_vm in *.
    monad_unfold.
    monad_unfold.
    rewrite Heqp3 in *.
    repeat break_let.
    repeat find_inversion.
    simpl in *.
    vmsts.
    repeat find_inversion.
    simpl in *.

    invc H7.
    (*invc H.
    + *)
      edestruct app_some''.
      reflexivity.
      rewrite Heqp0.
      simpl.
      dunit.
      apply Heqp3.
      eassumption.
      rewrite Heqp0.
      simpl.
      invc H6.
      eassumption.
      reflexivity.
      reflexivity.
      unfold runSt in *.

      edestruct app_some'' with (t:=a1).
      rewrite Heqp2.
      reflexivity.
      eassumption.
      eapply multi_ev_eval.
      reflexivity.
      rewrite Heqp0.
      simpl.
      admit.
      eassumption.
      rewrite Heqp0.
      simpl.
      reflexivity.
      invc H6.
      assert (p = st_pl).
      {
        admit.
      }
      subst.
      eassumption.
      reflexivity.
      reflexivity.
      unfold runSt in *.

      eapply IHt'2.
      reflexivity.
      eapply multi_ev_eval.
      reflexivity.
      rewrite Heqp0.
      simpl.
      admit.
      eassumption.
      rewrite Heqp0.
      simpl.
      reflexivity.
      rewrite Heqp2.
      simpl.
      eassumption.
      reflexivity; tauto.









      
      
      
      eapply IHt'1.
      reflexivity.
      eassumption.
      rewrite Heqp0.
      simpl.
      dunit.
      eassumption.
      rewrite Heqp0.
      simpl.
      econstructor.
      eassumption.
      eassumption.
      rewrite Heqp0.
      simpl.
      invc H6.
      eassumption.
      rewrite Heqp0.
      simpl.
      rewrite Heqp3.
      simpl.
      Check app_some''.

     
      
      
      

      invc H6.
      invc H0.
       *)
      
      eapply IHt'2.
      reflexivity.
      eapply multi_ev_eval.
      reflexivity.
      rewrite Heqp0.
      simpl.
      admit.
      
      
      eassumption.
      rewrite announ'.
      reflexivity.
      rewrite Heqp2.
      simpl.
      eassumption.
      rewrite Heqp2.
      simpl.
      econstructor.


      
      eassumption.

      edestruct IHt'1 with (ev:= (umeas n1 p0 i args)).
      reflexivity.
      eassumption.
      rewrite Heqp0.
      simpl.
      dunit.
      apply Heqp3.
      rewrite Heqp0.
      simpl.
      econstructor.
      eassumption.
      econstructor.
      rewrite Heqp0.
      simpl.
      eassumption.
      rewrite Heqp0.
      simpl.
      rewrite Heqp3.
      simpl.
      invc H8.
      econstructor
      
    
    
      
      
      
      
      
        
      destruct v0.
      repeat find_inversion.
      
      eexists.
      split.
      left.
      reflexivity.
      invc H10.
      inv H.
      simpl.
      econstructor.
      reflexivity.
      econstructor.
      simpl in *.
      eassumption.
    +
      cbn in *.
      inv H6.
      inv H0.
      inv H.
    +
      cbn in *.
      inv H6.
      inv H0.
      inv H.
    
    


Lemma app_correct :
  forall t t' p' app_comp app_comp_res app_comp_st tr_app_comp ev a_st st',

    t = snd (anno t' p') ->
    build_comp t empty_vmst = (Some tt, st') ->
    app_comp = exec_app_comp_t t' 0 p' empty_vmst  (* AM vm_st *) ->
    app_comp_res = runSt a_st app_comp (* ((option vm_st) * AM_St) *)  -> 
    app_comp_st = fromOpt (fst app_comp_res) empty_vmst (* vm_st *)  ->
    tr_app_comp = st_trace app_comp_st ->
    allMapped t 0 a_st mt ->                    
    measEvent t 0 ev ->

    exists ev', In ev' tr_app_comp /\ appEvent ev a_st ev'.
Proof.
  intros.
  edestruct app_some.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  subst.
  unfold runSt in *.
  unfold exec_app_comp_t in *.
  unfold exec_app_comp in *.
  monad_unfold.
  unfold build_app_comp in *.
  monad_unfold.
  repeat break_match; try solve_by_inversion.
  repeat find_inversion.
  rewrite announ' in *.
  simpl in *.
  assert (snd (runSt empty_vmst v) = x).
  congruence.
  clear H7.
  rewrite H.
  generalize dependent p'.
  generalize dependent ev.
  generalize dependent a_st.
  generalize dependent st'.
  generalize dependent x.
  generalize dependent a.
  generalize dependent v.

  induction t'; intros.
  -
    cbn in *.
    repeat break_let.
    repeat find_inversion.
    destruct a;
      monad_unfold;
      repeat find_inversion;
      monad_unfold;
      repeat find_inversion.
    +
      
      cbn in *.
      inv H6.
      inv H0.
      inv H.
    +
      cbn in *.
      repeat break_let.
      repeat find_inversion.
      destruct o;
        try solve_by_inversion.
      repeat find_inversion.
      inv H6.
      inv H0.
      inv H5.
      destruct_conjs.
      invc H1.
      rewrite H2 in *.
      monad_unfold.
      repeat find_inversion.
      eexists.
      split.
      left.
      reflexivity.
      invc H10.
      inv H.
      simpl.
      econstructor.
      reflexivity.
      econstructor.
      simpl in *.
      eassumption.
    +
      cbn in *.
      inv H6.
      inv H0.
      inv H.
    +
      cbn in *.
      inv H6.
      inv H0.
      inv H.
  -
    cbn in *.
    repeat break_let.
    simpl in *.
    monad_unfold.
    repeat break_let.
    unfold get_store_at in *.
    monad_unfold.
    dohtac.
    repeat find_inversion.
    inv H6.
    cbn in *.
    unfold run_vm in *.
    monad_unfold.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    dohtac.
    repeat find_inversion.
    simpl in *.
    inv H0.
    inv H.
    inv H5.
    eapply IHt'.
    reflexivity.
    rewrite Heqp.
    simpl.
    Print build_comp_at.
    apply build_comp_at.
    invc H6.
    clear H2.
    clear H1.
    econstructor.
    rewrite Heqp.
    simpl.
    admit.
    econstructor.
    rewrite Heqp.
    simpl.


    
    edestruct IHt'.
    reflexivity.
    cbn in *.
    
    
      
      
      
      
      destruct a0.
      econstructor.
      
      
    
  
      
    
    
  

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
  
  
  

