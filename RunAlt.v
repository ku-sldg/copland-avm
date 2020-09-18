Require Import Preamble GenStMonad MonadVM Instr VmSemantics MyStack ConcreteEvidence.
Require Import StructTactics.
Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics.

Lemma monad_left_id : forall S A B (a:A)(f:A -> (GenStMonad.St S) B) (s:S),
    (bind (ret a) f) s = (f a s).
Proof.
  intros.
  unfold ret.
  unfold bind.
  simpl.
  destruct (f a s).
  reflexivity.
Qed.

Lemma monad_right_id : forall S A (m:St S A) (s:S),
    bind m (ret) s = m s.
Proof.
  intros.
  unfold ret.
  unfold bind.
  destruct (m s).
  destruct o; auto.
Qed.

Lemma monad_right_id' : forall S (m:St S unit) (s:S),
    (m ;; (ret tt)) s = m s.
Proof.
  intros.
  unfold ret.
  unfold bind.
  destruct (m s).
  destruct o; auto.
  destruct u.
  auto.
Defined.

Lemma monad_comp : forall A B C S (m: St S A) (k:A -> St S B) (h:B -> St S C) (s:S),
    bind m (fun x => (bind (k x) h)) s = (bind (bind m k) h) s.
Proof.
  intros.
  unfold bind.
  destruct (m s).
  destruct o.
  - destruct (k a s0).
    destruct o.
    + destruct (h b s1).
      reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma gasd : forall (act:VM unit) (act2:VM unit) st,
    (act ;; ret tt ;; act2) st =
    (act ;; act2) st.
Proof.
  intros.
  unfold ret.
  cbn.
  unfold bind.
  remember (act st) as ooo.
  destruct ooo.
  destruct o.
  - break_let. reflexivity.
  - reflexivity.
Defined.

Lemma fafa : forall (act act2 act3: VM unit) st,
    ((act;; ret tt;; act2);;
     act3) st =
    ((act;; act2);;
     act3) st.
Proof.
  intros.
  rewrite <- monad_comp.
  rewrite <- monad_comp.
  unfold ret.
  unfold bind.
  remember (act st) as oo.
  destruct oo.
  destruct o.
  remember (act2 v) as ooo.
  destruct ooo.
  destruct o.
  break_let.
  reflexivity.
  reflexivity.
  reflexivity.
Defined.

Lemma hlhl : forall (act act2 act3 act4 : VM unit) st,
    ((act;; act2;; act3);;
     act4) st =
    (((act;; act2);; act3);;
     act4) st.
Proof.
  intros.
  unfold bind.
  remember (act st) as ooo.
  destruct ooo.
  destruct o.
  - remember (act2 v) as ooo.
    destruct ooo.
    destruct o.
    + remember (act3 v0) as ooo.
      destruct ooo.
      destruct o.
      ++ remember (act4 v1) as ooo.
         destruct ooo.
         reflexivity.
      ++ reflexivity.
    + reflexivity.
  - reflexivity.
Defined.

Lemma hghg : forall (act act2 act3 act4 act5 : VM unit) st,
    (((act;; act2;; act3);; act5);;
     act4) st =
    ((act;; act2;; act3);; act5;; act4) st.
Proof.
  intros.
  unfold bind.
  remember (act st) as ooo.
  destruct ooo.
  destruct o.
  - remember (act2 v) as ooo.
    destruct ooo.
    destruct o.
    + remember (act3 v0) as ooo.
      destruct ooo.
      destruct o.
      ++ remember (act5 v1) as ooo.
         destruct ooo.
         destruct o.
         +++
           remember (act4 v2) as ooo.
           destruct ooo.
           destruct o.
           reflexivity.
         
         reflexivity.
         +++ reflexivity.
      ++ reflexivity.
    + reflexivity.
  - reflexivity.
Defined.

Lemma hfhf : forall (act act2:VM unit) st il,
    (act;;
     (fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                act2)) st =
    (act;; (act2 ;;
            (fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                       (ret tt)))) st.
Proof.
  intros.
  generalize dependent act.
  generalize dependent st.
  generalize dependent act2.
  induction il; intros.
  - simpl.
    rewrite monad_comp.
    rewrite <- monad_right_id'.
    reflexivity.
  -
    simpl.
    rewrite IHil.
    repeat rewrite monad_comp.
   
    rewrite IHil.
    rewrite IHil.

    repeat rewrite monad_comp.
    rewrite fafa.


    Check gasd.
   

    assert (
      (((act;; act2;; build_comp a);; ret tt);;
       fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il (ret tt)) st =
      ((act;; act2;; build_comp a);; ret tt;; fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il (ret tt)) st).
    {
    rewrite hghg.
    reflexivity.
    }
    rewrite H.
    rewrite gasd.

    rewrite hlhl.
    reflexivity.
Defined.

Lemma gfds: forall (act:VM unit) (st:vm_st) il,
    (fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
               (act)) st =
    (act ;; 
     (fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                (ret tt))) st.
Proof.
  intros.
  generalize dependent act.
  generalize dependent st.
  induction il; intros.
  - simpl. rewrite monad_right_id'. reflexivity.

  - simpl.
    erewrite IHil.
    rewrite <- monad_comp.

    rewrite hfhf.
    rewrite monad_comp.
    rewrite monad_comp.

    rewrite fafa.
    reflexivity.
Defined.

Lemma fads : forall (act1:VM unit) act2 il st v z,
    act1 st = (Some z, v) ->
    fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
              (act1 ;; act2) st =
    fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
              (act2) v.
Proof.
  intros.
  rewrite gfds.
  rewrite <- monad_comp.
  unfold ret.
  unfold bind.
  rewrite H.
  break_let.
  break_match.
  destruct o0.
  - simpl in *.
    break_let.
    invc Heqp.
    rewrite gfds.
    unfold ret.
    unfold bind.
    rewrite Heqp0.
    break_let.
    congruence.
  - invc Heqp.
    rewrite <- Heqp0.
    rewrite gfds.
    unfold ret.
    unfold bind.
    rewrite Heqp0.
    reflexivity.
Defined.

Definition run_vm_fold (il:list AnnoInstr) : VM unit :=
  fold_left (fun (a:VM unit) (b:AnnoInstr) => a ;; (build_comp b)) il (GenStMonad.ret tt).

Definition run_vm' (il:list AnnoInstr) st : vm_st :=
  let c := run_vm_fold il in
  execSt st c.

Lemma vm_fold_step : forall a il st z v,
    run_vm_fold (a :: il) st = (Some z, v) ->
    run_vm_fold il (run_vm_step st a) = (Some z, v).
Proof.
  intros.
  simpl in *.
  cbn in *.
  rewrite gfds in H.
  rewrite <- monad_comp in H.
  rewrite monad_left_id in H.
  cbn in H.
  unfold ret in H.
  unfold bind in H.
  remember (build_comp a st) as ooo.
  destruct ooo.
  destruct o.
  - break_let.
    invc H.

    unfold run_vm_fold in *.
    unfold run_vm_step in *.
    unfold execSt in *.
    rewrite <- Heqooo.
    simpl.
    rewrite <- Heqp.
    reflexivity.
  - inv H.
Defined.


Lemma newLem : forall il a st z v,
    build_comp a st = (Some z, v) ->
    (fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
               (GenStMonad.ret tt) (snd (build_comp a st))) =
    (fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
               (GenStMonad.ret tt;; build_comp a) st).
Proof.
  intros.
  remember (build_comp a st) as aaa.
  destruct aaa.
  destruct o.
  + simpl.
    cbn.
    assert (
        fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                  (ret tt;; build_comp a) st =
        fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                  (build_comp a) st
      ) as H0.
    {
      Check bind.
      Print bind.
      Check tt.

      erewrite gfds.
      rewrite <- monad_comp.
      rewrite monad_left_id.
      erewrite gfds.
      reflexivity.
    }
        
    rewrite H0. clear H0.
    simpl.
    assert (
        fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                  (build_comp a) st =
        fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                  (build_comp a ;; ret tt) st
      ) as H0.
    {
      erewrite gfds.
      erewrite gfds.
      rewrite <- monad_comp.
      Check build_comp.

      rewrite gasd.
      reflexivity.
    }
        
    rewrite H0.
    clear H0.
    
    erewrite fads.
    reflexivity.
    symmetry. eassumption.
  +
    assert (
        fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                  (ret tt;; build_comp a) st =
        fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                  (build_comp a) st
      ) as H0.
    {
          
      erewrite gfds.
      rewrite <- monad_comp.
      rewrite monad_left_id.
      erewrite gfds.
      reflexivity.
    }

    rewrite H0. clear H0.

    assert (
        fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                  (build_comp a) st =
        fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                  (build_comp a ;; ret tt) st
      ) as H0.
    {
      erewrite gfds.
      erewrite gfds.
      rewrite <- monad_comp.
      Check build_comp.

      rewrite gasd.
      reflexivity.
    }
    rewrite H0.
    clear H0.
        
    simpl.
    erewrite fads.
    reflexivity.
    inv H.
    Unshelve.
    exact tt.
Defined.

Lemma runa : forall a il st z v,
    run_vm_fold (a :: il) st = (Some z, v) ->
    exists z' v',
    build_comp a st = (Some z', v').
Proof.
  intros.
  simpl in *.
  cbn in *.
  erewrite gfds in H.
  rewrite <- monad_comp in H.
  rewrite monad_left_id in H.
  cbn in H.
  unfold ret in H.
  unfold bind in H.
  remember (build_comp a st) as ooo.
  destruct ooo.
  destruct o.
  - break_let.
    invc H.

    destruct u.
    exists tt.
    exists v0.
    reflexivity.
  - inv H.
Defined.

Lemma fold_destruct : forall il1 il2 st st' st'' x x',
    run_vm_fold il1 st = (Some x, st') ->
    run_vm_fold il2 st' = (Some x', st'') ->
    run_vm_fold (il1 ++ il2) st = (Some x', st'').
Proof.
  induction il1; intros.
  - simpl.
    rewrite <- H0.
    simpl in *.
    unfold run_vm_fold in H.
    cbn in H.
    unfold ret in H.
    invc H.
    reflexivity.
  -
    cbn in *.
    unfold run_vm_fold in IHil1.
    rewrite gfds.
    cbn.
    simpl.
    monad_unfold.
    break_let.
    break_match.
    break_let.
    break_let.
    rewrite <- Heqp1.
    erewrite IHil1.
    reflexivity.
    rewrite <- H.
    rewrite gfds.
    monad_unfold.
    break_let.
    simpl.
    cbn.
    rewrite gfds.
    monad_unfold.
    break_let.
    break_match.
    break_let.
    break_let.
    repeat find_inversion.
    congruence.
    repeat find_inversion.
    break_let.
    congruence.
    repeat find_inversion.
    eauto.

    break_let.
    repeat find_inversion.
    rewrite gfds in H.
    monad_unfold.
    break_let.
    break_let.
    repeat break_let.
    repeat find_inversion.
Defined.

Lemma run_vm_iff : forall il st z v,
    (run_vm_fold il) st = (Some z, v) -> 
    run_vm il st = run_vm' il st.
Proof.
  intros.
  generalize dependent st.
  generalize dependent z.
  generalize dependent v.
  induction il; intros.
  - simpl.
    unfold run_vm'. simpl.
    unfold execSt.
    unfold run_vm_fold. simpl. reflexivity.
  - simpl.
    destruct runa with (a:=a) (il:=il) (st:=st) (z:=z) (v:=v).
    apply H.
    destruct_conjs.
    erewrite IHil.
    unfold run_vm'. simpl.
    unfold execSt.
    unfold snd.
    simpl.
    unfold run_vm_fold.
    simpl.
    cbn.
    unfold run_vm_step.
    simpl.
    cbn.
    unfold execSt.
    unfold snd.
    simpl.
    cbn.
    expand_let_pairs.
    expand_let_pairs.
    expand_let_pairs.
    unfold snd at 2.
    cbn.
    (*unfold GenStMonad.ret.*)
    simpl.
    cbn.
    expand_let_pairs.
    unfold snd at 1.
    unfold snd at 2.
    (*unfold fold_left.*)
    unfold snd.
    cbn.
    simpl.
    repeat expand_let_pairs.
    fold (GenStMonad.ret (S:=vm_st) (A:=unit)).
    assert (
    (fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                   (GenStMonad.ret tt) (snd (build_comp a st))) =
        (fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                   (GenStMonad.ret tt;; build_comp a) st)) as H00.
    eapply newLem.

    
    apply H1.

    congruence.


    apply vm_fold_step. eassumption.
Defined.

Require Import MonadVMFacts.

Set Nested Proofs Allowed.

Lemma run_vm_iff_helper : forall t t' il st n,
    t = snd (anno t' n) ->
    il = (instr_compiler t) ->
    exists z v,
      (run_vm_fold il) st = (Some z, v).
Proof.
  intros.
  generalize dependent H.
  generalize dependent t'.
  generalize dependent st.
  generalize dependent il.
  generalize dependent n.
  
  induction t; intros.
  - simpl in *.
    destruct a;
      try (boom; allss; simpl in *; cbn; boom; allss).
  -
    cbn in *.
    simpl in *.
    break_let.
    simpl in *.
    boom; allss.
    boom; allss.
    simpl.
    cbn.
    eauto.
  -
    unfold annotated in *.
    cbn in *.

    simpl in *.
    destruct t'; inv H;
      try (
          repeat break_let;
          simpl in *;
          inv H2).
    edestruct IHt1 with (st:=st) (il:=instr_compiler a).
    reflexivity.
    symmetry.
    rewrite Heqp.
    simpl.
    reflexivity.
    destruct_conjs.
    edestruct IHt2 with (st:=H0) (il:=instr_compiler a0).
    reflexivity.
    rewrite Heqp0.
    simpl. reflexivity.
    destruct_conjs.

    repeat eexists.


    eapply fold_destruct.
    eauto.
    vmsts.
    eauto.
  -
    simpl in *.
    destruct r; destruct s.
    subst.
    cbn.
    Print fold_destruct.
    Check fold_destruct.

    rewrite gfds.
    monad_unfold.
    cbn.
    break_let.
    rewrite <- Heqp.
    clear Heqp.
    simpl in *.
    vmsts.
    simpl in *.

    
    rewrite gfds.


    assert (
        fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b)
     (instr_compiler t1 ++
      abesr :: instr_compiler t2 ++ [ajoins (Nat.pred n1)]) 
     (ret tt) =
        run_vm_fold
          (instr_compiler t1 ++
                          abesr :: instr_compiler t2 ++ [ajoins (Nat.pred n1)])
      ) as HH.
    {
      reflexivity.
    }
    
    rewrite HH.
    clear HH.
    assert (
        (instr_compiler t1 ++
                        abesr :: instr_compiler t2 ++ [ajoins (Nat.pred n1)]) =
         (instr_compiler t1 ++
                        [abesr] ++ instr_compiler t2 ++ [ajoins (Nat.pred n1)])
      ) as HH.
    {
      reflexivity.
    }
    rewrite HH. clear HH.
    unfold bind.
    unfold ret.
    repeat break_let.
    rewrite app_assoc in Heqp.
    rewrite app_assoc in Heqp.
    assert (
        (((instr_compiler t1 ++ [abesr]) ++ instr_compiler t2) ++
            [ajoins (Nat.pred n1)]) =
        (instr_compiler t1 ++ ([abesr] ++ (instr_compiler t2 ++
                                                          ([ajoins (Nat.pred n1)]))))
      ) as HH.
    {
      simpl.
      repeat rewrite <- app_assoc.

      reflexivity.
    }
    
    rewrite HH in Heqp. clear HH.
    destruct t'; inv H;
    
      try (
          simpl in *;
          repeat break_let;
          simpl in *;
          inv H).
    
      
    
    edestruct IHt1 with (st:={|
           st_ev := splitEv s st_ev0;
           st_stack := push_stack EvidenceC (splitEv s0 st_ev0) st_stack0;
           st_trace := st_trace0 ++ [Term.split n st_pl0];
           st_pl := st_pl0;
           st_store := st_store0 |}) (il:=instr_compiler a).
    reflexivity.

    symmetry.
    rewrite Heqp0.
    simpl.
    reflexivity.
    destruct_conjs.
    
    vmsts.
    
    assert (
        push_stack EvidenceC (splitEv s0 st_ev0) st_stack0 =
        st_stack1) as HH.
    {
      Print do_stack1.
      Print run_vm'.
      assert (run_vm' (instr_compiler a) {|
         st_ev := splitEv s st_ev0;
         st_stack := push_stack EvidenceC (splitEv s0 st_ev0) st_stack0;
         st_trace := st_trace0 ++ [Term.split n st_pl0];
         st_pl := st_pl0;
         st_store := st_store0 |} =
              {| st_ev := st_ev1; st_stack := st_stack1; st_trace := st_trace1; st_pl := st_pl1; st_store := st_store1 |}).
      {
        simpl.
        cbn.
        unfold run_vm'.
        unfold execSt.
        rewrite H2.
        reflexivity.
      }
      
      erewrite <- run_vm_iff in H0.
      do_stack1 a.
      assumption.
      eassumption.
    }
    subst.
    
    
    unfold run_vm_fold in Heqp.
    rewrite fold_left_app in Heqp.
    rewrite gfds in Heqp.
    cbn in *.
    monad_unfold.
    simpl in *.

    vmsts.
    simpl in *.
    assert (
        fold_left
             (fun (a : VM unit) (b : AnnoInstr) (s : vm_st) =>
              match a s with
              | (Some _, s') => let '(b0, s'') := build_comp b s' in (b0, s'')
              | (None, s') => (None, s')
              end) (instr_compiler a) (fun s : vm_st => (Some tt, s))
             {|
             st_ev := splitEv s st_ev0;
             st_stack := push_stack EvidenceC (splitEv s0 st_ev0) st_stack0;
             st_trace := st_trace0 ++ [Term.split n st_pl0];
             st_pl := st_pl0;
             st_store := st_store0 |} =
        run_vm_fold (instr_compiler a)
         {|
             st_ev := splitEv s st_ev0;
             st_stack := push_stack EvidenceC (splitEv s0 st_ev0) st_stack0;
             st_trace := st_trace0 ++ [Term.split n st_pl0];
             st_pl := st_pl0;
             st_store := st_store0 |}) as HHH.
    {
      reflexivity.
    }
    rewrite HHH in Heqp. clear HHH.
    rewrite H2 in Heqp. clear H2.
    repeat break_let.
    repeat find_inversion.

    rewrite fold_left_app in Heqp2.
    cbn in *.
    repeat break_let.
    monad_unfold.
    vmsts.
    rewrite gfds in Heqp.
    cbn in *.
    monad_unfold.
    repeat break_let.

    repeat find_inversion.
    vmsts.

    edestruct IHt2 with
        (il:= instr_compiler a0)
        
        (st:= {|
            st_ev := splitEv s0 st_ev0;
            st_stack := push_stack EvidenceC st_ev1 st_stack0;
            st_trace := st_trace1;
            st_pl := st_pl1;
            st_store := st_store1 |}).
    reflexivity.
    symmetry.
    rewrite Heqp1.
    simpl.
    reflexivity.
    destruct_conjs.

    vmsts.
    assert (
        run_vm_fold (instr_compiler a0)
                    {|
            st_ev := splitEv s0 st_ev0;
            st_stack := push_stack EvidenceC st_ev1 st_stack0;
            st_trace := st_trace1;
            st_pl := st_pl1;
            st_store := st_store1 |} =
        fold_left
            (fun (a0 : VM unit) (b : AnnoInstr) (s : vm_st) =>
             match a0 s with
             | (Some _, s') => let '(b0, s'') := build_comp b s' in (b0, s'')
             | (None, s') => (None, s')
             end) (instr_compiler a0) (fun s : vm_st => (Some tt, s))
            {|
            st_ev := splitEv s0 st_ev0;
            st_stack := push_stack EvidenceC st_ev1 st_stack0;
            st_trace := st_trace1;
            st_pl := st_pl1;
            st_store := st_store1 |}) as HH.
    {
      reflexivity.
    }
      
    rewrite <- HH in Heqp8. clear HH.
    rewrite H0 in Heqp8.
    assert (push_stack EvidenceC st_ev1 st_stack0 = st_stack3).
    {
      Print do_stack1.
      Print run_vm'.
      assert (run_vm' (instr_compiler a0) {|
         st_ev := splitEv s0 st_ev0;
         st_stack := push_stack EvidenceC st_ev1 st_stack0;
         st_trace := st_trace1;
         st_pl := st_pl1;
         st_store := st_store1 |} =
              {| st_ev := st_ev4; st_stack := st_stack3; st_trace := st_trace4; st_pl := st_pl4; st_store := st_store4 |}).
      {
        simpl.
        cbn.
        unfold run_vm'.
        unfold execSt.
        
        rewrite H0.
        reflexivity.
      }
      
      erewrite <- run_vm_iff in H.
      do_stack1 a0.
      assumption.
      eassumption.
    }
    subst.
    clear H0.
    repeat find_inversion.
    repeat break_match;
      repeat find_inversion.
    eauto.

    unfold push_stack in *.
    unfold pop_stack in *.
    congruence.

  - (* abpar case *)
    subst.
    unfold run_vm_fold.
    cbn.
    monad_unfold.
    destruct s; destruct r.
    rewrite gfds.
    monad_unfold.
    repeat break_let.
    subst.
    monad_unfold.
    break_let.
    monad_unfold.
    simpl in *.
    vmsts.
    simpl in *.
    unfold Maps.map_set in *.
    
    unfold get_store_at in *.
    unfold get in *.
    simpl in *.
    assert (

        (st <- (fun s : vm_st => (Some s, s));;
         match Maps.map_get (StVM.st_store st) (fst (range t1)) with
         | Some e => ret e
         | None => failm
         end)
          {|
            st_ev := ppc (parallel_att_vm_thread (instr_compiler t1) (splitEv s st_ev2))
                         (parallel_att_vm_thread (instr_compiler t2) (splitEv s0 st_ev2));
            st_stack := st_stack2;
            st_trace := (st_trace2 ++ [Term.split n0 st_pl2]) ++
              shuffled_events (parallel_vm_events (instr_compiler t1) st_pl2)
                (parallel_vm_events (instr_compiler t2) st_pl2);
            st_pl := st_pl2;
            st_store := (fst (range t2), parallel_att_vm_thread (instr_compiler t2) (splitEv s0 st_ev2))
                          :: (fst (range t1), parallel_att_vm_thread (instr_compiler t1) (splitEv s st_ev2)) :: st_store2 |} =
        (Some (parallel_att_vm_thread (instr_compiler t1) (splitEv s st_ev2)), {|
            st_ev := ppc (parallel_att_vm_thread (instr_compiler t1) (splitEv s st_ev2))
                         (parallel_att_vm_thread (instr_compiler t2) (splitEv s0 st_ev2));
            st_stack := st_stack2;
            st_trace := (st_trace2 ++ [Term.split n0 st_pl2]) ++
              shuffled_events (parallel_vm_events (instr_compiler t1) st_pl2)
                (parallel_vm_events (instr_compiler t2) st_pl2);
            st_pl := st_pl2;
            st_store := (fst (range t2), parallel_att_vm_thread (instr_compiler t2) (splitEv s0 st_ev2))
                          :: (fst (range t1), parallel_att_vm_thread (instr_compiler t1) (splitEv s st_ev2)) :: st_store2 |})) as HH.
    {
      simpl.
      unfold bind.
      repeat break_let.
      unfold StVM.st_store in Heqp5.

      assert (
          Maps.map_get
              ((fst (range t2), parallel_att_vm_thread (instr_compiler t2) (splitEv s0 st_ev2))
                 :: (fst (range t1), parallel_att_vm_thread (instr_compiler t1) (splitEv s st_ev2)) :: st_store2) (fst (range t1)) =
          Some (parallel_att_vm_thread (instr_compiler t1) (splitEv s st_ev2))) as HH.
      {
        apply map_get_get_2.
        invc H.
        simpl in *.
        clear Heqp2.
        clear Heqp4.
        clear Heqp3.
        clear Heqp1.
        clear Heqp0.
        clear Heqp5.
        clear Heqp.

        eapply afaf.
        eassumption.
      }
      
      rewrite HH in Heqp5.
      simpl in Heqp5.
      unfold ret in Heqp5.
      repeat find_inversion.
      eauto.
    }
    rewrite HH in Heqp1. clear HH.
    break_let.

    assert (
        (st <- (fun s : vm_st => (Some s, s));;
             match Maps.map_get (StVM.st_store st) (fst (range t2)) with
             | Some e => ret e
             | None => failm
             end)
              {|
              st_ev := ppc (parallel_att_vm_thread (instr_compiler t1) (splitEv s st_ev2))
                         (parallel_att_vm_thread (instr_compiler t2) (splitEv s0 st_ev2));
              st_stack := st_stack2;
              st_trace := (st_trace2 ++ [Term.split n0 st_pl2]) ++
                          shuffled_events (parallel_vm_events (instr_compiler t1) st_pl2)
                            (parallel_vm_events (instr_compiler t2) st_pl2);
              st_pl := st_pl2;
              st_store := (fst (range t2), parallel_att_vm_thread (instr_compiler t2) (splitEv s0 st_ev2))
                            :: (fst (range t1), parallel_att_vm_thread (instr_compiler t1) (splitEv s st_ev2)) :: st_store2 |} =


        (Some (parallel_att_vm_thread (instr_compiler t2) (splitEv s0 st_ev2)),
          {|
              st_ev := ppc (parallel_att_vm_thread (instr_compiler t1) (splitEv s st_ev2))
                         (parallel_att_vm_thread (instr_compiler t2) (splitEv s0 st_ev2));
              st_stack := st_stack2;
              st_trace := (st_trace2 ++ [Term.split n0 st_pl2]) ++
                          shuffled_events (parallel_vm_events (instr_compiler t1) st_pl2)
                            (parallel_vm_events (instr_compiler t2) st_pl2);
              st_pl := st_pl2;
              st_store := (fst (range t2), parallel_att_vm_thread (instr_compiler t2) (splitEv s0 st_ev2))
                            :: (fst (range t1), parallel_att_vm_thread (instr_compiler t1) (splitEv s st_ev2)) :: st_store2 |})) as HH.
    {
      simpl.
      unfold bind.
      repeat break_let.
      unfold StVM.st_store in Heqp4.

      assert (
          Maps.map_get
              ((fst (range t2), parallel_att_vm_thread (instr_compiler t2) (splitEv s0 st_ev2))
                 :: (fst (range t1), parallel_att_vm_thread (instr_compiler t1) (splitEv s st_ev2)) :: st_store2) (fst (range t2)) =
          Some (parallel_att_vm_thread (instr_compiler t2) (splitEv s0 st_ev2))) as HH.
      {
        simpl.
        Search PeanoNat.Nat.eqb.
        rewrite PeanoNat.Nat.eqb_refl.
        reflexivity.
      }
      rewrite HH in Heqp4.
      simpl in Heqp4.
      unfold ret in Heqp4.
      repeat find_inversion.
      eauto.
    }
    rewrite HH in Heqp2. clear HH.
    repeat find_inversion.
    eauto.
Defined.

(*
Lemma run_vm_iff : forall il st z v,
    (run_vm_fold il) st = (Some z, v) -> 
    run_vm il st = run_vm' il st.
 *)

(*
Lemma run_vm_iff_helper : forall t il st, 
    il = (instr_compiler t) ->
    exists z v,
      (run_vm_fold il) st = (Some z, v).
*)

Lemma run_vm_iff_compiled : forall il st t t' n,
    il = instr_compiler t ->
    t = snd (anno t' n) ->
    run_vm il st = run_vm' il st.
Proof.
  intros.
  edestruct run_vm_iff_helper.
  eassumption.
  eassumption.
  destruct_conjs.
  eapply run_vm_iff.
  eassumption.
Defined.

Lemma run_vm_iff_compiled_corrolary : forall il st t t',
    il = instr_compiler t ->
    t = annotated t' ->
    run_vm il st = run_vm' il st.
Proof.
  intros.
  eapply run_vm_iff_compiled; eauto.
Defined.

Lemma corr_corr : forall il st t,
  il = instr_compiler (annotated t) ->
  run_vm il st = run_vm' il st.
Proof.
  intros.
  eapply run_vm_iff_compiled_corrolary; eauto.
Defined.
