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
(*
  induction il1; intros.
  - simpl in *.
    unfold run_vm_fold in H.
    monad_unfold.
    find_inversion.
    assumption.
  -
    simpl.
    monad_unfold.
    unfold run_vm_fold in H.
    Check newLem.
    cbn in H.
       
    unfold run_vm_fold.
    cbn.
    monad_unfold.
    unfold run_vm_fold in H.
    monad_unfold.

    simpl.
    cbn.
    unfold run_vm_fold.
    rewrite gfds in H.
    monad_unfold.
    break_let.
    destruct o.
    break_let.
    find_inversion.
    break_let.
    find_inversion.
    rewrite gfds in Heqp0.
    monad_unfold.
    break_let.
    find_inversion.
    rewrite gfds.
    monad_unfold.
    break_let.
    destruct o.
    break_let.
    break_let.
    find_inversion.
    rewrite <- Heqp3.
    find_inversion.
    destruct o0.
    rewrite gfds.
    cbn.
    break_let.
    rewrite <- H0.
    rewrite <- Heqp0.
    monad_unfold.
    rewrite Heqp0.
    admit.
    rewrite <- newLem.
    rewrite IHil1 with (il2:=il2) (st:=st) (st':=(snd(build_comp a st))) (x:=u).
    admit.
    break_let.
    inv H.
    rewrite <- newLem with (z:=x) (v:=st') in Heqp0.
    admit.
    monad_unfold.
    cbn in *.
    rewrite gfds in H.
    monad_unfold.
    break_let.
    destruct o.
    break_let.
    find_inversion.
    break_let.
    find_inversion.

    admit.
    rewrite <- H.
    unfold run_vm_fold.
    monad_unfold.
        
    reflexivity.
    apply H0.
    monad_unfold.
    cbn in H.
    simpl in H.
    rewrite gfds in H.
    monad_unfold.
    break_let.
    destruct o.
    break_let.
    invc H.
    break_let.
    symmetry.
    rewrite <- Heqp1.
    rewrite Heqp1.
    rewrite Heqp.
    reflexivity.
    destruct o.
    find_inversion.
    symmetry.
    apply Heqp1.
    erewrite <- Heqp.

    eapply IHil1.
*)     
Admitted.

Lemma run_vm_iff_helper : forall t il st, 
    il = (instr_compiler t) ->
    exists z v,
      (run_vm_fold il) st = (Some z, v).
Proof.
  induction t; intros.
  - simpl in *.
    destruct a;
      try (boom; allss; simpl in *; cbn; boom; allss).
  -
    boom; allss.
    destruct r.
    boom; allss.
    simpl.
    cbn.
    eauto.
  -
    simpl in *.
    subst.
    edestruct IHt1 with (st:=st).
    reflexivity.
    destruct_conjs.
    edestruct IHt2 with (st:=H).
    reflexivity.
    destruct_conjs.
    repeat eexists.


    eapply fold_destruct; eauto.
  -
    (*
    destruct IHt1 with (il:=instr_compiler t1) (st:=st); try reflexivity.
    destruct_conjs.
    destruct IHt2 with (il:=instr_compiler t2) (st:=H0); try reflexivity.
    destruct_conjs. *)
    simpl in *.
    destruct r; destruct s.
    cbn in *.
    simpl in *.
    subst.
    cbn.
    (*
    repeat eexists. *)
    simpl.
    unfold run_vm_fold.





    erewrite gfds.
    cbn.
    break_let.
    rewrite <- Heqp.
    clear Heqp.

    erewrite gfds.
    Print run_vm_fold.


    assert (
        fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b)
     (instr_compiler t1 ++
      abesr :: instr_compiler t2 ++ [ajoins (Nat.pred n0)]) 
     (ret tt) =
        run_vm_fold
          (instr_compiler t1 ++
                          abesr :: instr_compiler t2 ++ [ajoins (Nat.pred n0)])
      ) as HH.
    admit.
    rewrite HH.
    clear HH.
    assert (
        (instr_compiler t1 ++
                        abesr :: instr_compiler t2 ++ [ajoins (Nat.pred n0)]) =
         (instr_compiler t1 ++
                        [abesr] ++ instr_compiler t2 ++ [ajoins (Nat.pred n0)])
        ) as HH.
        
      
    admit.
    rewrite HH.
    clear HH.
    unfold bind.
    unfold ret.
    repeat break_let.
    rewrite app_assoc in Heqp.
    rewrite app_assoc in Heqp.
    assert (
        (((instr_compiler t1 ++ [abesr]) ++ instr_compiler t2) ++
            [ajoins (Nat.pred n0)]) =
        (instr_compiler t1 ++ ([abesr] ++ (instr_compiler t2 ++
                                                          ([ajoins (Nat.pred n0)]))))
      ) as HH.
    admit.
    rewrite HH in Heqp.
    clear HH.
    
    destruct IHt1 with (st:={|
    st_ev := splitEv s (st_ev st);
    st_stack := push_stack EvidenceC (splitEv s0 (st_ev st))
                  (st_stack (add_trace [Term.split n (st_pl st)] st));
    st_trace := st_trace (add_trace [Term.split n (st_pl st)] st);
    st_pl := st_pl (add_trace [Term.split n (st_pl st)] st);
    st_store := st_store (add_trace [Term.split n (st_pl st)] st) |}) (il:=instr_compiler t1).
    reflexivity.
    destruct_conjs.
    erewrite fold_destruct in Heqp.
    eauto.
    apply H0.
    cbn.
    rewrite gfds.
    unfold ret.
    monad_unfold.
    simpl in *.
    break_let.
    break_let.
    break_let.
    break_let.

    repeat break_match; simpl in *.
    repeat find_inversion.


    rewrite gfds in Heqp3.
    monad_unfold.
    break_let.
    assert (
        fold_left
            (fun (a0 : VM unit) (b : AnnoInstr) (s : vm_st) =>
             match a0 s with
             | (Some _, s') => let '(b0, s'') := build_comp b s' in (b0, s'')
             | (None, s') => (None, s')
             end) (instr_compiler t2 ++ [ajoins (Nat.pred n0)]) (fun s : vm_st => (Some tt, s))
            {|
            st_ev := e;
            st_stack := StVM.st_stack v7;
            st_trace := StVM.st_trace v7;
            st_pl := StVM.st_pl v7;
            st_store := StVM.st_store v7 |} =
        run_vm_fold (instr_compiler t2 ++ [ajoins (Nat.pred n0)])
            {|
            st_ev := e;
            st_stack := StVM.st_stack v7;
            st_trace := StVM.st_trace v7;
            st_pl := StVM.st_pl v7;
            st_store := StVM.st_store v7 |}).
    reflexivity.

    assert ( forall (a0:VM unit) s b,
         match a0 s with
             | (Some _, s') => let '(b0, s'') := build_comp b s' in (b0, s'')
             | (None, s') => (None, s')
         end =
    let (o2, s') := a0 s in match o2 with
                                  | Some _ => let '(b0, s'') := build_comp b s' in (b0, s'')
                                  | None => (None, s')
                            end).
    reflexivity.
    clear H2.
    rewrite H1 in Heqp0.
    clear H1.
    
    erewrite fold_destruct in Heqp0.
    find_inversion.
    find_inversion.
    unfold push_stackm in *.
    monad_unfold.
    break_let.
    break_let.
    find_inversion.
    find_inversion.
    unfold pop_stackm in *.
    monad_unfold.
    break_let.
    break_let.
    break_match.
    break_let.
    repeat find_inversion.
    unfold pop_stack in *.
    break_match.
    repeat find_inversion.
    inv Heqo2.
    repeat find_inversion.
    simpl in *.
    repeat find_inversion.
    destruct o4.
    repeat find_inversion.
    admit.
    inv H2.
    congruence.
    destruct IHt2 with (il:=instr_compiler t2) (st:={| st_ev := e; st_stack := StVM.st_stack v7; st_trace := StVM.st_trace v7; st_pl := StVM.st_pl v7; st_store := StVM.st_store v7 |}).
    reflexivity.
    destruct_conjs.
    admit.
    simpl.
    unfold run_vm_fold.
    cbn.
    repeat break_let.
    monad_unfold.
    repeat find_inversion.
    break_match.
    break_match.
    repeat find_inversion.
    admit.
    repeat find_inversion.
    unfold push_stackm in *.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    unfold pop_stackm in *.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    simpl in *.
    invc Heqv3.
    invc H1.
    invc H2.
    break_match.
    break_match.
    unfold pop_stack in *.
    break_match.
    inv Heqo1.
    repeat find_inversion.
    unfold pop_stack in *.
    break_match.
    repeat find_inversion.
    destruct st_stack2.
    inv Heqp3.
    repeat find_inversion.

    (*

    reflexivity.


    
    apply H2.
    reflexivity.



    
    admit.
    admit.
    admit.
    repeat find_inversion.
    repeat find_inversion.
    unfold push_stackm in *.
    monad_unfold.
    repeat break_let. congruence.
    repeat find_inversion.
    unfold push_stackm in *.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    symmetry in Heqp3.
    destruct H.
    unfold pop_stackm in *.
    monad_unfold.
    break_let.
    unfold pop_stack in *.
    break_match.
    break_let.
    find_inversion.
    inv Heqp0.
    find_inversion.
    find_inversion.
    break_match.
    subst.
    clear Heqo2.



    
    do_pop_stackm_fail.
    subst.
    rewrite gfds in Heqp5.
    monad_unfold.
    break_let.
    find_inversion.
    Check run_vm_fold.
    assert (
        fold_left
            (fun (a0 : VM unit) (b : AnnoInstr) (s : vm_st) =>
             match a0 s with
             | (Some _, s') => let '(b0, s'') := build_comp b s' in (b0, s'')
             | (None, s') => (None, s')
             end) (instr_compiler t2 ++ [ajoins (Nat.pred n0)]) (ret tt) {| st_ev := st_ev0; st_stack := []; st_trace := st_trace0; st_pl := st_pl0; st_store := st_store1 |} = 

        run_vm_fold (instr_compiler t2 ++ [ajoins (Nat.pred n0)]) {| st_ev := st_ev0; st_stack := []; st_trace := st_trace0; st_pl := st_pl0; st_store := st_store1 |}) as HHH.
    reflexivity.
    fold (run_vm_fold (instr_compiler t2 ++ [ajoins (Nat.pred n0)])
          {| st_ev := st_ev0; st_stack := []; st_trace := st_trace0; st_pl := st_pl0; st_store := st_store1 |}) in Heqp0.
    unfold run_vm_fold.
    reflexivity.
    rewrite HHH in Heqp0.
    erewrite fold_destruct in Heqp0.



    
    boom; allss.
    rewrite <- Heqp4.

    unfold push_stackm in *.
    monad_unfold.
    repeat find_inversion.

    admit.



    
    unfold put_ev in *.
    monad_unfold.
    repeat find_inversion.
    reflexivity.


    
    rewrite fold_destruct in H
    apply fold_destruct with (st':=H0) (x:=x).

    apply H0.
    cbn.
    repeat break_let.
    rewrite <- Heqp0.
    rewrite <- Heqp1.
    monad_unfold.
    repeat break_match.
    boom; allss.
    reflexivity.
    destruct x.
    allss.
    monad_unfold.
    unfold push_stackm in *.
    monad_unfold.
    find_inversion.
    reflexivity.
    
    reflexivity.
    

    
    monad_unfold.
    simpl.
    
    repeat break_let.
    repeat break_match.
    repeat find_inversion.
    repeat find_inversion.
    reflexivity.



    
    unfold bind.
    unfold ret.
    repeat break_let.
    invc Heqp.
    boom; allss.
    rewrite <- app_assoc.
    
    
    erewrite fold_destruct.
    
    monad_unfold.
    repeat break_let.
    simpl in *.
    repeat break_let.
    cbn.
    simpl in Heqp.
    Check run_vm_fold.
    Print run_vm_fold.
    Check run_vm.
    Print run_vm.
    Check run_vm_fold.
    assert (
        fold_left
           (fun (a0 : VM unit) (b : AnnoInstr) (s : vm_st) =>
            match a0 s with
            | (Some _, s') => let '(b0, s'') := build_comp b s' in (b0, s'')
            | (None, s') => (None, s')
            end)
           (instr_compiler t1 ++
            abesr :: instr_compiler t2 ++ [ajoins (Nat.pred n0)])
            =
        run_vm_fold
          (instr_compiler t1 ++
            abesr :: instr_compiler t2 ++ [ajoins (Nat.pred n0)])
           ).
    


    
    simpl in *.
    cbn in *.
    break_let.
    simpl in *.
    
    


    
    cbn in *.
    unfold run_vm_fold.
    rewrite H.
    unfold ret.
    unfold bind.
    
    
    + simpl in *.
      subst.
      simpl in *.
      cbn.
      boom; allss.
      break_let.
      break_let.
      find_inversion.
      monad_unfold.
      repeat break_let.
      allss.
    
  intros.
*) 
Admitted.


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

Lemma run_vm_iff_compiled : forall il st t,
    il = instr_compiler t -> 
    (*(run_vm_fold il) st = (Some z, v) ->  *)
    run_vm il st = run_vm' il st.
Proof.
  intros.
  edestruct run_vm_iff_helper.
  apply H.
  destruct_conjs.
  eapply run_vm_iff.
  apply H1.
Defined.
