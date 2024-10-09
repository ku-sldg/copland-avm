(*
Alternative ("big-step") definition of run_vm + proof that it corresponds to the one in VmSemantics.v.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Preamble GenStMonad MonadVM Instr VmSemantics MyStack ConcreteEvidenceT MonadLaws.
Require Import Event_system More_lists LTS Term Term_system.
Require Import StructTactics.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics.

Lemma hfhf : forall (act1 act2:VM unit) st il,
    (act1;;
     (fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                act2)) st =
    (act1;; (act2 ;;
            (fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il
                       (ret tt)))) st.
Proof.
  intros.
  generalize dependent act1.
  generalize dependent act2.
  generalize dependent st.
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
      (((act1;; act2;; build_comp a);; ret tt);;
       fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il (ret tt)) st =
      ((act1;; act2;; build_comp a);; ret tt;; fold_left (fun (a0 : VM unit) (b : AnnoInstr) => a0;; build_comp b) il (ret tt)) st).
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

(* Not provable, act1 could fail *)
(*
Lemma fads : forall (act1:VM unit) act2 il st v o,
    act1 st = (o, v) ->
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
    destruct o0.
    + simpl.
      break_let.
      repeat find_inversion.
      rewrite <- Heqp.
      rewrite gfds.
      destruct v1.
      simpl.
      cbn.
      break_let.
      destruct v.
      cbn.
      rewrite gfds.
      unfold bind.
      rewrite Heqp0.
      break_let.
      unfold bind in Heqp1.
      congruence.
    + congruence.
  - repeat find_inversion.
    break_match.
    break_match.
    repeat break_let.
    repeat find_inversion.
    rewrite gfds.
    unfold bind.
    rewrite Heqp0.
    repeat break_let.
    unfold ret in Heqp.
    congruence.
    + repeat find_inversion.
      rewrite gfds.
      unfold bind.
      rewrite Heqp0.
      reflexivity.
  - break_match.
    break_match.
    repeat break_let.
    repeat find_inversion.
    rewrite gfds.
    unfold bind.
    rewrite Heqp0.
    repeat break_let.
    unfold ret in *.
    rewrite gfds in Heqp.
    unfold bind in Heqp.
    repeat break_let.
    repeat find_inversion.
    congruence.
    
      
    
    
      
      
      rewrite <- Heqp0.


    
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
*)

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



    (*
    assert (build_comp a st = (None, v0)).
    admit.
    clear Heqaaa.
    unfold bind.
    unfold ret.
    rewrite gfds.
    cbn.
    break_let.
    simpl.

    destruct st.
    simpl.

    assert (
        (fun s : vm_st =>
     match build_comp a s with
     | (Some _, s') => (Some tt, s')
     | (None, s') => (None, s')
     end)
    {|
    st_ev := st_ev;
    st_stack := st_stack;
    st_trace := st_trace;
    st_pl := st_pl;
    st_store := st_store |}



        =
    match build_comp  a {|
    st_ev := st_ev;
    st_stack := st_stack;
    st_trace := st_trace;
    st_pl := st_pl;
    st_store := st_store |}  with
     | (Some _, s') => (Some tt, s')
     | (None, s') => (None, s')
    end) as HH by auto.
    repeat break_let.
    destruct o1; destruct o0; find_inversion.
    find_inversion.

    clear Heqp0.
    simpl.
    rewrite <- Heqp.
    rewrite gfds.
    unfold ret.
    unfold bind.
    repeat break_let.
    repeat find_inversion.
    rewrite gfds.
    simpl.
    cbn.
    unfold bind.
    rewrite Heqp1.
    unfold bind in Heqp.
    unfold ret in Heqp.
    rewrite Heqp in Heqp0.
    repeat find_inversion.
    rewrite <- HH.
     *)
    
   







    
    
    erewrite fads.
    reflexivity.
    symmetry.
    eassumption.
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
    congruence.
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
    repeat rewrite gfds in *.
    monad_unfold.
    break_let.
    simpl.
    cbn.
    (* rewrite gfds. *)
    monad_unfold.
    break_let.
    break_match.
    break_let.
    break_let.
    repeat find_inversion.
    congruence.
    repeat find_inversion.
    eauto.
    (*
    break_let.
    congruence.
    repeat find_inversion.
    eauto. *)

    break_let.
    repeat find_inversion.
    rewrite gfds in H.
    monad_unfold.
    repeat break_let.
    find_inversion.
    destruct o.
    inv Heqp.
    inv H.
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
    repeat break_let.
    monad_unfold.
    unfold get_store_at in *.
    monad_unfold.
    rewrite PeanoNat.Nat.eqb_refl in *.
    allss.
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
           st_stack := push_stack EvidenceTC (splitEv s0 st_ev0) st_stack0;
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
        push_stack EvidenceTC (splitEv s0 st_ev0) st_stack0 =
        st_stack1) as HH.
    {
      Print do_stack1.
      Print run_vm'.
      assert (run_vm' (instr_compiler a) {|
         st_ev := splitEv s st_ev0;
         st_stack := push_stack EvidenceTC (splitEv s0 st_ev0) st_stack0;
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
             st_stack := push_stack EvidenceTC (splitEv s0 st_ev0) st_stack0;
             st_trace := st_trace0 ++ [Term.split n st_pl0];
             st_pl := st_pl0;
             st_store := st_store0 |} =
        run_vm_fold (instr_compiler a)
         {|
             st_ev := splitEv s st_ev0;
             st_stack := push_stack EvidenceTC (splitEv s0 st_ev0) st_stack0;
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
            st_stack := push_stack EvidenceTC st_ev1 st_stack0;
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
            st_stack := push_stack EvidenceTC st_ev1 st_stack0;
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
            st_stack := push_stack EvidenceTC st_ev1 st_stack0;
            st_trace := st_trace1;
            st_pl := st_pl1;
            st_store := st_store1 |}) as HH.
    {
      reflexivity.
    }
      
    rewrite <- HH in Heqp8. clear HH.
    rewrite H0 in Heqp8.
    assert (push_stack EvidenceTC st_ev1 st_stack0 = st_stack3).
    {
      Print do_stack1.
      Print run_vm'.
      assert (run_vm' (instr_compiler a0) {|
         st_ev := splitEv s0 st_ev0;
         st_stack := push_stack EvidenceTC st_ev1 st_stack0;
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

Theorem vm_ordered_alt : forall t tr ev0 ev1 e e' s s' o o' t',
    t = annotated t' -> 
    run_vm'
      (instr_compiler t)
      (mk_st e s [] 0 o) =
      (mk_st e' s' tr 0 o') ->
    prec (ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  eapply vm_ordered; eauto.
  erewrite corr_corr; eauto.
  rewrite H.
  auto.
Defined.
