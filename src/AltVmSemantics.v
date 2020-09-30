Require Import More_lists Preamble Term ConcreteEvidence LTS GenStMonad.
Require Import Instr MyStack MonadVM MonadVMFacts RunAlt.

Require Import Main Event_system Term_system.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import StructTactics.


Set Nested Proofs Allowed.

(** IO Axioms *)

Definition remote_events (t:AnnoTerm) (p:Plc) : (list Ev).
Admitted.

Definition parallel_att_vm_thread (li:list AnnoInstr) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_vm_events (li:list AnnoInstr) (p:Plc) : list Ev.
Admitted.

Definition shuffled_events (el1:list Ev) (el2:list Ev) : list Ev.
Admitted.

Definition build_comp (i:AnnoInstr): VM unit :=
  match i with
  | aprimInstr x a =>
    p <- get_pl ;;
    e <- do_prim x p a ;;
    put_ev e           
  | asplit x sp1 sp2 =>
    e <- get_ev ;;
      p <- get_pl ;;
      pr <- split_evm x sp1 sp2 e p;;
      let '(e1,e2) := pr in
      put_ev e1 ;;
      push_stackm e2
  | ajoins i =>
    e <- get_ev ;;
      p <- get_pl ;;
      er <- pop_stackm ;;
      put_ev (ssc er e) ;;
      add_tracem [Term.join i p]
  | ajoinp i loc1 loc2 =>
    p <- get_pl ;;
      e1 <- get_store_at loc1 ;;
      e2 <- get_store_at loc2 ;;
      add_tracem [Term.join i p] 
  | abesr =>
    e <- get_ev ;;
      er <- pop_stackm ;;
      push_stackm e ;;
      put_ev er    
  | areqrpy reqi rpyi q annt =>
    e <- get_ev ;;
      put_ev (toRemote (unanno annt) q e) ;;
      (* put_store reqi (toRemote (unanno annt) q e) ;; *)
      (* TODO: make this contingent on a good remote setup.  Need to model such a situation *)
      p <- get_pl ;;
      let newTrace :=
          [req reqi p q (unanno annt)] ++
          (remote_events annt q) ++
          [rpy (Nat.pred rpyi) p q] in
      (* TODO: move remote_events annt q trace to get_store_at, models successful remote execution *)
      add_tracem newTrace
  | abep loc1 loc2 il1 il2 =>
    e <- get_ev ;;
      p <- get_pl ;;
      er <- pop_stackm ;;
      let res1 := parallel_att_vm_thread il1 e in
      let res2 := parallel_att_vm_thread il2 er in
      let el1 := parallel_vm_events il1 p in
      let el2 := parallel_vm_events il2 p in
      put_store loc1 res1 ;;
                put_store loc2 res2 ;;
                put_ev (ppc res1 res2) ;;
                add_tracem (shuffled_events el1 el2)
     (* TODO:  axioms asserting we had valid VM threads available to execute them *)
  end.

(*
(** Function-style semantics for VM *)

(* Transform vm_st for a single instruction (A -> B -> A) function for fold_left *)
Definition run_vm_step (a:vm_st) (b:AnnoInstr) : vm_st :=
  execSt a (build_comp b).

Definition run_vm (il:list AnnoInstr) st : vm_st :=
  fold_left (run_vm_step) il st.

Definition run_vm_t (t:AnnoTerm) st : vm_st :=
  run_vm (instr_compiler t) st.
*)

Lemma st_congr :
  forall st tr e p s o,
    st_ev st = e ->
    st_stack st = s ->
    st_trace st = tr ->
    st_pl st = p ->
    st_store st = o ->
    st =  {| st_ev := e; st_trace := tr; st_stack := s; st_pl := p; st_store := o |}.
Proof.
  intros.
  subst; destruct st; auto.
Defined.

Ltac unfoldm :=  repeat unfold run_vm' in *; monad_unfold.

Ltac boom :=
  repeat unfoldm;
  repeat (desp; unfoldm);
  try_pop_all;
  vmsts.

Ltac do_run :=
  match goal with
  | [H:  run_vm' (_ :: _) _ = _ |- _ ] => invc H; unfold run_vm' in *; repeat monad_unfold
  end.

Ltac do_flip :=
  match goal with
  | [H: (pop_stackm _ = _) |- _ ] =>
    (*idtac "doing pop_stackm flip"; *)
    symmetry in H
  end.

Ltac allss :=
  repeat find_inversion;
  try bogus;
  repeat (do_get_store_at_facts; subst; eauto);
  repeat (do_get_store_at_facts_fail; subst; eauto);
  repeat do_flip;
  repeat do_pop_stackm_facts;
  repeat do_pop_stackm_fail;
  repeat get_store_at_bogus;
  try do_bd;
  subst; eauto.

Print do_bd.

(* Starting trace has no effect on store *)
Lemma trace_irrel_store : forall il1 tr1 tr1' tr2 e e' s s' p1' p1 o' o,
    run_vm' il1
           {| st_ev := e;  st_trace := tr1;  st_stack := s;  st_pl := p1;  st_store := o  |} =
           {| st_ev := e'; st_trace := tr1'; st_stack := s'; st_pl := p1'; st_store := o' |} ->
    
    st_store (
        run_vm' il1
           {| st_ev := e;  st_trace := tr2;  st_stack := s;  st_pl := p1;  st_store := o  |}) = o'.
Proof.
  induction il1; intros.
  - simpl.
    inv H. reflexivity.   
  - simpl; destruct a;
          try destruct p;
          try destruct r;
          boom;
          subst; eauto;
          repeat monad_unfold;
          repeat break_match;
          allss.
    + simpl.
      erewrite <- IHil1.
      unfold run_vm_fold in *.
      cbn in *.
      monad_unfold.
      eauto.
      unfold snd in *.
      cbn in *.
      simpl in *.
      repeat break_let.
      cbn in *.
      simpl in *.
      rewrite gfds in *.
      simpl in *.
      cbn in *.
      repeat break_let.
      repeat find_inversion.
      rewrite Heqp2 in Heqp3.
      congruence.
      simpl in H.
      unfold run_vm_fold in *.
      unfold snd in *.
      repeat break_let.
      vmsts.
      repeat find_inversion.
      monad_unfold.
      simpl in *.
      rewrite gfds in *.
      simpl in *.
      cbn in *.
      repeat break_let.

      repeat find_inversion.
      rewrite Heqp1 in Heqp2.
      invc Heqp2.
      
      reflexivity.
    +
      cbn in *.
      unfold run_vm_fold in *.
      erewrite <- IHil1.
      rewrite gfds in *.
      monad_unfold.
      unfold snd in *.
      repeat break_let.
      repeat find_inversion.
      rewrite Heqp3 in *.
      congruence.
     
      rewrite gfds in *.
      monad_unfold.
      unfold snd in *.
      repeat break_let.
      repeat find_inversion.
      rewrite Heqp2 in *.
      repeat find_inversion.
      reflexivity.


    +
      cbn in *.
      unfold run_vm_fold in *.
      erewrite <- IHil1.
      rewrite gfds in *.
      monad_unfold.
      unfold snd in *.
      repeat break_let.
      repeat find_inversion.
      rewrite Heqp3 in *.
      congruence.
     
      rewrite gfds in *.
      monad_unfold.
      unfold snd in *.
      repeat break_let.
      repeat find_inversion.
      rewrite Heqp2 in *.
      repeat find_inversion.
      reflexivity.
    +
      cbn in *.
      unfold run_vm_fold in *.
      erewrite <- IHil1.
      rewrite gfds in *.
      monad_unfold.
      unfold snd in *.
      repeat break_let.
      repeat find_inversion.
      rewrite Heqp3 in *.
      congruence.
     
      rewrite gfds in *.
      monad_unfold.
      unfold snd in *.
      repeat break_let.
      repeat find_inversion.
      rewrite Heqp2 in *.
      repeat find_inversion.
      reflexivity.
    +
      cbn in *.
      unfold run_vm_fold in *.
      erewrite <- IHil1.
      rewrite gfds in *.
      monad_unfold.
      unfold snd in *.
      repeat break_let.
      repeat find_inversion.
      rewrite Heqp3 in *.
      congruence.
     
      rewrite gfds in *.
      monad_unfold.
      unfold snd in *.
      repeat break_let.
      repeat find_inversion.
      rewrite Heqp2 in *.
      repeat find_inversion.
      reflexivity.
    + 
      
Abort.

(*
(* Starting trace has no effect on evidence *)
Lemma trace_irrel_ev : forall il1 tr1 tr1' tr2 e e' s s' p1' p1 o1 o1',
    run_vm il1 {| st_ev := e; st_trace := tr1; st_stack := s; st_pl := p1; st_store := o1 |} =
    {| st_ev := e'; st_trace := tr1'; st_stack := s'; st_pl := p1'; st_store := o1' |} ->
    
    st_ev (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_stack := s; st_pl := p1; st_store := o1 |}) = e'.
Proof.
    induction il1; intros.
  - simpl.
    inv H. reflexivity.   
  - simpl; destruct a;
          try destruct p0;
          try destruct r;
          boom;
          subst; eauto;
            repeat monad_unfold;
            repeat break_match;
            allss.
Defined.

(* Starting trace has no effect on place *)
Lemma trace_irrel_place : forall il1 tr1 tr1' tr2 e e' s s' p p' o o',
    run_vm il1 {| st_ev := e; st_trace := tr1; st_stack := s; st_pl := p; st_store := o |} =
    {| st_ev := e'; st_trace := tr1'; st_stack := s'; st_pl := p'; st_store := o' |} ->
    
    st_pl (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_stack := s; st_pl := p; st_store := o |}) = p'.
Proof.
    induction il1; intros.
  - simpl.
    inv H. reflexivity.   
  - simpl; destruct a;
      try destruct p0;
      try destruct r;
      boom;
      subst; eauto;
        repeat monad_unfold;
        repeat break_match;
        allss.
Defined.

(* Starting trace has no effect on stack *)
Lemma trace_irrel_stack : forall il1 tr1 tr1' tr2 e e' s s' p1 p1' o1 o1',
    run_vm il1 {| st_ev := e; st_trace := tr1; st_stack := s; st_pl := p1'; st_store := o1' |} =
    {| st_ev := e'; st_trace := tr1'; st_stack := s'; st_pl := p1; st_store := o1 |} ->
    
    st_stack (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_stack := s; st_pl := p1'; st_store := o1' |}) =
    s'.
Proof.
    induction il1; intros.
  - simpl.
    inv H. reflexivity.   
  - simpl; destruct a;
      try destruct p0;
      try destruct r;
      boom;
      subst; eauto;
        repeat monad_unfold;
        repeat break_match;
        allss.
Defined.
*)


(* A distributive property of st_trace.  Says we can pull the front of a starting trace (m) outside and prepend it to a st_trace call with the rest of the original starting trace (k) as the starting trace *)
Lemma gen_foo : forall il m k e s p o,
    st_trace (
        snd (
            (fold_left  (fun (a0:VM unit) (b:AnnoInstr) => a0 ;; (VmSemantics.build_comp b)) il (ret tt))
              {| st_ev := e; st_trace := m ++ k;  st_stack := s; st_pl := p; st_store := o |})) =
    m ++ st_trace (
        snd (
            (fold_left  (fun (a0:VM unit) (b:AnnoInstr) => a0 ;; (VmSemantics.build_comp b)) il (ret tt))
              {| st_ev := e; st_trace := k; st_stack := s; st_pl := p; st_store := o |})).
Proof.
  induction il; simpl; intros m k e s p o.
  - auto.
  - destruct a as [n p0 | n sp1 sp2 | n | l m' n | | | i q t (*| i rpyi q*)];
      try ( (* aprim, asplit, areqrpy, ajoinp cases *)
          try destruct r;
          try (unfold run_vm_step; fold run_vm_step);
          repeat monad_unfold; repeat break_match;
          boom; repeat allss;
          rewrite IHil at 1;
          symmetry; 
          rewrite IHil at 1);
      try (rewrite <- app_assoc at 1; congruence)(*;
      try (rewrite app_assoc at 1; congruence)*);

      try ( (* ajoins, abesr, abep, cases *)
          try destruct r;
          try (unfold run_vm_step; fold fun_vm_step);
          repeat monad_unfold; repeat break_match;
          boom; repeat allss;
          rewrite IHil at 1;
          symmetry;
          rewrite IHil at 1;
          rewrite app_assoc at 1;
          congruence).
    + simpl.
      destruct p0.
      ++
        rewrite gfds.
        rewrite gfds.
        unfold bind.
        unfold ret.
        repeat break_let.
        repeat find_inversion.
        unfold get_pl in *.
        unfold bind in Heqp2.
        unfold get in Heqp2.
        cbn in Heqp2.
        invc Heqp2.
        cbn in Heqp1.
        invc Heqp1.
        simpl.
        unfold bind in Heqp6.
        unfold get in Heqp6.
        cbn in Heqp6.
        invc Heqp6.
        cbn in Heqp5.
        invc Heqp5.
        simpl.
        unfold snd in IHil.
        cbn in IHil.
Abort.

(*

        rewrite gfds in IHil.
        erewrite IHil.
        unfold bind.
        unfold ret.
        unfold snd.
        repeat break_let.
        simpl in *.
        repeat find_inversion.
        monad_unfold.
        repeat find_inversion.


        
        simpl.
        cbn.
        simpl.
        cbn.
        unfold snd.
        simpl.
        cbn.
        break_let.
        break_let.
        break_let.
        break_let.
        repeat find_inversion.
        vmsts.
        simpl.
        unfold snd in IHil.
        cbn in IHil.
        pairs.
        eauto.
        erewrite <- IHil in *.
        break_let.
        monad_unfold.
        repeat break_let.
        simpl.
      unfold snd in *.
      repeat break_let.
      cbn in *.
      simpl in *.
      rewrite gfds in *.
      monad_unfold.
      repeat break_let.
      rewrite gfds in *.
      repeat find_inversion.
      simpl in *.
      
      eauto.
     
      
Defined.
*)

(* Instance of gen_foo where k=[] *)
Lemma foo : forall il m e s p o,
    st_trace (fold_left (run_vm_step) il
                        {| st_ev := e; st_trace := m;  st_stack := s; st_pl := p; st_store := o |}) =
    m ++ st_trace (fold_left (run_vm_step) il
                        {| st_ev := e; st_trace := []; st_stack := s; st_pl := p; st_store := o |}).
Proof.
  intros.
  assert (m = m ++ []) as H. rewrite app_nil_r. auto.
  rewrite H at 1.
  eapply gen_foo.
Defined.

Lemma compile_not_empty :
  forall t,
    (instr_compiler t) <> [].
Proof.
  intros.
  induction t;
    try destruct a;
    try destruct r;
    try destruct s;
    simpl; try congruence.
  - simpl.
    destruct (instr_compiler t1); simpl; congruence.
Defined.

(* Congruence lemmas for Copland LTS semantics *)
Lemma lstar_stls :
  forall st0 st1 t tr,
    lstar st0 tr st1 -> lstar (ls st0 t) tr (ls st1 t).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Qed.

Lemma lstar_strem : forall st st' tr p r,
    lstar st tr
          st' ->
    lstar (rem r p st) tr (rem r p st').
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.

Lemma lstar_stbsl:
  forall st0 st1 j t p e tr,
    lstar st0 tr st1 ->
    lstar (bsl j st0 t p e) tr (bsl j st1 t p e).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.

Lemma lstar_stbsr:
  forall st0 st1 j e tr,
    lstar st0 tr st1 ->
    lstar (bsr j e st0) tr (bsr j e st1).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.

(*
Lemma star_stbp:
  forall st0 st1 st2 st3 j,
    star st0 st1 ->
    star st2 st3 ->
    star (bp j st0 st2) (bp j st1 st3).
Proof.
  intros.
  induction H; auto.
  - induction H0; auto.
    eapply star_tran; eauto.
  - eapply star_tran; eauto.
Qed.*)


Lemma put_ev_after_immut_stack{A:Type} : forall s (h:VM A) e,
    st_stack (execSt s h) = st_stack (execSt s (h ;; (put_ev e))).
Proof.
  intros.
  unfold put_ev.
  unfold execSt.
  destruct s.
  unfold snd.
  monad_unfold.
  destruct (h {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace |}).
  destruct o; eauto.
Defined.

(*
Lemma update_ev_immut_stack'{A:Type} : forall s (h:VM A) e,
    st_stack (execSt s h) = st_stack (execSt s ((put_ev e);; h)).
Proof.
Abort.
*)  (* NOT true for arbitrary h:  h could match on e to update its stack *)


Lemma ssc_inv : forall e1 e1' e2 e2',
    e1 = e1' ->
    e2 = e2' ->
    ssc e1 e2 = ssc e1' e2'.
Proof.
  intros.
  congruence.
Defined.

Axiom para_eval_vm : forall t e,
    parallel_eval_thread (unanno t) e = parallel_att_vm_thread (instr_compiler t) e.

Lemma record_congr :
  forall A,
    A =
    {| st_ev := st_ev A;
       st_stack := st_stack A;
       st_trace := st_trace A;
       st_pl := st_pl A;
       st_store := st_store A|}.
Proof.
  intros A.
  destruct A.
  reflexivity.
Defined.

Ltac st_equiv :=
  match goal with
  | |- _ ++ _ ++ _ ++
        st_trace (fold_left _ _ ?st1) =
      _ ++ _ ++ _ ++
        st_trace (fold_left _ _ ?st2) =>
    (*idtac "matched" ;*)
    assert (st1 = st2)
      by (
          eapply st_congr; simpl;
          try (try erewrite trace_irrel_ev;
               try erewrite trace_irrel_stack;
               try erewrite trace_irrel_store;
               try reflexivity;
               rewrite <- record_congr; reflexivity))  
  end.

Lemma st_trace_destruct' :
  forall il1 il2 e s m p o,
    st_trace
      (fold_left run_vm_step il2
                 (fold_left run_vm_step il1
                            {| st_ev := e;
                               st_stack := s;
                               st_trace := m;
                               st_pl := p;
                               st_store := o|})) =
    m ++ 
    st_trace
      (fold_left run_vm_step il1 
                 {| st_ev := e;
                    st_stack := s;
                    st_trace := [];
                    st_pl := p;
                    st_store := o |}) ++
      st_trace
      (fold_left run_vm_step il2
                 {| st_ev :=
                      (st_ev
                         (fold_left run_vm_step il1 
                           {| st_ev := e; st_stack := s; st_trace := [];
                               st_pl := p; st_store := o |}));
                    st_stack :=
                      (st_stack
                         (fold_left run_vm_step il1 
                           {| st_ev := e; st_stack := s; st_trace := [];
                              st_pl := p; st_store := o |}));
                    st_trace := [];
                    st_pl := p;
                    st_store :=
                      (st_store
                         (fold_left run_vm_step il1 
                                    {| st_ev := e; st_stack := s; st_trace := [];
                                       st_pl := p; st_store := o |}));|}).
Proof.
  induction il1; try reflexivity; intros.
  - simpl.
    erewrite foo.
    reflexivity.
  - simpl.
    Check foo.
    destruct a as [n p0 | n sp1 sp2 | n | l m' n | | i q t (*| i rpyi q*) | l m' ls1 ls2];
      try (  (* apriminstr, asplit, reqrpy cases *)
          try destruct r;
          unfold run_vm_step; fold run_vm_step;
          monad_unfold;
          rewrite foo;
          rewrite <- app_assoc;
          rewrite IHil1;
          rewrite <- app_assoc;
          st_equiv;
          congruence);
      try (boom; allss);
      try (
          boom; repeat break_match; allss;
          rewrite foo;
          rewrite IHil1;
          repeat rewrite <- app_assoc;
          st_equiv;
          rewrite H;
          eauto).
Defined.

Lemma pl_immut : forall il e s tr p o,
    st_pl
      (fold_left run_vm_step il
                 {|
                   st_ev := e;
                   st_stack := s;
                   st_trace := tr;
                   st_pl := p;
                   st_store := o |}) = p.
Proof.
  induction il; intros.
  - simpl. reflexivity.
  -
    destruct a as [n p0 | n sp1 sp2 | n | l m n | | | i q t (*| i rpyi q*)];
      try (boom; repeat break_match; allss).
Defined.

Lemma trace_under_st_ev : forall il1 e s trd trd' p o,
    StVM.st_ev
      (fold_left run_vm_step il1
                 {|
                   st_ev := e;
                   st_stack := s;
                   st_trace := trd;
                   st_pl := p;
                   st_store := o |}) =
    StVM.st_ev
      (fold_left run_vm_step il1
                 {|
                   st_ev := e;
                   st_stack := s;
                   st_trace := trd';
                   st_pl := p;
                   st_store := o |}).
Proof.
  intros.
  erewrite trace_irrel_ev; eauto.
  eapply st_congr; eauto.
Defined.

Lemma trace_under_st_stack : forall il1 e s trd trd' p o,
    StVM.st_stack
      (fold_left run_vm_step il1
                 {|
                   st_ev := e;
                   st_stack := s;
                   st_trace := trd;
                   st_pl := p;
                   st_store := o |}) =
    StVM.st_stack
      (fold_left run_vm_step il1
                 {|
                   st_ev := e;
                   st_stack := s;
                   st_trace := trd';
                   st_pl := p;
                   st_store := o |}).
Proof.
  intros.
  erewrite trace_irrel_stack; eauto.
  eapply st_congr; eauto.
Defined.
    
Lemma trace_under_st_store : forall il1 e s trd trd' p o,
    StVM.st_store
      (fold_left run_vm_step il1
                 {|
                   st_ev := e;
                   st_stack := s;
                   st_trace := trd;
                   st_pl := p;
                   st_store := o |}) =
    StVM.st_store
      (fold_left run_vm_step il1
                 {|
                   st_ev := e;
                   st_stack := s;
                   st_trace := trd';
                   st_pl := p;
                   st_store := o |}).
Proof.
  intros.
  erewrite trace_irrel_store; eauto.
  eapply st_congr; eauto.
Defined.

Lemma destruct_compiled_appended : forall trd trd' il1 il2 e e'' s s'' p p'' o o'',
    run_vm
      (il1 ++ il2)
        {| st_ev := e;   st_stack := s;   st_trace := trd; st_pl := p; st_store := o |} =
        {| st_ev := e''; st_stack := s''; st_trace := trd'; st_pl := p''; st_store := o''  |} ->
    (exists tr1 e' s' p' o',
        run_vm
          (il1)
          {| st_ev := e;  st_stack := s;  st_trace := trd; st_pl := p; st_store := o  |} =
          {| st_ev := e'; st_stack := s'; st_trace := tr1; st_pl := p'; st_store := o'  |} /\
        exists tr2,
          run_vm
            (il2)
            {| st_ev := e';  st_stack := s';  st_trace := tr1; st_pl := p'; st_store := o' |} =
            {| st_ev := e''; st_stack := s''; st_trace := tr1 ++ tr2; st_pl := p''; st_store := o''  |} /\
          trd' = tr1 ++ tr2).
Proof.
  intros.
  remember (run_vm (il1) {| st_ev := e; st_stack := s; st_trace := trd; st_pl := p |}) as A.
  
  exists (st_trace A).
  exists (st_ev A).
  exists (st_stack A).
  exists (st_pl A).
  exists (st_store A).
  Check st_congr.

  split; try apply record_congr.
  -
    remember (run_vm (il2)
                     {| st_ev := st_ev A;
                        st_stack := st_stack A;
                        st_trace := st_trace A;
                        st_pl := st_pl A;
                        st_store := st_store A|}) as B.
    
  exists (st_trace (run_vm (il2)
                      {| st_ev := st_ev A;
                         st_stack := st_stack A;
                         st_pl := p;
                         st_trace := [];
                         st_store := st_store A |})).
  rewrite HeqB.
  rewrite HeqA.
  unfold run_vm in *.
  Check record_congr.
  
  rewrite <- record_congr.

  rewrite <- fold_left_app.
  rewrite foo.
  destruct A; unfold run_vm.
  Check trace_irrel_ev.
  simpl in HeqB.
  destruct B.
  Check trace_under_st_ev.


  erewrite trace_under_st_ev. (*with (trd':=[]).*)
  erewrite trace_under_st_stack.
  erewrite trace_under_st_store.
  
  split.
  +
    rewrite <- app_assoc.
    Check st_trace_destruct'.
    erewrite <- st_trace_destruct'.
    rewrite fold_left_app in *.
    rewrite H.
    reflexivity.
  +

    erewrite trace_under_st_ev. (*with (trd':=[]).*)
    erewrite trace_under_st_stack.
    erewrite trace_under_st_store.

    (*rewrite <- HH.*)
    symmetry.
    rewrite fold_left_app in *.
    repeat 
    rewrite <- foo.
    assert (
        StVM.st_trace (fold_left run_vm_step il2
        (fold_left run_vm_step il1
           {| st_ev := e; st_stack := s; st_trace := trd; st_pl := p; st_store := o |})) =
        StVM.st_trace ({| st_ev := e''; st_stack := s''; st_trace := trd'; st_pl := p''; st_store := o'' |})) as H1 by congruence.
    simpl in *. rewrite <- H1.


    
    assert (StVM.st_pl (fold_left run_vm_step il1
                        {|
                        st_ev := e;
                        st_stack := s;
                        st_trace := trd;
                        st_pl := p;
                        st_store := o |}) = p) as H2 by (apply pl_immut).
    rewrite <- H2 at 4.
    rewrite <- record_congr. auto.
Defined.

Lemma restl' : forall il e e' s s' x tr p p' o o',
    run_vm il {| st_ev := e; st_stack := s; st_trace := x; st_pl := p; st_store := o |} =
    {| st_ev := e'; st_stack := s'; st_trace := x ++ tr; st_pl := p'; st_store := o' |} ->

    run_vm il {| st_ev := e; st_stack := s; st_trace := []; st_pl := p; st_store := o |} =
    {| st_ev := e'; st_stack := s'; st_trace := tr; st_pl := p'; st_store := o' |}.
Proof.
  intros.
  assert (
      st_trace (run_vm il {| st_ev := e; st_stack := s; st_trace := x; st_pl := p; st_store := o |}) =
      st_trace ({| st_ev := e'; st_stack := s'; st_trace := x ++ tr; st_pl := p'; st_store := o' |})).
  congruence.
  eapply st_congr;
    try eapply trace_irrel_ev;
    try eapply trace_irrel_stack;
    try eapply trace_irrel_place;
    try eapply trace_irrel_store;
    eauto.
  + (* st_trace case *)
    rewrite foo in *.
    simpl in *.
    Check app_inv_head.
    eapply app_inv_head.
    eauto.
Defined.

Lemma destruct_compiled_appended_fresh : forall trd' il1 il2 e e'' s s'' p p'' o o'',
    run_vm
      (il1 ++ il2)
        {| st_ev := e;   st_stack := s;   st_trace := []; st_pl := p; st_store := o |} =
        {| st_ev := e''; st_stack := s''; st_trace := trd'; st_pl := p''; st_store := o''  |} ->
    (exists tr1 e' s' p' o',
        run_vm
          (il1)
          {| st_ev := e;  st_stack := s;  st_trace := []; st_pl := p; st_store := o  |} =
          {| st_ev := e'; st_stack := s'; st_trace := tr1; st_pl := p'; st_store := o'  |} /\
        exists tr2,
          run_vm
            (il2)
            {| st_ev := e';  st_stack := s';  st_trace := []; st_pl := p'; st_store := o' |} =
            {| st_ev := e''; st_stack := s''; st_trace := tr2; st_pl := p''; st_store := o''  |} /\
          trd' = tr1 ++ tr2).
Proof.
  intros trd' il1 il2 e e'' s s'' p p'' o o' H0.
  edestruct (destruct_compiled_appended); eauto.
  destruct_conjs.
  assert (p = H2) as H8. {
    assert (st_pl (run_vm il1 {| st_ev := e; st_stack := s; st_trace := []; st_pl := p; st_store := o |}) =
            st_pl {| st_ev := H; st_stack := H1; st_trace := x; st_pl := H2; st_store := H3 |}). {
    congruence. }
    rewrite pl_immut in H8.
    simpl in *. auto. }
  exists x. exists H. exists H1. exists p. exists H3.
  split.
  - 
    congruence.
  - exists H5.
    split.
    + rewrite H8.
      eapply restl'; eauto.
    + assumption.
Defined.

Ltac do_dca :=
  match goal with
  | [ H: run_vm (_ ++ _) _ = _ |- _] =>
    idtac "ran do_dca";
    apply destruct_compiled_appended in H;
    destruct_conjs
  end.

Ltac do_dca_fresh :=
  match goal with
  | [ H: run_vm (_ ++ _) _ = _ |- _] =>
    idtac "ran do_dca";
    apply destruct_compiled_appended_fresh in H;
    destruct_conjs
  end.

Ltac do_stack0 :=                    
  match goal with
  | [H:  run_vm (instr_compiler _)
                {| st_ev := _; st_stack := ?s0; st_trace := _ |} =
         {| st_ev := _; st_stack := ?s1; st_trace := _ |} |- _ ] =>
    assert (s0 = s1) by (eauto)
  end.

(* When running an entire compiled term, stack is restored to where it started *)
Lemma multi_stack_restore : forall t tr1 tr1' e e' s s' p p' o o',
    run_vm (instr_compiler t)
           {| st_ev := e;  st_stack := s;  st_trace := tr1;  st_pl := p;  st_store := o |} =
           {| st_ev := e'; st_stack := s'; st_trace := tr1'; st_pl := p'; st_store := o' |}  ->
    s = s'.
Proof.
  induction t; intros; simpl in *.
  - (* asp_instr case *)
    destruct a;
      inv H; try reflexivity.
  - (* aatt case *)
    destruct r.
    invc H.
    reflexivity.
  - (* alseq case *)
    do_dca.
    eapply IHt2.
    assert (s = H1).
    eapply IHt1; eauto.
    subst.
    eapply restl'; eauto.
  - (* abseq case *)
    destruct s.
    destruct r.
    simpl in *.

    (* do_run. *)
    
    do_dca.
      
    simpl in *.
    do_stack0.
    unfoldm.

    subst.
    (*
    rewrite H1 in Heqppp. *)
    monad_unfold.

    unfold push_stack in *.
    do_dca.

    do_run. 
    desp.
    
    pairs.
    do_stack0.
    subst.
    do_pop_stackm_facts.
 
    congruence.
    do_stack0.
    subst.
    monad_unfold.
    unfold pop_stackm in *. monad_unfold. congruence.

  - (* abpar case *)
    destruct s.
    destruct r. 
 
    boom; repeat (break_match; allss).
Defined.

Ltac do_stack1 t1 :=
  match goal with
  | [H:  run_vm (instr_compiler t1)
                {| st_ev := _; st_stack := ?s0; st_trace := _ |} =
         {| st_ev := _; st_stack := ?s1; st_trace := _ |} |- _ ] =>
    assert (s0 = s1) by (eapply multi_stack_restore; eauto)
  end; destruct_conjs.

Ltac do_stack t1 t2 :=
  match goal with
  | [H:  run_vm (instr_compiler t1)
                {| st_ev := _; st_stack := ?s0; st_trace := _ |} =
         {| st_ev := _; st_stack := ?s1; st_trace := _ |},
         G:  run_vm (instr_compiler t2)
                    {| st_ev := _; st_stack := ?s; st_trace := _ |} =
             {| st_ev := _; st_stack := ?s'; st_trace := _ |} |- _ ] =>
    assert (s0 = s1 /\ s = s') by (split;eapply multi_stack_restore; eauto)
  end; destruct_conjs.

Lemma store_get_set : forall e s tr p o n e1 e' v0,
    get_store_at n
      {|
        st_ev := e;
        st_stack := s;
        st_trace := tr;
        st_pl := p;
        st_store := Maps.map_set o n e1 |} =
    (Some e', v0) ->
    e' = e1.
Proof.
  intros.
  boom; repeat (break_match; allss).
  unfold get_store_at in *.
  unfold get in *. simpl in *.
  cbn in H.
  break_let.
  rewrite PeanoNat.Nat.eqb_refl in Heqp0.
  boom; repeat (break_match; allss); congruence.
Defined.

Lemma store_get_set_fail_none : forall n e s tr p o e1 v,
    get_store_at n
     {|
       st_ev := e;
       st_stack := s;
       st_trace := tr;
       st_pl := p;
       st_store := Maps.map_set o n e1 |} =
    (None, v) ->
    False.
Proof.
  intros.
  unfold get_store_at in *.
  cbn in H.
  break_let.
  rewrite PeanoNat.Nat.eqb_refl in Heqp0.
  boom; repeat (break_match; allss); congruence.
Defined.

Lemma multi_ev_eval : forall t tr tr' e e' s s' p p' o o',
    run_vm (instr_compiler t)
           {| st_ev := e; st_stack := s;  st_trace := tr; st_pl := p; st_store := o |} =
           {| st_ev := e'; st_stack := s'; st_trace := tr'; st_pl := p'; st_store := o' |}  ->
    e' = eval (unanno t) e.
Proof.
  induction t; intros.
  - (* aasp case *)
    destruct a; inv H; try reflexivity.
  - (* aatt case *)
    simpl in *.
    destruct r.
    simpl in *.
    unfoldm.
    allss.
  - (* lseq case *)
    simpl in *.
    do_dca.
    simpl.
    eapply IHt2.
    assert (H2 = p).
    Check pl_immut.
    assert (st_pl (fold_left run_vm_step (instr_compiler t1)
                             {|
                               st_ev := e;
                               st_stack := s;
                               st_trace := tr;
                               st_pl := p;
                               st_store := o |}) = p).
    eapply pl_immut.
    assert (st_pl
             (run_vm (instr_compiler t1)
         {|
         st_ev := e;
         st_stack := s;
         st_trace := tr;
         st_pl := p;
         st_store := o |}) =
       st_pl ({|
       st_ev := H0;
       st_stack := H1;
       st_trace := H;
       st_pl := H2;
       st_store := H3 |})).
    congruence.
    rewrite <- H8 in H9.
    simpl in H9.
    rewrite H8 in H9.
    unfold run_vm in *.
    congruence.
    
    assert (H0 = eval (unanno t1) e).
    eauto.
    subst.
    eauto.
  - (* abseq case *)
    destruct s; simpl in *.
    destruct r.
    
    unfold run_vm_step in *. monad_unfold; monad_unfold.
    
    do_dca.

    do_run.
    desp.
    pairs.

    do_dca.
    do_run.
    desp.
    pairs.

    do_stack1 t2.
    subst.

    unfold pop_stackm in *. monad_unfold.
    pairs.
    apply ssc_inv.
    eauto.
   
    eapply IHt2.
    do_stack1 t1.
    subst.
    unfold pop_stack in *. monad_unfold.
    pairs.
    assert (H2 = p). {
      assert ( st_pl ( run_vm (instr_compiler t1) {|
         st_ev := splitEv s e;
         st_stack := push_stack EvidenceC (splitEv s1 e) s0;
         st_trace := tr ++ [Term.split n p];
         st_pl := p;
         st_store := o |}) =
     st_pl (  {|
       st_ev := H0;
       st_stack := push_stack EvidenceC (splitEv s1 e) s0;
       st_trace := H;
       st_pl := H2;
       st_store := H3 |} )).
      congruence.
      simpl in H1.
      rewrite <- H1.
      apply pl_immut.
      }
    subst.
    eauto.

    do_stack t1 t2.
   
    subst. simpl in *. unfold pop_stackm in Heqppp. monad_unfold.
    pairs.

    unfold pop_stackm in *. monad_unfold.
    unfold push_stack in *. congruence.

    do_stack1 t1.
    subst.
    unfold pop_stackm in *. monad_unfold. congruence.
  - (* abpar case *)
    simpl.
    destruct s.
    destruct r.

    unfold run_vm_step in *. repeat monad_unfold.
    simpl in *.
    unfold run_vm_step in *.
    repeat monad_unfold.

    repeat break_match;
      try
        (boom; allss;
         repeat rewrite para_eval_vm;
         eauto).
Defined.

Lemma suffix_prop : forall il e e' s s' tr tr' p p' o o',
    run_vm il
           {|
             st_ev := e;
             st_stack := s;
             st_trace := tr;
             st_pl := p;
             st_store := o |} =
    {|
      st_ev := e';
      st_stack := s';
      st_trace := tr';
      st_pl := p';
      st_store := o' |} ->
    exists l, tr' = tr ++ l.
Proof.
  intros.
  assert (st_trace (run_vm il
           {|
             st_ev := e;
             st_stack := s;
             st_trace := tr;
             st_pl := p;
             st_store := o |}) =
    st_trace ({|
      st_ev := e';
      st_stack := s';
      st_trace := tr';
      st_pl := p';
      st_store := o' |})) as H0.
  congruence.

  simpl in H0.
  eexists.
  rewrite <- H0.
  rewrite foo.
  reflexivity.
Defined.

Axiom run_at : forall t e s n o,
      run_vm (instr_compiler t)
             {| st_ev := e;
                st_stack := s;
                st_trace := [];
                st_pl := n;
                st_store := o |} =
             {| st_ev := (eval (unanno t) e);
                st_stack := s;
                st_trace := remote_events t n;
                st_pl := n;
                st_store := o |}.

Lemma get_store_in : forall x st st' o y,
    get_store_at x st = (None, st') ->
    st_store st = o ->
    Maps.map_get o x = (Some y) ->
    False.
Proof.
  intros.
  destruct st.
  simpl in *.
  subst.
  monad_unfold.
  unfold get_store_at in *.
  monad_unfold.
  rewrite H1 in *.
  find_inversion.
Defined.

Lemma map_get_get(*{V:Type}`{forall x y : V, Dec (x = y)}*) :
  forall (k:nat) (v:EvidenceC) l',
    Maps.map_get ((k,v) :: l') k = Some v.
Proof.
  intros.
  simpl.
  break_match; eauto.
  rewrite PeanoNat.Nat.eqb_refl in Heqb. congruence.
Defined.

Lemma map_get_get_2(*{V:Type}`{forall x y : V, Dec (x = y)}*) :
  forall (k:nat) (v:EvidenceC) k' v' l',
    k <> k' ->
    Maps.map_get ((k',v') :: (k,v) :: l') k = Some v.
Proof.
  intros.
  simpl.
  Search PeanoNat.Nat.eqb.
  remember (PeanoNat.Nat.eqb k k') as oo.
  
  destruct oo.
  Search PeanoNat.Nat.eqb.
  assert (k = k').
  apply EqNat.beq_nat_eq. auto.
  congruence.
  rewrite PeanoNat.Nat.eqb_refl. reflexivity.
Defined.

(*
Lemma wf_bpar : forall t r s x y,
    (*well_formed (abpar r s x y) -> *)
    (annotated t = (abpar r s x y)) ->
  range x <> range y.
Proof.
  intros.
  assert (well_formed (annotated t)).
  unfold annotated. apply anno_well_formed.
  intros.
  generalize dependent x.
  generalize dependent y.
  generalize dependent r.
  generalize dependent s.
  generalize dependent H0.
  induction t; intros.
  - inv H.
  - unfold annotated in *. unfold anno in *. fold anno in *.
    simpl in *. expand_let_pairs. simpl in *. inv H.
  - unfold annotated in *. unfold anno in *. fold anno in *.
    simpl in *. expand_let_pairs. simpl in *. inv H.
    expand_let_pairs. simpl in *. solve_by_inversion.
  - unfold annotated in *. unfold anno in *. fold anno in *.
    simpl in *. expand_let_pairs. simpl in *. inv H.
    expand_let_pairs. solve_by_inversion.
  - unfold annotated in *. unfold anno in *. fold anno in *.
    repeat expand_let_pairs. simpl in *.
    invc H0.
    invc H.
    destruct (anno t1 1).
    simpl in *.
    destruct (anno t2 n).
    simpl in *.
    destruct (range a).
    destruct (range a0).
    simpl in *.
    subst.
    find_inversion.
Abort.
*)

Axiom bpar_shuffle : forall x p t1 t2 et1 et2,
    lstar (bp x (conf t1 p et1) (conf t2 p et2))
          (shuffled_events (parallel_vm_events (instr_compiler t1) p)
                           (parallel_vm_events (instr_compiler t2) p))
          (bp x (stop p (aeval t1 p et1)) (stop p (aeval t2 p et2))).

Lemma afff : forall t' (n:nat) r s x t n,
    snd (anno t' n) = aatt (r,s) x t ->
    exists t'' n', t = snd (anno t'' n').
Proof.
  intros.
  destruct t';
    try (
        unfold anno in H;
        repeat break_let;
        cbn in *;
        inv H; tauto).
  - cbn in *.
    simpl in *.
    break_let.
    simpl in *.
    inv H.
    exists t'.
    exists (S r).
    rewrite Heqp.
    simpl.
    reflexivity.
Defined.

Lemma afaff : forall t' n r t1 t2,
    snd (anno t' n) = alseq r t1 t2 ->
    exists t'' n', t1 = snd (anno t'' n').
Proof.
  intros.
  destruct t';
    try (
        unfold anno in H;
        repeat break_let;
        simpl in *;
        inv H;
        tauto).
  - cbn in *.
    simpl in *.
    repeat break_let.
    simpl in *.
    inv H.
    exists t'1.
    exists (n).
    rewrite Heqp.
    simpl.
    reflexivity.
Defined.

Lemma afaff2 : forall t' n r t1 t2,
    snd (anno t' n) = alseq r t1 t2 ->
    exists t'' n', t2 = snd (anno t'' n').
Proof.
  intros.
  destruct t';
    try (
        unfold anno in H;
        repeat break_let;
        simpl in *;
        inv H;
        tauto).
  - cbn in *.
    simpl in *.
    repeat break_let.
    simpl in *.
    inv H.
    exists t'2.
    exists (n0).
    rewrite Heqp0.
    simpl.
    reflexivity.
Defined.

Lemma afaff3 : forall t' n n0 n1 s s1 t1 t2,
    snd (anno t' n) =  abseq (n0, n1) (s, s1) t1 t2 ->
    exists t'' n', t1 = snd (anno t'' n').
Proof.
  intros.
  destruct t';
    try (
        unfold anno in H;
        repeat break_let;
        simpl in *;
        inv H;
        tauto).
  - cbn in *.
    simpl in *.
    repeat break_let.
    simpl in *.
    inv H.
    exists t'1.
    exists (S n0).
    rewrite Heqp.
    simpl.
    reflexivity.
Defined.

Lemma afaff4 : forall t' n n0 n1 s s1 t1 t2,
    snd (anno t' n) =  abseq (n0, n1) (s, s1) t1 t2 ->
    exists t'' n', t2 = snd (anno t'' n').
Proof.
  intros.
  destruct t';
    try (
        unfold anno in H;
        repeat break_let;
        simpl in *;
        inv H;
        tauto).
  - cbn in *.
    simpl in *.
    repeat break_let.
    simpl in *.
    inv H.
    exists t'2.
    exists (n2).
    rewrite Heqp0.
    simpl.
    reflexivity.
Defined.

Lemma run_lstar : forall t tr et e e' s s' p p' o o' t' n,
   (* annotated x = t -> *)
    (*well_formed t -> *)
    t = snd (anno t' n) -> 
    (*t = annotated t' ->  *)
    run_vm (instr_compiler t)
           (mk_st e s [] p o) =
           (mk_st e' s' tr p' o') ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros  t tr et e e' s s' p p' o o' t' n HH H.
  assert (s = s') as H0. {
  eapply multi_stack_restore; eauto. }
  rewrite <- H0 in H.
  clear H0.
  
  generalize dependent tr.
  generalize dependent et.
  generalize dependent p.
  generalize dependent p'.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent o.
  generalize dependent o'.
  generalize dependent t'.
  generalize dependent n.
  induction t; intros. (* unfold annotated in *. *)
  - (* aasp case *)
    destruct a;
     simpl in *; 
      invc H;
        econstructor; try (econstructor; reflexivity).
  - (* aatt case *)
    simpl in *.
    destruct r.
    unfoldm.
    unfold run_vm_step in *.
    monad_unfold.

    find_inversion.  

    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    cbn.


    edestruct afff; eauto.
    destruct_conjs.
    
    eapply IHt; eauto.

    apply run_at.
    econstructor.
    apply stattstop.
    econstructor.   
    
  - (* alseq case *)
    simpl in *.
    econstructor.
    econstructor.

    do_dca_fresh.
    subst.

    do_stack1 t1.

    eapply lstar_transitive.
    
    eapply lstar_stls.
    subst.

    edestruct afaff; eauto.
    destruct_conjs.
    
    eapply IHt1; eauto.
  
    (* inv wft. eauto. *)
    eapply lstar_silent_tran.
    apply stlseqstop.

    edestruct afaff2; eauto.
    destruct_conjs.
 
    eapply IHt2; eauto.
    (* inv wft. eauto. *)
    assert (p = H2). {
      assert (
          st_pl (run_vm (instr_compiler t1)
                        {| st_ev := e; st_stack := s; st_trace := [];
                           st_pl := p; st_store := o |}) =
          st_pl ({| st_ev := H0; st_stack := H1; st_trace := H;
                    st_pl := H2; st_store := H3 |}))
        by congruence.
      rewrite pl_immut in *. simpl in *.
      congruence. }
    subst; eauto.

  - (* abseq case *)
    destruct s; destruct r; simpl in *.
    unfold run_vm_step in *. monad_unfold; monad_unfold.
     
        
    assert (exists l, tr = [Term.split n0 p] ++ l)
      as H0 by (eapply suffix_prop; eauto).
    destruct H0 as [H0 H1].
    rewrite H1 in *. clear H1.
    assert (run_vm
              ((instr_compiler t1 ++ abesr :: instr_compiler t2 ++
                               [ajoins (Init.Nat.pred n1)]))
              {| st_ev := splitEv s e;
                  st_stack := push_stack EvidenceC (splitEv s1 e) s0;
                  st_trace := []; st_pl := p; st_store := o |} =
             {| st_ev := e'; st_stack := s0; st_trace := H0; st_pl := p'; st_store := o' |})
        as H2 by (eapply restl'; eauto).
     
     do_dca_fresh.
     assert (p = H4). {
       assert (
           st_pl (run_vm (instr_compiler t1)
         {|
         st_ev := splitEv s e;
         st_stack := push_stack EvidenceC (splitEv s1 e) s0;
         st_trace := [];
         st_pl := p;
         st_store := o |}) =
           st_pl ({| st_ev := H1; st_stack := H3; st_trace := H2;
                     st_pl := H4; st_store := H5 |})).
       congruence.
       rewrite pl_immut in *. simpl in *. auto. }
     do_stack1 t1.
     rewrite H9.
     eapply lstar_tran.
     econstructor.
     eapply lstar_transitive.
     eapply lstar_stbsl.

     edestruct afaff3; eauto.
     destruct_conjs.
     
     eapply IHt1; eauto.
     (* inv wft; eauto. *)
  
     rewrite H11 in *.
     eassumption.
     simpl.
     eapply lstar_silent_tran.
     apply stbslstop.
     
     do_run.
     do_dca_fresh.
     clear H.
     rewrite H14.
     do_stack1 t2.
     eapply lstar_transitive.
     eapply lstar_stbsr.

    edestruct afaff4; eauto.
    destruct_conjs.
     
     eapply IHt2; eauto.
     (* inv wft; eauto. *)
     rewrite H in *.
     eauto.

     do_run.
     pairs.
     eapply lstar_tran.
     assert (p' = H4). {
       assert (st_pl (run_vm (instr_compiler t2)
         {|
         st_ev := splitEv s1 e;
         st_stack := push_stack EvidenceC H1 s0;
         st_trace := [];
         st_pl := H4; st_store := H5 |}) =
               st_pl (
                   {| st_ev := H0;
                      st_stack := push_stack EvidenceC H1 s0;
                      st_trace := H13;
                      st_pl := p'; st_store := o' |})).
       congruence.
       rewrite pl_immut in *. simpl in *. auto. }
     subst.
     apply stbsrstop.
     econstructor.
     Unshelve. eauto. eauto. eauto.
  - (* abpar case *)
    destruct s. destruct r.
    simpl in *.
    unfold run_vm_step in *. monad_unfold; monad_unfold.
    repeat break_match.
    +
      vmsts.
      repeat find_inversion.
      do_get_store_at_facts; eauto.
      do_get_store_at_facts; eauto.
      subst.
      simpl.
      econstructor.
      econstructor.
      eapply lstar_transitive.
      simpl.

      apply bpar_shuffle.
      econstructor.
      apply stbpstop.
      econstructor.
    + vmsts.
      repeat find_inversion.
      do_get_store_at_facts; eauto.
      subst.
      invc H4.
      unfold Maps.map_set in *.
      Check In.

      elimtype False. eapply get_store_in.
      eassumption.
      simpl.
      reflexivity.

      eapply map_get_get.
    + vmsts.
      repeat find_inversion.
      subst.
      unfold Maps.map_set in *.
      elimtype False. eapply get_store_in.
      eassumption.
      simpl.
      reflexivity.
      eapply map_get_get_2.
      eapply afaf; eauto.
Defined.


Lemma run_lstar_corrolary : forall t tr et e s p o t' n,
    t = snd (anno t' n) -> 
    st_trace (run_vm (instr_compiler t)
                     (mk_st e s [] p o)) = tr ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  Check run_lstar.
  eapply run_lstar with (t:=t) (tr:=tr) (e:=e) (s:=s) (p:=p) (o:=o); eauto.
  Check st_congr.
  eapply st_congr; try reflexivity.
  eassumption.
Defined.

Theorem vm_ordered' : forall t tr ev0 ev1 e e' s s' o o' t' n,
    well_formed t ->
    t = snd (anno t' n) -> 
    run_vm
      (instr_compiler t)
      (mk_st e s [] 0 o) =
      (mk_st e' s' tr 0 o') ->
    prec (ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  Check ordered.
  eapply ordered with (p:=0) (e:=mt); eauto.
  eapply run_lstar; eauto.
Defined.

Locate prec.

Theorem vm_ordered : forall t tr ev0 ev1 e e' s s' o o' t',
    t = annotated t' -> 
    run_vm
      (instr_compiler t)
      (mk_st e s [] 0 o) =
      (mk_st e' s' tr 0 o') ->
    prec (ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  Check ordered.
  eapply ordered with (p:=0) (e:=mt); eauto.
  -
    unfold annotated in H.
    subst.
    eapply anno_well_formed; eauto.
  -
    eapply run_lstar; eauto.
Defined.
