Require Import More_lists Preamble Term ConcreteEvidence LTS GenStMonad.
Require Import Instr MyStack MonadVM MonadVMFacts.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.

Require Import StructTactics.

(*From QuickChick Require Import QuickChick Tactics. *)


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

Definition prim_trace (i:nat) (p:Plc) (a:Prim_Instr) : (list Ev) :=
  match a with
  | copy => [Term.copy i p]
  | umeas asp_id => [Term.umeas i p asp_id]
  | sign => [Term.sign i p]
  | hash => [Term.hash i p]
  end.

Definition prim_ev (a:Prim_Instr)(* (p:Plc) *) (e:EvidenceC) : EvidenceC :=
  match a with
  | copy => e
  | umeas i =>
    let bs := invokeUSM i in
    (uuc i bs e)
  | sign =>
    let bs := signEv e in
    (ggc bs e)
  | hash =>
    let bs := hashEv e in
    (hhc bs e)
  end. 

Definition build_comp (i:AnnoInstr): VM unit :=
  match i with
  | aprimInstr x a =>
    p <- get_pl ;;
    modify_evm (prim_ev a) ;;
               add_tracem (prim_trace x p a)              
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
      (* put_store reqi (toRemote (unanno annt) q e) ;; *) (* TODO: make this contingent on a good remote setup.  Need to model such a situation *)
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
             (* TODO: need to add axioms somehow to capture
                trace of tr s.t. (shuffle el1 el2 = tr)

                Perhaps we introduce a "start thread" event, where that event holds the events associated with the instructions executed.  Would require some sort of environment to listen for results from outstanding threads, and axioms asserting we had valid VM threads available to execute them *)
  end.

(** Function-style semantics for VM *)

(* Transform vm_st for a single instruction (A -> B -> A) function for fold_left *)
Definition run_vm_step (a:vm_st) (b:AnnoInstr) : vm_st :=
  execSt a (build_comp b).

Definition run_vm (il:list AnnoInstr) st : vm_st :=
  fold_left (run_vm_step) il st.

Definition run_vm_t (t:AnnoTerm) st : vm_st :=
  run_vm (instr_compiler t) st.

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

Ltac unfoldm :=  repeat unfold run_vm_step in *; monad_unfold.

Ltac boom :=
  repeat unfoldm;
  repeat (desp; unfoldm);
  try_pop_all;
  vmsts.

Ltac do_run :=
  match goal with
  | [H:  run_vm (_ :: _) _ = _ |- _ ] => invc H; unfold run_vm_step in *; repeat monad_unfold
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
    run_vm il1
           {| st_ev := e;  st_trace := tr1;  st_stack := s;  st_pl := p1;  st_store := o  |} =
           {| st_ev := e'; st_trace := tr1'; st_stack := s'; st_pl := p1'; st_store := o' |} ->
    
    st_store (
        run_vm il1
           {| st_ev := e;  st_trace := tr2;  st_stack := s;  st_pl := p1;  st_store := o  |}) = o'.
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

(*

          try (unfold failm in *; congruence).
    unfold failm in *. repeat find_inversion.
    eauto.
    unfold failm in *. repeat find_inversion. eauto.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
      
Defined.
*)

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





(* A distributive property of st_trace.  Says we can pull the front of a starting trace (m) outside and prepend it to a st_trace call with the rest of the original starting trace (k) as the starting trace *)
Lemma gen_foo : forall il m k e s p o,
    st_trace (fold_left (run_vm_step) il
                        {| st_ev := e; st_trace := m ++ k;  st_stack := s; st_pl := p; st_store := o |}) =
    m ++ st_trace (fold_left (run_vm_step) il
                        {| st_ev := e; st_trace := k; st_stack := s; st_pl := p; st_store := o |}).
Proof.
  induction il; simpl; intros m k e s p o.
  - auto.
  - destruct a as [n p0 | n sp1 sp2 | n | l m' n | | | i q t (*| i rpyi q*)];
      try ( (* aprim, asplit areqrpy cases *)
          try destruct r;
          unfold run_vm_step; fold run_vm_step; monad_unfold;  
          rewrite IHil at 1;
          symmetry; 
          rewrite IHil at 1;

          rewrite <- app_assoc;
          tauto). 
       
    + (* ajoins case *)

      boom; allss.
      allss.
      rewrite IHil at 1.
      symmetry.
      rewrite IHil at 1.
      rewrite app_assoc at 1.
      congruence.

    + (* ajoinp case *)   
      unfold run_vm_step in *; fold run_vm_step in *;
        repeat monad_unfold;
        repeat break_match;
        try (allss; tauto);
        try (repeat find_inversion;
             vmsts;
             get_store_at_bogus).

      allss.
    
      erewrite IHil at 1.
      symmetry.
      erewrite IHil at 1.
      rewrite app_assoc. eauto.
           
    + (* abesr case *)
      boom; try allss.
      
    + (* abep case *)
      boom; try allss.

      invc H4.
      erewrite IHil at 1.
      symmetry.
      erewrite IHil at 1.
      erewrite app_assoc.
      eauto.
Defined.

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
          congruence).
     
    + (* joins case *)
      boom; allss.
      invc H4.
      rewrite foo.
      rewrite IHil1.

      rewrite <- app_assoc.
      rewrite app_nil_l.
      rewrite <- app_assoc.
      st_equiv.
      rewrite H.
      unfold run_vm_step.
      eauto.


      (*
      eassumption.
      congruence.
      
      rewrite app_assoc.


      st_equiv.
      simpl.
      rewrite IHil1.
      rewrite <- app_assoc.
      rewrite IHil1.
      
      unfold run_vm_step. fold run_vm_step.
      monad_unfold.
      unfold get_ev. monad_unfold.
      repeat (desp;bogus).
      rewrite foo.
      simpl.
      rewrite IHil1.
      try_pop_all.
      repeat do_pop_stackm_facts; subst.
      rewrite app_nil_l.
      repeat rewrite <- app_assoc.
      st_equiv.
      congruence.      
      repeat do_pop_stackm_fail; subst.
      rewrite IHil1.
      auto. 
       *)
      
    + (* ajoinp case *)

      (*boom; repeat break_match; allss. *)
       
      unfold run_vm_step. fold run_vm_step.
      repeat monad_unfold.
      (*monad_unfold. *)
      repeat break_match;
        try (get_store_at_bogus; congruence);
        try (repeat find_inversion;
             vmsts;
             bogus; congruence).
      ++
      allss.
      rewrite foo.
      rewrite IHil1.
      repeat rewrite <- app_assoc.
      st_equiv.
      rewrite H.
      eauto.
      ++
        allss.
        
        (*
        repeat find_inversion.
          vmsts.
          apply get_store_at_facts in Heqp2; eauto.
          apply get_store_at_facts in Heqp5; eauto.
          repeat do_bd.
          destruct_conjs.
          subst.
          try (do_get_store_at_facts_fail; eauto;
          do_get_store_at_facts_fail; eauto).
          subst.
          repeat do_bd.
          subst; eauto. *)
      ++
        allss.
        (*
        do_get_store_at_facts_fail; eauto.
        do_get_store_at_facts_fail; eauto.
        pairs.
        repeat find_inversion.
        eauto. *)
      
    + (* abesr case *)
      boom; allss.

      (*

      unfold run_vm_step. fold run_vm_step.
      monad_unfold.
      unfold get_ev. monad_unfold.
      repeat (desp;bogus).
      rewrite foo.
      simpl.
      rewrite IHil1.
      try_pop_all.
      repeat do_pop_stackm_facts; subst.
      unfold push_stackm in *. monad_unfold. pairs.
      auto.
      repeat do_pop_stackm_fail; subst.
      rewrite IHil1.
      auto.
       *)
      
    + (* abep case *)
      boom; allss.



      (*
      unfold run_vm_step. fold run_vm_step.
      monad_unfold.
      unfold get_store_at.
      monad_unfold.
      repeat break_match. *)
      ++
        find_inversion.

        rewrite foo.
        rewrite IHil1.
        repeat rewrite <- app_assoc.
        simpl.
        st_equiv.
        rewrite H.
        eauto.
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

(*

      try (
          simpl;
          try destruct p0;
          try destruct r;
          unfold run_vm_step; fold run_vm_step; monad_unfold;
          eauto; tauto)
      try (boom; repeat break_match; allss).
Defined.

   (*   try ( simpl; unfold run_vm_step; fold run_vm_step; monad_unfold;
            unfold get_ev; monad_unfold;
            desp;
            simpl; do_pop_stackm_facts; subst; eauto;
            do_pop_stackm_fail; subst; eauto). *)                   
    + (* ajoins case *)
      boom; allss.
      (*
      simpl. unfold run_vm_step. fold run_vm_step. monad_unfold.
      unfold get_ev. monad_unfold.
      desp.
      simpl. do_pop_stackm_facts. subst. eauto.
      do_pop_stackm_fail. subst. eauto. *)
    + (* ajoinp case *)
      boom; repeat break_match; allss.

      (*
      simpl. unfold run_vm_step. fold run_vm_step. monad_unfold.
      unfold get_store_at.
      monad_unfold.
      repeat break_match;
        try eauto;
        allss; eauto.
      ++ invc Heqp5.
      ++ invc Heqp4.
      ++ invc Heqp5.
      ++ invc Heqp4.
         eauto.
      ++ invc Heqp5.
      ++ invc Heqp2. eauto.
*)
                
    + (* abesr case *)
      boom; allss.
      (*
      simpl. unfold run_vm_step. fold run_vm_step. monad_unfold.
      unfold get_ev. monad_unfold.
      desp.
      simpl. do_pop_stackm_facts. subst. eauto.
      do_pop_stackm_fail. subst. eauto. *)
    + (* abep case *)
      boom; allss.
      (*
      simpl. unfold run_vm_step. fold run_vm_step. monad_unfold.
      unfold get_store_at.
      monad_unfold.
      repeat break_match;
        try eauto;
        allss; eauto.
      ++
        repeat do_flip.
        do_pop_stackm_facts.
        subst.
        eauto.
      ++ repeat do_flip.
         do_pop_stackm_fail.
         subst.
         eauto.     *)
Defined.
*)

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
  
  rewrite <- record_congr.

  rewrite <- fold_left_app.
  rewrite foo.
  destruct A; unfold run_vm.
  Check trace_irrel_ev.
  simpl in HeqB.
  destruct B.

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

  (*
    eapply st_congr;
      try
        ( destruct A;
          erewrite trace_irrel_ev; eauto;
          erewrite trace_irrel_stack; eauto;
          erewrite trace_irrel_store; eauto;
          
            try erewrite trace_irrel_stack;
            try erewrite trace_irrel_ev;
            try erewrite trace_irrel_store;
            try reflexivity; eauto).
  Admitted.
*)

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

  erewrite trace_under_st_ev. (*with (trd':=[]).*)
  erewrite trace_under_st_stack.
  erewrite trace_under_st_store.
  
  split.
  +
    rewrite <- app_assoc.
    erewrite <- st_trace_destruct'.
    rewrite fold_left_app in *.
    rewrite H.
    apply record_congr.
  +

    erewrite trace_under_st_ev. (*with (trd':=[]).*)
    erewrite trace_under_st_stack.
    erewrite trace_under_st_store.

    (*rewrite <- HH.*)
    symmetry.
    unfold run_vm in H.
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

    do_run.
    
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
    unfold pop_stackm in *. monad_unfold. congruence.


(*
    do_stack0.
    subst.
    monad_unfold.
    bogus.
    do_pop_stackm_fail.
    subst.
    do_dca.
    monad_unfold.
    unfold push_stack in *.  
    congruence. *)
  - (* abpar case *)

    
    destruct s.
    destruct r. 
 
    boom; repeat (break_match; allss).
Defined.

    (*  
    +
      vmsts.
      allss.
      (*
      repeat find_inversion.
      simpl in *.
      allss.
      do_get_store_at_facts; eauto.
      do_get_store_at_facts; eauto.
      subst.
      eauto. *)
    +
      vmsts.
      allss.
      (*
      repeat find_inversion.
      simpl in *.
      do_get_store_at_facts; eauto.
      do_get_store_at_facts_fail; eauto.
    
      subst.
      eauto. *)
    + vmsts.
      repeat find_inversion.
      simpl in *.
      do_get_store_at_facts_fail; eauto.
Defined.
*)

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
  boom; repeat (break_match; allss); congruence.
Defined.

(*

  congruence.
  congruence.
  congruence.
  break_match. break_match.
  find_inversion.
  monad_unfold.
  find_inversion.
  monad_unfold.
  break_match.
  break_match.
  congruence.
  congruence.
  break_match.
  congruence.
  congruence.
  find_inversion.
  monad_unfold.
  unfold failm in *.
  find_inversion.
Defined.
*)

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
  boom; repeat (break_match; allss); congruence.
Defined.

(*

  break_match. break_match.
  find_inversion.
  monad_unfold.
  find_inversion.
  break_match. break_match.
  congruence.
  congruence.
  break_match.
  congruence.
  congruence.
Defined.
*)

Lemma multi_ev_eval : forall t tr tr' e e' s s' p p' o o',
    run_vm (instr_compiler t)
           {| st_ev := e; st_stack := s;  st_trace := tr; st_pl := p; st_store := o |} =
           {| st_ev := e'; st_stack := s'; st_trace := tr'; st_pl := p'; st_store := o' |}  ->
    e' = eval (unanno t) e.
Proof.
  induction t; intros.
  - (* aasp case *)
    destruct a; inv H; reflexivity.
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
  break_match; eauto.
  congruence.
  congruence.
Defined.

Lemma map_get_get_2(*{V:Type}`{forall x y : V, Dec (x = y)}*) :
  forall (k:nat) (v:EvidenceC) k' v' l',
    k <> k' ->
    Maps.map_get ((k',v') :: (k,v) :: l') k = Some v.
Proof.
  intros.
  simpl.
  repeat (
  break_match; eauto;
  break_match; eauto;
  try congruence).
Defined.

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

Axiom bpar_shuffle : forall x p t1 t2 et1 et2,
    lstar (bp x (conf t1 p et1) (conf t2 p et2))
          (shuffled_events (parallel_vm_events (instr_compiler t1) p)
                           (parallel_vm_events (instr_compiler t2) p))
          (bp x (stop p (aeval t1 p et1)) (stop p (aeval t2 p et2))).

Lemma run_lstar : forall t tr et e e' s s' p p' o o',
   (* annotated x = t -> *)
    (*well_formed t -> *)
    run_vm (instr_compiler t)
           (mk_st e s [] p o) =
           (mk_st e' s' tr p' o') ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros  t tr et e e' s s' p p' o o' H.
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
    (*
    break_match. break_match.
    break_match.
    simpl in *. *)
    find_inversion.
(*
    break_match. break_match.
    repeat find_inversion. *)
    vmsts.
    (*
    find_inversion.
    break_match.
    find_inversion.
    break_match. *)
    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    
    eapply IHt; eauto.
    Print run_at.
   (* inv wft. eauto. *)

    apply run_at.
    

    econstructor.
    Print step.

    apply stattstop.
    econstructor.
    (*
    congruence.
    break_match.
    congruence.
    congruence.
    unfold failm in *.
    congruence.
    simpl in *.
    find_inversion.
    break_match. break_match.
    vmsts.
    find_inversion.
    find_inversion.
    break_match.
    break_match.
    congruence.
    congruence.
    break_match.
    congruence.
    congruence. *)
    
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
    
    eapply IHt1; eauto.
    (* inv wft. eauto. *)
    eapply lstar_silent_tran.
    apply stlseqstop.
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
     
        
    assert (exists l, tr = [Term.split n p] ++ l)
      as H0 by (eapply suffix_prop; eauto).
    destruct H0 as [H0 H1].
    rewrite H1 in *. clear H1.
    assert (run_vm
              ((instr_compiler t1 ++ abesr :: instr_compiler t2 ++
                               [ajoins (Init.Nat.pred n0)]))
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
      admit.
      (*
      inv wft.
      Print anno.
      
      subst.
      simpl in *.
      rewrite <- H5.

      Print instr_compiler. *)    
Admitted.

Lemma run_lstar_corrolary : forall t tr et e s p o,
   (* annotated x = t -> *)
    (*well_formed t -> *)
    st_trace (run_vm (instr_compiler t)
                     (mk_st e s [] p o)) = tr ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  Check run_lstar.
  eapply run_lstar with (t:=t) (tr:=tr) (e:=e) (s:=s) (p:=p) (o:=o).
  Check st_congr.
  eapply st_congr; try reflexivity.
  eassumption.
Defined.
  

Require Import Main.
Require Import Event_system.
Require Import Term_system.

Theorem vm_ordered : forall t tr ev0 ev1 e e' s s' o o',
    well_formed t ->
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

  
  
