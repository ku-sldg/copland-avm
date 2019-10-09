Require Import More_lists Preamble Term LTS.
Require Import Instr MyStack MonadVM MonadVMFacts.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.

Require Import Verdi.Net.
Require Import Verdi.LockServ.
Require Import Verdi.Verdi.

Set Nested Proofs Allowed.

(** IO Axioms *)

Definition remote_events (t:AnnoTerm) (p:Plc) : (list Ev).
Admitted.

Definition parallel_att_vm_thread (li:list AnnoInstr) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_vm_events (li:list AnnoInstr) : list Ev.
Admitted.

Definition prim_trace (i:nat) (p:Plc) (a:Prim_Instr) : (list Ev) :=
  match a with
  | copy => [Term.copy i p]
  | kmeas asp_id q A => [Term.kmeas i p asp_id q A]
  | umeas asp_id A => [Term.umeas i p asp_id A]
  | sign => [Term.sign i p]
  | hash => [Term.hash i p]
  end.

Definition prim_ev (a:Prim_Instr) (e:EvidenceC) : EvidenceC :=
  match a with
  | copy => e
  | kmeas i q args =>
    let bs := invokeKIM i q args in
    (kkc i args q bs e)
  | umeas i args =>
    let bs := invokeUSM i args in
    (uuc i args bs e)
  | sign =>
    let bs := signEv e in
    (ggc e bs)
  | hash =>
    let bs := hashEv e in
    (hhc bs e)
  end. 

Definition build_comp (*(s:ev_stack)*) (i:AnnoInstr): VM unit :=
  match i with
  | aprimInstr x a =>
    p <- get_pl ;;
    modify_evm (prim_ev a) ;;
               add_tracem (prim_trace x p a)              
  | asplit x sp1 sp2 =>
    e <- get_ev ;;
      p <- get_pl ;;
      p <- split_evm x sp1 sp2 e p;;
      let '(e1,e2) := p in
      put_ev e1 ;;
      push_stackm e2
  | ajoins i =>
    e <- get_ev ;;
      p <- get_pl ;;
      er <- pop_stackm ;;
      put_ev (ssc er e) ;;
      add_tracem [Term.join i p]
      (*
  | ajoinp i =>
    (*e <- pop_stackm ;;*)
    e <- get_ev ;;
      er <- pop_stackm ;;
      put_ev (ppc e er) ;; (*push_stackm (ppc e er) ;; *)
      add_tracem [Term.join i] *)
  | abesr =>
    e <- get_ev ;;
      er <- pop_stackm ;;
      push_stackm e ;;
      put_ev er    
  | areq reqi q annt =>
    e <- get_ev ;;
      put_store reqi (toRemote (unanno annt) q e) ;; (* TODO: make this contingent on a good remote setup.  Need to model such a situation *)
      p <- get_pl ;;
      (*put_ev (toRemote (unanno annt) q e) ;;
      let '(reqi,rpyi_last) := rg in
      let rpyi := Nat.pred rpyi_last in *)
      let newTrace :=
          [req reqi p q (unanno annt)] ++ (remote_events annt q) (* ++ [rpy rpyi p q] *) in
      add_tracem newTrace

  | arpy i rpyi q =>
    p <- get_pl ;;
      e <- get_store_at rpyi ;;
      put_ev e ;;
      add_tracem [rpy i p q]
    



(*
  | areqrpy rg q annt =>
    e <- get_ev ;;
      p <- get_pl ;;
      put_ev (toRemote (unanno annt) q e) ;;
      let '(reqi,rpyi_last) := rg in
      let rpyi := Nat.pred rpyi_last in
      let newTrace :=
          [req reqi p q (unanno annt)] ++ (remote_events annt q) ++ [rpy rpyi p q] in
      add_tracem newTrace*) (*
  | abep rg1 rg2 il1 il2 =>
    e <- get_ev ;;
      er <- pop_stackm ;;
      let res1 := parallel_att_vm_thread il1 e in
      let res2 := parallel_att_vm_thread il2 er in
      let el1 := parallel_vm_events il1 in
      let el2 := parallel_vm_events il2 in
      put_ev res1 ;;
             push_stackm res2
             (* TODO: need to add axioms somehow to capture
                trace of tr s.t. (shuffle el1 el2 = tr)

                Perhaps we introduce a "start thread" event, where that event holds the events associated with the instructions executed.  Would require some sort of environment to listen for results from outstanding threads, and axioms asserting we had valid VM threads available to execute them *)
*)
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

Ltac unfoldm :=  unfold run_vm_step in *; monad_unfold;
                 unfold get_ev; monad_unfold.

Ltac boom := repeat
               unfoldm; desp; vmsts;
             bogus;
             unfoldm; desp; vmsts;
             try_pop_all;
             bogus.
(*
  MonadVM.st_store
    (fold_left run_vm_step il1
       {| st_ev := e; st_stack := s; st_trace := trd; st_pl := p; st_store := o |}) =
  MonadVM.st_store
    (fold_left run_vm_step il1
       {| st_ev := e; st_stack := s; st_trace := []; st_pl := p; st_store := o |})
 *)

Ltac do_run :=
  match goal with
  | [H:  run_vm (_ :: _) _ = _ |- _ ] => invc H; unfold run_vm_step in *; monad_unfold; monad_unfold
  end.

Lemma bound_and_deterministic : forall (s:ev_store) n (e1 e2:EvidenceC),
    Maps.bound_to s n e1 ->
    Maps.bound_to s n e2 ->
    e1 = e2.
Proof.
  intros.
  inv H. inv H0.
  congruence.
Defined.

      Ltac do_bd :=
        match goal with
        | [ H: Maps.bound_to ?s ?n ?e1,
               G: Maps.bound_to ?s ?n ?e2  |- _ ] =>
          assert (e1 = e2)
            by (eapply bound_and_deterministic; eauto);
          clear H; clear G
        end.

Lemma trace_irrel_store : forall il1 tr1 tr1' tr2 e e' s s' p1' p1 p o' o,

    run_vm il1 {| st_ev := e; st_trace := tr1; st_stack := s; st_pl := p1; st_store := o |} =
    {| st_ev := e'; st_trace := tr1'; st_stack := s'; st_pl := p1'; st_store := o' |} ->
    
    st_store (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_stack := s; st_pl := p; st_store := o |}) = o'.
Proof.
  induction il1; intros.
  - simpl.
    inversion H. reflexivity.   
  - 
    simpl; destruct a;
      try
        (try destruct p0;
         try destruct r;
         unfold run_vm_step;
         monad_unfold;
         eapply IHil1;
         simpl in H;
         unfold run_vm_step in H; simpl in *; monad_unfold; 
         eassumption);
      try (
          boom;
          try_pop_all;
          repeat do_pop_stackm_facts;
          repeat do_pop_stackm_fail;
          subst; eauto; tauto).

    + (* apry case *)
      simpl in *.
      unfold run_vm_step in *. fold run_vm_step in *. 
      repeat monad_unfold.
      repeat break_match.
      simpl.
      repeat find_inversion.
      do_get_store_at_facts; eauto.
      do_get_store_at_facts; eauto.


      do_bd.
      subst; eauto.
      repeat find_inversion.
      bogus.
      bogus.

      do_get_store_at_facts_fail; eauto.
      do_get_store_at_facts_fail; eauto.
      repeat find_inversion.

      subst.
      erewrite IHil1; eauto.      
Defined.
           
Lemma trace_irrel : forall il1 tr1 tr1' tr2 e e' s s' p1' p1 p o1 o1',

    run_vm il1 {| st_ev := e; st_trace := tr1; st_stack := s; st_pl := p1; st_store := o1 |} =
    {| st_ev := e'; st_trace := tr1'; st_stack := s'; st_pl := p1'; st_store := o1' |} ->
    
    st_ev (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_stack := s; st_pl := p; st_store := o1 |}) = e'.
Proof.
  induction il1; intros.
  - simpl.
    inversion H. reflexivity.   
  - 
    simpl; destruct a;
      try
        (try destruct p0;
         try destruct r;
         unfold run_vm_step;
         monad_unfold;
         eapply IHil1;
         simpl in H;
         unfold run_vm_step in H; simpl in *; monad_unfold; 
         eassumption);
      try (
          boom;
          try_pop_all;
          repeat do_pop_stackm_facts;
          repeat do_pop_stackm_fail;
          subst; eauto; tauto).

        + (* apry case *)
      simpl in *.
      unfold run_vm_step in *. fold run_vm_step in *. 
      repeat monad_unfold.
      repeat break_match.
      simpl.
      repeat find_inversion.
      do_get_store_at_facts; eauto.
      do_get_store_at_facts; eauto.


      do_bd.
      subst; eauto.
      repeat find_inversion.
      bogus.
      bogus.

      do_get_store_at_facts_fail; eauto.
      do_get_store_at_facts_fail; eauto.
      repeat find_inversion.

      subst.
      erewrite IHil1; eauto.  
    (*
    + (* apry case *)
      simpl in *.
      unfold run_vm_step in *. fold run_vm_step in *. 
      repeat monad_unfold.
      repeat break_match.
      simpl.
      repeat find_inversion.
      do_get_store_at_facts; eauto.
      do_get_store_at_facts; eauto.
      admit.
      repeat find_inversion.
      simpl in *.
      erewrite IHil1; eauto.
      do_get_store_at_facts; eauto.
      do_get_store_at_facts_fail; eauto.
      subst.
      


      (*do_bd. *)
      subst; eauto.
      repeat find_inversion.
      bogus.
      bogus.

      do_get_store_at_facts_fail; eauto.
      do_get_store_at_facts_fail; eauto.
      repeat find_inversion.

      subst.
      erewrite IHil1; eauto.  *)
    
Defined.

Lemma place_irrel : forall il1 tr1 tr1' tr2 e e' s s' p p' o o',

    run_vm il1 {| st_ev := e; st_trace := tr1; st_stack := s; st_pl := p; st_store := o |} =
    {| st_ev := e'; st_trace := tr1'; st_stack := s'; st_pl := p'; st_store := o' |} ->
    
    st_pl (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_stack := s; st_pl := p; st_store := o |}) = p'.
Proof.
    induction il1; intros.
  - simpl.
    inversion H. reflexivity.   
  - 
    simpl; destruct a;
      try
        (try destruct p0;
         (*try destruct r; *)
         unfold run_vm_step;
         monad_unfold;
         eapply IHil1;
         simpl in H;
         unfold run_vm_step in H; simpl in *; monad_unfold; 
         eassumption);

      try (
          boom;
          try_pop_all;
          repeat do_pop_stackm_facts;
          repeat do_pop_stackm_fail;
          subst; eauto).

            + (* apry case *)
      simpl in *.
      unfold run_vm_step in *. fold run_vm_step in *. 
      repeat monad_unfold.
      repeat break_match.
      simpl.
      repeat find_inversion.
      do_get_store_at_facts; eauto.
      do_get_store_at_facts; eauto.


      do_bd.
      subst; eauto.
      repeat find_inversion.
      bogus.
      bogus.

      do_get_store_at_facts_fail; eauto.
      do_get_store_at_facts_fail; eauto.
      repeat find_inversion.

      subst.
      erewrite IHil1; eauto.
Defined.

Lemma stack_irrel : forall il1 tr1 tr1' tr2 e e' s s' p1 p1' p o1 o1',
    run_vm il1 {| st_ev := e; st_trace := tr1; st_stack := s; st_pl := p1'; st_store := o1' |} =
    {| st_ev := e'; st_trace := tr1'; st_stack := s'; st_pl := p1; st_store := o1 |} ->
    
    st_stack (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_stack := s; st_pl := p; st_store := o1' |}) =
    s'.
  (*
    st_trace (
        run_vm il1 {| st_ev := e1; st_trace := tr2; st_stack := s |}).*)
Proof.
    induction il1; intros.
  - simpl.
    inversion H. reflexivity.   
  - 
    simpl; destruct a as [n p0 | n sp1 sp2 | n | | i q t | i rpyi q];
      try
        (try destruct p0;
         (*try destruct r; *)
         unfold run_vm_step;
         monad_unfold;
         eapply IHil1;
         simpl in H;
         unfold run_vm_step in H; simpl in *; monad_unfold; 
         eassumption);
      try (
          boom;
          try_pop_all;
          repeat do_pop_stackm_facts;
          repeat do_pop_stackm_fail;
          subst; eauto).

    + (* apry case *)
      simpl in *.
      unfold run_vm_step in *. fold run_vm_step in *. 
      repeat monad_unfold.
      repeat break_match.
      simpl.
      repeat find_inversion.
      do_get_store_at_facts; eauto.
      do_get_store_at_facts; eauto.


      do_bd.
      subst; eauto.
      repeat find_inversion.
      bogus.
      bogus.

      do_get_store_at_facts_fail; eauto.
      do_get_store_at_facts_fail; eauto.
      repeat find_inversion.

      subst.
      erewrite IHil1; eauto.
Defined.

Lemma foo : forall il m e s p o,
    st_trace (fold_left (run_vm_step) il
                        {| st_ev := e; st_trace := m; st_stack := s; st_pl := p; st_store := o |}) =
    m ++ st_trace (fold_left (run_vm_step) il
                             {| st_ev := e; st_trace := []; st_stack := s; st_pl := p; st_store := o |}).
Proof.
  induction il; simpl; intros m e s p o.
  - rewrite app_nil_r. auto.
  - destruct a as [n p0 | n sp1 sp2 | n | | i q t | i rpyi q];
      try ( (* prim, asplit aatt cases *)
          (*try destruct r; *)
          unfold run_vm_step; fold run_vm_step; monad_unfold;  
          rewrite IHil at 1;
          symmetry; 
          rewrite IHil at 1;

          rewrite <- app_assoc;
          tauto). 
       
    + (* ajoins case *)     
      unfold run_vm_step; fold run_vm_step; monad_unfold; monad_unfold.     
      desp.
      simpl.
      desp.
      simpl.
      pairs.
      rewrite IHil at 1.
      symmetry.
      rewrite IHil at 1.
      do_double_pop.
      repeat do_pop_stackm_facts.
      subst.
      rewrite app_nil_l.

      rewrite app_assoc at 1.
      congruence.

      bogus.
      desp.
      bogus.
     
      pairs.
      subst.
      rewrite IHil.
      auto.
    + (* abesr case *)
      boom.
      simpl.
      
      rewrite IHil at 1.
      symmetry.
      rewrite IHil at 1.
      do_double_pop.
      repeat do_pop_stackm_facts.
      subst.
      rewrite app_nil_l.
      congruence.

      repeat do_pop_stackm_fail.
      subst.
      apply IHil.
    + (* arpy case *)
      unfold run_vm_step; fold run_vm_step; monad_unfold; monad_unfold.
      repeat break_match.
      repeat find_inversion.
      do_get_store_at_facts; eauto.
      do_get_store_at_facts; eauto.
      subst.
      rewrite IHil at 1.
      symmetry.
      rewrite IHil at 1.
      rewrite app_nil_l.
      rewrite app_assoc.
      do_bd. congruence.
      bogus.
      bogus.
      repeat find_inversion.
      do_get_store_at_facts_fail; eauto.
      do_get_store_at_facts_fail; eauto.
      subst.
      eauto.
Defined.

Lemma compile_not_empty :
  forall t,
    (instr_compiler t) <> [].
Proof.
  intros.
  induction t.
  - destruct a; simpl; congruence.
  - simpl. congruence. 
  - simpl.
    Search (_ <> []).
    destruct (instr_compiler t1); simpl; congruence.
  - simpl. destruct s. congruence.
Defined.

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

Ltac heee l :=
  assert (l = l ++ []) as HH; auto; rewrite HH.

Lemma ya :
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
        st_trace (fold_left run_vm_step _ ?st1) =
      _ ++ _ ++ _ ++
        st_trace (fold_left run_vm_step _ ?st2) =>
    idtac "matched" ;
    assert (st1 = st2)
      by (
          eapply st_congr; simpl;
          try (try erewrite trace_irrel;
               try erewrite stack_irrel;
               try erewrite trace_irrel_store;
               try reflexivity;
               rewrite <- ya; reflexivity))  
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
    destruct a as [n p0 | n sp1 sp2 | n | | r q t];
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

    + (* abesr case *)

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
    destruct a as [n p0 | n sp1 sp2 | n | | r q t];
      try (
          simpl;
          try destruct p0;
          try destruct r;
          unfold run_vm_step; fold run_vm_step; monad_unfold;
          eauto; tauto).
   (*   try ( simpl; unfold run_vm_step; fold run_vm_step; monad_unfold;
            unfold get_ev; monad_unfold;
            desp;
            simpl; do_pop_stackm_facts; subst; eauto;
            do_pop_stackm_fail; subst; eauto). *)                   
    + simpl. unfold run_vm_step. fold run_vm_step. monad_unfold.
      unfold get_ev. monad_unfold.
      desp.
      simpl. do_pop_stackm_facts. subst. eauto.
      do_pop_stackm_fail. subst. eauto.
    + simpl. unfold run_vm_step. fold run_vm_step. monad_unfold.
      unfold get_ev. monad_unfold.
      desp.
      simpl. do_pop_stackm_facts. subst. eauto.
      do_pop_stackm_fail. subst. eauto.
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

  split; try apply ya.
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
  
  rewrite <- ya.

  rewrite <- fold_left_app.
  rewrite foo.

  assert (
      {|
        st_ev := st_ev
                   (fold_left run_vm_step il1
                              {|
                                st_ev := e;
                                st_stack := s;
                                st_trace := trd;
                                st_pl := p;
                                st_store := o |});
        st_stack := st_stack
                      (fold_left run_vm_step il1
                                 {|
                                   st_ev := e;
                                   st_stack := s;
                                   st_trace := trd;
                                   st_pl := p;
                                   st_store := o |});
        st_trace := [];
        st_pl := p;
        st_store := st_store
                      (fold_left run_vm_step il1
                                 {|
                                   st_ev := e;
                                   st_stack := s;
                                   st_trace := trd;
                                   st_pl := p;
                                   st_store := o |}) |} =

      {|
        st_ev := st_ev
                   (fold_left run_vm_step il1
                              {|
                                st_ev := e;
                                st_stack := s;
                                st_trace := [];
                                st_pl := p;
                                st_store := o |});
        st_stack := st_stack
                      (fold_left run_vm_step il1
                                 {|
                                   st_ev := e;
                                   st_stack := s;
                                   st_trace := [];
                                   st_pl := p;
                                   st_store := o |});
        st_trace := [];
        st_pl := p;
        st_store :=  st_store
                      (fold_left run_vm_step il1
                                 {|
                                   st_ev := e;
                                   st_stack := s;
                                   st_trace := [];
                                   st_pl := p;
                                   st_store := o |}); |}
    ) as HH. {
    eapply st_congr;
      try
        ( destruct A;
          erewrite trace_irrel; eauto;
          erewrite stack_irrel; eauto;
          erewrite trace_irrel_store; eauto;
          
            try erewrite stack_irrel;
            try erewrite trace_irrel;
            try erewrite trace_irrel_store;
            try reflexivity; eauto).
  }

  
  rewrite HH.
  split.
  +
  rewrite <- app_assoc. 
  rewrite <- st_trace_destruct'.
  rewrite fold_left_app in *.
  rewrite H.
  apply ya.
  +
    rewrite <- HH.
    symmetry.
    unfold run_vm in H.
    rewrite fold_left_app in *.
    repeat 
    rewrite <- foo.
    assert (
        st_trace (fold_left run_vm_step il2
        (fold_left run_vm_step il1
           {| st_ev := e; st_stack := s; st_trace := trd; st_pl := p; st_store := o |})) =
        st_trace ({| st_ev := e''; st_stack := s''; st_trace := trd'; st_pl := p''; st_store := o'' |})) as H1 by congruence.
    simpl in *. rewrite <- H1.



    assert (st_pl (fold_left run_vm_step il1
                        {|
                        st_ev := e;
                        st_stack := s;
                        st_trace := trd;
                        st_pl := p;
                        st_store := o |}) = p) as H2 by (apply pl_immut).
    rewrite <- H2 at 4.
    rewrite <- ya. auto.
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
    try eapply trace_irrel;
    try eapply stack_irrel;
    try eapply place_irrel;
    try eapply trace_irrel_store;
    eauto.
  + rewrite foo in *.
    simpl in *.
    erewrite app_inv_head; eauto.
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

Lemma multi_stack_restore : forall t tr1 tr1' e e' s s' p p' o o',
    run_vm (instr_compiler t)
           {| st_ev := e; st_stack := s; st_trace := tr1;
              st_pl := p; st_store := o |} =
    {| st_ev := e'; st_stack := s'; st_trace := tr1';
       st_pl := p'; st_store := o' |}  ->
    s = s'.
Proof.
  induction t; intros; simpl in *.
  - (* asp_instr case *)
    destruct a;
      inv H; try reflexivity.


  - (* aatt case *)
    destruct r.
    inv H.
    auto.
  - (* alseq case *)
    do_dca.
    eapply IHt2.
    assert (s = H1).
    eapply IHt1; eauto.
    subst.
    eapply restl'; eauto.
  - (* abseq case *)
    destruct s.
    do_run.
    
    do_dca.
      
    simpl in *.
    do_stack0.
    unfoldm.
    repeat desp.
    subst.
    (*
    rewrite H1 in Heqppp. *)
    monad_unfold.
    unfold pop_stackm in *. monad_unfold.
    pairs.

    destruct_conjs.
    unfold push_stackm in *. monad_unfold. pairs.

    monad_unfold.
    unfold push_stack in *.
    do_dca.
    do_run.
    monad_unfold.
    desp.
    pairs.
    do_stack0.
    subst.
    do_pop_stackm_facts.
 
    congruence.
    do_stack0.
    subst.
    unfold pop_stackm in *. monad_unfold. congruence.
    do_stack0.
    subst.
    monad_unfold.
    bogus.
    do_pop_stackm_fail.
    subst.
    do_dca.
    monad_unfold.
    unfold push_stack in *.  
    congruence.
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
    unfoldm.
    invc H.
    auto.   
  - (* lseq case *)
    simpl in *.
    do_dca.
    simpl.
    eapply IHt2.
    assert (H0 = eval (unanno t1) e).
    eauto.
    subst.
    eauto.
  - (* abseq case *)
    destruct s; simpl in *.
    
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
    eauto.

    do_stack t1 t2.
   
    subst. simpl in *. unfold pop_stackm in Heqppp. monad_unfold.
    pairs.

    unfold pop_stackm in *. monad_unfold.
    unfold push_stack in *. congruence.

    do_stack1 t1.
    subst.
    unfold pop_stackm in *. monad_unfold. congruence.
Defined.

Lemma st_stack_restore : forall t e s tr p o,
    st_stack
      (run_vm (instr_compiler t)
              {| st_ev := e;
                 st_stack := s;
                 st_trace := tr;
                 st_pl := p;
                 st_store := o |}) = s.
Proof.
  intros.
  erewrite multi_stack_restore.
  reflexivity.
  eapply ya.
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

Lemma run_lstar : forall t tr et e e' s s' p p' o o',
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
  induction t; intros.
  - (* aasp case *)
    destruct a;
     simpl in *; 
      invc H;
        econstructor; try (econstructor; reflexivity).
  - (* aatt case *)
    simpl in *.
    destruct r.
    unfoldm.
    invc H.
    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
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
    
    eapply IHt1; eauto.
    eapply lstar_silent_tran.
    apply stlseqstop.
    eapply IHt2; eauto.
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
     destruct s; simpl in *.  
     unfold run_vm_step in *. monad_unfold; monad_unfold.
        
     assert (exists l, tr = [Term.split (fst r) p] ++ l)
       as H0 by (eapply suffix_prop; eauto).
     destruct H0 as [H0 H1].
     rewrite H1 in *. clear H1.
     assert (run_vm
               ((instr_compiler t1 ++ abesr :: instr_compiler t2 ++
                                [ajoins (Init.Nat.pred (snd r))]))
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