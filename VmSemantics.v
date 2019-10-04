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

Definition remote_events (t:AnnoTerm) (p:Plc) : (list Ev).
Admitted.

Definition parallel_att_vm_thread (li:list AnnoInstr) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_vm_events (li:list AnnoInstr) : list Ev.
Admitted.

(*
Axiom remote_events_axiom : forall t tr,
    trace t tr -> remote_events t = tr.*)

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
                  (*push_stackm e1*)
  | ajoins i =>    (*let (er,r') := pop_stackr r in *)
    (*e <- pop_stackm ;;*)
    e <- get_ev ;;
      p <- get_pl ;;
      er <- pop_stackm ;;
      put_ev (ssc er e) ;; (*push_stackm (ssc er e) ;; *)
      add_tracem [Term.join i p]
      (*
  | ajoinp i =>
    (*e <- pop_stackm ;;*)
    e <- get_ev ;;
      er <- pop_stackm ;;
      put_ev (ppc e er) ;; (*push_stackm (ppc e er) ;; *)
      add_tracem [Term.join i] *)
  | abesr =>
    (*e <- pop_stackm ;;*)
    e <- get_ev ;;
      er <- pop_stackm ;;
      push_stackm e ;;
      put_ev er
      
  | areqrpy rg q annt =>
    e <- get_ev ;;
      p <- get_pl ;;
      put_ev (toRemote (unanno annt) q e) ;;
      let '(reqi,rpyi_last) := rg in
      let rpyi := Nat.pred rpyi_last in
      let newTrace :=
          [req reqi p q (unanno annt)] ++ (remote_events annt q) ++ [rpy rpyi p q] in
      add_tracem newTrace (*
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
  forall st tr e p s,
    st_ev st = e ->
    st_stack st = s ->
    st_trace st = tr ->
    st_pl st = p ->
    st =  {| st_ev := e; st_trace := tr; st_stack := s; st_pl := p |}.
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
           
Lemma trace_irrel : forall il1 tr1 tr1' tr2 e e' s s' p1' p1 p,

    run_vm il1 {| st_ev := e; st_trace := tr1; st_stack := s; st_pl := p1 |} =
    {| st_ev := e'; st_trace := tr1'; st_stack := s'; st_pl := p1' |} ->
    
    st_ev (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_stack := s; st_pl := p |}) = e'.
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
          subst; eauto).
Defined.

Lemma place_irrel : forall il1 tr1 tr1' tr2 e e' s s' p p',

    run_vm il1 {| st_ev := e; st_trace := tr1; st_stack := s; st_pl := p |} =
    {| st_ev := e'; st_trace := tr1'; st_stack := s'; st_pl := p' |} ->
    
    st_pl (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_stack := s; st_pl := p |}) = p'.
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
          subst; eauto).
Defined.

Ltac do_run :=
  match goal with
  | [H:  run_vm (_ :: _) _ = _ |- _ ] => invc H; unfold run_vm_step in *; monad_unfold; monad_unfold
  end.

Lemma stack_irrel : forall il1 tr1 tr1' tr2 e e' s s' p1 p1' p,
    run_vm il1 {| st_ev := e; st_trace := tr1; st_stack := s; st_pl := p1' |} =
    {| st_ev := e'; st_trace := tr1'; st_stack := s'; st_pl := p1 |} ->
    
    st_stack (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_stack := s; st_pl := p |}) =
    s'.
  (*
    st_trace (
        run_vm il1 {| st_ev := e1; st_trace := tr2; st_stack := s |}).*)
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
          subst; eauto).
Defined.

Lemma foo : forall il m e s p,
    st_trace (fold_left (run_vm_step) il
                        {| st_ev := e; st_trace := m; st_stack := s; st_pl := p |}) =
    m ++ st_trace (fold_left (run_vm_step) il
                             {| st_ev := e; st_trace := []; st_stack := s; st_pl := p |}).
Proof.
  induction il; simpl; intros m e s p.
  - rewrite app_nil_r. auto.
  - destruct a; try ( (* prim, asplit aatt, cases *)
                    try destruct r;
    
    unfold run_vm_step; fold run_vm_step; monad_unfold;
    
    rewrite IHil at 1;
    symmetry; 
    rewrite IHil at 1;

    rewrite <- app_assoc;
    tauto).
    
    
    + (* joins case *)
      
      unfold run_vm_step; fold run_vm_step; monad_unfold; monad_unfold.     
      desp.
      simpl.
      desp.
      simpl.
      pairs.
      rewrite IHil at 1.
      symmetry.
      rewrite IHil at 1.
      assert (st_trace = m ++ st_trace0). {
        assert (st_trace = m). {
          eapply pop_stackm_pure; eauto. 
           }
        assert (st_trace0 = []). {
          eapply pop_stackm_pure; eauto.
        }
        subst.
        rewrite app_nil_r. congruence.
      }
      subst.
      do_double_pop.

      rewrite app_assoc at 1.
      rewrite app_assoc at 1.
      repeat do_pop_stackm_facts.
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
      assert (st_trace = m ++ st_trace0). {
        assert (m = st_trace). {
          symmetry.
          eapply pop_stackm_pure; eauto.
           }
        assert (st_trace0 = []). {
          eapply pop_stackm_pure; eauto.
        }
        subst.
        rewrite app_nil_r.
        congruence. }

      rewrite H.
      rewrite app_assoc at 1.

      do_double_pop.
      repeat do_pop_stackm_facts.
      congruence.
      bogus.

      monad_unfold.
      repeat do_pop_stackm_fail.
      subst.
      apply IHil.
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
       st_pl := st_pl A |}.
Proof.
  intros.
  destruct A.
  reflexivity.
Defined.

Lemma st_trace_destruct' :
  forall il1 il2 e s m p,
    st_trace
      (fold_left run_vm_step il2
                 (fold_left run_vm_step il1
                            {| st_ev := e;
                               st_stack := s;
                               st_trace := m;
                               st_pl := p|})) =
    m ++ 
    st_trace
      (fold_left run_vm_step il1 
                 {| st_ev := e;
                    st_stack := s;
                    st_trace := [];
                    st_pl := p |}) ++
      st_trace
      (fold_left run_vm_step il2
                 {| st_ev :=
                      (st_ev
                         (fold_left run_vm_step il1 
                           {| st_ev := e; st_stack := s; st_trace := [];
                               st_pl := p |}));
                    st_stack :=
                      (st_stack
                         (fold_left run_vm_step il1 
                           {| st_ev := e; st_stack := s; st_trace := [];
                              st_pl := p |}));
                    st_trace := [];
                    st_pl :=
                      (*(st_pl
                         (fold_left run_vm_step il1
                            {|
                              st_ev := e;
                              st_stack := s;
                              st_trace := [];
                                 st_pl := p |}))*)p |}).
Proof.
  induction il1; try reflexivity; intros.
  - simpl.
    erewrite foo.
    reflexivity.
  - simpl.
    Check foo.
    destruct a.
    + (* apriminstr case *)
    unfold run_vm_step. fold run_vm_step.
    monad_unfold.
    rewrite foo.
    rewrite <- app_assoc.
    simpl in IHil1.
    rewrite IHil1.
    
    Check st_congr.
      (*
           : forall (st : vm_st) (tr : list Ev) (e : EvidenceC) 
         (p : nat) (s : ev_stack),
       st_ev st = e ->
       st_stack st = s ->
       st_trace st = tr ->
       st_pl st = p ->
       st = {| st_ev := e; st_stack := s; st_trace := tr; st_pl := p |}
       *)
    Check trace_irrel.
        (*
        trace_irrel
        : forall (il1 : list AnnoInstr) (tr1 tr1' tr2 : list Ev)
         (e e' : EvidenceC) (s s' : ev_stack) (p p' : nat),
       run_vm il1
         {| st_ev := e; st_stack := s; st_trace := tr1; st_pl := p' |} =
       {| st_ev := e'; st_stack := s'; st_trace := tr1'; st_pl := p |} ->
       st_ev
         (run_vm il1
            {| st_ev := e; st_stack := s; st_trace := tr2; st_pl := p |}) = e'
         *)

    Ltac st_equiv :=

      match goal with
      
      | |- _ ++ _ ++ _ ++
            st_trace (fold_left run_vm_step _ ?st1) =
          _ ++ _ ++ _ ++
            st_trace (fold_left run_vm_step _ ?st2) =>
        idtac "matched" ;
        assert (st1 = st2) by (
        eapply st_congr; simpl;
        try (try erewrite trace_irrel;
             try erewrite stack_irrel;
             try reflexivity;
             rewrite <- ya; reflexivity))
        
      end.

    rewrite <- app_assoc.
    st_equiv.
     
    rewrite H. 

    congruence.

    + (* asplit case *)
      unfold run_vm_step. fold run_vm_step.
      monad_unfold.
      rewrite foo.
      rewrite <- app_assoc.
      rewrite IHil1.

      rewrite <- app_assoc.
      st_equiv.
      congruence.
     
    + (* joins case *)
      
      unfold run_vm_step. fold run_vm_step.
      monad_unfold.
      unfold get_ev. monad_unfold.
      desp.
      desp.
      rewrite foo.
      pairs.
      simpl.
      rewrite IHil1.
      try_pop_all.
      repeat 
      do_pop_stackm_facts.
      subst.
      rewrite app_nil_l.
      rewrite <- app_assoc.
      rewrite <- app_assoc.
      st_equiv.
      congruence.      
      
      bogus.   
      desp.
      bogus.
      repeat do_pop_stackm_fail.
      
      subst.
      rewrite IHil1.
      auto.

    + (* abesr case *)

      unfold run_vm_step. fold run_vm_step.
      monad_unfold.
      unfold get_ev. monad_unfold.
      desp.
      desp.
      simpl in *.
      rewrite foo.
      pairs.
      simpl.
      rewrite IHil1.
      try_pop_all.
      repeat do_pop_stackm_facts.
      subst.
      simpl in *.
      auto.
      bogus.   
      desp; bogus.
      repeat do_pop_stackm_fail.   
      subst.
      rewrite IHil1.
      auto.
    + (* areqrpy case *)
      destruct r.
      unfold run_vm_step. fold run_vm_step.
      monad_unfold.
      rewrite foo.
      rewrite <- app_assoc.
      rewrite IHil1.
      rewrite <- app_assoc.
      st_equiv.
      congruence.      
Defined.


(*
Lemma st_trace_destruct :
  forall il1 il2 e s,
    st_trace
      (fold_left run_vm_step il2
                 (fold_left run_vm_step il1
                            {| st_ev := e; st_stack := s; st_trace := [] |})) =
    st_trace
      (fold_left run_vm_step il1 
                 {| st_ev := e; st_stack := s; st_trace := [] |}) ++
      st_trace
      (fold_left run_vm_step il2
                 {| st_ev := st_ev((fold_left run_vm_step il1 
                 {| st_ev := e; st_stack := s; st_trace := [] |}));
                    st_stack := st_stack((fold_left run_vm_step il1 
                 {| st_ev := e; st_stack := s; st_trace := [] |}));
                    st_trace := [] |}).
Proof.
  intros.
  erewrite st_trace_destruct'; eauto.
Defined.
*)

Lemma destruct_compiled_appended : forall trd trd' il1 il2 e e'' s s'' p p'',
    run_vm
      (il1 ++ il2)
        {| st_ev := e;   st_stack := s;   st_trace := trd; st_pl := p |} =
        {| st_ev := e''; st_stack := s''; st_trace := trd'; st_pl := p''  |} ->
    (exists tr1 e' s' p',
        run_vm
          (il1)
          {| st_ev := e;  st_stack := s;  st_trace := trd; st_pl := p  |} =
          {| st_ev := e'; st_stack := s'; st_trace := tr1; st_pl := p'  |} /\
        exists tr2,
          run_vm
            (il2)
            {| st_ev := e';  st_stack := s';  st_trace := tr1; st_pl := p' |} =
            {| st_ev := e''; st_stack := s''; st_trace := tr1 ++ tr2; st_pl := p''  |} /\
          trd' = tr1 ++ tr2).
Proof.
  intros.
  remember (run_vm (il1) {| st_ev := e; st_stack := s; st_trace := trd; st_pl := p |}) as A.
  
  exists (st_trace A).
  exists (st_ev A).
  exists (st_stack A).
  exists (st_pl A).
  Check st_congr.

  split.
  +
    apply ya.
  +
    
  remember (run_vm (il2)
                   {| st_ev := st_ev A; st_stack := st_stack A; st_trace := st_trace A; st_pl := st_pl A |}) as B.
  exists (st_trace (run_vm (il2)
                      {| st_ev := st_ev A;
                         st_stack := st_stack A;
                         st_pl := p;
                         st_trace := [] |})).
  rewrite HeqB.
  rewrite HeqA.
  unfold run_vm in *.
  
  rewrite <- ya.

  rewrite <- fold_left_app.
  rewrite foo.
  Check st_trace_destruct'.


  assert (


      {|
                   st_ev := st_ev
                              (fold_left run_vm_step il1
                                 {|
                                 st_ev := e;
                                 st_stack := s;
                                 st_trace := trd;
                                 st_pl := p |});
                   st_stack := st_stack
                                 (fold_left run_vm_step il1
                                    {|
                                    st_ev := e;
                                    st_stack := s;
                                    st_trace := trd;
                                    st_pl := p |});
                   st_trace := [];
                   st_pl := (*st_pl
                              (fold_left run_vm_step il1
                                 {|
                                 st_ev := e;
                                 st_stack := s;
                                 st_trace := trd;
                                 st_pl := p |})*)p |} =

      {|
                   st_ev := st_ev
                              (fold_left run_vm_step il1
                                 {|
                                 st_ev := e;
                                 st_stack := s;
                                 st_trace := [];
                                 st_pl := p |});
                   st_stack := st_stack
                                 (fold_left run_vm_step il1
                                    {|
                                    st_ev := e;
                                    st_stack := s;
                                    st_trace := [];
                                    st_pl := p |});
                   st_trace := [];
                   st_pl := (*st_pl
                              (fold_left run_vm_step il1
                                 {|
                                 st_ev := e;
                                 st_stack := s;
                                 st_trace := [];
                                 st_pl := p |})*) p |}
    ). {
    eapply st_congr;
      try
        ( destruct A;
          erewrite trace_irrel; eauto;
          erewrite stack_irrel; eauto;
          
            try erewrite stack_irrel;
            try erewrite trace_irrel;
            try reflexivity; eauto). }

  
  rewrite H0.
  split.
  rewrite <- app_assoc.
  Check st_trace_destruct'.
  assert (st_pl
            (fold_left run_vm_step il1
                       {|
                         st_ev := e;
                         st_stack := s;
                         st_trace := trd;
                         st_pl := p |}) =
          st_pl
            (fold_left run_vm_step il1
                       {|
                         st_ev := e;
                         st_stack := s;
                         st_trace := [];
                         st_pl := p |})).
  eapply place_irrel.
  rewrite <- ya. reflexivity.
 (* admit. (* TODO:  trace irrel ish lemma *) *)
  (*rewrite H1. *)
  Check st_trace_destruct'.
  
  rewrite <- st_trace_destruct'.
  rewrite fold_left_app in *.
  rewrite H.
  apply ya.
  -
    rewrite <- H0.
    symmetry.
    unfold run_vm in H.
    rewrite fold_left_app in H.
    repeat 
    rewrite <- foo.
    assert (
        st_trace (fold_left run_vm_step il2
        (fold_left run_vm_step il1
           {| st_ev := e; st_stack := s; st_trace := trd; st_pl := p |})) =
        st_trace ({| st_ev := e''; st_stack := s''; st_trace := trd'; st_pl := p'' |})).
    congruence.
    simpl in H1. rewrite <- H1.

    Lemma pl_immut : forall il e s tr p,
      st_pl
                     (fold_left run_vm_step il
                        {|
                        st_ev := e;
                        st_stack := s;
                        st_trace := tr;
                        st_pl := p |}) = p.
    Proof.
    Admitted.

    assert (st_pl (fold_left run_vm_step il1
                        {|
                        st_ev := e;
                        st_stack := s;
                        st_trace := trd;
                        st_pl := p |}) = p).
    apply pl_immut.
    rewrite <- H2 at 4.
    rewrite <- ya. auto.
Defined.


Lemma restl' : forall il e e' s s' x tr p p',
    run_vm il {| st_ev := e; st_stack := s; st_trace := x; st_pl := p |} =
    {| st_ev := e'; st_stack := s'; st_trace := x ++ tr; st_pl := p' |} ->

    run_vm il {| st_ev := e; st_stack := s; st_trace := []; st_pl := p |} =
    {| st_ev := e'; st_stack := s'; st_trace := tr; st_pl := p' |}.
Proof.
  intros.
  assert (
      st_trace (run_vm il {| st_ev := e; st_stack := s; st_trace := x; st_pl := p |}) =
      st_trace ({| st_ev := e'; st_stack := s'; st_trace := x ++ tr; st_pl := p' |})).
  congruence.
  eapply st_congr;
    try eapply trace_irrel;
    try eapply stack_irrel;
    try eapply place_irrel;
    eauto.
  + rewrite foo in H0.
    simpl in H0.
    eapply app_inv_head in H0. eauto.
Defined.

Lemma destruct_compiled_appended_fresh : forall trd' il1 il2 e e'' s s'' p p'',
    run_vm
      (il1 ++ il2)
        {| st_ev := e;   st_stack := s;   st_trace := []; st_pl := p |} =
        {| st_ev := e''; st_stack := s''; st_trace := trd'; st_pl := p''  |} ->
    (exists tr1 e' s' p',
        run_vm
          (il1)
          {| st_ev := e;  st_stack := s;  st_trace := []; st_pl := p  |} =
          {| st_ev := e'; st_stack := s'; st_trace := tr1; st_pl := p'  |} /\
        exists tr2,
          run_vm
            (il2)
            {| st_ev := e';  st_stack := s';  st_trace := []; st_pl := p' |} =
            {| st_ev := e''; st_stack := s''; st_trace := tr2; st_pl := p''  |} /\
          trd' = tr1 ++ tr2).
Proof.
  intros.
  edestruct (destruct_compiled_appended); eauto.
  destruct_conjs.
  assert (p = H2). {
    assert (st_pl (run_vm il1 {| st_ev := e; st_stack := s; st_trace := []; st_pl := p |}) =
            st_pl {| st_ev := H0; st_stack := H1; st_trace := x; st_pl := H2 |}). {
    congruence. }
    rewrite pl_immut in H7.
    simpl in *. auto. }
  exists x. exists H0. exists H1. exists p.
  split.
  - 
    congruence.
  - exists H4.
    split.
    + rewrite H7.
      eapply restl'; eauto.
    + assumption.
Defined.

Lemma multi_stack_restore : forall t tr1 tr1' e e' s s' p p',
    run_vm (instr_compiler t)
           {| st_ev := e; st_stack := s;  st_trace := tr1; st_pl := p |} =
           {| st_ev := e'; st_stack := s'; st_trace := tr1'; st_pl := p' |}  ->
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
    edestruct destruct_compiled_appended; eauto.
      destruct_conjs.
      eapply IHt2.
      assert (s = H1).
      eapply IHt1; eauto.
      subst.
      eapply restl'; eauto.
  - (* abseq case *)
    destruct s.
    do_run.
    edestruct destruct_compiled_appended. apply H1.
    destruct_conjs.
    clear H1.
    
    simpl in *.
    assert (H0 = push_stack EvidenceC (splitEv s1 e) s0). {
      symmetry.
      eauto. }
    unfoldm.
    desp.
    desp.
    rewrite H1 in Heqppp.
    monad_unfold.
    unfold pop_stackm in Heqppp. monad_unfold.
    pairs.
    

    edestruct destruct_compiled_appended.
    eassumption. clear H5.
    destruct_conjs.
    unfold push_stackm in Heqppp0. monad_unfold. pairs.
    assert (H1 = push_stack EvidenceC H s0). {
      symmetry.
      eauto. }
    (*do_pop_stackm_facts.
    subst. *)
    monad_unfold.
    unfold push_stack in *.
 
    unfold run_vm_step in *. monad_unfold.
    monad_unfold.
    desp.
    invc H8. eauto.
    do_pop_stackm_facts. subst. inv H12. reflexivity.
    do_pop_stackm_fail. invc H8. inv H10.
    bogus.

    do_pop_stackm_fail. subst.
    edestruct destruct_compiled_appended; eauto.
    destruct_conjs. inv H1.
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

Lemma multi_ev_eval : forall t tr tr' e e' s s' p p',
    run_vm (instr_compiler t)
           {| st_ev := e; st_stack := s;  st_trace := tr; st_pl := p |} =
           {| st_ev := e'; st_stack := s'; st_trace := tr'; st_pl := p' |}  ->
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
    edestruct destruct_compiled_appended; eauto.
    destruct_conjs.
    simpl.
    eapply IHt2.
    assert (H0 = eval (unanno t1) e).
    eauto.
    subst.
    eauto.
    (*eapply restl'; eauto. *)
  - (* abseq case *)
    destruct s; simpl in *.
    
    unfold run_vm_step in *. monad_unfold; monad_unfold.
    
    edestruct destruct_compiled_appended. eassumption. clear H.
    destruct_conjs.

    do_run.
    desp.
    pairs.

    (*
    desp.
    Print desp.
    
    remember (pop_stackm {| st_ev := H0; st_stack := H; st_trace := x |}) as p;
    destruct p; destruct o.
    remember ( push_stackm H v) as p.
    destruct p. destruct o.
    destruct v. destruct v0. simpl in *. *)
    edestruct destruct_compiled_appended. eassumption.
    destruct_conjs. clear H7.
    do_run.
    desp.


    (*
    invc H8.
    unfold run_vm_step in *. monad_unfold.
    unfold get_ev in *. monad_unfold.

    remember (pop_stackm {| st_ev := H3; st_stack := H4; st_trace := x0 |}) as p.
    destruct p. destruct o.
    remember (push_stackm (ssc e1 H3) v) as p.
    destruct p. destruct o. *)

        
    (* destruct v. destruct v0. simpl in *. monad_unfold. *)
    (*
    unfold push_stackm in *. monad_unfold.
    unfold pop_stackm in *. monad_unfold.

    remember (pop_stack EvidenceC H4) as p.
    destruct p. destruct p.

    remember (pop_stack EvidenceC H4) as p.
    destruct p. destruct p.
    remember (pop_stack EvidenceC H0) as p.
    destruct p. destruct p.
    destruct (pop_stack EvidenceC H4).
    destruct p.
    pairs.
    pairs.
    invc Heqp4.
    invc Heqp3.
    unfold pop_stack in *.
    pairs.
    remember (pop_stack EvidenceC H0) as p.
    destruct p. destruct p.
    pairs.
    assert (H0 = push_stack EvidenceC (splitEv s1 e) s0). {
      symmetry.
      eapply multi_stack_restore; eauto. }
    subst. simpl in *.
    invc Heqp5.
    invc Heqp. *)
    invc H12.
    Check splitEv.
    do_stack1 t2.

    rewrite <- H7 in Heqppp0.
        unfold pop_stackm in Heqppp0. monad_unfold.
    
    assert (e1 = (eval (unanno t1) (splitEv s e))). {
      eapply IHt1.
      assert (H0 = e1). {

        
        pairs. reflexivity.
        }
      subst. eauto.
    }

    assert (H4 = (eval (unanno t2) (splitEv s1 e))). {
      eapply IHt2.
      assert (e0 = splitEv s1 e). {
        pairs.
        assert (H =  push_stack EvidenceC (splitEv s1 e) s0). {
          symmetry.
          eapply multi_stack_restore; eauto. }
        rewrite H0 in Heqppp.
        unfold pop_stackm in *. monad_unfold.
        inv Heqppp. pairs.
        reflexivity. }
      subst. eauto.
    }
    congruence.



     do_stack t1 t2.
   
(*
    assert (H = (push_stack EvidenceC (splitEv s1 e) s0)). {
     
      
      symmetry.
      eapply multi_stack_restore; eauto. } *)
    subst. simpl in *. unfold pop_stackm in Heqppp. monad_unfold.
    invc Heqppp.
(*
    assert (H4 = push_stack EvidenceC H0 s0). {
      symmetry.
      eapply multi_stack_restore; eauto. } *)
    (*rewrite H in Heqp0.*) unfold pop_stackm in *. monad_unfold.
    inv Heqppp0.

    do_stack1 t1.
    subst.
    unfold pop_stackm in *. monad_unfold. inv Heqppp.
Defined.

Lemma st_stack_restore : forall t e s tr p,
    st_stack
      (run_vm (instr_compiler t)
              {| st_ev := e;
                 st_stack := s;
                 st_trace := tr;
                 st_pl := p |}) = s.
Proof.
  intros.
  erewrite multi_stack_restore.
  reflexivity.
  eapply ya.
Defined.

Lemma suffix_prop : forall il e e' s s' tr tr' p p',
    run_vm il
           {|
             st_ev := e;
             st_stack := s;
             st_trace := tr;
             st_pl := p |} =
    {|
      st_ev := e';
      st_stack := s';
      st_trace := tr';
      st_pl := p' |} ->
    exists l, tr' = tr ++ l.
Proof.
  intros.
  assert (st_trace (run_vm il
           {|
             st_ev := e;
             st_stack := s;
             st_trace := tr;
           st_pl := p |}) =
    st_trace ({|
      st_ev := e';
      st_stack := s';
      st_trace := tr';
      st_pl := p' |})).
  congruence.

  simpl in H0.
  eexists.
  rewrite <- H0.
  rewrite foo.
  reflexivity.
Defined.

Lemma run_lstar : forall t tr et e e' s s' p p',
    run_vm (instr_compiler t)
           (mk_st e s [] p) =
           (mk_st e' s' tr p') ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  assert (s = s'). {
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
  induction t; intros.
  - (* aasp case *)
    destruct a;
     simpl in *; 
      invc H;
        econstructor; try (econstructor; reflexivity).
      (*haa;
      econstructor.*)
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
    Axiom run_at : forall t e s n,
      run_vm (instr_compiler t)
             {| st_ev := e; st_stack := s; st_trace := []; st_pl := n |} =
      {| st_ev := (eval (unanno t) e); st_stack := s; st_trace := remote_events t n; st_pl := n |}.
    apply run_at.

    econstructor.
    apply stattstop.
    econstructor.
    
  - (* alseq case *)
    simpl in *.
    econstructor.
    econstructor.
    edestruct destruct_compiled_appended_fresh; eauto.
    destruct_conjs.
    subst.

    do_stack1 t1.

    eapply lstar_transitive.
    
    eapply lstar_stls.
    
    rewrite H6 in H3.
    eapply IHt1; eauto.
    eapply lstar_silent_tran.
    apply stlseqstop.
    eapply IHt2.
    eauto.
    assert (p = H2). {
      assert (
          st_pl (run_vm (instr_compiler t1) {| st_ev := e; st_stack := s; st_trace := []; st_pl := p |}) =
          st_pl ({| st_ev := H0; st_stack := H1; st_trace := x; st_pl := H2 |})).
      congruence.
      rewrite pl_immut in H7. simpl in *.
      congruence. }
    subst; eauto.

  - (* abseq case *)
     destruct s; simpl in *.
    
     unfold run_vm_step in *. monad_unfold; monad_unfold.


     
       
              
     assert (exists l, tr = [Term.split (fst r) p] ++ l).
     eapply suffix_prop; eauto.
     destruct_conjs.
     rewrite H1 in H.
     assert (run_vm ((instr_compiler t1 ++
                                     abesr :: instr_compiler t2 ++ [ajoins (Init.Nat.pred (snd r))]))
                    {| st_ev := splitEv s e;
                       st_stack := push_stack EvidenceC (splitEv s1 e) s0;
                       st_trace := []; st_pl := p |} =
             {| st_ev := e'; st_stack := s0; st_trace := H0; st_pl := p' |}).
     eapply restl'; eauto.
     rewrite H1.
     
    
     edestruct destruct_compiled_appended_fresh; eauto.
     destruct_conjs.
     assert (p = H5). {
       assert (
           st_pl (run_vm (instr_compiler t1)
         {|
         st_ev := splitEv s e;
         st_stack := push_stack EvidenceC (splitEv s1 e) s0;
         st_trace := [];
         st_pl := p |}) =
           st_pl ({| st_ev := H3; st_stack := H4; st_trace := x; st_pl := H5 |})).
       congruence.
       rewrite pl_immut in H10. simpl in H10. auto. }
     clear H2.
     do_stack1 t1.
     rewrite H9.
     eapply lstar_tran.
     econstructor.
     eapply lstar_transitive.
     eapply lstar_stbsl.
     eapply IHt1. eassumption.

          
     
     rewrite H2 in H6.
     eassumption.
     simpl.
     eapply lstar_silent_tran.
     apply stbslstop.
     
     do_run.
     edestruct destruct_compiled_appended_fresh; eauto.
     destruct_conjs.
     clear H12. clear H.
     rewrite H10.
     do_stack1 t2.
     eapply lstar_transitive.
     eapply lstar_stbsr.
     eapply IHt2; eauto.
     rewrite H in H4.
     eauto.

     do_run.
     invc H12.
     eapply lstar_tran.
     assert (p' = H5). {
       assert (st_pl (run_vm (instr_compiler t2)
         {|
         st_ev := splitEv s1 e;
         st_stack := push_stack EvidenceC H3 s0;
         st_trace := [];
         st_pl := H5 |}) =
               st_pl ({| st_ev := H0; st_stack := push_stack EvidenceC H3 s0; st_trace := x0; st_pl := p' |})).
       congruence.
       rewrite pl_immut in H. simpl in H. auto. }
     subst.
     apply stbsrstop.
     econstructor.
     Unshelve. eauto. eauto.
Defined.


Require Import Main.
Require Import Event_system.
Require Import Term_system.

Theorem vm_ordered : forall t tr ev0 ev1 e e' s s',
    well_formed t ->
    run_vm
      (instr_compiler t)
      (mk_st e s [] 0) =
      (mk_st e' s' tr 0) ->
    prec (ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  Check ordered.
  eapply ordered with (p:=0) (e:=mt); eauto.
  eapply run_lstar; eauto.
Defined.