(*
Proofs about the Copland Virtual Machine implementation, linking it to the Copland reference semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import More_lists Defs Term_Defs AnnoFacts Term ConcreteEvidence LTS Event_system Term_system Main.
Require Import GenStMonad MonadVM MonadVMFacts Maps StructTactics Auto.
Require Import Axioms_Io Impl_vm External_Facts Helpers_VmSemantics.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics Coq.Program.Equality.
Require Import Coq.Arith.Peano_dec Lia.

Set Nested Proofs Allowed.

Lemma st_trace_irrel : forall t tr1 tr1' tr2 tr2' e e' e'' p p' p'',
    well_formed_r t ->
    copland_compile t
           {| st_ev := e;  st_trace := tr1; st_pl := p (*;  st_store := o*)  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p' (*; st_store := o'*) |}) ->

    copland_compile t
           {| st_ev := e;  st_trace := tr2; st_pl := p(*;  st_store := o*) |} =
    (Some tt, {| st_ev := e''; st_trace := tr2'; st_pl := p''(*; st_store := o''*) |}) ->
    
    e' = e'' /\ p' = p'' (*/\ o' = o''*) .
Proof.
  intros.

  assert (st_ev
      (execSt (copland_compile t)
              {| st_ev := e;  st_trace := tr2; st_pl := p (*;  st_store := o*)  |}) = e').
  eapply trace_irrel_ev; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_pl
            (execSt (copland_compile t)
                    {| st_ev := e;  st_trace := tr2; st_pl := p (*;  st_store := o*)  |}) = p').
  eapply trace_irrel_pl; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  (*
  assert (st_store
            (execSt (copland_compile t)
                    {| st_ev := e;  st_trace := tr2; st_pl := p (*;  st_store := o*)  |}) = o').
  eapply trace_irrel_store; eauto. *)
  unfold execSt in *.
  subst''.
  simpl in *.
  repeat split; congruence.
Defined.

Lemma st_trace_cumul' : forall t m k e p v,
    well_formed_r t ->
    copland_compile t
               {| st_ev := e; st_trace := m ++ k; st_pl := p (*; st_store := o*) |} =
    (Some tt, v) -> 
    st_trace
      ( execSt (copland_compile t)
               {| st_ev := e; st_trace := m ++ k; st_pl := p(*; st_store := o*) |}) =
    m ++
      st_trace
          (execSt (copland_compile t)
                  {| st_ev := e; st_trace := k; st_pl := p(*; st_store := o*) |}).
Proof.
  
  induction t; intros.
  -
    destruct r.
    destruct a;
      simpl;
      repeat rewrite app_assoc;
      reflexivity.
  -
    repeat (df; try dohtac; df).
    repeat rewrite app_assoc.
    reflexivity.
  -
    df.
    annogo.
    do_wf_pieces.
    dosome.
    do_asome.
    subst.
    df.
    dohi.
    assert (
        StVM.st_trace
          (snd (copland_compile t1 {| st_ev := e; st_trace := m ++ k; st_pl := p(*; st_store := o*) |}))
        =
        m ++
          StVM.st_trace
          (snd (copland_compile t1 {| st_ev := e; st_trace := k; st_pl := p(*; st_store := o*) |}))).
    eapply IHt1; eauto.
    repeat subst'.
    simpl in *.
    subst.
    assert (
        StVM.st_trace
          (snd (copland_compile t2
           {| st_ev := st_ev0; st_trace := m ++ st_trace0; st_pl := st_pl0(*; st_store := st_store0*) |})) =
        m ++
          StVM.st_trace
          (snd (copland_compile t2
           {| st_ev := st_ev0; st_trace := st_trace0; st_pl := st_pl0(*; st_store := st_store0*) |}))) as HH.
    eapply IHt2; eauto.
    repeat (subst'; simpl in * ).
    eauto.
    
  - (* abseq case *)
    annogo.
        
    do_wf_pieces.
    df.
    dosome.

    do_asome.
    subst.
    df.
    annogo.
    df.
    dohi.

    assert (
        StVM.st_trace
           (snd (copland_compile t1 {| st_ev := splitEv s0 e; st_trace := m ++ (k ++ [Term_Defs.split n p]); st_pl := p (*; st_store := o*) |})) =
         m ++
         StVM.st_trace
         (snd (copland_compile t1 {| st_ev := splitEv s0 e; st_trace := k ++ [Term_Defs.split n p]; st_pl := p; (*st_store := o*) |}))).
    {
      rewrite <- app_assoc in *. (*Heqp4. *)
      eapply IHt1; eauto.
    }
    subst'.
    df.
    rewrite app_assoc in *.
    subst'.
    df.  
    subst.

    assert (
         StVM.st_trace (snd (copland_compile t2{| st_ev := splitEv s1 e; st_trace := m ++ st_trace0; st_pl := st_pl0; (*st_store := st_store0*) |})) =
         m ++ StVM.st_trace (snd (copland_compile t2 {| st_ev := splitEv s1 e; st_trace := st_trace0; st_pl := st_pl0; (*st_store := st_store0*) |}))
      ).
    eapply IHt2; eauto.
    subst'.
    df.
    tauto.
    
  -
    



    annogo.
        
    do_wf_pieces.
    df.
    dosome.

    do_asome.
    subst.
    df.
    annogo.
    do_pl_immut.
    do_pl_immut.
    do_pl_immut.
    do_pl_immut.
    
    df.
    subst.
    (*
    dohtac. *)
    dosome.
    df.
    (*
    destruct (map_get st_store5 n1); try solve_by_inversion.
    df.

    assert (map_get st_store0 n1 = Some (splitEv s1 e)).
    {
      eapply store_untouched; eauto.
      econstructor.
      df.
      dohtac.
      tauto.
      invc H.
      unfold not; intros.
      unfold list_subset in *.
      unfold incl in *.
      invc H17.
      unfold not in H4.
      invc H5.
      unfold not in *.
      apply H4.
      right.
      apply in_or_app.
      eauto.
    }
    rewrite H0 in *.
    df.
     
    

    Check always_some.
    assert (o2 = Some tt).
    {
      eapply always_some; eauto.
    }
    subst.
    df.
     *)
    


    (*
    eapply IHt1 in Heqp15.
    Focus 2.
    eassumption.
    df.

    vmsts.
    df.
    
    subst'.

    eapply IHt1 in Heqp5.
    Focus 2.
    eassumption.
    df.
    vmsts.
    df.

    subst'.
    *)

    
    
    
   

    assert (
        StVM.st_trace
          (snd (copland_compile t1
                 {| st_ev := splitEv s0 e;
                    st_trace := m ++ (k ++ [Term_Defs.split n p]);
                    st_pl := p;
                    (*st_store := map_set o n1 (splitEv s1 e)*) |})) =
         m ++
         StVM.st_trace
         (snd (copland_compile t1
                               {| st_ev := splitEv s0 e;
                                  st_trace := k ++ [Term_Defs.split n p];
                                  st_pl := p;
                                  (*st_store := map_set o n1 (splitEv s1 e)*) |}))).
    {
      rewrite <- app_assoc in *. (*Heqp4. *)
      eapply IHt1; eauto.
    }
    subst'.
    df.
    rewrite app_assoc in *.
    subst'.
    df.  
    subst.

    assert (
        StVM.st_trace (snd (copland_compile t2
                                            {| st_ev := splitEv s1 e;
                                               st_trace := m ++ st_trace0;
                                               st_pl := p;
                                               (*st_store := st_store4*) |})) =
        m ++ StVM.st_trace (snd (copland_compile t2
                                                 {| st_ev := splitEv s1 e;
                                                    st_trace := st_trace0;
                                                    st_pl := p;
                                                    (*st_store := st_store4*) |}))
      ).
    eapply IHt2; eauto.
    subst'.
    df.
    subst.
    tauto.

    (*

    vmsts.
    df.
    do_pl_immut.
    subst.

    (*
    assert (e0 = splitEv s1 e). admit.
    subst.
    df. 


    


    
    tauto.
    tauto.  




















    
    do_wf_pieces.
     *)
    
    repeat (df; dohtac; df).
    repeat (rewrite app_assoc).

    dosome.
    df.
    repeat break_match; try solve_by_inversion.

    df.

    vmsts.
    df.

    repeat (rewrite app_assoc).

    vmsts.
    df.

    eapply IHt1 in Heqp5.
    Focus 2.
    eassumption.
    df.
    vmsts.
    df.subst.

    eapply IHt1 in Heqp15.
    Focus 2.
    eassumption.
    df.
    vmsts.
    df.
    subst.

    eapply IHt2 in Heqp1.

    assert 

    
    edestruct IHt1; [eassumption | eassumption | idtac].

    
    eassumption.
    eassumption.


    
    tauto.
*)
Defined.

(* Instance of st_trace_cumul' where k=[] *)
Lemma st_trace_cumul : forall t m e p v,
    well_formed_r t ->
    copland_compile t
               {| st_ev := e; st_trace := m; st_pl := p(*; st_store := o*) |} =
    (Some tt, v) -> 
    
    st_trace
      (execSt (copland_compile t)
              {| st_ev := e; st_trace := m; st_pl := p(*; st_store := o*) |}) =
    m ++
      st_trace
      (execSt (copland_compile t)
                     {| st_ev := e; st_trace := []; st_pl := p(*; st_store := o*) |}).
Proof.
  intros.
  assert (m = m ++ []) as HH by (rewrite app_nil_r; auto).
  rewrite HH at 1.
  eapply st_trace_cumul'; eauto.
  rewrite app_nil_r.
  eauto.
Defined.

Lemma suffix_prop : forall t e e' tr tr' p p',
    well_formed_r t ->
    copland_compile t
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p(*;
             st_store := o*) |} =
    (Some tt, {|
      st_ev := e';
      st_trace := tr';
      st_pl := p' (*;
      st_store := o'*) |}) ->
    exists l, tr' = tr ++ l.
Proof.
  intros.
  assert (st_trace
            (execSt (copland_compile t)
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p(*;
             st_store := o*) |}) =
    st_trace ({|
      st_ev := e';
      st_trace := tr';
      st_pl := p'(*;
      st_store := o'*) |})) as H00.
  df.
  congruence.
  simpl in H00.
  eexists.
  rewrite <- H00.
  erewrite st_trace_cumul.
  eauto.
  eauto.
  eauto.
Defined.

Ltac do_suffix name :=
  match goal with
  | [H': copland_compile ?t
         {| st_ev := _;st_trace := ?tr; st_pl := _ (*; st_store := _*) |} =
         (Some tt,
          {| st_ev := _; st_trace := ?tr'; st_pl := _ (*; st_store := _*) |}),
         H2: well_formed_r ?t |- _] =>
    assert_new_proof_as_by
      (exists l, tr' = tr ++ l)
      ltac:(eapply suffix_prop; [apply H2 | apply H'])
             name
  end.

Lemma alseq_decomp_gen : forall r t1' t2' e e'' p p'' init_tr tr,
    well_formed_r (alseq r t1' t2') ->
    copland_compile (alseq r t1' t2') {| st_ev := e; st_trace := init_tr; st_pl := p(*; st_store := o*) |} =
    (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p''(*; st_store := o''*) |}) ->

    exists e' tr' p',
      copland_compile t1' {| st_ev := e; st_trace := init_tr; st_pl := p(*; st_store := o*) |} =
      (Some  tt, {| st_ev := e'; st_trace := tr'; st_pl := p'(*; st_store := o'*) |}) /\
      (*exists tr'', *)
        copland_compile t2' {| st_ev := e'; st_trace := tr'; st_pl := p'(*; st_store := o'*) |} =
        (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p''(*; st_store := o''*) |}) (*/\
        tr = tr' ++ tr''.  *).     
Proof.
  intros.  
  do_wf_pieces.
  df.
  dosome.
  annogo.
  exists st_ev. exists st_trace. exists st_pl. (*exists st_store. *)
  split.
  reflexivity.



  (*
  destruct
    (copland_compile t2'
                {| st_ev := st_ev; st_trace := init_tr; st_pl := st_pl(*; st_store := st_store*) |}) eqn:hey.
   *)
  
  vmsts.
  do_asome.
  subst.
  annogo.

  (*
  exists st_trace0.
  dohi.
  
  split.
  reflexivity. *)

  do_suffix hi.
  do_suffix hey.
  eassumption.
Defined.

(*

  destruct_conjs.
  subst.

  pose st_trace_cumul'.

  exists hi.
  split.

  
  specialize e0 with (t:= t2') (m:=st_trace) (e:=st_ev) (p:= st_pl)
                      (*(o:=st_store) *)
                      (v:={| st_ev := st_ev0; st_trace := tr; st_pl := st_pl0(*; st_store := st_store0*) |}).
  intros.
  repeat concludes.
  repeat ff.
  df.
  subst'.
  repeat ff.
  tauto. 
Defined.
*)





Lemma alseq_decomp : forall r t1' t2' e e'' p p'' tr,
    well_formed_r (alseq r t1' t2') ->
    copland_compile (alseq r t1' t2') {| st_ev := e; st_trace := []; st_pl := p(*; st_store := o*) |} =
    (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p''(*; st_store := o''*) |}) ->

    exists e' tr' p',
      copland_compile t1' {| st_ev := e; st_trace := []; st_pl := p(*; st_store := o*) |} =
      (Some  tt, {| st_ev := e'; st_trace := tr'; st_pl := p'(*; st_store := o'*) |}) /\
      exists tr'',
        copland_compile t2' {| st_ev := e'; st_trace := []; st_pl := p'(*; st_store := o'*) |} =
        (Some tt, {| st_ev := e''; st_trace := tr''; st_pl := p''(*; st_store := o''*) |}) /\
        tr = tr' ++ tr''.     
Proof.
  intros.  
  do_wf_pieces.
  df.
  dosome.
  annogo.
  exists st_ev. exists st_trace. exists st_pl. (*exists st_store. *)
  split.
  reflexivity.
  destruct
    (copland_compile t2'
                {| st_ev := st_ev; st_trace := []; st_pl := st_pl(*; st_store := st_store*) |}) eqn:hey.
  vmsts.
  do_asome.
  subst.
  annogo.

  exists st_trace0.
  dohi.
  
  split.
  reflexivity.

  pose st_trace_cumul.
  specialize st_trace_cumul with (t:= t2') (m:=st_trace) (e:=st_ev) (p:= st_pl)
                      (*(o:=st_store) *)
                      (v:={| st_ev := st_ev0; st_trace := tr; st_pl := st_pl0(*; st_store := st_store0*) |}).
  intros.
  repeat concludes.
  df.
  subst'.
  df.
  tauto. 
Defined.

Lemma restl : forall t e e' x tr p p',
    well_formed_r t ->
    copland_compile t {| st_ev := e; st_trace := x; st_pl := p(*; st_store := o*) |} =
    (Some tt, {| st_ev := e'; st_trace := x ++ tr; st_pl := p'(*; st_store := o'*) |}) ->

    copland_compile t {| st_ev := e; st_trace := []; st_pl := p(*; st_store := o*) |} =
    (Some tt, {| st_ev := e'; st_trace := tr; st_pl := p'(*; st_store := o'*) |}).
Proof.
  intros.
  
  assert (
      st_trace (run_cvm t {| st_ev := e; st_trace := x; st_pl := p(*; st_store := o*) |}) =
      st_trace ({| st_ev := e'; st_trace := x ++ tr; st_pl := p'(*; st_store := o'*) |})).
  {
    unfold run_cvm. 
    monad_unfold.
    subst'.
    simpl.
    reflexivity.
  }
  
  unfold run_cvm in *.
  assert (
   st_ev
     (execSt
        (copland_compile t)
               {| st_ev := e; st_trace := []; st_pl := p(*; st_store := o*) |}) = e').
  eapply trace_irrel_ev; eauto.

  assert (
   st_pl
     (execSt
        (copland_compile t)
               {| st_ev := e; st_trace := []; st_pl := p(*; st_store := o*) |}) = p').
  eapply trace_irrel_pl; eauto.

  (*
  assert (
   st_store
     (execSt
        (copland_compile t)
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) = o').
  eapply trace_irrel_store; eauto.
   *)
  

  assert (
      (execSt
         (copland_compile t)
         {| st_ev := e; st_trace := []; st_pl := p(*; st_store := o*) |}) =
      {| st_ev := e'; st_trace := tr; st_pl := p'(*; st_store := o'*) |}).
  {
    eapply st_congr; eauto.
    erewrite st_trace_cumul in H1.
    eapply app_inv_head.
    eauto.
    eauto.
    eauto.
  }
  
  destruct (copland_compile t {| st_ev := e; st_trace := []; st_pl := p(*; st_store := o*) |}) eqn:aa.
  simpl in *.
  vmsts.
  simpl in *.
  repeat find_inversion.
  do_asome.
  df.
  tauto.
Defined.

Ltac do_restl :=
  match goal with
  | [H: copland_compile ?t
        {| st_ev := ?e; st_trace := ?tr; st_pl := ?p(*; st_store := ?o*) |} =
        (Some tt,
         {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_pl := ?p'(*; st_store := ?o'*) |}),
        H2: well_formed_r ?t |- _] =>
    assert_new_proof_by
      (copland_compile t {| st_ev := e; st_trace := []; st_pl := p(*; st_store := o*) |} =
       (Some tt,
        {| st_ev := e'; st_trace := x; st_pl := p'(*; st_store := o'*) |}))
      ltac:(eapply restl; [apply H2 | apply H])
  end.

Locate Ev_Shape.

Axiom remote_Ev_Shape: forall e es t n,
    Ev_Shape e es ->
    Ev_Shape (toRemote t n e) (eval (unanno t) n es).

Lemma cvm_refines_lts_evidence : forall t tr tr' e e' p p' es e's,
    well_formed_r t ->
    copland_compile t (mk_st e tr p) = (Some tt, (mk_st e' tr' p')) ->
    Ev_Shape e es ->
    Term_Defs.eval (unanno t) p es = e's ->
    Ev_Shape e' e's.
Proof.
  induction t; intros.
  -
    destruct a;
      try (
          df;
          eauto).
  -
    (*
    do_wf_pieces. *)
    repeat (df; try dohtac; df).    
    annogo.

    (*
    eapply IHt.
    eassumption.
    eapply copland_compile_at; eauto.
    eassumption.
    reflexivity.
     *)

    apply remote_Ev_Shape; eauto.

  -
    do_wf_pieces.
    do_suffix blah.
    destruct_conjs.
    subst.

    edestruct alseq_decomp.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.
    destruct_conjs.
    df.
    dosome.
    
    eapply IHt2.
    + eassumption.
    + eassumption.
    + eapply IHt1.
      ++ eassumption.
      ++ eassumption.
      ++ eassumption.      
      ++ reflexivity.
    +
      repeat do_pl_immut.
      subst.
      congruence.
      
  -
    do_wf_pieces.
    df.
    repeat break_match;
      try solve_by_inversion;
      try (df; tauto).
    +
      df.
      annogo.
      simpl in *.
      do_suffix blah.
      do_suffix blah'.
      destruct_conjs; subst.
      repeat do_restl.
      
      econstructor.
      destruct s0.
      ++
        eapply IHt1; eauto.
      ++
        simpl in *.
        eapply IHt1; eauto.
      ++
        destruct s1.
        +++
          simpl.
          repeat do_pl_immut.
          subst.
          eapply IHt2; eauto.
        +++
          simpl.
          repeat do_pl_immut.
          subst.
          eapply IHt2; eauto.

          
  -
    do_wf_pieces.
    repeat (df; dohtac; df).
    dosome.
    vmsts.
    econstructor.
    destruct s0.
    +
      simpl.
      df.
      eapply IHt1.
      apply H3.
      eassumption.
      (*
      eapply copland_compile_par. *)
      eassumption.

      tauto.
    +
      simpl.
      eapply IHt1.
      df.
      eassumption.
      (*
      eapply copland_compile_par. *)
      eassumption.
      df.
      econstructor.
      tauto.
    +
      destruct s1.
      ++
        simpl.
        df.
        eapply IHt2.
        eassumption.
        eassumption.
        (*
        eapply copland_compile_par. *)
        eassumption.
        do_pl_immut.
        do_pl_immut.
        subst.
        tauto.
      ++
        simpl.
        df.
        do_pl_immut.
        do_pl_immut.
        subst.
        eapply IHt2.
        eassumption.
        (*
        eapply copland_compile_par. *)
        eassumption.
        econstructor.
        tauto.
        (*
        eauto.
        Unshelve.
        eauto.
        eauto.
        eauto.
        eauto.
         *)
Defined.

Axiom remote_LTS: forall t n et, 
    lstar (conf t n et) (remote_events t n) (stop n (aeval t n et)).


Lemma eval_aeval: forall t1 p et,
    eval (unanno t1) p et = aeval t1 p et.
Proof.
  induction t1; intros.
  -
    ff.
  -
    ff.
  -
    ff.
    erewrite IHt1_1.
    eauto.
  -
    ff.
    erewrite IHt1_1.
    erewrite IHt1_2.
    eauto.
  -
    ff.
    erewrite IHt1_1.
    erewrite IHt1_2.
    eauto.
    
Defined.

Lemma evshape_split: forall e et s,
    Ev_Shape e et ->
    Ev_Shape (splitEv s e) (splitEv_T s et).
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros.
  -
    invc H.
    destruct s.
    ff.
    eauto.
    ff.
    eauto.
  -
    invc H.
    destruct s; ff.
  -
    invc H.
    destruct s; ff.
  -
    invc H.
    destruct s; ff.
  -
    invc H.
    destruct s; ff.
  -
    invc H.
    destruct s; ff.
    
Defined.
   
Lemma cvm_refines_lts_event_ordering : forall t tr et e e' p p',
    well_formed_r t ->
    Ev_Shape e et ->
    copland_compile t (mk_st e [] p) = (Some tt, (mk_st e' tr p')) ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros t tr et e e' p p' H H'.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    destruct a;
      df;
      econstructor; try (econstructor; reflexivity).
  - (* aatt case *)
    (*do_wf_pieces. *)
    destruct r.
    repeat (df; try dohtac; df).
    Print remote_LTS.
    
    assert (lstar (conf t n et) (remote_events t n) (stop n (aeval t n et))).
    {
      apply remote_LTS.
    }
    assert (et_fun e = et).
    {
      pose ev_evshape.
      pose (e0 e).
      eapply evshape_determ.
      eassumption.
      eassumption.
    }
    rewrite H1.
    


      
    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    cbn.
    
    
    apply H0.
    (*
    
    eapply IHt; eauto.
    admit.
    apply copland_compile_at.
    admit.
     *)
    
    (* eassumption. *)
    econstructor.
    apply stattstop.
    econstructor.
  -  
    do_wf_pieces.  
    edestruct alseq_decomp; eauto.
    destruct_conjs.         
    econstructor.
    econstructor.
    subst.
    eapply lstar_transitive.
    eapply lstar_stls.
    df.
    eapply IHt1.
    eassumption.
    eassumption.
    eassumption.
    eapply lstar_silent_tran.
    apply stlseqstop.
    df.
    repeat do_pl_immut.
    subst.   
    eapply IHt2 with (e:= x).
    eassumption.
    eapply cvm_refines_lts_evidence.
    apply H1.
    eassumption.
    eassumption.

    eapply eval_aeval; eauto.  
    eassumption.
    
    
    
  -    
    do_wf_pieces.
    destruct r; destruct s.
    df.
    vmsts.
    dosome.
    df.

    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat do_pl_immut.
    subst.
    repeat rewrite <- app_assoc.

    eapply lstar_tran.
    econstructor.
    simpl.

    eapply lstar_transitive.
    simpl.

    eapply lstar_stbsl.  
     
    eapply IHt1.
    eassumption.
    Focus 2.
    eassumption.

    eapply evshape_split; eauto.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
        
    eapply IHt2.
    eassumption.
    Focus 2.
    eassumption.
    eapply evshape_split; eauto.

    econstructor.
    eapply stbsrstop.
    econstructor.


  -    
    do_wf_pieces.
    destruct r; destruct s.
    df.
    vmsts.
    dosome.
    df.

    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat do_pl_immut.
    subst.
    repeat rewrite <- app_assoc.

    eapply lstar_tran.
    econstructor.
    simpl.

    eapply lstar_transitive.
    simpl.

    eapply lstar_stbparl.

    (*
    eapply lstar_stparl.   *)
     
    eapply IHt1.
    eassumption.
    Focus 2.
    eassumption.

    eapply evshape_split; eauto.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_transitive.

    eapply lstar_stbparr.

    (*

    eapply lstar_silent_tran.
    econstructor.

    apply stbpstop.


    
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr. *)
        
    eapply IHt2.
    eassumption.
    Focus 2.
    eassumption.
    eapply evshape_split; eauto.

    econstructor.

    eapply stbpstop.

    econstructor.
Defined.

    (*
  -
    do_wf_pieces.
    do_pl_immut.
    subst.
    destruct s; destruct r.
    repeat (df; dohtac; df).
    dosome.
    vmsts.
    df.
    
    do_pl_immut.
    df.
    subst.
    eapply lstar_transitive.
   

    econstructor.
    (*
    assert (n1 = fst (range t1)).
    {
      rewrite Heqr.
      eauto.
    }
    assert (n3 = fst (range t2)).
    {
      rewrite Heqr0.
      eauto.
    }
    subst. *)

    eapply lstar_transitive.
    simpl.
    apply bpar_shuffle.
    econstructor.
    (*
    assert (n2 = snd (range t1)).
    {
      rewrite Heqr.
      eauto.
    }
    assert (n4 = snd (range t2)).
    {
      rewrite Heqr0.
      eauto.
    }
    subst.
     *)
    
    
    apply stbpstop.
    econstructor.
    (*
    Unshelve.
    exact mtc.
    eauto.  *)
*)

Lemma cvm_refines_lts_event_ordering_corrolary : forall t tr et e e' p p',
    well_formed_r t ->
    Ev_Shape e et ->
    copland_compile t (mk_st e [] p) = (Some tt, (mk_st e' tr p')) ->
    st_trace (run_cvm t
                     (mk_st e [] p)) = tr ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  destruct (copland_compile t {| st_ev := e; st_trace := []; st_pl := p(*; st_store := o*) |}) eqn:hi.
  simpl in *.
  vmsts.
  simpl in *.
  apply cvm_refines_lts_event_ordering with (t:=t) (tr:=tr) (e:=e) (p:=p) (e':=st_ev) (p':=st_pl); eauto.
  
  (*destruct o0. *)
  try dunit.
  rewrite hi.
  unfold run_cvm in *.
  monad_unfold.
  rewrite hi in *.
  simpl in *.
  subst.
  solve_by_inversion.
  (*
  reflexivity.
  solve_by_inversion. *)
Defined.

(*
Lemma wf_implies_wfr: forall t,
    well_formed_r t ->
    well_formed_r t.
Proof.
  induction t; intros;
    try destruct a;
    ff.
Defined.
*)

Theorem cvm_respects_event_system' : forall t tr ev0 ev1 e e' et,
    well_formed_r t ->
    Ev_Shape e et ->
    copland_compile 
      t
      (mk_st e [] 0) =
      (Some tt, (mk_st e' tr 0)) ->
    prec (ev_sys t 0 et) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  eapply ordered with (p:=0) (e:=et); eauto.
  (*eapply wf_implies_wfr; eauto. *)
  eapply cvm_refines_lts_event_ordering; eauto.
Defined.

Theorem cvm_respects_event_system : forall t tr ev0 ev1 e e' t' i n et,
    (*NoDup ls ->
    length ls = nss t' -> *)
    (*t = annotated t' ls -> *)
    anno t' i = (n, t) ->
    Ev_Shape e et ->
    copland_compile
      t
      (mk_st e [] 0) =
      (Some tt, (mk_st e' tr 0)) ->
    prec (ev_sys t 0 et) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  assert (well_formed_r t).
  unfold annotated in H.
    subst.
    eapply anno_well_formed_r; eauto.
    eapply ordered with (p:=0) (e:=et); eauto.
    (*eapply wf_implies_wfr; eauto. *)
    eapply cvm_refines_lts_event_ordering; eauto.
Defined.
