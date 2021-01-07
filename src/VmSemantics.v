(*
Proofs about the Copland Virtual Machine implementation, linking it to the Copland reference semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import More_lists Term ConcreteEvidence LTS Event_system Term_system Main.
Require Import GenStMonad MonadVM MonadVMFacts Maps StructTactics Auto.
Require Import Axioms_Io Impl_vm External_Facts Helpers_VmSemantics.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics Coq.Program.Equality.
Require Import Coq.Arith.Peano_dec Lia.

Set Nested Proofs Allowed.

Check split.

Fixpoint ev_sys (t: AnnoTerm) p: EvSys Ev :=
  match t with
  | aasp (i, j) x => leaf (i, j) (asp_event i x p)
  | aatt (i, j) q x =>
    before (i, j)
      (leaf (i, S i) (req i i p q (unanno x)))
      (*(before (S i, j)
              (ev_sys x q) *)
      (leaf (pred j, j) (rpy (pred j) (pred j) p q))
  | alseq r x y => before r (ev_sys x p)
                          (ev_sys y p)
  | abseq (i, j) s x y =>
    before (i, j)
           (leaf (i, S i)
                 (Term.split i p))
           (before (S i, j)
                   (before (S i, (pred j))
                           (ev_sys x p)
                           (ev_sys y p))
                   (leaf ((pred j), j)
                   (join (pred j) p)))
  | abpar (i, j) s x y =>
    before (i, j)
           (leaf (i, S i)
                 (Term.split i p))
           (before (S i, j)
                   (merge (S i, (pred j))
                          (ev_sys x p)
                          (ev_sys y p))
                   (leaf ((pred j), j)
                   (join (pred j) p)))
  end.

Locate ev_sys.

Inductive store_event: Ev -> Plc -> Loc -> Prop :=
| put_event: forall i x p q t, store_event (req i x p q t) p x
| get_event: forall i x p q, store_event (rpy i x p q) p x.

Inductive store_event_evsys: EvSys Ev -> Plc -> Loc -> Prop :=
| inevsys_leaf: forall r ev p loc,
    store_event ev p loc ->
    store_event_evsys (leaf r ev) p loc
| inevsys_before_l: forall r es1 es2 p loc,
    store_event_evsys es1 p loc ->
    store_event_evsys (before r es1 es2) p loc
| inevsys_before_r: forall r es1 es2 p loc,
    store_event_evsys es2 p loc ->
    store_event_evsys (before r es1 es2) p loc
| inevsys_merge_l: forall r es1 es2 p loc,
    store_event_evsys es1 p loc ->
    store_event_evsys (merge r es1 es2) p loc
| inevsys_merge_r: forall r es1 es2 p loc,
    store_event_evsys es2 p loc ->
    store_event_evsys (merge r es1 es2) p loc.

(*
Inductive merge_conflict: EvSys Ev -> Prop :=
| merge_conflictc: forall r es1 es2 loc,
    store_event_evsys es1 loc ->
    store_event_evsys es2 loc ->
    merge_conflict (merge r es1 es2).
*)

Inductive store_conflict: Plc -> EvSys Ev -> Prop :=
| store_conflict_merge: forall r es1 es2 p loc,
    store_event_evsys es1 p loc ->
    store_event_evsys es2 p loc ->
    store_conflict p (merge r es1 es2)
| store_conflict_before_l: forall r p es1 es2,
    store_conflict p es1 ->
    store_conflict p (before r es1 es2)
| store_conflict_before_r: forall r p es1 es2,
    store_conflict p es2 ->
    store_conflict p (before r es1 es2).

Inductive top_level_at: (*Plc ->*) Loc -> AnnoTerm -> Prop :=
(*| top_at_rec: forall r p q loc t',
          top_level_at q loc t' ->
          top_level_at p loc (aatt r q t') *)
| top_at_l: forall q t' loc loc2,
    top_level_at loc (aatt (loc,loc2) q t')
| top_at_r: forall q t' loc loc2,
    top_level_at (pred loc2) (aatt (loc,loc2) q t')
| top_lseq_l: forall r loc t1 t2,
    top_level_at loc t1 ->
    top_level_at loc (alseq r t1 t2)
| top_lseq_r: forall r loc t1 t2,
    top_level_at loc t2 ->
    top_level_at loc (alseq r t1 t2)
| top_bseq_l: forall r s loc t1 t2,
    top_level_at loc t1 ->
    top_level_at loc (abseq r s t1 t2)
| top_bseq_r: forall r s loc t1 t2,
    top_level_at loc t2 ->
    top_level_at loc (abseq r s t1 t2)
| top_bpar_l: forall r s loc t1 t2,
    top_level_at loc t1 ->
    top_level_at loc (abpar r s t1 t2)
| top_bpar_r: forall r s loc t1 t2,
    top_level_at loc t2 ->
    top_level_at loc (abpar r s t1 t2).

Lemma store_event_facts: forall p loc t,
    store_event_evsys (ev_sys t p) p loc ->
    top_level_at loc t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
    
      inv H;
        repeat break_let;
        try solve_by_inversion;
        inv H0; inv H1.
  -
    cbn in *.
    repeat break_let.
    invc H.
    +
      invc H5.
      invc H3.
      econstructor.
    +
      invc H5.
      invc H3.
      econstructor.
  -
    cbn in *.
    invc H.
    +
      econstructor.
      eauto.
    +
      eapply top_lseq_r.
      eauto.
  -
    cbn in *.
    repeat break_let.
    invc H.
    +
      invc H5.
      invc H3.
    +
      invc H5.
      ++
        invc H4.
        +++
          econstructor.
          eauto.
        +++
          eapply top_bseq_r.
          eauto.
      ++
        invc H4.
        invc H3.
  -
    cbn in *.
    repeat break_let.
    invc H.
    +
      invc H5.
      invc H3.
    +
      invc H5.
      ++
        invc H4.
        +++
          econstructor.
          eauto.
        +++
          eapply top_bpar_r.
          eauto.
      ++
        invc H4.
        invc H3.
Defined.

Lemma wf_att_fact: forall x y q t',
    well_formed (aatt (x, y) q t') ->
    x > (Nat.pred y) ->
    False.
Proof.
  intros.
  inv H.
  simpl in *.
  lia.
Defined.

Lemma good_par : forall r s p t1 t2 loc,
    well_formed (abpar r s t1 t2) ->
    store_event_evsys (ev_sys t1 p) p loc ->
    store_event_evsys (ev_sys t2 p) p loc ->
    False.
Proof.
  intros.
  eapply store_event_facts in H0.
  eapply store_event_facts in H1.
  inv H.
  Check anno_mono.
  inv H0; inv H1; cbn in *.

  invc H0; invc H1;
    try lia.

  invc H0; invc H1;
    try lia.

  eapply wf_att_fact.
  apply H7.
  lia.

  rewrite <- H3 in *.
  subst.
  invc H7.
  simpl in *.
  lia.


  

  invc H6.
  simpl in *.
  subst.

  invc H0; try lia.
  pose (wf_mono t' H12).
  simpl in *.
  subst.
  rewrite <- H13 in *.
  rewrite H14 in *.
  simpl in *.
  destruct (range t') eqn:hey.
  simpl in *.
  subst.
  destruct r.
  simpl in *.
  subst.
  destruct r0.
  simpl in *.
  subst.
  clear H1.
  invc H7.
  subst.

  simpl in *.
  subst.
  pose (wf_mono t1 H4).
  subst.
  rewrite H8 in *.
  subst.
  rewrite <- H6 in *; clear H6.
  rewrite <- H8 in *; clear H8.
  
  subst.
  admit.
  
Admitted.

Theorem no_store_conflicts: forall t p,
    well_formed t ->
    not (store_conflict p (ev_sys t p)).
Proof.
  Print ev_sys.
  unfold not; intros.
  generalize dependent p.
  induction t; intros.
  -
    destruct a;
      try (inv H0; repeat break_let; solve_by_inversion).
  -
    cbn in *.
    repeat break_let.
    invc H0.
    +
      solve_by_inversion.
    +
      solve_by_inversion.
  -
    inv H.
    invc H0; eauto.
  -
    inv H.
    invc H0;
      repeat break_let;
      try solve_by_inversion.
    +
      invc H1.
      solve_by_inversion.
    +
      invc H1.
      invc H3.
      ++
        invc H2; eauto.
      ++
        solve_by_inversion.
  -
    inv H.
    invc H0;
      repeat break_let;
      try solve_by_inversion.
    +
      invc H1.
      solve_by_inversion.
    +
      invc H1.
      invc H3; try solve_by_inversion.
      invc H2.



      eapply good_par; eauto.
Defined.
  
  



Lemma st_trace_irrel : forall t tr1 tr1' tr2 tr2' e e' e'' p p' p'' o o' o'',
    well_formed t ->
    copland_compile t
           {| st_ev := e;  st_trace := tr1; st_pl := p;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p'; st_store := o' |}) ->

    copland_compile t
           {| st_ev := e;  st_trace := tr2; st_pl := p;  st_store := o  |} =
    (Some tt, {| st_ev := e''; st_trace := tr2'; st_pl := p''; st_store := o'' |}) ->
    
    e' = e'' /\ p' = p'' /\ o' = o''.
Proof.
  intros.

  assert (st_ev
      (execSt (copland_compile t)
              {| st_ev := e;  st_trace := tr2; st_pl := p;  st_store := o  |}) = e').
  eapply trace_irrel_ev; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_pl
            (execSt (copland_compile t)
                    {| st_ev := e;  st_trace := tr2; st_pl := p;  st_store := o  |}) = p').
  eapply trace_irrel_pl; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_store
            (execSt (copland_compile t)
                    {| st_ev := e;  st_trace := tr2; st_pl := p;  st_store := o  |}) = o').
  eapply trace_irrel_store; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.
  repeat split; congruence.
Defined.

Lemma st_trace_cumul' : forall t m k e p o v,
    well_formed t ->
    copland_compile t
               {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |} =
    (Some tt, v) -> 
    st_trace
      ( execSt (copland_compile t)
               {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |}) =
    m ++
      st_trace
          (execSt (copland_compile t)
                  {| st_ev := e; st_trace := k; st_pl := p; st_store := o |}).
Proof.
  
  induction t; intros.
  -
    destruct r.
    destruct a;
      simpl;
      repeat rewrite app_assoc;
      reflexivity.
  -
    repeat (df; dohtac; df).
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
          (snd (copland_compile t1 {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |}))
        =
        m ++
          StVM.st_trace
          (snd (copland_compile t1 {| st_ev := e; st_trace := k; st_pl := p; st_store := o |}))).
    eapply IHt1; eauto.
    repeat subst'.
    simpl in *.
    subst.
    assert (
        StVM.st_trace
          (snd (copland_compile t2
           {| st_ev := st_ev0; st_trace := m ++ st_trace0; st_pl := st_pl0; st_store := st_store0 |})) =
        m ++
          StVM.st_trace
          (snd (copland_compile t2
           {| st_ev := st_ev0; st_trace := st_trace0; st_pl := st_pl0; st_store := st_store0 |}))) as HH.
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
           (snd (copland_compile t1 {| st_ev := splitEv s0 e; st_trace := m ++ (k ++ [Term.split n p]); st_pl := p; st_store := o |})) =
         m ++
         StVM.st_trace
         (snd (copland_compile t1 {| st_ev := splitEv s0 e; st_trace := k ++ [Term.split n p]; st_pl := p; st_store := o |}))).
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
         StVM.st_trace (snd (copland_compile t2{| st_ev := splitEv s1 e; st_trace := m ++ st_trace0; st_pl := st_pl0; st_store := st_store0 |})) =
         m ++ StVM.st_trace (snd (copland_compile t2 {| st_ev := splitEv s1 e; st_trace := st_trace0; st_pl := st_pl0; st_store := st_store0 |}))
      ).
    eapply IHt2; eauto.
    subst'.
    df.
    tauto.  
  -
    do_wf_pieces.
    repeat (df; dohtac; df).
    repeat (rewrite app_assoc).
    tauto.
Defined.

(* Instance of st_trace_cumul' where k=[] *)
Lemma st_trace_cumul : forall t m e p o v,
    well_formed t ->
    copland_compile t
               {| st_ev := e; st_trace := m; st_pl := p; st_store := o |} =
    (Some tt, v) -> 
    
    st_trace
      (execSt (copland_compile t)
              {| st_ev := e; st_trace := m; st_pl := p; st_store := o |}) =
    m ++
      st_trace
      (execSt (copland_compile t)
                     {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}).
Proof.
  intros.
  assert (m = m ++ []) as HH by (rewrite app_nil_r; auto).
  rewrite HH at 1.
  eapply st_trace_cumul'; eauto.
  rewrite app_nil_r.
  eauto.
Defined.

Lemma suffix_prop : forall t e e' tr tr' p p' o o',
    well_formed t ->
    copland_compile t
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p;
             st_store := o |} =
    (Some tt, {|
      st_ev := e';
      st_trace := tr';
      st_pl := p';
      st_store := o' |}) ->
    exists l, tr' = tr ++ l.
Proof.
  intros.
  assert (st_trace
            (execSt (copland_compile t)
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p;
             st_store := o |}) =
    st_trace ({|
      st_ev := e';
      st_trace := tr';
      st_pl := p';
      st_store := o' |})) as H00.
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
         {| st_ev := _;st_trace := ?tr; st_pl := _; st_store := _ |} =
         (Some tt,
          {| st_ev := _; st_trace := ?tr'; st_pl := _; st_store := _ |}),
         H2: well_formed ?t |- _] =>
    assert_new_proof_as_by
      (exists l, tr' = tr ++ l)
      ltac:(eapply suffix_prop; [apply H2 | apply H'])
             name
  end.

Lemma alseq_decomp : forall r t1' t2' e e'' p p'' o o'' tr,
    well_formed (alseq r t1' t2') ->
    copland_compile (alseq r t1' t2') {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p''; st_store := o'' |}) ->

    exists e' tr' p' o',
      copland_compile t1' {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
      (Some  tt, {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |}) /\
      exists tr'',
        copland_compile t2' {| st_ev := e'; st_trace := []; st_pl := p'; st_store := o' |} =
        (Some tt, {| st_ev := e''; st_trace := tr''; st_pl := p''; st_store := o'' |}) /\
        tr = tr' ++ tr''.     
Proof.
  intros.  
  do_wf_pieces.
  df.
  dosome.
  annogo.
  exists st_ev. exists st_trace. exists st_pl. exists st_store.
  split.
  reflexivity.
  destruct
    (copland_compile t2'
                {| st_ev := st_ev; st_trace := []; st_pl := st_pl; st_store := st_store |}) eqn:hey.
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
                      (o:=st_store)
                      (v:={| st_ev := st_ev0; st_trace := tr; st_pl := st_pl0; st_store := st_store0 |}).
  intros.
  repeat concludes.
  df.
  subst'.
  df.
  tauto. 
Defined.

Lemma restl : forall t e e' x tr p p' o o',
    well_formed t ->
    copland_compile t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |}) ->

    copland_compile t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}).
Proof.
  intros.
  
  assert (
      st_trace (run_cvm t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |}) =
      st_trace ({| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |})).
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
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) = e').
  eapply trace_irrel_ev; eauto.

  assert (
   st_pl
     (execSt
        (copland_compile t)
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) = p').
  eapply trace_irrel_pl; eauto.

  assert (
   st_store
     (execSt
        (copland_compile t)
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) = o').
  eapply trace_irrel_store; eauto.

  assert (
      (execSt
         (copland_compile t)
         {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) =
      {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}).
  {
    eapply st_congr; eauto.
    erewrite st_trace_cumul in H1.
    eapply app_inv_head.
    eauto.
    eauto.
    eauto.
  }
  
  destruct (copland_compile t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) eqn:aa.
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
        {| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_store := ?o |} =
        (Some tt,
         {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_pl := ?p'; st_store := ?o' |}),
        H2: well_formed ?t |- _] =>
    assert_new_proof_by
      (copland_compile t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
       (Some tt,
        {| st_ev := e'; st_trace := x; st_pl := p'; st_store := o' |}))
      ltac:(eapply restl; [apply H2 | apply H])
  end.

Lemma cvm_refines_lts_evidence : forall t tr tr' e e' p p' o o' es e's,
    well_formed t ->
    copland_compile t (mk_st e tr p o) = (Some tt, (mk_st e' tr' p' o')) ->
    Ev_Shape e es ->
    Term.eval (unanno t) p es = e's ->
    Ev_Shape e' e's.
Proof.
  induction t; intros.
  -
    destruct a;
      try (
          df;
          eauto).
  -
    do_wf_pieces.
    repeat (df; dohtac; df).    
    annogo.
    eapply IHt.
    eassumption.
    eapply copland_compile_at; eauto.
    eassumption.
    reflexivity.
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
    econstructor.
    destruct s0.
    +
      simpl.
      eapply IHt1.
      apply H3.     
      eapply copland_compile_par.
      eassumption.
      eassumption.
      tauto.
    +
      simpl.
      eapply IHt1.
      eassumption.
      eapply copland_compile_par.
      eassumption.
      econstructor.
      tauto.
    +
      destruct s1.
      ++
        simpl.
        eapply IHt2.
        eassumption.
        eapply copland_compile_par.
        eassumption.
        eassumption.
        tauto.
      ++
        simpl.
        eapply IHt2.
        eassumption.
        eapply copland_compile_par.
        eassumption.
        econstructor.
        eauto.
        Unshelve.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
Defined.
   
Lemma cvm_refines_lts_event_ordering : forall t tr et e e' p p' o o',
    well_formed t ->
    copland_compile t (mk_st e [] p o) = (Some tt, (mk_st e' tr p' o')) ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros t tr et e e' p p' o o' H.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    destruct a;
      df;
      econstructor; try (econstructor; reflexivity).
  - (* aatt case *)
    do_wf_pieces.
    destruct r.
    repeat (df; dohtac; df).
    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    cbn.
    eapply IHt; eauto.
    apply copland_compile_at.
    eassumption.
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
    eapply lstar_silent_tran.
    apply stlseqstop.
    df.
    repeat do_pl_immut.
    subst.   
    eapply IHt2; eauto.    
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
    eassumption.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
        
    eapply IHt2.
    eassumption.
    eassumption.

    econstructor.
    eapply stbsrstop.
    econstructor.
  -
    destruct s; destruct r.
    repeat (df; dohtac; df).
    econstructor.
    econstructor.
    eapply lstar_transitive.
    simpl.
    apply bpar_shuffle.
    econstructor.
    apply stbpstop.
    econstructor.     
    Unshelve.
    exact mtc.
    eauto. 
Defined.

Lemma cvm_refines_lts_event_ordering_corrolary : forall t tr et e e' p p' o o',
    well_formed t -> 
    copland_compile t (mk_st e [] p o) = (Some tt, (mk_st e' tr p' o')) ->
    st_trace (run_cvm t
                     (mk_st e [] p o)) = tr ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  destruct (copland_compile t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) eqn:hi.
  simpl in *.
  vmsts.
  simpl in *.
  apply cvm_refines_lts_event_ordering with (t:=t) (tr:=tr) (e:=e) (p:=p) (o:=o) (e':=st_ev) (p':=st_pl) (o':=st_store); eauto.
  destruct o0.
  dunit.
  rewrite hi.
  unfold run_cvm in *.
  monad_unfold.
  rewrite hi in *.
  simpl in *.
  subst.
  reflexivity.
  solve_by_inversion.
Defined.

Theorem cvm_respects_event_system' : forall t tr ev0 ev1 e e' o o',
    well_formed t -> 
    copland_compile 
      t
      (mk_st e [] 0 o) =
      (Some tt, (mk_st e' tr 0 o')) ->
    prec (Term_system.ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  eapply ordered with (p:=0) (e:=mt); eauto.
  eapply cvm_refines_lts_event_ordering; eauto.
Defined.

Theorem cvm_respects_event_system : forall t tr ev0 ev1 e e' o o' t',
    t = annotated t' -> 
    copland_compile
      t
      (mk_st e [] 0 o) =
      (Some tt, (mk_st e' tr 0 o')) ->
    prec (Term_system.ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  assert (well_formed t).
  unfold annotated in H.
    subst.
    eapply anno_well_formed; eauto.
    eapply ordered with (p:=0) (e:=mt); eauto.
    eapply cvm_refines_lts_event_ordering; eauto.
Defined.
