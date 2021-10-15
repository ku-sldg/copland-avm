(*
Proofs about the Copland Virtual Machine implementation, linking it to the Copland reference semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import More_lists Defs Term_Defs Term ConcreteEvidence LTS Event_system Term_system Main.
Require Import GenStMonad MonadVM Maps StructTactics Auto.
Require Import Axioms_Io Impl_vm External_Facts Helpers_VmSemantics.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics Coq.Program.Equality.
Require Import Coq.Arith.Peano_dec Lia.

Set Nested Proofs Allowed.

Lemma st_trace_irrel : forall t tr1 tr1' tr2 tr2' e e' e'' p p' p'',
    well_formed_r t ->
    copland_compile t
           {| st_ev := e; st_trace := tr1; st_pl := p |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p' |}) ->

    copland_compile t
           {| st_ev := e; st_trace := tr2; st_pl := p |} =
    (Some tt, {| st_ev := e''; st_trace := tr2'; st_pl := p'' |}) ->
    
    e' = e'' /\ p' = p''.
Proof.
  intros.

  assert (st_ev
      (execSt (copland_compile t)
              {| st_ev := e; st_trace := tr2; st_pl := p |}) = e').
  eapply trace_irrel_ev; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_pl
            (execSt (copland_compile t)
                    {| st_ev := e; st_trace := tr2; st_pl := p |}) = p').
  eapply trace_irrel_pl; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.
  
  subst''.
  simpl in *.
  repeat split; try congruence.
Defined.

Lemma st_trace_cumul' : forall t m k e p v,
    well_formed_r t ->
    copland_compile t
               {| st_ev := e; st_trace := m ++ k; st_pl := p |} =
    (Some tt, v) -> 
    st_trace
      ( execSt (copland_compile t)
               {| st_ev := e; st_trace := m ++ k; st_pl := p |}) =
    m ++
      st_trace
          (execSt (copland_compile t)
                  {| st_ev := e; st_trace := k; st_pl := p |}).
Proof.
  induction t; intros.
  -
    destruct r.
    destruct a;
      simpl;
      df;
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
          (snd (copland_compile t1 {| st_ev := e; st_trace := m ++ k; st_pl := p |}))
        =
        m ++
          StVM.st_trace
          (snd (copland_compile t1 {| st_ev := e; st_trace := k; st_pl := p |}))).
    eapply IHt1; eauto.
    repeat subst'.
    simpl in *.
    subst.
    assert (
        StVM.st_trace
          (snd (copland_compile t2
           {| st_ev := st_ev0; st_trace := m ++ st_trace0; st_pl := st_pl0 |})) =
        m ++
          StVM.st_trace
          (snd (copland_compile t2
           {| st_ev := st_ev0; st_trace := st_trace0; st_pl := st_pl0 |}))) as HH.
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
          (snd (copland_compile t1 {| st_ev := (splitEv_l s e);
                                      st_trace := m ++ (k ++ [Term_Defs.split n p]);
                                      st_pl := p |})) =
         m ++
         StVM.st_trace
         (snd (copland_compile t1 {| st_ev := (splitEv_l s e);
                                     st_trace := k ++ [Term_Defs.split n p];
                                     st_pl := p |}))).
    {
      rewrite <- app_assoc in *.
      eapply IHt1; eauto.
    }
    subst'.
    df.
    rewrite app_assoc in *.
    subst'.
    df.  
    subst.

    assert (
        StVM.st_trace (snd (copland_compile t2{| st_ev := (splitEv_r s e);
                                                 st_trace := m ++ st_trace0;
                                                 st_pl := st_pl0 |})) =
        m ++ StVM.st_trace (snd (copland_compile t2 {| st_ev := (splitEv_r s e);
                                                       st_trace := st_trace0;
                                                       st_pl := st_pl0 |}))
      ).
    eapply IHt2; eauto.

    subst'.
    df.
    subst.
    tauto.

  - (* abpar case *)
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
          (snd (copland_compile t {| st_ev := (splitEv_l s e);
                                      st_trace := m ++ (k ++ [Term_Defs.split n p] ++ [cvm_thread_start n l p a (get_et (splitEv_r s e))]);
                                      st_pl := p |})) =
         m ++
         StVM.st_trace
         (snd (copland_compile t {| st_ev := (splitEv_l s e);
                                     st_trace := k ++ [Term_Defs.split n p] ++ [cvm_thread_start n l p a (get_et (splitEv_r s e))];
                                     st_pl := p |}))).
    {
      repeat rewrite <- app_assoc in *.
      eapply IHt; eauto.
    }
    subst'.

    rewrite app_assoc in *.
    subst'.
    df.
    assert (
        ((k ++ [Term_Defs.split n p]) ++
                                      [cvm_thread_start n l p a (get_et (splitEv_r s e))]) =
        ( k ++ [Term_Defs.split n p; cvm_thread_start n l p a (get_et (splitEv_r s e))])
      ).
    {
      rewrite <- app_assoc.
      tauto.
    }
    rewrite H0 in *; clear H0.
    rewrite Heqp1 in *; clear Heqp1.
    df.
    repeat rewrite <- app_assoc in *.
    df.
    subst'.
    df.
    subst.
    rewrite <- app_assoc.
    tauto.
Defined.


(* Instance of st_trace_cumul' where k=[] *)
Lemma st_trace_cumul : forall t m e p v,
    well_formed_r t ->
    copland_compile t
               {| st_ev := e; st_trace := m; st_pl := p |} =
    (Some tt, v) -> 
    
    st_trace
      (execSt (copland_compile t)
              {| st_ev := e; st_trace := m; st_pl := p |}) =
    m ++
      st_trace
      (execSt (copland_compile t)
                     {| st_ev := e; st_trace := []; st_pl := p |}).
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
             st_pl := p |} =
    (Some tt, {|
       st_ev := e';
      st_trace := tr';
      st_pl := p' |}) ->
    exists l, tr' = tr ++ l.
Proof.
  intros.
  assert (st_trace
            (execSt (copland_compile t)
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p |}) =
    st_trace ({|
                 st_ev := e';
      st_trace := tr';
      st_pl := p' |})) as H00.
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
         {| st_ev := _; st_trace := ?tr; st_pl := _ |} =
         (Some tt,
          {| st_ev := _; st_trace := ?tr'; st_pl := _ |}),
         H2: well_formed_r ?t |- _] =>
    assert_new_proof_as_by
      (exists l, tr' = tr ++ l)
      ltac:(eapply suffix_prop; [apply H2 | apply H'])
             name
  end.

Lemma alseq_decomp_gen : forall r t1' t2' e e'' p p'' init_tr tr,
    well_formed_r (alseq_par r t1' t2') ->
    copland_compile (alseq_par r t1' t2') {| st_ev := e; st_trace := init_tr; st_pl := p |} =
    (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p'' |}) ->

    exists e' tr' p',
      copland_compile t1' {| st_ev := e; st_trace := init_tr; st_pl := p |} =
      (Some  tt, {| st_ev := e'; st_trace := tr'; st_pl := p' |}) /\
        copland_compile t2' {| st_ev := e'; st_trace := tr'; st_pl := p' |} =
        (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p'' |}).     
Proof.
  intros.  
  do_wf_pieces.
  df.
  dosome.
  annogo.
  exists st_ev. exists st_trace. exists st_pl.
  split.
  reflexivity.
  
  vmsts.
  do_asome.
  subst.
  annogo.
  
  do_suffix hi.
  do_suffix hey.
  eassumption.
Defined.

Lemma alseq_decomp : forall r t1' t2' e e'' p p'' tr,
    well_formed_r (alseq_par r t1' t2') ->
    copland_compile (alseq_par r t1' t2') {| st_ev := e; st_trace := []; st_pl := p |} =
    (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p'' |}) ->

    exists e' tr' p',
      copland_compile t1' {| st_ev := e; st_trace := []; st_pl := p |} =
      (Some  tt, {| st_ev := e'; st_trace := tr'; st_pl := p' |}) /\
      exists tr'',
        copland_compile t2' {| st_ev := e'; st_trace := []; st_pl := p' |} =
        (Some tt, {| st_ev := e''; st_trace := tr''; st_pl := p'' |}) /\
        tr = tr' ++ tr''.     
Proof.
  intros.  
  do_wf_pieces.
  df.
  dosome.
  annogo.
  exists st_ev. exists st_trace. exists st_pl.
  split.
  reflexivity.
  destruct
    (copland_compile t2'
                {| st_ev := st_ev; st_trace := []; st_pl := st_pl |}) eqn:hey.
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
                      (v:={| st_ev := st_ev0; st_trace := tr; st_pl := st_pl0 |}).
  intros.
  repeat concludes.
  df.
  subst'.
  df.
  tauto. 
Defined.

Lemma restl : forall t e e' x tr p p',
    well_formed_r t ->
    copland_compile t {| st_ev := e; st_trace := x; st_pl := p |} =
    (Some tt, {| st_ev := e'; st_trace := x ++ tr; st_pl := p' |}) ->

    copland_compile t {| st_ev := e; st_trace := []; st_pl := p |} =
    (Some tt, {| st_ev := e'; st_trace := tr; st_pl := p' |}).
Proof.
  intros.
  
  assert (
      st_trace (run_cvm t {| st_ev := e; st_trace := x; st_pl := p |}) =
      st_trace ({| st_ev := e'; st_trace := x ++ tr; st_pl := p' |})).
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
               {| st_ev := e; st_trace := []; st_pl := p |}) = e').
  eapply trace_irrel_ev; eauto.

  assert (
   st_pl
     (execSt
        (copland_compile t)
               {| st_ev := e; st_trace := []; st_pl := p |}) = p').
  eapply trace_irrel_pl; eauto.
  
  assert (
      (execSt
         (copland_compile t)
         {| st_ev := e; st_trace := []; st_pl := p |}) =
      {| st_ev := e'; st_trace := tr; st_pl := p' |}).
  {
    eapply st_congr; eauto.
    erewrite st_trace_cumul in H1.
    eapply app_inv_head.
    eauto.
    eauto.
    eauto.
  }
  
  destruct (copland_compile t {| st_ev := e; st_trace := []; st_pl := p |}) eqn:aa.
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
        {| st_ev := ?e; st_trace := ?tr; st_pl := ?p |} =
        (Some tt,
         {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_pl := ?p' |}),
        H2: well_formed_r ?t |- _] =>
    assert_new_proof_by
      (copland_compile t {| st_ev := e; st_trace := []; st_pl := p |} =
       (Some tt,
        {| st_ev := e'; st_trace := x; st_pl := p' |}))
      ltac:(eapply restl; [apply H2 | apply H])
  end.

Lemma splitEv_T_l_LEFT: forall e bits bits' es e0 sp,
    et_size e = es ->
    splitEv_l (ALL,sp) (evc bits e) = (evc bits' e0) ->
    et_size e0 = es. (* (splitEv_T_l LEFT es). *)
Proof.
  intros.
  ff.
Defined.

Lemma aeval_anno: forall a i n e0,
    (aeval (snd (anno (unanno a) i)) n e0 = aeval a n e0).
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    ff.
  -
    ff.
    eauto.
    simpl.
    erewrite <- IHa.
    rewrite Heqp.
    simpl.
    tauto.
  -
    ff.
    erewrite <- IHa1.
    erewrite <- IHa2.
    rewrite Heqp0.
    rewrite Heqp.
    simpl.
    tauto.
  -
    ff.
    erewrite <- IHa1.
    erewrite <- IHa2.
    rewrite Heqp0.
    rewrite Heqp.
    simpl.
    tauto.
  -
    ff.
    erewrite <- IHa1.
    erewrite <- IHa2.
    rewrite Heqp0.
    rewrite Heqp.
    simpl.
    tauto.
Defined.

Lemma evc_inv: forall e,
    e = evc (get_bits e) (get_et e).
Proof.
  destruct e; eauto.
Defined.

Lemma front_app{A} :
  forall (x:A) xs ys,
    
    x :: xs ++ ys = [x] ++ xs ++ ys.
Proof.
  intros.
  tauto.
Defined.


Lemma cvm_refines_lts_evidence' : forall t tr tr' e e' p p',
    well_formed_r t ->
    copland_compile t (mk_st e tr p) = (Some tt, (mk_st e' tr' p')) ->
    get_et e' = (Term_Defs.eval (unanno (unannoPar t)) p (get_et e)).

Proof.
  induction t; intros.
  - (* aasp case *)
    destruct a;
      try (
          try unfold get_et;
          df;
          eauto).

  - (* at case *)
    repeat df. 
    annogo.
    do_wf_pieces.
    destruct e.
    ff.
    erewrite eval_aeval.
    simpl.
        
    rewrite aeval_anno.
    eapply remote_Evidence_Type_Axiom.

    (*
    eapply IHt.
    eassumption.
    eapply copland_compile_at.
    eassumption.
     *)
    

  - (* alseq case *)
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

    destruct x.
    destruct e'.
    vmsts.

    repeat do_pl_immut; subst.

    assert (e3 = get_et (evc e2 e3)) by tauto.
    repeat jkjke'.
    
  - (* abseq case *)
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

      assert (e1 = get_et (evc e0 e1)) by tauto.
      jkjke.
      assert (e3 = get_et (evc e2 e3)) by tauto.
      jkjke.

      assert (get_et (evc e0 e1) = (eval (unanno (unannoPar t1)) p (splitEv_T_l s (get_et e)))).
      {
        destruct s; destruct s.
        ++
          eapply IHt1;
          eassumption.
        ++
          unfold splitEv_T_l.
          assert (mt = get_et (evc [] mt)) by tauto.
          jkjke.
      }
      ff.
      rewrite H6.
      

      assert (get_et (evc e2 e3) = (eval (unanno (unannoPar t2)) p (splitEv_T_r s (get_et e)))).
      {
        repeat do_pl_immut; subst.
        destruct s.
        destruct s0.
        ++
          unfold splitEv_T_r.
          eauto.
        ++
          assert (mt = get_et (evc [] mt)) by tauto.
          jkjke.
          ff.
      }
      ff.

  - (* abpar case *)
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
      (* do_suffix blah'. *)
      destruct_conjs; subst.
      repeat do_restl.

      assert (e1 = get_et (evc e0 e1)) by tauto.
      jkjke.
      assert (e3 = get_et (evc e2 e3)) by tauto.
      jkjke.

      assert (get_et (evc e0 e1) = (eval (unanno (unannoPar t)) p (splitEv_T_l s (get_et e)))).
      {
        destruct s; destruct s.
        ++
          eapply IHt;
          eassumption.
        ++
          unfold splitEv_T_l.
          assert (mt = get_et (evc [] mt)) by tauto.
          jkjke.
      }
      ff.
      rewrite H5.

      do_pl_immut.
      subst.


      assert (e3 = (eval (unanno a) p (splitEv_T_r s (get_et e)))).
      {
        rewrite par_evidence in *.
         destruct s.
         destruct s; destruct s0;
           simpl in *.
         +
           rewrite eval_aeval with (i:=0).
           rewrite aeval_anno.
           erewrite <- remote_Evidence_Type_Axiom. (*with (bits:=[]). *)
           rewrite at_evidence.
           erewrite <- evc_inv.
           rewrite Heqe2.
           ff.
         +
           rewrite eval_aeval with (i:=0).
           rewrite aeval_anno.
           unfold mt_evc in *.
           erewrite <- remote_Evidence_Type_Axiom. (*with (bits:=[]). *)
           rewrite at_evidence.
          (* erewrite <- evc_inv. *)
           rewrite Heqe2.
           ff.
         +
           rewrite eval_aeval with (i:=0).
           rewrite aeval_anno.
           unfold mt_evc in *.
           erewrite <- remote_Evidence_Type_Axiom. (*with (bits:=[]). *)
           rewrite at_evidence.
           erewrite <- evc_inv.
           rewrite Heqe2.
           ff.
         +
           rewrite eval_aeval with (i:=0).
           rewrite aeval_anno.
           unfold mt_evc in *.
           erewrite <- remote_Evidence_Type_Axiom. (*with (bits:=[]). *)
           rewrite at_evidence.
          (* erewrite <- evc_inv. *)
           rewrite Heqe2.
           ff.
      }
      rewrite H5.
      tauto.
      Unshelve.
      eauto.
Defined.

Lemma cvm_refines_lts_evidence : forall t tr tr' bits bits' et et' p p',
    well_formed_r t ->
    copland_compile t (mk_st (evc bits et) tr p) = (Some tt, (mk_st (evc bits' et') tr' p')) ->
    et' = (Term_Defs.eval (unanno (unannoPar t)) p et).
Proof.
  intros.
  assert (et = get_et (evc bits et)) by tauto.
  assert (et' = get_et (evc bits' et')) by tauto.
  rewrite H1; rewrite H2.
  eapply cvm_refines_lts_evidence'; eauto.
Defined.

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

(*
Definition cvm_shuffled_events (e1:list CVM_Event) (e2:list CVM_Event): list CVM_Event.
Admitted.
 *)



(*

Inductive cvm_to_lts_event: Ev -> Ev -> Prop :=
| cvm_cpy: forall n p,
    cvm_to_lts_event (copy n p) (copy n p)
| cvm_umeas: forall n p i args tpl tid,
    cvm_to_lts_event (umeas n p i args tpl tid)
                     (umeas n p i args tpl tid)
| cvm_sign: forall n p et,
    cvm_to_lts_event (sign n p et)
                     (sign n p et)
| cvm_hash: forall n p et,
    cvm_to_lts_event (hash n p et)
                     (hash n p et)
| cvm_req: forall n p q t et,
    cvm_to_lts_event (req n p q t et)
                     (req n p q t et)
| cvm_rpy: forall n p q et,
    cvm_to_lts_event (rpy n p q et)
                     (rpy n p q et)
| cvm_split: forall n p,
    cvm_to_lts_event (Term_Defs.split n p)
                     (Term_Defs.split n p)
| cvm_join: forall n p,
    cvm_to_lts_event (Term_Defs.join n p)
                     (Term_Defs.join n p).
                     

Inductive cvm_to_lts_trace: list Ev -> list Ev -> Prop :=
(*| cvm_remote: forall a n,
    cvm_to_lts_trace (remote_events a n) (remote_events a n) *)
| cvm_shuffle: forall cvm_l1 lts_l1 n n0 loc p t et,
    cvm_to_lts_trace cvm_l1 lts_l1 ->
    cvm_to_lts_trace
      ([cvm_thread_start n loc p t et] ++
                                       cvm_l1 ++
                                       [cvm_thread_end n0 loc p t])
      ([Term_Defs.split n p] ++
                             (shuffled_events lts_l1 (remote_events t p)) ++
                             [join n0 p])
| cvm_refl_event: forall cvm_e1 lts_e1,
    cvm_to_lts_event cvm_e1 lts_e1 ->
    cvm_to_lts_trace [cvm_e1] [lts_e1]


    
(*
| cvm_refl: forall ls,
    (
    (forall n loc p t et,  ~ (In (cvm_thread_start n  loc  p  t et) ls)) /\
    (forall n0 loc' p' t', ~ (In (cvm_thread_end   n0 loc' p' t')   ls))
    ) ->
    cvm_to_lts_trace ls ls
*)
| cvm_move: forall tr_lts tr_cvm rest_lts rest_cvm,
    cvm_to_lts_trace tr_cvm tr_lts ->
    cvm_to_lts_trace
      rest_cvm
      rest_lts ->
    cvm_to_lts_trace (tr_cvm ++ rest_cvm) (tr_lts ++ rest_lts).
Hint Constructors cvm_to_lts_trace : core.


(*

Inductive cvm_to_lts_event: Ev -> CVM_Event -> Prop :=
| cvmlts_copy: forall n p,
    cvm_to_lts_event (copy n p) (cvm_copy n p)
| cvmlts_umeas: forall n p i args tpl tid,
    cvm_to_lts_event (umeas n p i args tpl tid)
                     (cvm_umeas n p i args tpl tid)
| cvmlts_sign: forall n p et,
    cvm_to_lts_event (sign n p et)
                     (cvm_sign n p et)
| cvmlts_hash: forall n p et,
    cvm_to_lts_event (hash n p et)
                     (cvm_hash n p et)
| cvmlts_req: forall n p q t et,
    cvm_to_lts_event (req n p q t et)
                     (cvm_req n p q t et)
| cvmlts_rpy: forall n p q et,
    cvm_to_lts_event (rpy n p q et)
                     (cvm_rpy n p q et)
| cvm_split: forall n p,
    cvm_to_lts_event (Term_Defs.split n p)
                     (cvm_split n p)
| cvmlts_join: forall n p,
    cvm_to_lts_event (Term_Defs.join n p)
                     (cvm_join n p).
(*
| cvmlts_splitp: forall n p loc t et,
    cvm_to_lts_event (Term_Defs.split n p)
                     (cvm_splitp n loc p t et)
| cvmlts_joinp: forall n p loc t,
    cvm_to_lts_event (Term_Defs.join n p)
                     (cvm_joinp n loc p t).
*)
Hint Constructors cvm_to_lts_event : core.

Check shuffled_events.
Locate shuffled_events.
Locate shuffle.


Inductive cvm_to_lts_trace: list Ev -> list CVM_Event -> Prop :=
(*| cvm_remote: forall t n,
    cvm_to_lts_trace (lts_remote_events t n) (remote_events t n) *)
| cvm_empty: cvm_to_lts_trace [] []
| cvm_shuffle: forall l1 cvm_l1 n n0 loc p t et,
    cvm_to_lts_trace l1 cvm_l1 ->
    cvm_to_lts_trace
      ([Term_Defs.split n p] ++
       (shuffled_events l1 (lts_remote_events t p)) ++
       [Term_Defs.join n0 p])
      ([cvm_splitp n loc p t et] ++ cvm_l1 ++ [cvm_joinp n0 loc p t])
      (*
| cvm_move: forall tr_lts tr_cvm rest_lts rest_cvm,
    cvm_to_lts_trace tr_lts tr_cvm ->
    cvm_to_lts_trace
      rest_lts
      rest_cvm ->
    cvm_to_lts_trace (tr_lts ++ rest_lts) (tr_cvm ++ rest_cvm)
*)
| cvm_move_one: forall e1_lts e1_cvm rest_lts rest_cvm,
    cvm_to_lts_event e1_lts e1_cvm ->
    cvm_to_lts_trace rest_lts rest_cvm ->
    cvm_to_lts_trace
      ([e1_lts] ++ rest_lts)
      ([e1_cvm] ++ rest_cvm)
| cvm_move_remote: forall a n rest_lts rest_cvm,
    (*cvm_to_lts_event e1_lts e1_cvm -> *)
    cvm_to_lts_trace rest_lts rest_cvm ->
    cvm_to_lts_trace
      (lts_remote_events a n ++ rest_lts)
      (remote_events a n ++ rest_cvm).
Hint Constructors cvm_to_lts_trace : core.
 *)

 *)

Axiom thread_bookend_peel: forall t p et etr n l a n0 tr,
    lstar (conf (unannoPar t) p et) tr (stop p (aeval (unannoPar t) p et)) ->
    ([cvm_thread_start n l p a etr] ++ tr ++ [cvm_thread_end (Nat.pred n0) l p a] =
     (shuffled_events tr (remote_events a p))
    ).


Lemma cvm_refines_lts_event_ordering : forall t cvm_tr bits bits' et et' p p',
    well_formed_r t ->
    (*Ev_Shape e et -> *)
    copland_compile t (mk_st (evc bits et) [] p) = (Some tt, (mk_st (evc bits' et') cvm_tr p')) ->
    lstar (conf (unannoPar t) p et) cvm_tr (stop p (aeval (unannoPar t) p et)).
Proof.
  intros t cvm_tr bits bits' et et' p p' H H'.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)

     destruct a;
      df;
      econstructor; try (econstructor; reflexivity).
    
      

  - (* aatt case *)
    destruct r.
    repeat (df; try dohtac; df).
    
    assert (lstar (conf a n et) (remote_events a n) (stop n (aeval a n et))).
    {
      apply remote_LTS.
    }

    

    (*
    pose ev_evshape.
    pose (e0 e).
    
    assert (et_fun e = et).
    {
      pose ev_evshape.
      pose (e0 e).
      eapply evshape_determ.
      eassumption.
      eassumption.
    }
    rewrite H1. *)
    

    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    cbn.
    
    apply H0.
    jkjke.
    ff.
    assert (et' = (aeval a n et)).
    {
      erewrite <- remote_Evidence_Type_Axiom.
      jkjke.
    }
    subst.
    
      

    econstructor.
    apply stattstop.
    econstructor.



  -  (* alseq case *)
    do_wf_pieces.
    edestruct alseq_decomp; eauto.
    destruct_conjs.
    destruct x.
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
    eapply IHt2. (*with (e:= x). *)
    eassumption.
    assert (e0 = Term_Defs.eval (unanno (unannoPar t1)) p et).
    eapply cvm_refines_lts_evidence; eauto.

    subst.
    rewrite <- eval_aeval.
    
    eassumption.


  -    (* abseq case *)
    do_wf_pieces.
    destruct r; destruct s; destruct s; destruct s0.
    +
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
      (*
    
    2: {
      eassumption.
      } *)
      eassumption.
      
      unfold run_cvm in *.
      monad_unfold.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      econstructor.

      eapply stbsrstop.
      econstructor.


    +
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
      (*
    
    2: {
      eassumption.
      } *)
      eassumption.
      
      unfold run_cvm in *.
      monad_unfold.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      econstructor.

      eapply stbsrstop.
      econstructor.
 
    +
      
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
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      unfold run_cvm in *.
      monad_unfold.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      econstructor.

      eapply stbsrstop.
      econstructor.
    +
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
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      unfold run_cvm in *.
      monad_unfold.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      econstructor.

      eapply stbsrstop.
      econstructor.





  - (* abpar case *)
    do_wf_pieces.
    destruct r; destruct s; destruct s; destruct s0.
    +
      df.
      vmsts.
      dosome.
      df.

      do_suffix blah.
      (*
      do_suffix blah'. *)
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.

      assert (lstar (conf (unannoPar t) p et) blah (stop p (aeval (unannoPar t) p et))).
      eauto.



      



      eapply lstar_tran.
      econstructor.
      simpl.

      assert (
          (cvm_thread_start n l p a et
                            :: blah ++ [cvm_thread_end (Nat.pred n0) l p a; join (Nat.pred n0) p]) =
          (([cvm_thread_start n l p a et] ++
                                         blah ++ [cvm_thread_end (Nat.pred n0) l p a]) ++ [join (Nat.pred n0) p])).
      { rewrite front_app.
        repeat rewrite <- app_assoc.
        tauto.
      }
      subst'.
      


      erewrite thread_bookend_peel.

      eapply lstar_transitive.

      eapply bpar_shuffle.
      eassumption.

      eapply lstar_tran.
      apply stbpstop.
      econstructor.
      eassumption.

    +
      df.
      vmsts.
      dosome.
      df.

      do_suffix blah.
      (*
      do_suffix blah'. *)
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.

      assert (lstar (conf (unannoPar t) p et) blah (stop p (aeval (unannoPar t) p et))).
      eauto.



      



      eapply lstar_tran.
      econstructor.
      simpl.

      assert (
          (cvm_thread_start n l p a mt
                            :: blah ++ [cvm_thread_end (Nat.pred n0) l p a; join (Nat.pred n0) p]) =
          (([cvm_thread_start n l p a mt] ++
                                         blah ++ [cvm_thread_end (Nat.pred n0) l p a]) ++ [join (Nat.pred n0) p])).
      { rewrite front_app.
        repeat rewrite <- app_assoc.
        tauto.
      }
      subst'.
      


      erewrite thread_bookend_peel.

      eapply lstar_transitive.

      eapply bpar_shuffle.
      eassumption.

      eapply lstar_tran.
      apply stbpstop.
      econstructor.
      eassumption.





          +
      df.
      vmsts.
      dosome.
      df.

      do_suffix blah.
      (*
      do_suffix blah'. *)
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.

      assert (lstar (conf (unannoPar t) p mt) blah (stop p (aeval (unannoPar t) p mt))).
      eauto.



      



      eapply lstar_tran.
      econstructor.
      simpl.

      assert (
          (cvm_thread_start n l p a et
                            :: blah ++ [cvm_thread_end (Nat.pred n0) l p a; join (Nat.pred n0) p]) =
          (([cvm_thread_start n l p a et] ++
                                         blah ++ [cvm_thread_end (Nat.pred n0) l p a]) ++ [join (Nat.pred n0) p])).
      { rewrite front_app.
        repeat rewrite <- app_assoc.
        tauto.
      }
      subst'.
      


      erewrite thread_bookend_peel.

      eapply lstar_transitive.

      eapply bpar_shuffle.
      eassumption.

      eapply lstar_tran.
      apply stbpstop.
      econstructor.
      eassumption.




          +
      df.
      vmsts.
      dosome.
      df.

      do_suffix blah.
      (*
      do_suffix blah'. *)
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.

      assert (lstar (conf (unannoPar t) p mt) blah (stop p (aeval (unannoPar t) p mt))).
      eauto.



      



      eapply lstar_tran.
      econstructor.
      simpl.

      assert (
          (cvm_thread_start n l p a mt
                            :: blah ++ [cvm_thread_end (Nat.pred n0) l p a; join (Nat.pred n0) p]) =
          (([cvm_thread_start n l p a mt] ++
                                         blah ++ [cvm_thread_end (Nat.pred n0) l p a]) ++ [join (Nat.pred n0) p])).
      { rewrite front_app.
        repeat rewrite <- app_assoc.
        tauto.
      }
      subst'.
      


      erewrite thread_bookend_peel.

      eapply lstar_transitive.

      eapply bpar_shuffle.
      eassumption.

      eapply lstar_tran.
      apply stbpstop.
      econstructor.
      eassumption.
Defined.







(*

Lemma cvm_refines_lts_event_ordering : forall t cvm_tr bits bits' et et' p p',
    well_formed_r t ->
    (*Ev_Shape e et -> *)
    copland_compile t (mk_st (evc bits et) [] p) = (Some tt, (mk_st (evc bits' et') cvm_tr p')) ->
    exists tr,
    lstar (conf (unannoPar t) p et) tr (stop p (aeval (unannoPar t) p et)) /\
    cvm_to_lts_trace cvm_tr tr.
Proof.
  intros t cvm_tr bits bits' et et' p p' H.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    destruct a;
      df;
      eexists;
      split;
      econstructor; try econstructor;
        try (
            unfold not; intros;
            invc H0; try solve_by_inversion).

    (*
    +
      invc H'';
        try solve_by_inversion.
      invc H0;
        try solve_by_inversion.
      invc H1; try solve_by_inversion.
    +
      invc H'';
        try solve_by_inversion.
      invc H0;
        try solve_by_inversion.
      invc H1; try solve_by_inversion.
    +
      invc H'';
        try solve_by_inversion.
      invc H0;
        try solve_by_inversion.
      invc H1; try solve_by_inversion.
    +
      invc H'';
        try solve_by_inversion.
      invc H0;
        try solve_by_inversion.
      invc H1; try solve_by_inversion.
    (*
      econstructor; try (econstructor; reflexivity).

  (*
    
    +
      assert (et = et_fun e).
      {
        eapply evshape_determ; eauto.
        apply ev_evshape; eauto.
      }
      rewrite <- H0.
      econstructor; try (econstructor; reflexivity). *)
     *)
     *)
    
      
    
    
  - (* aatt case *)
    destruct r.
    repeat (df; try dohtac; df).
    
    assert (lstar (conf a n et) (remote_events a n) (stop n (aeval a n et))).
    {
      
      apply remote_LTS.
    }

    

    (*
    pose ev_evshape.
    pose (e0 e).
    
    assert (et_fun e = et).
    {
      pose ev_evshape.
      pose (e0 e).
      eapply evshape_determ.
      eassumption.
      eassumption.
    }
    rewrite H1. *)




    (*

    invc H''; try solve_by_inversion.
    invc H2; try solve_by_inversion.

    assert ((req n0 p' n (unanno a) et :: tr0) =
            [req n0 p' n (unanno a) et] ++ tr0).
    admit.
    rewrite H2; clear H2.

    assert (    (cvm_req n0 p' n (unanno a) et
     :: remote_events a n ++
     [cvm_rpy (Nat.pred n1) p' n (get_et (toRemote a n (evc bits et)))]) =
                ( [cvm_req n0 p' n (unanno a) et]
     ++ remote_events a n ++
     [cvm_rpy (Nat.pred n1) p' n (get_et (toRemote a n (evc bits et)))])).
    admit.
    rewrite H2; clear H2.
    econstructor.
    econstructor.
    econstructor.
    simpl in *.

    Lemma lstar_at_decomp: forall i p a n et tr,
      lstar (rem i p (conf a n et)) tr (stop p (aeval a n et)) ->
      exists tr1, 
        tr = tr1 ++ [rpy (Nat.pred i) p n (aeval a n et)] /\
        lstar (conf a n et) tr1 (stop n (aeval a n et)).
    Proof.
    Admitted.

    edestruct lstar_at_decomp; eauto.
    destruct_conjs.
    rewrite H2.

    econstructor.

    Axiom remote_lts_axiom: forall a n et x,
      lstar (conf a n et) x (stop n (aeval a n et)) ->
      x = lts_remote_events a n.

    simpl.

    assert (x = lts_remote_events a n).
    {
      eapply remote_lts_axiom; eauto.
    }
    rewrite H5.

    admit. (* TODO: lemma or extra rule in relation? *)
    econstructor.
    rewrite remote_Evidence_Type_Axiom.
    econstructor.
    

    (*
    erewrite remote_lts_axiom.
    
    

    simpl in *.

    Check lstar_strem.

    invc H3; try solve_by_inversion.
    admit.
    invc H2.
    invc H2; try solve_by_inversion.
    admit.
    invc H2.
    invc H9
    invc H4; try solve_by_inversion.
    invc H2; try solve_by_inversion.


    
    eapply cvm_move.
*)



     *)




    eexists.
    split.
    

    
    

    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    cbn.
    
    apply H0.
    (*
    jkjke.
    ff. *)
    assert (et' = (aeval a n et)).
    {
      erewrite <- remote_Evidence_Type_Axiom.
      jkjke.
    }
    subst.
    
      

    econstructor.
    apply stattstop.
    econstructor.
    simpl.



     repeat (rewrite front_app).
     

     (*
     assert ((req n0 p' n (unanno a) et  :: lts_remote_events a n ++ [rpy (Nat.pred n1) p' n (aeval a n et)]) =
             [req n0 p' n (unanno a) et] ++  lts_remote_events a n ++ [rpy (Nat.pred n1) p' n (aeval a n et)]).
     {
       tauto.
       Search app.

      

       rewrite front_app.
       tauto.
     }

    rewrite H1; clear H1.

    assert (    (cvm_req n0 p' n (unanno a) et
     :: remote_events a n ++
     [cvm_rpy (Nat.pred n1) p' n (get_et (toRemote a n (evc bits et)))]) =
                ( [cvm_req n0 p' n (unanno a) et]
     ++ remote_events a n ++
     [cvm_rpy (Nat.pred n1) p' n (get_et (toRemote a n (evc bits et)))])).
    admit.
    rewrite H1; clear H1.
      *)
     
    econstructor.
    econstructor.

    (*
    split.
    +
      intros.
      unfold not; intros HH;
        invc HH; try solve_by_inversion.
     *)
    

    (*
    split; intros;
      try (
          unfold not; intros HH;
          invc HH; try solve_by_inversion).
     *)
    


    
    econstructor.

    econstructor.

    (*

    Axiom not_thread_start_remote: forall n loc p t et a q,
        ~ In (cvm_thread_start n loc p t et) (remote_events a q).

     Axiom not_thread_end_remote: forall n loc p t a q,
      ~ In (cvm_thread_end n loc p t) (remote_events a q).

     split; intros;
       try apply not_thread_start_remote;
       try apply not_thread_end_remote.
     *)
    
      



    
    (*
    admit. (*econstructor.*) (* TODO: lemma or extra rule in relation?   Done... *)
     
    
    econstructor. *)

    admit. (* TODO: axiom or lstar lemma *)

    econstructor.
    
    rewrite remote_Evidence_Type_Axiom.
    econstructor.
   

    (*
    split; intros;
      try (
          unfold not; intros HH;
          invc HH; try solve_by_inversion).
     *)
    
   

    
    
  -  
    do_wf_pieces.
    edestruct alseq_decomp; eauto.
    destruct_conjs.
    destruct x.
    subst.
    df.
    edestruct IHt1; eauto.
    edestruct IHt2; eauto.
    destruct_conjs.
    eexists.
    split.
    +
      

      eapply lstar_transitive.
      eapply lstar_silent_tran.
      econstructor.

    eapply lstar_stls.
    df.
    simpl.
    eassumption.
    (*
    eapply IHt1.
    eassumption.
    eassumption. *)

    eapply lstar_silent_tran.
    apply stlseqstop.
    df.
    repeat do_pl_immut.
    subst.

    assert (e0 = Term_Defs.eval (unanno (unannoPar t1)) p et).
    eapply cvm_refines_lts_evidence; eauto.
    subst.
    rewrite <- eval_aeval.
    

    
    eassumption.
    +
      econstructor; eauto.

      (*
      eauto.

      



      
      invc H9.
      ++
        simpl.
        eauto.
      ++
        



        
      eauto.
      simpl.
      econstructor.
      eauto.
      eauto.
       *)
      


    (*
    eapply IHt2. (*with (e:= x). *)
    eassumption.
    assert (e0 = Term_Defs.eval (unanno t1) p et).
    eapply cvm_refines_lts_evidence; eauto.

    subst.
    rewrite <- eval_aeval.
    
    eassumption.
     *)
    
    
  -    (* abseq case *)
    do_wf_pieces.
    destruct r; destruct s; destruct s; destruct s0.
    +
      df.
      vmsts.
      dosome.
      df.
      simpl.

      do_suffix blah.
      do_suffix blah'.
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.
      edestruct IHt1; eauto.
      edestruct IHt2; eauto.
      destruct_conjs.

      eexists.
      split.
      ++

      eapply lstar_tran.
      econstructor.
      simpl.

      eapply lstar_transitive.
      simpl.

      eapply lstar_stbsl.
      eassumption.

      (*
      
      eapply IHt1.
      eassumption. 
      (*
    
    2: {
      eassumption.
      } *)
      eassumption.
       *)
      
      
      unfold run_cvm in *.
      monad_unfold.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.

      eassumption.

      (*
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption. *)
      
      econstructor.

      eapply stbsrstop.
      econstructor.
      ++
        simpl.
        repeat (rewrite front_app).
        (*
        assert ((Term_Defs.split n p :: x ++ x0 ++ [join (Nat.pred n0) p]) =
                ([Term_Defs.split n p] ++ x ++ x0 ++ [join (Nat.pred n0) p])).
        admit.
        rewrite H8.

        assert ((StVM.cvm_split n p :: blah' ++ blah ++ [cvm_join (Nat.pred n0) p]) =
                ([StVM.cvm_split n p] ++ blah' ++ blah ++ [cvm_join (Nat.pred n0) p])).
        admit.
        rewrite H9.
         *)
        
        econstructor.
        econstructor.

        (*

        split; intros;
          try (
              unfold not; intros HH;
              invc HH; try solve_by_inversion).
         *)

        econstructor.
        
        


        
        econstructor.
        eauto.
        econstructor.
        eauto.
        econstructor.

        (*

        split; intros;
          try (
              unfold not; intros HH;
              invc HH; try solve_by_inversion).
         *)

        econstructor.
        
    +
      
      df.
      vmsts.
      dosome.
      df.
      simpl.

      do_suffix blah.
      do_suffix blah'.
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.
      edestruct IHt1; eauto.
      edestruct IHt2; eauto.
      destruct_conjs.

      eexists.
      split.
      ++

      eapply lstar_tran.
      econstructor.
      simpl.

      eapply lstar_transitive.
      simpl.

      eapply lstar_stbsl.
      eassumption.

      (*
      
      eapply IHt1.
      eassumption. 
      (*
    
    2: {
      eassumption.
      } *)
      eassumption.
       *)
      
      
      unfold run_cvm in *.
      monad_unfold.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.

      eassumption.

      (*
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption. *)
      
      econstructor.

      eapply stbsrstop.
      econstructor.
      ++
        simpl.
        repeat (rewrite front_app).
        (*
        assert ((Term_Defs.split n p :: x ++ x0 ++ [join (Nat.pred n0) p]) =
                ([Term_Defs.split n p] ++ x ++ x0 ++ [join (Nat.pred n0) p])).
        admit.
        rewrite H8.

        assert ((StVM.cvm_split n p :: blah' ++ blah ++ [cvm_join (Nat.pred n0) p]) =
                ([StVM.cvm_split n p] ++ blah' ++ blah ++ [cvm_join (Nat.pred n0) p])).
        admit.
        rewrite H9.
        eauto.
         *)




        econstructor.
        econstructor.

        (*

        split; intros;
      try (
          unfold not; intros HH;
          invc HH; try solve_by_inversion).
         *)
        econstructor.
        


        
        econstructor.
        eauto.
        econstructor.
        eauto.
        econstructor.

        (*

        split; intros;
      try (
          unfold not; intros HH;
          invc HH; try solve_by_inversion).
         *)
        econstructor.





        (*
        
        econstructor.
        econstructor.
        econstructor.
        eauto.
         *)
        
    +
      df.
      vmsts.
      dosome.
      df.
      simpl.

      do_suffix blah.
      do_suffix blah'.
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.
      edestruct IHt1; eauto.
      edestruct IHt2; eauto.
      destruct_conjs.

      eexists.
      split.
      ++

      eapply lstar_tran.
      econstructor.
      simpl.

      eapply lstar_transitive.
      simpl.

      eapply lstar_stbsl.
      eassumption.

      (*
      
      eapply IHt1.
      eassumption. 
      (*
    
    2: {
      eassumption.
      } *)
      eassumption.
       *)
      
      
      unfold run_cvm in *.
      monad_unfold.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.

      eassumption.

      (*
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption. *)
      
      econstructor.

      eapply stbsrstop.
      econstructor.
      ++
        simpl.
        repeat (rewrite front_app).
        (*
        assert ((Term_Defs.split n p :: x ++ x0 ++ [join (Nat.pred n0) p]) =
                ([Term_Defs.split n p] ++ x ++ x0 ++ [join (Nat.pred n0) p])).
        admit.
        rewrite H8.

        assert ((StVM.cvm_split n p :: blah' ++ blah ++ [cvm_join (Nat.pred n0) p]) =
                ([StVM.cvm_split n p] ++ blah' ++ blah ++ [cvm_join (Nat.pred n0) p])).
        admit.
        rewrite H9.
        eauto.
         *)

                econstructor.
                econstructor.

                (*

        split; intros;
      try (
          unfold not; intros HH;
          invc HH; try solve_by_inversion).
                 *)
                econstructor.
        


        
        econstructor.
        eauto.
        econstructor.
        eauto.
        econstructor.

        (*

        split; intros;
      try (
          unfold not; intros HH;
          invc HH; try solve_by_inversion).
         *)
        econstructor.



        (*
        econstructor.
        econstructor.
        econstructor.
        eauto.
         *)
        
    +
      df.
      vmsts.
      dosome.
      df.
      simpl.

      do_suffix blah.
      do_suffix blah'.
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.
      edestruct IHt1; eauto.
      edestruct IHt2; eauto.
      destruct_conjs.

      eexists.
      split.
      ++

      eapply lstar_tran.
      econstructor.
      simpl.

      eapply lstar_transitive.
      simpl.

      eapply lstar_stbsl.
      eassumption.

      (*
      
      eapply IHt1.
      eassumption. 
      (*
    
    2: {
      eassumption.
      } *)
      eassumption.
       *)
      
      
      unfold run_cvm in *.
      monad_unfold.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.

      eassumption.

      (*
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption. *)
      
      econstructor.

      eapply stbsrstop.
      econstructor.
      ++
        simpl.
        repeat (rewrite front_app).
        (*
        assert ((Term_Defs.split n p :: x ++ x0 ++ [join (Nat.pred n0) p]) =
                ([Term_Defs.split n p] ++ x ++ x0 ++ [join (Nat.pred n0) p])).
        admit.
        rewrite H8.

        assert ((StVM.cvm_split n p :: blah' ++ blah ++ [cvm_join (Nat.pred n0) p]) =
                ([StVM.cvm_split n p] ++ blah' ++ blah ++ [cvm_join (Nat.pred n0) p])).
        admit.
        rewrite H9.
        eauto.
         *)


                econstructor.
        econstructor.

        (*
        split; intros;
      try (
          unfold not; intros HH;
          invc HH; try solve_by_inversion).
         *)
        econstructor.
        


        
        econstructor.
        eauto.
        econstructor.
        eauto.
        econstructor.

        (*
        split; intros;
      try (
          unfold not; intros HH;
          invc HH; try solve_by_inversion).
         *)
        econstructor.


        (*
        econstructor.
        econstructor.
        econstructor.
        eauto.
         *)
        

        
    
(*   
    +
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
      (*
    
    2: {
      eassumption.
      } *)
      eassumption.
      
      unfold run_cvm in *.
      monad_unfold.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      econstructor.

      eapply stbsrstop.
      econstructor.
 
    +
      
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
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      unfold run_cvm in *.
      monad_unfold.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      econstructor.

      eapply stbsrstop.
      econstructor.
    +
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
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      unfold run_cvm in *.
      monad_unfold.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      econstructor.

      eapply stbsrstop.
      econstructor.
 *)



  - (* abpar case *)
    do_wf_pieces.
    destruct r; destruct s; destruct s; destruct s0.
    +
      df.
      vmsts.
      dosome.
      df.
      simpl.

      do_suffix blah.
      (* do_suffix blah'. *)
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.
      edestruct IHt; eauto.
      (*
      edestruct IHt2; eauto. *)
      destruct_conjs.


      exists ([Term_Defs.split n p] ++ (shuffled_events x (remote_events a p)) ++
                               [Term_Defs.join (Nat.pred n0) p]).

      
      split.
      ++

      eapply lstar_tran.
      econstructor.
      simpl.

      eapply lstar_transitive.
      simpl.



      simpl.
      apply bpar_shuffle.
      eassumption.



      (*

      eapply lstar_stbparl.
      eassumption.

      (*
      
      eapply IHt1.
      eassumption. 
      (*
    
    2: {
      eassumption.
      } *)
      eassumption.
       *)
      
      
      unfold run_cvm in *.
      monad_unfold.

      (*

      eapply lstar_silent_tran.
      apply stbplstop. *)
      
      eapply lstar_transitive.
      eapply lstar_stbparr.

      apply remote_LTS.  *)
      econstructor.
      eapply stbpstop.
      econstructor.
      ++

        (*
        simpl.

        assert ( (Term_Defs.split n p :: x ++ lts_remote_events a p ++ [join (Nat.pred n0) p]) =
                 ([Term_Defs.split n p] ++ x ++ lts_remote_events a p ++ [join (Nat.pred n0) p])).
        admit.
        rewrite H5; clear H5.



        assert ((cvm_splitp n l p a et :: blah ++ [cvm_joinp (Nat.pred n0) l p a]) =
                ([cvm_splitp n l p a et] ++ blah ++ [cvm_joinp (Nat.pred n0) l p a])).
        admit.
        rewrite H5; clear H5. *)

          



        

        eapply cvm_shuffle.
        eassumption.
    +
      df.
      vmsts.
      dosome.
      df.
      simpl.

      do_suffix blah.
      (* do_suffix blah'. *)
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.
      edestruct IHt; eauto.
      (*
      edestruct IHt2; eauto. *)
      destruct_conjs.


      exists ([Term_Defs.split n p] ++ (shuffled_events x (remote_events a p)) ++
                               [Term_Defs.join (Nat.pred n0) p]).

      
      split.
      ++

      eapply lstar_tran.
      econstructor.
      simpl.

      eapply lstar_transitive.
      simpl.



      simpl.
      apply bpar_shuffle.
      eassumption.



      (*

      eapply lstar_stbparl.
      eassumption.

      (*
      
      eapply IHt1.
      eassumption. 
      (*
    
    2: {
      eassumption.
      } *)
      eassumption.
       *)
      
      
      unfold run_cvm in *.
      monad_unfold.

      (*

      eapply lstar_silent_tran.
      apply stbplstop. *)
      
      eapply lstar_transitive.
      eapply lstar_stbparr.

      apply remote_LTS.  *)
      econstructor.
      eapply stbpstop.
      econstructor.
      ++

        (*
        simpl.

        assert ( (Term_Defs.split n p :: x ++ lts_remote_events a p ++ [join (Nat.pred n0) p]) =
                 ([Term_Defs.split n p] ++ x ++ lts_remote_events a p ++ [join (Nat.pred n0) p])).
        admit.
        rewrite H5; clear H5.



        assert ((cvm_splitp n l p a et :: blah ++ [cvm_joinp (Nat.pred n0) l p a]) =
                ([cvm_splitp n l p a et] ++ blah ++ [cvm_joinp (Nat.pred n0) l p a])).
        admit.
        rewrite H5; clear H5. *)

        eapply cvm_shuffle.
        eassumption.
    +
      df.
      vmsts.
      dosome.
      df.
      simpl.

      do_suffix blah.
      (* do_suffix blah'. *)
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.
      edestruct IHt; eauto.
      (*
      edestruct IHt2; eauto. *)
      destruct_conjs.


      exists ([Term_Defs.split n p] ++ (shuffled_events x (remote_events a p)) ++
                               [Term_Defs.join (Nat.pred n0) p]).

      
      split.
      ++

      eapply lstar_tran.
      econstructor.
      simpl.

      eapply lstar_transitive.
      simpl.



      simpl.
      apply bpar_shuffle.
      eassumption.



      (*

      eapply lstar_stbparl.
      eassumption.

      (*
      
      eapply IHt1.
      eassumption. 
      (*
    
    2: {
      eassumption.
      } *)
      eassumption.
       *)
      
      
      unfold run_cvm in *.
      monad_unfold.

      (*

      eapply lstar_silent_tran.
      apply stbplstop. *)
      
      eapply lstar_transitive.
      eapply lstar_stbparr.

      apply remote_LTS.  *)
      econstructor.
      eapply stbpstop.
      econstructor.
      ++

        (*
        simpl.

        assert ( (Term_Defs.split n p :: x ++ lts_remote_events a p ++ [join (Nat.pred n0) p]) =
                 ([Term_Defs.split n p] ++ x ++ lts_remote_events a p ++ [join (Nat.pred n0) p])).
        admit.
        rewrite H5; clear H5.



        assert ((cvm_splitp n l p a et :: blah ++ [cvm_joinp (Nat.pred n0) l p a]) =
                ([cvm_splitp n l p a et] ++ blah ++ [cvm_joinp (Nat.pred n0) l p a])).
        admit.
        rewrite H5; clear H5. *)

        eapply cvm_shuffle.
        eassumption.
    +
      df.
      vmsts.
      dosome.
      df.
      simpl.

      do_suffix blah.
      (* do_suffix blah'. *)
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.
      edestruct IHt; eauto.
      (*
      edestruct IHt2; eauto. *)
      destruct_conjs.

      exists ([Term_Defs.split n p] ++ (shuffled_events x (remote_events a p)) ++
                               [Term_Defs.join (Nat.pred n0) p]).

      
      split.
      ++

      eapply lstar_tran.
      econstructor.
      simpl.

      eapply lstar_transitive.
      simpl.



      simpl.
      apply bpar_shuffle.
      eassumption.



      (*

      eapply lstar_stbparl.
      eassumption.

      (*
      
      eapply IHt1.
      eassumption. 
      (*
    
    2: {
      eassumption.
      } *)
      eassumption.
       *)
      
      
      unfold run_cvm in *.
      monad_unfold.

      (*

      eapply lstar_silent_tran.
      apply stbplstop. *)
      
      eapply lstar_transitive.
      eapply lstar_stbparr.

      apply remote_LTS.  *)
      econstructor.
      eapply stbpstop.
      econstructor.
      ++

        (*
        simpl.

        assert ( (Term_Defs.split n p :: x ++ lts_remote_events a p ++ [join (Nat.pred n0) p]) =
                 ([Term_Defs.split n p] ++ x ++ lts_remote_events a p ++ [join (Nat.pred n0) p])).
        admit.
        rewrite H5; clear H5.



        assert ((cvm_splitp n l p a et :: blah ++ [cvm_joinp (Nat.pred n0) l p a]) =
                ([cvm_splitp n l p a et] ++ blah ++ [cvm_joinp (Nat.pred n0) l p a])).
        admit.
        rewrite H5; clear H5. *)

        eapply cvm_shuffle.
        eassumption.



        (*

        Unshelve.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        exact (aasp (0,0) CPY).
        exact (aasp (0,0) CPY).
        eauto.
         *)
        
Admitted.


  *)      













  





(****  OLD CVM REFINES LTS ORDERING PROOF   








        




      
        econstructor.
        econstructor.
        econstructor.
        econstructor






        
        

      eapply lts_remote_events.

      

      eassumption.

      (*
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption. *)
      
      econstructor.

      eapply stbsrstop.
      econstructor.
      ++
        simpl.
        assert ((Term_Defs.split n p :: x ++ x0 ++ [join (Nat.pred n0) p]) =
                ([Term_Defs.split n p] ++ x ++ x0 ++ [join (Nat.pred n0) p])).
        admit.
        rewrite H8.

        assert ((StVM.cvm_split n p :: blah' ++ blah ++ [cvm_join (Nat.pred n0) p]) =
                ([StVM.cvm_split n p] ++ blah' ++ blah ++ [cvm_join (Nat.pred n0) p])).
        admit.
        rewrite H9.
        eauto.
        econstructor.
        econstructor.
        econstructor.
        eauto.









    
    +
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
      
      eapply IHt1.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      unfold run_cvm in *.
      monad_unfold.

      (*
    eapply lstar_transitive.
    
    apply stbpstepleft.
    apply stbpstop. *)
      
      eapply lstar_transitive.
      eapply lstar_stbparr.
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      econstructor.

      eapply stbpstop.
      econstructor.

    +
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
      
      eapply IHt1.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      unfold run_cvm in *.
      monad_unfold.

      (*
    eapply lstar_transitive.
    
    apply stbpstepleft.
    apply stbpstop. *)
      
      eapply lstar_transitive.
      eapply lstar_stbparr.
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      econstructor.

      eapply stbpstop.
      econstructor.

    +
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
      
      eapply IHt1.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      unfold run_cvm in *.
      monad_unfold.

      (*
    eapply lstar_transitive.
    
    apply stbpstepleft.
    apply stbpstop. *)
      
      eapply lstar_transitive.
      eapply lstar_stbparr.
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.

      econstructor.

      eapply stbpstop.
      econstructor.

    +
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
      
      eapply IHt1.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      unfold run_cvm in *.
      monad_unfold.

      (*
    eapply lstar_transitive.
    
    apply stbpstepleft.
    apply stbpstop. *)
      
      eapply lstar_transitive.
      eapply lstar_stbparr.
      
      eapply IHt2.
      eassumption.
      (*
    2: {
      eassumption.
      } *)
      eassumption.
      
      econstructor.

      eapply stbpstop.
      econstructor.
Defined.
 *)

(*
    exists tr,
    lstar (conf (unannoPar t) p et) tr (stop p (aeval (unannoPar t) p et)) /\
    cvm_to_lts_trace tr cvm_tr.
 *)


Lemma cvm_refines_lts_event_ordering_corrolary : forall t cvm_tr bits (*bits'*) et (*et'*) p (*p'*),
    well_formed_r t ->
    st_trace (run_cvm t
                      (mk_st (evc bits et) [] p)) = cvm_tr ->
    lstar (conf (unannoPar t) p et) cvm_tr (stop p (aeval (unannoPar t) p et)).
Proof.
  (*
  intros.
  destruct (copland_compile t {| st_ev := (evc bits et); st_trace := []; st_pl := p |}) eqn:hi.
  simpl in *.
  vmsts.
  simpl in *.
  apply cvm_refines_lts_event_ordering with (t:=t) (tr:=tr) (bits:=bits) (et:=et) (bits':=bits') (et':=et') (p:=p) (p':=st_pl); eauto.
  
  try dunit.
  rewrite hi.
  unfold run_cvm in *.
  monad_unfold.
  rewrite hi in *.
  simpl in *.
  subst.
  solve_by_inversion.
   *)
  








  
  intros.
  destruct (copland_compile t {| st_ev := (evc bits et); st_trace := []; st_pl := p |}) eqn:hi.
  simpl in *.
  vmsts.
  simpl in *.
  Check cvm_refines_lts_event_ordering.
  simpl.
  assert (o = Some tt).
  {
    eapply always_some.
    eassumption.
    eassumption.
  }
  subst.
  destruct st_ev.

  unfold run_cvm in *.
  monad_unfold.
  rewrite hi in *.
  simpl in *.
  Check cvm_refines_lts_event_ordering.
  (*
cvm_refines_lts_event_ordering
     : forall (t : AnnoTermPar) (cvm_tr : list Ev) (bits bits' : EvBits)
         (et et' : Evidence) (p p' : nat),
       well_formed_r t ->
       copland_compile t {| st_ev := evc bits et; st_trace := []; st_pl := p |} =
       (Some tt, {| st_ev := evc bits' et'; st_trace := cvm_tr; st_pl := p' |}) ->
       exists tr : list Ev,
         lstar (conf (unannoPar t) p et) tr (stop p (aeval (unannoPar t) p et)) /\
         cvm_to_lts_trace cvm_tr tr
   *)
  
  
  eapply cvm_refines_lts_event_ordering with (t:=t) (cvm_tr:=st_trace) (bits:=bits) (et:=et) (bits':=e) (et':=e0) (p:=p) (p':=st_pl); eauto.
  (*
  
  try dunit.
  rewrite hi.
  unfold run_cvm in *.
  monad_unfold.
  rewrite hi in *.
  simpl in *.
  tauto. *)
Defined.

Lemma range_par: forall t,
    range_par t = range (unannoPar t).
Proof.
  destruct t; eauto.
Defined.

Lemma wfr_implies_wfrannt :
  forall t,
    well_formed_r t ->
    well_formed_r_annt (unannoPar t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
        invc H;
    repeat find_apply_hyp_hyp;
    repeat rewrite range_par in *;
    econstructor; eauto.
Defined.


(*
    Lemma cvm_splitp_contra: forall tr_lts n loc p t et,
      cvm_to_lts_trace [cvm_thread_start n loc p t et] tr_lts  ->
      False.
    Proof.
      intros.
      generalizeEverythingElse H.
      dependent induction H; intros.
      -
        Search (_ ++ _ = [] -> _).
        edestruct app_eq_nil.
        eassumption.
        invc H1.
      -
        assert (
            (tr_cvm = [cvm_splitp n loc p t et] /\ rest_cvm = []) \/
            (rest_cvm = [cvm_splitp n loc p t et] /\ tr_cvm = [])).
        {
          Search (_ ++ _ = [_]).
          edestruct app_eq_unit.
          eassumption.
          destruct H1.
          subst.
          right.
          split; tauto.
          destruct_conjs.
          subst.
          left; eauto.
        }

        destruct H1;
          destruct_conjs; subst; eauto.
      -
        invc H.
    Defined.

        Lemma cvm_joinp_contra: forall tr_lts n loc p t,
      cvm_to_lts_trace tr_lts [cvm_joinp n loc p t] ->
      False.
    Proof.
      intros.
      generalizeEverythingElse H.
      dependent induction H; intros.
      (*
      -
        Search (_ ++ _ = [] -> _).
        edestruct app_eq_nil.
        eassumption.
        invc H1. *)
      -
        assert (
            (tr_cvm = [cvm_joinp n loc p t] /\ rest_cvm = []) \/
            (rest_cvm = [cvm_joinp n loc p t] /\ tr_cvm = [])).
        {
          Search (_ ++ _ = [_]).
          edestruct app_eq_unit.
          eassumption.
          destruct H1.
          subst.
          right.
          split; tauto.
          destruct_conjs.
          subst.
          left; eauto.
        }

        destruct H1;
          destruct_conjs; subst; eauto.
      -
        invc H.
    Defined.

            Lemma cvm_to_lts_non_empty: forall lts_tr,
          cvm_to_lts_trace lts_tr [] ->
          False.
        Proof.
          intros.
          dependent induction H.
          simpl.
          assert (tr_cvm = [] /\ rest_cvm = []).
          {
            Search (_ ++ _ = []).
            eapply app_eq_nil; eauto.
          }
          destruct_conjs.
          eauto.
        Defined.

              Lemma cvm_to_lts_event_determ: forall e1_lts e2_lts e1_cvm,
        cvm_to_lts_event e1_lts e1_cvm ->
        cvm_to_lts_event e2_lts e1_cvm ->
        e1_lts = e2_lts.
      Proof.
      Admitted.
 *)



(*
    well_formed_r t ->
    (*Ev_Shape e et -> *)
    copland_compile 
      t
      (mk_st (evc bits et) [] 0) =
    (Some tt, (mk_st (evc bits' et') cvm_tr 0)) ->
    cvm_to_lts_trace cvm_tr tr ->
 *)

(*
Axiom remote_events_non_empty: forall a n,
    remote_events a n <> [].
 *)




(*
Lemma cvm_to_lts_nil_l_contra: forall tr_lts,
  cvm_to_lts_trace [] tr_lts ->
  False.
Proof.
  intros.
  dependent induction H.
  (*
  +
    edestruct remote_events_non_empty.
    eauto.
   *)
  
  +
    ff.
    simpl.
    assert (tr_cvm = [] /\ rest_cvm = []).
    {
      Search (_ ++ _ = []).
      eapply app_eq_nil; eauto.
    }
    destruct_conjs; subst.
    eauto.
Defined.

Lemma cvm_to_lts_nil_r_contra: forall tr_cvm,
  cvm_to_lts_trace tr_cvm [] ->
  False.
Proof.
  intros.
  dependent induction H.
  (*
  +
    edestruct remote_events_non_empty.
    eauto.
   *)
  
  +
    ff.
    simpl.
    assert (tr_lts = [] /\ rest_lts = []).
    {
      Search (_ ++ _ = []).
      eapply app_eq_nil; eauto.
    }
    destruct_conjs; subst.
    eauto.
Defined.
    
(*
Lemma cvm_to_lts_nil_l: forall tr_lts,
    cvm_to_lts_trace [] tr_lts ->
    tr_lts = [].
Proof.
  intros.
  dependent induction H; intros.
  -
    ff.
  -
    ff.
    simpl.
    assert (tr_cvm = [] /\ rest_cvm = []).
    {
      Search (_ ++ _ = []).
      eapply app_eq_nil; eauto.
    }
    destruct_conjs; subst.
    assert (tr_lts = []) by eauto.
    assert (rest_lts = []) by eauto.
    subst.
    tauto.
Defined.
*)


Lemma copy_determ: forall n p tr,
    cvm_to_lts_trace [copy n p] tr ->
    tr = [copy n p].
Proof.
  intros.
  dependent induction H; intros.
  (*
  -
    tauto.
   *)
  
  -
    solve_by_inversion.
  -
     assert (tr_cvm = [copy n p] /\ rest_cvm = [] \/
            rest_cvm = [copy n p] /\ tr_cvm = []).
    {
      edestruct app_eq_unit.
      eassumption.
      destruct_conjs; subst.
      right; eauto.
      destruct_conjs; subst.
      left; eauto.
    }
    door; subst.
    exfalso.
    eapply cvm_to_lts_nil_l_contra; eauto.
    exfalso.
    eapply cvm_to_lts_nil_l_contra; eauto.
Defined.

    
    
(*    
    
  invc H.
  -
    tauto.
  -
    invc H1.
    tauto.
  -
    
    
    
  generalizeEverythingElse H.
  dependent induction H; intros.
  -
    ff.
  -
    ff.
    simpl.

    assert (tr_cvm = [copy n p] /\ rest_cvm = [] \/
            rest_cvm = [copy n p] /\ tr_cvm = []).
    {
      edestruct app_eq_unit.
      eassumption.
      destruct_conjs; subst.
      right; eauto.
      destruct_conjs; subst.
      left; eauto.
    }
    door;
      subst.
    +
      assert (rest_lts = []).
      {
        eapply cvm_to_lts_nil_l; eauto.
      }
      subst.
      rewrite app_nil_r.
      eauto.
    +
      assert (tr_lts = []).
      {
        eapply cvm_to_lts_nil_l; eauto.
      }
      subst.
      simpl.
      eauto.
Defined.
*)


Lemma cvm_to_lts_determ:
  forall t p p' bits bits' et et' tr tr' cvm_tr,
    well_formed_r t ->
    copland_compile 
      t
      (mk_st (evc bits et) [] p) =
    (Some tt, (mk_st (evc bits' et') cvm_tr p')) ->
    cvm_to_lts_trace cvm_tr tr ->
    cvm_to_lts_trace cvm_tr tr' ->
    tr = tr'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; ff.
    +

      (*
      invc H2.
      invc H1.
      congruence.
      invc H2.
      congruence.
      assert (
          (tr_cvm = [copy n p'] /\ rest_cvm = []) \/
          (rest_cvm = [copy n p'] /\ tr_cvm = [])
        ).
      {
        admit.
      }
      door; subst.
      ++
        exfalso.
        eapply cvm_to_lts_nil_l_contra; eauto.
      ++
        exfalso.
        eapply cvm_to_lts_nil_l_contra; eauto.
      ++
        invc H3.
        invc H1.
        congruence.
        invc H2.
        congruence.

        assert (
          (tr_cvm = [copy n p'] /\ rest_cvm = []) \/
          (rest_cvm = [copy n p'] /\ tr_cvm = [])
        ).
      {
        admit.
      }
      door; subst.
      +++
        exfalso.
        eapply cvm_to_lts_nil_l_contra; eauto.
      +++
        exfalso.
        eapply cvm_to_lts_nil_l_contra; eauto.
      ++
       *)
      
        

        
        
        
      
        
      

      
      assert (tr' = [copy n p']).
      {
        eapply copy_determ; eauto.
      }
      assert (tr = [copy n p']).
      {
        eapply copy_determ; eauto.
      }
      congruence.
    +
      assert (tr' = [umeas n2 p' n l n0 n1]).
      {
        admit.
      }
      assert (tr = [umeas n2 p' n l n0 n1]).
      {
        admit.
      }
      congruence.
    +
      assert (tr' = [sign n p' et]).
      {
        admit.
      }
      assert (tr = [sign n p' et]).
      {
        admit.
      }
      congruence.
    +
      assert (tr' = [hash n p' et]).
      {
        admit.
      }
      assert (tr = [hash n p' et]).
      {
        admit.
      }
      congruence.
  -
    ff.

    assert (tr' =
            (req n0 p' n (unanno a) et
          :: remote_events a n ++
          [rpy (Nat.pred n1) p' n (get_et (toRemote a n (evc bits et)))])).
    {
      admit.
    }

    assert (tr =
            (req n0 p' n (unanno a) et
          :: remote_events a n ++
          [rpy (Nat.pred n1) p' n (get_et (toRemote a n (evc bits et)))])).
    {
      admit.
    }
    congruence.
  -
    ff.
    ff.
    simpl.
    monad_unfold.
    ff.
    ff.
    simpl.
    vmsts.
    dunit.
    do_wf_pieces.
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs.
    subst.
    simpl in *.

    do_restl.
    destruct st_ev.

    assert (exists tr1 tr2,
               cvm_to_lts_trace blah' tr1 /\
               cvm_to_lts_trace blah tr2 /\
               tr = tr1 ++ tr2).
    {
      Lemma cvm_to_lts_lseq_decomp: forall t1 t2 r bits et e e0 bits' et' p st_pl p' blah' blah tr,
        well_formed_r (alseq_par r t1 t2) ->
        copland_compile t1 {| st_ev := evc bits et; st_trace := []; st_pl := p |} =
        (Some tt, {| st_ev := evc e e0; st_trace := blah'; st_pl := st_pl |}) ->
        
        copland_compile t2 {| st_ev := evc e e0; st_trace := []; st_pl := st_pl |} =
        (Some tt, {| st_ev := evc bits' et'; st_trace := blah; st_pl := p' |}) ->
        cvm_to_lts_trace (blah' ++ blah) tr ->
        (exists tr1 tr2,
               cvm_to_lts_trace blah' tr1 /\
               cvm_to_lts_trace blah tr2 /\
               tr = tr1 ++ tr2).
      Proof.
        intros.
        generalizeEverythingElse H2.
        dependent induction H2; intros.
        -
          ff.
          simpl.

          (*
          assert (
              (In (cvm_thread_start n loc p t et) blah') /\
              (In (cvm_thread_end n0 loc p t) blah)
            ).
          {
            admit.
          }
           *)

          assert (
              ( exists ls,
                  blah' = [cvm_thread_start n loc p t et] ++ ls) /\
              ( exists ls,
                  blah = [cvm_thread_end n0 loc p t] ++ ls)
            ).
          {
            admit.
          }
          destruct_conjs.
          

          (*
          exists blah'.
          exists blah.
          split. *)
          
          admit.
        -
          assert (
              (blah' = [cvm_e1] /\ blah = []) \/
              (blah = [cvm_e1] /\ blah' = [])
            ).
          {
            admit.
          }
          
          door.
          +
            admit. (* trace from t2 cannot be empty *)
          +
            admit. (* trace from t1 cannot be empty *)
        -

          invc H2_.
          +
            assert (rest_cvm = blah).
            {
              admit.
            }
            rewrite <- H3 in *; clear H3.

            assert (([cvm_thread_start n loc p0 t et0] ++ cvm_l1 ++ [cvm_thread_end n0 loc p0 t]) = blah').
            {
              admit.
            }
            rewrite <- H3 in *; clear H3.

            eexists.
            eexists.
            split.
            econstructor.
            eassumption.
            split.
            eassumption.
            tauto.
          +
            assert (exists ls,
                       blah' = [cvm_e1] ++ ls /\
                       rest_cvm = ls ++ blah).
            {
              admit.
            }
            destruct_conjs.
            subst.

            edestruct IHcvm_to_lts_trace2.
            2: { eassumption. }
            2: { eassumption. }
            2: { eassumption. }
            
            
            
            
            
            
            eassumption.

            eexists.
            eexists.
            split.

           
          
            
                
            
          
                 


          
          exists blah'.
          exists blah.
          split.
          econstructor.
          admit.
          split.
          econstructor.
          admit.
          tauto.
        -
          


          
          edestruct IHcvm_to_lts_trace1.
          Focus 2.
          eassumption.
          Focus 2.
          eassumption.
          Focus 2.
          eassumption.
          admit.
          destruct_conjs.
          edestruct IHcvm_to_lts_trace2.
          Focus 2.
          eassumption.
          Focus 2.
          eassumption.
          Focus 2.
          eassumption.
          admit.
          destruct_conjs.
          subst.
          exists (x0 ++ H2).
          exists (x1 ++ H6).
          split.

          
          eassumption.
          
          eassumption.
          
          



          
      Admitted.

      eapply cvm_to_lts_lseq_decomp; eauto.
      
    }

    assert (exists tr1 tr2,
               cvm_to_lts_trace blah' tr1 /\
               cvm_to_lts_trace blah tr2 /\
               tr' = tr1 ++ tr2).
    {
      eapply cvm_to_lts_lseq_decomp; eauto.
    }
    destruct_conjs.
    subst.
    assert (H5 = H6) by eauto.
    assert (H11 = H7) by eauto.
    subst.
    tauto.
  -
    
    {
      eapply IHt1.
      eassumption.
      eassumption.
    
    


    invc H1.
    
    +
      rewrite <- H5 in *; clear H5.
      invc H2.
      ++
        assert (cvm_l0 = cvm_l1).
        {
          admit.
        }
        assert (n2 = n0).
        {
          admit.
        }
        subst.
        
        
      
    
    
    
    
    
      
      
      
      
      
      
      
      
      


      
      invc H2; try solve_by_inversion.
      ++
        invc H1; try solve_by_inversion.

        assert (tr_cvm = [copy n p'] /\ rest_cvm = [] \/
                rest_cvm = [copy n p'] /\ tr_cvm = []).
        {
          admit.
        }
        door; subst.
        +++
          
          assert (rest_lts = []).
          {
            admit.
          }
          subst.
          repeat rewrite app_nil_r in *.
          
          invc H3; try solve_by_inversion.
        

      
  













  

  (*
  intros.
  generalizeEverythingElse H.
  dependent induction H; intros.
  -
    invc H0.
    +
      assert (cvm_l0 = cvm_l1).
      {
        admit.
      }
      assert (n2 = n0).
      {
        admit.
      }
      
      subst.
      find_apply_hyp_hyp.
      subst.
      tauto.
    +
      destruct_conjs.
      specialize H0 with (n1:=n) (loc0:=loc) (p0:=p) (t0:=t) (et0:=et).
      unfold not in H0.
      exfalso.
      eapply H0.
      econstructor.
      tauto.
    +
      assert (
          (tr_cvm =
           [cvm_thread_start n loc p t et] ++ cvm_l1 ++ [cvm_thread_end n0 loc p t] /\
           rest_cvm = []) \/
          (rest_cvm =
           [cvm_thread_start n loc p t et] ++ cvm_l1 ++ [cvm_thread_end n0 loc p t] /\
           tr_cvm = [])
        ). (* TODO: one more "in between" case *)
      {
        admit.
      }
      door; subst.
      ++
        clear H1.
        assert (rest_lts = []).
        {
          admit.
        }
        subst.
        rewrite app_nil_r.
        clear H3.



        (*
        
        invc H2.
        +++
          assert (cvm_l0 = cvm_l1).
          {
            admit.
          }
          assert (n2 = n0).
          {
            admit.
          }
          assert (rest_lts = []).
          {
            admit.
          }
          assert (lts_l1 = lts_l0).
          {
            eapply IHcvm_to_lts_trace.
            subst.
            eassumption.
          }
          
          subst.
          rewrite app_nil_r.
          tauto.
        +++
          admit.
        +++
          assert (rest_lts = []).
          {
            admit.
          }
          subst.
          rewrite app_nil_r.
          clear H3.
          
          
          
          
      
      
      
 *)     
      
      
*)


    
  Admitted.



  (*
  intros.
  generalizeEverythingElse H.
  dependent induction H; intros.
  -
    assert (exists ls,
               tr' =
               [Term_Defs.split n p] ++
                                     (shuffled_events ls (lts_remote_events t p)) ++
                                     [Term_Defs.join n0 p] /\
               cvm_to_lts_trace ls cvm_l1).
    {
      admit.
    }
    destruct_conjs.
    assert (l1 = H1) by eauto.
    subst.
    tauto.
    

(*
  
  (*
  -
    inversion H0.
    +
      tauto.
    +
      inversion H0.
      assert (tr_cvm = [] /\ rest_cvm = []).
      {
        admit. (* OK *)
      }
      destruct_conjs; subst.
      invc H1.
      invc H3.
      tauto. *)
      
      
      
  -
    invc H0.
    +
      
    assert (cvm_l0 = cvm_l1).
    {
      Search (_ ++ [_] = _ ++ [_]).
      edestruct app_inj_tail.
      eassumption.
      eauto.
    }
    subst.
    
    assert (l1 = l0).
    {
    eapply IHcvm_to_lts_trace.
    eassumption.
    }
    subst.
    assert (n2 = n0).
    {
      edestruct app_inj_tail.
      eassumption.
      solve_by_inversion.

    }
    subst.
    tauto.
    +
    assert (cvm_splitp n loc p t et :: cvm_l1 ++ [cvm_joinp n0 loc p t] =
            [cvm_splitp n loc p t et] ++ cvm_l1 ++ [cvm_joinp n0 loc p t]).
    {
      tauto.
    }
    rewrite H0 in *; clear H0.

    assert ((tr_cvm = [cvm_splitp n loc p t et] /\
             rest_cvm = cvm_l1 ++ [cvm_joinp n0 loc p t]) \/
            (tr_cvm = [cvm_splitp n loc p t et] ++ cvm_l1 /\
             rest_cvm = [cvm_joinp n0 loc p t]) \/
            ( (exists ls, tr_cvm = [cvm_splitp n loc p t et] ++ ls) /\
              (exists ls', rest_cvm = ls' ++ [cvm_joinp n0 loc p t])) \/
            (tr_cvm = [cvm_splitp n loc p t et] ++ cvm_l1 ++ [cvm_joinp n0 loc p t] /\
             rest_cvm = []) \/
            (rest_cvm = [cvm_splitp n loc p t et] ++ cvm_l1 ++ [cvm_joinp n0 loc p t] /\
             tr_cvm = [])
           ).
                   
    {
      admit.
    }
    repeat door; subst.
    ++
      exfalso.
      eapply cvm_splitp_contra; eauto.
    ++
      exfalso.
      eapply cvm_joinp_contra; eauto.
    ++
      assert (cvm_l1 = H0 ++ H3).
      {
        admit.
      }
      subst.

      assert (exists cvm_ls,
                 tr_lts =
                 ([Term_Defs.split n p] ++ shuffled_events l1 (lts_remote_events t p) ++ [Term_Defs.join n p]) /\
                 H0 = cvm_ls ++ [cvm_joinp n loc p t] /\
                 cvm_to_lts_trace l1 cvm_ls
             ).
      {
        admit.
      }
      destruct_conjs.
      subst.

      assert (exists cvm_ls,
                 rest_lts =
                 ([Term_Defs.split n0 p] ++ shuffled_events l1 (lts_remote_events t p) ++ [Term_Defs.join n0 p]) /\
                 H3 = [cvm_splitp n0 loc p t et] ++ cvm_ls /\
                 cvm_to_lts_trace l1 cvm_ls
             ).
      {
        admit.
      }
      destruct_conjs.
      subst.
      
             



      


      
      
                 H0 = cvm_l1 ++ [cvm_joinp n loc p t] /\
                 cvm_to_lts_trace 


      
      clear H1.
      
      
      
      
      

    

    (*
    assert (tr_cvm = [cvm_splitp n loc p t et] /\
            rest_cvm = cvm_l1 ++ [cvm_joinp n0 loc p t]).
    {
      admit.
    }
    destruct_conjs.
    subst.
     *)
    

    

    exfalso.
    eapply cvm_splitp_contra; eauto.
    +
      admit.
 *)
    
  -
    assert (tr_cvm = [] \/
            rest_cvm [] \/
            
    
      
    admit.
  -
    invc H0.
    +
      admit.
    +
      assert (tr_cvm = [e1_cvm] /\ rest_cvm = [] \/
              rest_cvm = [e1_cvm] /\ tr_cvm = []).
      {
        admit. (* OK *)
      }
      destruct H0;
        destruct_conjs;
        subst.
      ++

        exfalso.
        eapply cvm_to_lts_non_empty; eauto.

      ++
         exfalso.
        eapply cvm_to_lts_non_empty; eauto.

    +
      


      assert (e1_lts = e1_lts0).
      {
        eapply cvm_to_lts_event_determ; eauto.
      }
      subst.
      tauto.
      
      eassumption.
      eassumption.
      
        
        invc H4.
        invc H2.
        +++
          admit.
        +++
          
      
      
    




    
    
    invc H1.
    +
    
    


    
    invc H2.
    ++
      admit.
    ++
      assert (tr_cvm = [] \/ rest_cvm = []).
      {
        admit.
      }
      destruct H2.
      +++
        subst.
        assert (rest_cvm = [cvm_splitp n loc p t et]).
        {
          admit.
        }
        subst.
        invc H6
        
      
      
    



    

    Search "++".

    edestruct app_eq_app.
    apply H1.
    invc H0.
    ++
    destruct_conjs.
    subst.

    invc H2.
    +++
      edestruct app_eq_app.
      apply H3.
      invc H0.
      ++++
        destruct_conjs.
        subst.
        clear H1.
        clear H3.
        invc H4.
        +++++




    



    edestruct app_eq_app.
    apply H3.
    invc H0.
    destruct_conjs.
    subst.
    clear H1.
    clear H3.
    invc H4; try solve_by_inversion.
    assert (n0 = n2 /\ loc0 = loc /\ p0 = p /\ t0 = t).
    {
      admit.
    }
    destruct_conjs; subst.
    
    assert (l1 = l0).
    {
      eapply IHcvm_to_lts_trace.
      
      eassumption.

    assert (tr_cvm = [cvm_splitp n loc p t et] /\ rest_cvm = 
    
    rewrite front_app.



    
    admit.
    
    
    

    
Admitted.
*)   (* END cvm_to_lts_determ attempt *)

*)

Theorem cvm_respects_event_system' : forall t cvm_tr ev0 ev1 bits bits' et et',
    well_formed_r t ->
    (*Ev_Shape e et -> *)
    copland_compile 
      t
      (mk_st (evc bits et) [] 0) =
    (Some tt, (mk_st (evc bits' et') cvm_tr 0)) ->
    (*cvm_to_lts_trace cvm_tr tr -> *)
    prec (ev_sys (unannoPar t) 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  eapply ordered.
  eapply wfr_implies_wfrannt; eauto.
  eapply cvm_refines_lts_event_ordering; eauto.
  eassumption.
Defined.

(*




  
  edestruct cvm_refines_lts_event_ordering.
  eassumption.
  eassumption.
  destruct_conjs.
  (*
  assert (x = tr).
  {
    eapply cvm_to_lts_determ; eauto.
  }
  subst.
   *)
  
  eapply ordered.
  eapply wfr_implies_wfrannt; eauto.
  eassumption.
  eassumption.
*)
  



(*
Theorem cvm_respects_event_system' : forall t cvm_tr ev0 ev1 bits bits' et et',
    well_formed_r t ->
    (*Ev_Shape e et -> *)
    copland_compile 
      t
      (mk_st (evc bits et) [] 0) =
    (Some tt, (mk_st (evc bits' et') cvm_tr 0)) ->
    (
        exists tr,
    lstar (conf (unannoPar t) 0 et) tr (stop 0 (aeval (unannoPar t) 0 et)) /\
    cvm_to_lts_trace tr cvm_tr ->
    (prec (ev_sys (unannoPar t) 0 et) ev0 ev1 ->
     earlier tr ev0 ev1)).
Proof.
  intros.
  eexists.
  intros.
  destruct_conjs.
  eapply ordered.
  eapply wfr_implies_wfrannt.
  eassumption.
  eassumption.
  eassumption.
  






  
  edestruct cvm_refines_lts_event_ordering.
  eassumption.
  eassumption.
  destruct_conjs.
  exists x.
  intros.
  eapply ordered.
  eapply wfr_implies_wfrannt.
  eassumption.
  eassumption.
  eassumption.
Defined.

  split.
  eassumption.
  split.
  eassumption.
  intros.
  eapply ordered with (p:=0) (e:=et); eauto.
  eapply wfr_implies_wfrannt; eauto.
Defined.
 *)

Lemma anno_unanno_par: forall a l l' annt,
    anno_par a l = (l', annt) ->
    unannoPar annt = a.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    ff.
  -
    ff.
  -
    ff.
    assert (unannoPar a = a1) by eauto.
    assert (unannoPar a0 = a2) by eauto.
    congruence.
  -
    ff.
    assert (unannoPar a = a1) by eauto.
    assert (unannoPar a0 = a2) by eauto.
    congruence.
  -
    ff.
    assert (unannoPar a = a1) by eauto.
    congruence.
Defined.

Lemma fst_annopar: forall a a' l l',
    anno_par a l = (l', a') ->
    fst (range a) = fst (Term_Defs.range_par a').
Proof.
  intros.
  generalizeEverythingElse a.
  destruct a; intros; ff.
Defined.


(*
Lemma snd_annopar: forall a2_1 a2_2 l' l3 a2 l0' a3,
    anno_par a2_1 l' = (l3, a2) ->
    anno_par a2_2 l3 = (l0', a3) ->
    snd (Term_Defs.range_par a2) = fst (Term_Defs.range_par a3).
Proof.
  intros.
  generalizeEverythingElse a2_2.
  induction a2_2; intros.
  -
    ff.
Admitted.
 *)


Lemma snd_annopar_snd: forall a a' l l',
    anno_par a l = (l', a') ->
    Term_Defs.range_par a' = range a.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros; ff.
Defined.

Lemma wfr_par_irrel: forall a2 l l' l0 l0' a0 a0',
    well_formed_r_annt a2 ->
    anno_par a2 l' = (l0', a0') ->
    anno_par a2 l = (l0, a0) ->
    well_formed_r a0 ->
    well_formed_r a0'.
Proof.
  intros.
  unfold annotated_par in *.
  (*
      unfold anno_par in H.
      repeat break_let.
      simpl.
      fold anno_par in *. *)
  generalizeEverythingElse a2.
  induction a2; intros.
  -
    ff.
  -
    ff.
  -
    ff.
    invc H2.
    invc H.
    
    assert (well_formed_r a2).
    {
      eauto.
    }
    assert (well_formed_r a3).
    {
      eauto.
    }

    (*

        assert (a1 = a3).
        {
          eapply anno_par_same; eauto.
        }
        assert (a = a2).
        {
          eapply anno_par_same; eauto.
        }
        subst.
     *)
    

    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    erewrite <- fst_annopar.
    erewrite <- fst_annopar.
    reflexivity.
    eassumption.
    eassumption.
    erewrite snd_annopar_snd.
    erewrite snd_annopar_snd.
    2: { eassumption. }
    2: { eassumption. }
    subst'.
    subst'.
    congruence.

    (*

    eapply snd_annopar.
    eassumption.
    eassumption.
    subst'. *)

    assert (
        Term_Defs.range_par a1 =
        Term_Defs.range_par a3).
    {
      rewrite range_par.
      rewrite range_par.
      erewrite anno_unanno_par.
      erewrite anno_unanno_par.
      reflexivity.
      eassumption.
      eassumption.
    }
    congruence.
  -
    ff.
    invc H2.
    invc H.
    
    assert (well_formed_r a2).
    {
      eauto.
    }
    assert (well_formed_r a3).
    {
      eauto.
    }

    (*

        assert (a1 = a3).
        {
          eapply anno_par_same; eauto.
        }
        assert (a = a2).
        {
          eapply anno_par_same; eauto.
        }
        subst.
     *)
    

    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    subst'.
    erewrite <- fst_annopar.
    erewrite <- fst_annopar.
    reflexivity.
    eassumption.
    eassumption.

        erewrite snd_annopar_snd.
    erewrite snd_annopar_snd.
    2: { eassumption. }
    2: { eassumption. }
    subst'.
    subst'.
    congruence.

    (*

    eapply snd_annopar.
    eassumption.
    eassumption.
    subst'. *)

    assert (
        Term_Defs.range_par a1 =
        Term_Defs.range_par a3).
    {
      rewrite range_par.
      rewrite range_par.
      erewrite anno_unanno_par.
      erewrite anno_unanno_par.
      reflexivity.
      eassumption.
      eassumption.
    }
    congruence.
  -
    ff.
    invc H2.
    
    invc H.
    
    assert (well_formed_r a1).
    {
      eauto.
    }
    (*
        assert (well_formed_r a3).
        {
          eauto.
        }
     *)
    

    (*

        assert (a1 = a3).
        {
          eapply anno_par_same; eauto.
        }
        assert (a = a2).
        {
          eapply anno_par_same; eauto.
        }
        subst.
     *)
    

    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    subst'.
    erewrite <- fst_annopar.
    erewrite <- fst_annopar.
    reflexivity.
    eassumption.
    eassumption.
    subst'.
    subst'.
    rewrite <- H9.

    (*

        erewrite snd_annopar_snd.
        2: { eassumption. }
        

        eapply snd_annopar.
        eassumption.
        eassumption.
        subst'. *)

    assert (
        Term_Defs.range_par a1 =
        Term_Defs.range_par a).
    {
      rewrite range_par.
      rewrite range_par.
      erewrite anno_unanno_par.
      erewrite anno_unanno_par.
      reflexivity.
      eassumption.
      eassumption.
    }
    congruence.
    congruence.
Defined.

Lemma wfr_annt_implies_wfr_par: forall a l l' a0,
    well_formed_r_annt a ->
    anno_par a l = (l', a0) ->
    well_formed_r a0.
Proof.

  
  intros.
  generalizeEverythingElse a.
  induction a; intros;
    invc H.
  -
    try econstructor;
      ff.
  -
    ff.
  -


    (*
          ff.
          assert (well_formed_r (annotated_par a1)) by eauto.
          assert (well_formed_r (annotated_par a2)) by eauto.
     *)
    

    
    unfold anno_par in *.
    repeat break_let.
    fold anno_par in *.
    invc H0.
    simpl.

    (*
          assert (a = annotated_par a1).
          {
            unfold annotated_par.
            subst'.
            tauto.
          }
          subst.
     *)
    assert (well_formed_r a) by eauto.
    assert (well_formed_r a3) by eauto.
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.



    eapply fst_annopar; eauto.

        erewrite snd_annopar_snd.
    erewrite snd_annopar_snd.
    2: { eassumption. }
    2: { eassumption. }
    subst'.
    congruence.

    
    

(*
    eapply snd_annopar; eauto.
 *)
    

    subst'.

    rewrite range_par.

    assert (unannoPar a3 = a2).
    {
      eapply anno_unanno_par.
      eassumption.
    }
    congruence.
  -
    

    (*
          ff.
          assert (well_formed_r (annotated_par a1)) by eauto.
          assert (well_formed_r (annotated_par a2)) by eauto.
     *)
    

    
    unfold anno_par in *.
    repeat break_let.
    fold anno_par in *.
    invc H0.
    simpl.

    (*
          assert (a = annotated_par a1).
          {
            unfold annotated_par.
            subst'.
            tauto.
          }
          subst.
     *)
    assert (well_formed_r a) by eauto.
    assert (well_formed_r a3) by eauto.
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    rewrite H7.



    eapply fst_annopar; eauto.



        erewrite snd_annopar_snd.
    erewrite snd_annopar_snd.
    2: { eassumption. }
    2: { eassumption. }
    subst'.
    congruence.

    
    

(*
    eapply snd_annopar; eauto.
 *)
    

    subst'.

    rewrite range_par.

    assert (unannoPar a3 = a2).
    {
      eapply anno_unanno_par.
      eassumption.
    }
    congruence.
  -

    
    (*
          ff.
          assert (well_formed_r (annotated_par a1)) by eauto.
          assert (well_formed_r (annotated_par a2)) by eauto.
     *)
    

    
    unfold anno_par in *.
    repeat break_let.
    fold anno_par in *.
    invc H0.
    simpl.

    (*
          assert (a = annotated_par a1).
          {
            unfold annotated_par.
            subst'.
            tauto.
          }
          subst.
     *)
    assert (well_formed_r a) by eauto.
    (*
          assert (well_formed_r a3) by eauto. *)
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    rewrite H7.



    eapply fst_annopar; eauto.
    rewrite <- H8.

    erewrite snd_annopar_snd; eauto.

    eassumption.
Defined.

Theorem cvm_respects_event_system : forall t cvm_tr ev0 ev1 bits bits' et et' t',
    t = annotated_par (annotated t') ->
    (*Ev_Shape e et ->*)
    copland_compile
      t
      (mk_st (evc bits et) [] 0) =
    (Some tt, (mk_st (evc bits' et') cvm_tr 0)) ->
     (*cvm_to_lts_trace cvm_tr tr -> *)
    prec (ev_sys (unannoPar t) 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.

            (*
    prec (ev_sys t 0 et) ev0 ev1 ->
    earlier tr ev0 ev1. *)
Proof.
  intros.
  assert (well_formed_r t).
  {
    unfold annotated in H.
    unfold snd in *.
    break_let.
    subst.
    assert (well_formed_r_annt (annotated t')).
    {
      unfold annotated.
      unfold snd in *.
      eapply anno_well_formed_r.
      rewrite Heqp.
      reflexivity.
    }
    unfold annotated in *.
    unfold snd in *.
    rewrite Heqp in *.

    Search "implies".

    Print annotated_par.

    (*
    Lemma annoPar_range_irrel: forall a2 l l0 a0,
        anno_par a2 l = (l0, a0) ->
        range a2 = range (unannoPar a0).
    Proof.
    Admitted.
     *)

    (*
    Lemma anno_par_same: forall ap l1 l1' l2 l2' annt annt',
        anno_par ap l1 = (l1', annt) ->
        anno_par ap l2 = (l2', annt') ->
        annt = annt'.
    Proof.
      intros.
      generalizeEverythingElse ap.
      induction ap; intros.
      -
        ff.
      -
        ff.
      -
        ff.
        assert (a1 = a) by eauto.
        assert (a2 = a0) by eauto.
        congruence.
      -
        ff.
        assert (a1 = a) by eauto.
        assert (a2 = a0) by eauto.
        congruence.
      -
        ff.
        assert (a0 = a) by eauto.
        subst.
        assert (a2 = a0) by eauto.
        congruence.

    Admitted.
     *)
    



    


        
        
        


(*
          
        eapply snd_annopar_snd.
        erewrite snd_annopar_snd.
        2: { eassumption. }
        
        eassumption.


        tauto.
      - (* abseq case *)
                ff.
        invc H2.
        invc H.
        
        assert (well_formed_r a2).
        {
          eauto.
        }
        assert (well_formed_r a3).
        {
          eauto.
        }

        assert (a1 = a3).
        {
          eapply anno_par_same; eauto.
        }
        assert (a = a2).
        {
          eapply anno_par_same; eauto.
        }
        subst.

        econstructor.
        eassumption.
        eassumption.
        destruct r.
        simpl in *.
        subst.
        tauto.
        eassumption.
        subst'.
        tauto.
      -
        ff.
        invc H2.
        invc H.
        
        assert (well_formed_r a1).
        {
          eauto.
        }
        (*
        assert (well_formed_r a2_2).
        {
          eauto.
        }
         *)

        assert (a = a1).
        {
          eapply anno_par_same; eauto.
        }
        

        (*
        assert (a1 = a3).
        {
          eapply anno_par_same; eauto.
        }
        assert (a = a2).
        {
          eapply anno_par_same; eauto.
        }
         *)
        
        subst.

        econstructor.
        eassumption.
        eassumption.
        destruct r.
        simpl in *.
        subst.
        tauto.
        eassumption.
        subst'.
        tauto.
        Defined.
 *)
    
        


    (*
        Lemma fst_annopar: forall a a' l l',
          anno_par a l = (l', a') ->
          fst (range a) = fst (Term_Defs.range_par a').
        Proof.
        Admitted.

        eapply fst_annopar; eauto.

        Lemma snd_annopar: forall a2_1 a2_2 l' l3 a2 l0' a3,
          anno_par a2_1 l' = (l3, a2) ->
          anno_par a2_2 l3 = (l0', a3) ->
          snd (Term_Defs.range_par a2) = fst (Term_Defs.range_par a3).
        
        
          simpl.
          eapply IHa2_2.
        
          eapply IHa2_1.
    

    Lemma wfr_par_irrel: forall a2 l l0 a0,
        well_formed_r (annotated_par a2) ->
        anno_par a2 l = (l0, a0) ->
        well_formed_r a0.
    Proof.
      intros.
      unfold annotated_par in *.
      (*
      unfold anno_par in H.
      repeat break_let.
      simpl.
      fold anno_par in *. *)
      generalizeEverythingElse a2.
      induction a2; intros.
      -
        ff.
      -
        ff.
      -
        unfold annotated_par in *.
        unfold anno_par in H.
        cbn in H0.
        repeat break_let.
        fold anno_par in *.
        simpl in *.
        ff.
        invc H.
        pairs.
        destruct r.
        ff.
        subst.
        ff.
        simpl.
        econstructor.
        eauto.
        eauto.
        simpl.
        eapply IHa2_2.
        apply H3

        assert (well_formed_r a).
        {
          eapply IHa2_1.
          subst'.
          simpl.
          eassumption.
          eassumption.
        }

        assert (well_formed_r a1).
        {
          eapply IHa2_2.
          subst'.
          simpl.
          eassumption.
          eassumption.
          eapply IHa2_2.
          subst'.
          simpl.
          eassumption.
        
          




        
        repeat break_let.
        df.

        assert (well_formed_r a2).
        {
          eapply IHa2_1.
          

        
        invc H.
        econstructor.
        eapply IHa2_2.
        
        
        


        
        assert (well_formed_r a2).
        eapply IHa2_1.
        
        find_apply_hyp_hyp.
        subst'.
        ff.
        edestruct IHa2_1.
        
        


        
    Admitted.
     *)
    






          

        
          
(*

          eapply snd_annopar; eauto.

          subst'.

          rewrite range_par.

          assert (unannoPar a3 = a2).
          {
            eapply anno_unanno_par.
            eassumption.
          }
          congruence.
          
          







          
          assert (a0 = annotated_par a2).
          {
            unfold annotated_par.
            subst'.
          econstructor.
          eassumption.
         
          



          eapply wfr_par_irrel.
          2: { eassumption. }
          eassumption.
          eassumption.

          eapply wfr_par_irrel.
          2: { eassumption. }
          eassumption.
          eassumption.
          
          
          cbn.
          Search range.
          rewrite range_par.
          rewrite H5.



          rewrite anno_unanno_par.
          tauto.
          repeat rewrite range_par.
          rewrite anno_unanno_par.
          rewrite H6.



          erewrite annoPar_range_irrel; eauto.
          rewrite H7.

          rewrite range_par.

          erewrite annoPar_range_irrel; eauto.
        +
          
          


          
          rewrite range_par.
          rewrite H6.
          rewrite range_par.
          
          



          
          assert (a0 = annotated_par a2).
          {
            unfold annotated_par.
            subst'.
            tauto.
          simpl.


          
          subst.
          simpl.
          econstructor.
          
          eauto.
          
          unfold snd.
          break_let.
          repeat break_let.
          invc Heqp0.
          econstructor.
          ff.
          econstructor.
          



        
        invc H;
        repeat find_apply_hyp_hyp;
        repeat rewrite range_par in *;
        econstructor; eauto.
       *)
      
     



    unfold annotated_par.
    assert (exists a', (annotated_par a) = a').
    {
      eexists.
      reflexivity.
    }
    destruct_conjs.
    unfold annotated_par in H3.
    rewrite H3.
   
    
    eapply wfr_annt_implies_wfr_par with (l:= 0).
    eassumption.
    assert (anno_par a 0 = (fst (anno_par a 0), snd (anno_par a 0))).
    {
      destruct (anno_par a 0); tauto.
    }
    rewrite H4.
    rewrite H3.
    reflexivity.
  }

  eapply ordered with (p:=0) (e:=et); eauto.
  eapply wfr_implies_wfrannt; eauto.
  eapply cvm_refines_lts_event_ordering; eauto.

  (*
  eassumption.
  eassumption.
  destruct_conjs.
  assert (tr = x).
  {
    eapply cvm_to_lts_determ; eauto.
  }
  subst.
  eassumption.
   *)
  
Defined.
















(*
Lemma splitEv_T_l_LEFT: forall e bits bits' es e0,
    et_size e = es ->
    splitEv_l LEFT (evc bits e) = (evc bits' e0) ->
    et_size e0 = es. (* (splitEv_T_l LEFT es). *)
Proof.
  intros.
  ff.
Defined.
*)

(*
Lemma splitEv_T_l_LEFT: forall e es e0,
    Ev_Shape e es ->
    splitEv_l LEFT e = e0 ->
    Ev_Shape e0 (splitEv_T_l LEFT es).
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros;
    ff.
Defined.

Axiom remote_Ev_Shape: forall e es t n,
    Ev_Shape e es ->
    Ev_Shape (toRemote t n e) (eval (unanno t) n es).
 *)

(*
Definition Ev_Shape' (bits:list BS) (et:Evidence) :=
  length bits = et_size et.

Axiom remote_Ev_Shape: forall et et' t n bits bits',
    Ev_Shape' bits et ->
    toRemote t n (evc bits et) = evc bits' et' ->
    Ev_Shape' bits' (eval (unanno t) n et).
 *)



(*
Lemma cvm_refines_lts_evidence : forall t tr tr' bits bits' et et' p p',
    well_formed_r t ->
    copland_compile t (mk_st (evc bits et) tr p) = (Some tt, (mk_st (evc bits' et') tr' p')) ->
    Ev_Shape' bits et ->
    (*
    Term_Defs.eval (unanno t) p es = e's -> *)
    et' = (Term_Defs.eval (unanno t) p et) /\
    Ev_Shape' bits' et'.

Proof.
  induction t; intros.
  -
    destruct a;
      try (
          df;
          eauto).
    +
      split.
      eauto.
      unfold Ev_Shape' in *.
      ff.
    +
      split.
      eauto.
      unfold Ev_Shape' in *.
      ff.

    +
      split.
      eauto.
      unfold Ev_Shape' in *.
      ff.

  -
    repeat df. 
    annogo.
    do_wf_pieces.
    edestruct IHt; eauto.
    rewrite <- H3.
    apply copland_compile_at.
    eauto.

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

    destruct x.
    vmsts.

    edestruct IHt1.
    eassumption.
    eassumption.
    eassumption.
    subst.

    edestruct IHt2.
    eassumption. eassumption.
    eassumption.
    subst.
    split.
    repeat do_pl_immut.
    subst.
    eauto.
    eassumption.     
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

      
      destruct s; ff.
      ++
        edestruct IHt1; eauto.
        subst.
        edestruct IHt2.
        eassumption.
        eassumption.
        unfold Ev_Shape'. ff.
        subst.
        repeat do_pl_immut. subst.
        split. eauto. df.
        unfold Ev_Shape' in *.
        ff.
        Search length.
        rewrite app_length.
        subst.
        lia.
      ++
        edestruct IHt1; eauto. cbv. lia.
        subst.
        edestruct IHt2; eauto.
        unfold Ev_Shape'. ff.
        subst.
        repeat do_pl_immut. subst.
        split. eauto. df.
        unfold Ev_Shape' in *.
        ff.
        Search length.
        rewrite app_length.
        subst.
        lia.
      ++
        edestruct IHt1; eauto.
        subst.
        edestruct IHt2; eauto.
        unfold Ev_Shape'. ff.
        subst.
        repeat do_pl_immut. subst.
        split. eauto. df.
        unfold Ev_Shape' in *.
        ff.
        Search length.
        rewrite app_length.
        subst.
        lia.
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

      
      destruct s; ff.
      ++
        edestruct IHt1; eauto.
        subst.
        edestruct IHt2.
        eassumption.
        eassumption.
        unfold Ev_Shape'. ff.
        subst.
        repeat do_pl_immut. subst.
        split. eauto. df.
        unfold Ev_Shape' in *.
        ff.
        Search length.
        rewrite app_length.
        subst.
        lia.
      ++
        edestruct IHt1; eauto. cbv. lia.
        subst.
        edestruct IHt2; eauto.
        unfold Ev_Shape'. ff.
        subst.
        repeat do_pl_immut. subst.
        split. eauto. df.
        unfold Ev_Shape' in *.
        ff.
        Search length.
        rewrite app_length.
        subst.
        lia.
      ++
        edestruct IHt1; eauto.
        subst.
        edestruct IHt2; eauto.
        unfold Ev_Shape'. ff.
        subst.
        repeat do_pl_immut. subst.
        split. eauto. df.
        unfold Ev_Shape' in *.
        ff.
        Search length.
        rewrite app_length.
        subst.
        lia.
Defined.
*)

(*
Proof.
  induction t; intros.
  -
    destruct a;
      try (
          df;
          eauto).
    +
      split.
      eauto.
      unfold Ev_Shape' in *.
      ff.
    +
      split.
      eauto.
      unfold Ev_Shape' in *.
      ff.

    +
      split.
      eauto.
      unfold Ev_Shape' in *.
      ff.




    

  (*  
    +
      assert (Ev_Shape e (et_fun e)).
      {
        eapply ev_evshape.
      }

      assert (es = (et_fun e)).
      {
        eapply evshape_determ.
        eauto.
        eauto.
      }
      subst.
      eauto.
*)
      
      
      
  -
    repeat df. 
    annogo.

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
      destruct s.
      ++
        eapply IHt1; eauto.
        (*

        eapply splitEv_T_l_LEFT; eauto. *)
        
      ++
        simpl in *.
        eapply IHt1; eauto.
        
      ++
        ff.
        eauto.
      ++
        simpl in *.
        repeat do_pl_immut.
        subst.
        destruct s.
        +++
          ff.
          eauto.
        +++
          ff.
          eauto.
        +++
          ff.
          eauto.

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
      destruct s.
      ++
        eapply IHt1; eauto.

        (*
        eapply splitEv_T_l_LEFT; eauto. *)
        
      ++
        simpl in *.
        eapply IHt1; eauto.
      ++
        ff.
        eauto.
      ++
        simpl in *.
        repeat do_pl_immut.
        subst.
        destruct s.
        +++
          ff.
          eauto.
        +++
          ff.
          eauto.
        +++
          ff.
          eauto.
Defined.
*)




(*
Lemma evshape_split_l: forall e et s,
    Ev_Shape e et ->
    Ev_Shape ((splitEv_l s e)) (splitEv_T_l s et).
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros;
    try (destruct s; ff; tauto).
Defined.

Lemma evshape_split_r: forall e et s,
    Ev_Shape e et ->
    Ev_Shape ((splitEv_r s e)) (splitEv_T_r s et).
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros;
    try (destruct s; ff; tauto).
Defined.
 *)





(*
Lemma cvm_refines_lts_event_ordering : forall t tr e e' et p p',
    well_formed_r t ->
    Ev_Shape e et ->
    copland_compile t (mk_st e [] p) = (Some tt, (mk_st e' tr p')) ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros t tr e e' et p p' H H'.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    destruct a;
      df;
      econstructor; try (econstructor; reflexivity).
    
    +
      assert (et = et_fun e).
      {
        eapply evshape_determ; eauto.
        apply ev_evshape; eauto.
      }
      rewrite <- H0.
      econstructor; try (econstructor; reflexivity).
      
      
  - (* aatt case *)
    destruct r.
    repeat (df; try dohtac; df).
    
    assert (lstar (conf t n et) (remote_events t n) (stop n (aeval t n et))).
    {
      apply remote_LTS.
    }

    

    pose ev_evshape.
    pose (e0 e).
    
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
    +
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
    2: {
      eassumption.
    }
    eassumption.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
        
    eapply IHt2.
    eassumption.
    2: {
      eassumption.
    }
    
    econstructor.
    econstructor.
    eapply stbsrstop.
    econstructor.
    +
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
    2: {
      eassumption.
    }

    econstructor.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
        
    eapply IHt2.
    eassumption.
    2: {
      eassumption.
    }   
    eassumption.

    econstructor.
    eapply stbsrstop.
    econstructor.

    +
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
    2: {
      eassumption.
    }

    eassumption.

    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
        
    eapply IHt2.
    eassumption.

    2: {
      eassumption.
    }

    eassumption.

    econstructor.
    eapply stbsrstop.
    econstructor.

  -    
    do_wf_pieces.
    destruct r; destruct s.
    +
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
     
    eapply IHt1.
    eassumption.

    2: {
      eassumption.
    }
    eassumption.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_transitive.

    eapply lstar_stbparr.
        
    eapply IHt2.
    eassumption.

    2: {
      eassumption.
    }

    econstructor.

    econstructor.

    eapply stbpstop.

    econstructor.

    +
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
     
    eapply IHt1.
    eassumption.
    2: {
      eassumption.
    }
    
    econstructor.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_transitive.

    eapply lstar_stbparr.
        
    eapply IHt2.
    eassumption.

    2: {
      eassumption.
    }

    eassumption.

    econstructor.

    eapply stbpstop.

    econstructor.

    +
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
     
    eapply IHt1.
    eassumption.
    2: {
      eassumption.
    }
    eassumption.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_transitive.

    eapply lstar_stbparr.
        
    eapply IHt2.
    eassumption.
    2: {
      eassumption.
    }
    eassumption.

    econstructor.

    eapply stbpstop.

    econstructor.
Defined.
*)
