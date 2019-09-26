Require Import More_lists Preamble Term LTS.
Require Import Instr MyStack MonadVM.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.

Require Import Verdi.Net.
Require Import Verdi.LockServ.
Require Import Verdi.Verdi.

Set Nested Proofs Allowed.

Definition remote_events (t:AnnoTerm) : (list Ev).
Admitted.

Definition parallel_att_vm_thread (li:list AnnoInstr) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_vm_events (li:list AnnoInstr) : list Ev.
Admitted.

(*
Axiom remote_events_axiom : forall t tr,
    trace t tr -> remote_events t = tr.*)

Definition prim_trace (i:nat) (a:Prim_Instr) : (list Ev) :=
  match a with
  | copy => [Term.copy i]
  | kmeas asp_id q A => [Term.kmeas i asp_id q A]
  | umeas asp_id A => [Term.umeas i asp_id A]
  | sign => [Term.sign i]
  | hash => [Term.hash i]
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
    modify_evm (prim_ev a) ;;
               add_tracem (prim_trace x a)
               
  | asplit x sp1 sp2 =>
    e <- get_ev ;;
      p <- split_evm x sp1 sp2 e;;
      let '(e1,e2) := p in
      put_ev e1 ;;
      push_stackm e2
                  (*push_stackm e1*)
  | ajoins i =>    (*let (er,r') := pop_stackr r in *)
    (*e <- pop_stackm ;;*)
    e <- get_ev ;;
      er <- pop_stackm ;;
      push_stackm (ssc er e) ;;
      add_tracem [Term.join i]
      (*
  | ajoinp i =>
    (*e <- pop_stackm ;;*)
    e <- get_ev ;;
      er <- pop_stackm ;;
      push_stackm (ppc e er) ;;
      add_tracem [Term.join i] *)
  | abesr =>
    (*e <- pop_stackm ;;*)
    e <- get_ev ;;
      er <- pop_stackm ;;
      push_stackm e ;;
      put_ev er
      (*
  | areqrpy rg q annt =>
    e <- get_ev ;;
      put_ev (toRemote (unanno annt) q e) ;;
      let '(reqi,rpyi_last) := rg in
      let rpyi := Nat.pred rpyi_last in
      let newTrace :=
          [req reqi q (unanno annt)] ++ (remote_events annt) ++ [rpy rpyi q] in
      add_tracem newTrace
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
  fold_left run_vm_step il st.

Definition run_vm_t (t:AnnoTerm) st : vm_st :=
  run_vm (instr_compiler t) st.

(*
(** Relational-style semantics for VM *)
Record vm_config : Type :=
  mk_config
    {vm_ev:EvidenceC ;
     vm_list:list AnnoInstr ;
      vm_stack:ev_stack
    }.


Inductive vm_step : vm_config -> vm_config -> (list Ev) -> Prop :=
| do_vmStep : forall e i l s,
    let res_st := execSt (mk_st e s []) (build_comp i) in
    let e' := st_ev res_st in
    let s' := st_stack res_st in
    let tr' := st_trace res_st in
    vm_step (mk_config e (i::l) s) (mk_config e' l s') tr'.

Definition vm_multi : step_relation vm_config Ev := refl_trans_1n_trace vm_step.

Lemma step_implies_multi : forall e e' i l tr s s',
    vm_step (mk_config e (i::l) s) (mk_config e' l s') tr ->
    vm_multi (mk_config e (i::l) s) (mk_config e' l s') tr.
Proof.
  intros.
  cut (vm_multi {| vm_ev := e; vm_list := i :: l; vm_stack := s |}
                   {| vm_ev := e'; vm_list := l; vm_stack := s' |} (tr++[])).
  rewrite app_nil_r. auto.
  repeat econstructor; eauto.
Defined.
Hint Resolve step_implies_multi.
*)

Lemma st_congr :
  forall st tr e s,
    st_ev st = e ->
    st_stack st = s ->
    st_trace st = tr ->
    st =  {| st_ev := e; st_trace := tr; st_stack := s |}.
Proof.
  intros.
  subst; destruct st; auto.
Defined.

Lemma trace_irrel : forall il1 tr1 tr1' tr2 e e' s s',

    run_vm il1 {| st_ev := e; st_trace := tr1; st_stack := s |} =
    {| st_ev := e'; st_trace := tr1'; st_stack := s' |} ->
    
    st_ev (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_stack := s |}) = e'.
Proof.
  induction il1; intros.
  - simpl.
    inversion H. reflexivity.
    
  -
    simpl;
    destruct a; try (destruct p; 
    unfold run_vm_step;
    monad_unfold;
    eapply IHil1;
    simpl in H;
    unfold run_vm_step in H; simpl in *; monad_unfold; 
    apply H).
Admitted.

Lemma ev_irrel : forall il1 tr1 e1 e2 s s',
(*
    run_vm il1 {| st_ev := e; st_trace := tr1 |} =
    {| st_ev := e'; st_trace := tr1' |} -> *)
    
    st_trace (
        run_vm il1 {| st_ev := e1; st_trace := tr1; st_stack := s |}) =
    st_trace (
        run_vm il1 {| st_ev := e2; st_trace := tr1; st_stack := s' |}).
Proof.
  induction il1; intros.
  - simpl.
    reflexivity.
  -
    (*
    simpl;
    destruct a; destruct p; 
    unfold run_vm_step;
    monad_unfold;
    eapply IHil1;
    simpl in H;
    unfold run_vm_step in H; simpl in *; monad_unfold; 
      apply H.
Defined. *)
Admitted.


Lemma stack_irrel : forall il1 tr1 tr1' tr2 e e' s s',
    run_vm il1 {| st_ev := e; st_trace := tr1; st_stack := s |} =
    {| st_ev := e'; st_trace := tr1'; st_stack := s' |} ->
    
    st_stack (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_stack := s |}) =
    s'.
  (*
    st_trace (
        run_vm il1 {| st_ev := e1; st_trace := tr2; st_stack := s |}).*)
Proof.
  induction il1; intros.
  - simpl.
    inversion H. reflexivity.
  -
    (*
    simpl;
    destruct a; destruct p; 
    unfold run_vm_step;
    monad_unfold;
    eapply IHil1;
    simpl in H;
    unfold run_vm_step in H; simpl in *; monad_unfold; 
      apply H.
Defined. *)
Admitted.


Lemma hihi : forall il (m : list Ev) (e : EvidenceC) s,
    st_trace (fold_left run_vm_step il
                        {| st_ev := e; st_trace := m; st_stack := s |}) =
    m ++
      st_trace (fold_left run_vm_step il
                          {| st_ev := e; st_trace := []; st_stack := s |}) ->

    (st_trace
       (fold_left run_vm_step il
                  {| st_ev := e; st_trace := m; st_stack := s |})) =
    (m ++
       st_trace
       (fold_left run_vm_step il
                  {| st_ev :=  e; st_trace := []; st_stack := s |})).
Proof.
  intros.
  auto.
Defined.

          Lemma push_stackm_pure : forall o e st_ev st_ev0 st_stack st_stack0 st_trace st_trace0,
            (o, {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0 |}) =
            push_stackm e
                        {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace |} ->
            st_trace0 = st_trace /\ st_ev = st_ev0.
          Proof.
          Admitted.

                    Lemma pop_stackm_pure : forall o st_ev st_ev0 st_stack st_stack0 st_trace st_trace0,
            (o, {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0 |}) =
            pop_stackm {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace |} ->
            st_trace0 = st_trace /\ st_ev = st_ev0.
          Proof.
          Admitted.

          Lemma push_stackm_succeeds : forall e st st',
          push_stackm e st = (None, st') -> False.
      Proof.
      Admitted.

      Lemma pop_stackm_determ : forall e0 e0' e e' e2 e2' s s' s2' tr tr' tr2 tr2',
        (Some e0', {| st_ev := e'; st_stack := s'; st_trace := tr' |}) =
        pop_stackm {| st_ev := e; st_stack := s; st_trace := tr |} ->
        (Some e0, {| st_ev := e2'; st_stack := s2'; st_trace := tr2' |}) =
        pop_stackm {| st_ev := e2; st_stack := s; st_trace := tr2 |} ->
        False.
      Proof.
      Admitted.

      Lemma pop_stackm_fail : forall e e' s s' tr tr',
          (None, {| st_ev := e'; st_stack := s'; st_trace := tr' |}) =
          pop_stackm {| st_ev := e; st_stack := s; st_trace := tr |} ->
          s = s'.
        Proof.
        Admitted.

Lemma foo : forall il m e s,
    st_trace (fold_left run_vm_step il
                        {| st_ev := e; st_trace := m; st_stack := s |}) =
    m ++ st_trace (fold_left run_vm_step il
                             {| st_ev := e; st_trace := []; st_stack := s |}).
Proof.
  induction il; simpl; intros m e s.
  - rewrite app_nil_r. auto.
  - destruct a; try ( (* prim and asplit cases *)
    
    unfold run_vm_step; fold run_vm_step; monad_unfold;
    
      rewrite IHil at 1;
      symmetry; 
      rewrite IHil at 1;
       (*
    assert ( st_trace
    (fold_left run_vm_step il
               {| st_ev := prim_ev p e; st_trace := prim_trace n p; st_stack := s |}) =
             
             (prim_trace n p) ++
                              st_trace (fold_left run_vm_step il
                                                  {| st_ev := prim_ev p e; st_trace := []; st_stack := s |})) as H by (apply IHil);
    
    rewrite H; *)
    
    (*erewrite hihi; eauto; *)
    rewrite <- app_assoc;
    tauto).
    
    
    + (* joins case *)
      unfold run_vm_step; fold run_vm_step; monad_unfold.
      unfold add_tracem. monad_unfold.

      remember (pop_stackm {| st_ev := e; st_stack := s; st_trace := m |}) as p. 
      destruct p.
      destruct o.
      
      remember ( push_stackm (ssc e0 e) v) as q.
      destruct q.
      destruct o. simpl.
      dependent destruction v.
      dependent destruction v0.
      simpl.

      remember (pop_stackm {| st_ev := e; st_stack := s; st_trace := [] |}) as r.
      destruct r.
      destruct o.

      remember (push_stackm (ssc e1 e) v) as y.
      destruct y. destruct o.

      dependent destruction v.
      dependent destruction v0.
      rewrite IHil at 1.
      simpl.
      symmetry.
      rewrite IHil at 1.
      assert (st_trace0 = m ++ st_trace2). {
        assert (st_trace0 = st_trace). {
          


          eapply push_stackm_pure; eauto.
           }
        assert (st_trace = m). {



          eapply pop_stackm_pure; eauto.
        }
        assert (st_trace1 = []). {
          eapply pop_stackm_pure; eauto.
          }
        assert (st_trace2 = st_trace1). {
          eapply push_stackm_pure; eauto.
        }
        subst.
        rewrite app_nil_r. congruence.
      }
      rewrite H.
      rewrite app_assoc at 1.
      rewrite app_assoc at 1.
      erewrite ev_irrel.
      reflexivity.
      Search (False).


      assert (False). eapply push_stackm_succeeds; eauto. contradiction.



      assert (False). eapply pop_stackm_determ; eauto. contradiction.
      
        
      assert (False). eapply push_stackm_succeeds; eauto. contradiction.

      remember (pop_stackm {| st_ev := e; st_stack := s; st_trace := [] |}) as r.
      destruct r.
      destruct o.
      
      remember (push_stackm (ssc e0 e) v0) as r.
      destruct r.
      destruct o.
      dependent destruction v.
      dependent destruction v0.
      assert (False). eapply pop_stackm_determ; eauto. contradiction.

      assert (False). eapply push_stackm_succeeds; eauto. contradiction.
      
     
      simpl.
      dependent destruction v.
      dependent destruction v0.
      assert (s = st_stack). {
      eapply pop_stackm_fail; eauto. }
      subst.
      assert (st_trace = m /\ e = st_ev). {
     
        eapply pop_stackm_pure. eassumption. }

      assert (st_trace0 = [] /\ e = st_ev0). {
        eapply pop_stackm_pure; eassumption. }

      assert (st_stack = st_stack0). {
        


        eapply pop_stackm_fail; eauto.
        
          
        }

      destruct_conjs.
      subst.
(*
          v = {| st_ev := e; st_stack := s; st_trace := m |}). {
        
        admit.
      } *)
      (*
      assert (v0 = {| st_ev := e; st_stack := s; st_trace := [] |}). {
        admit.
      } *)

      
      (* rewrite H. *)
      rewrite IHil.
      congruence.
  + (* abesr case *)
    
      assert (v0 = 
      
      




      
      destruct v0; destruct v2.
      unfold add_trace. simpl.
      rewrite IHil at 1.
      symmetry.
      rewrite IHil at 1.
      (*erewrite hihi; auto.*)
      simpl.
      erewrite ev_irrel.
    Check hihi.
    rewrite IHil at 1.
    assert ( st_trace
    (fold_left run_vm_step il
               {| st_ev := prim_ev p e; st_trace := prim_trace n p; st_stack := s |}) =
             
             (prim_trace n p) ++
                              st_trace (fold_left run_vm_step il
                                                  {| st_ev := prim_ev p e; st_trace := []; st_stack := s |})).
    apply IHil.
    rewrite H.
    
    erewrite hihi; eauto.
    rewrite <- app_assoc.
    auto.
      
Defined.



(*
Lemma multi_implies_run: forall il tr e e' s s',
  vm_multi (mk_config e il s) (mk_config e' [] s') tr ->
  run_vm il (mk_st e s []) = {| st_ev := e'; st_trace := tr; st_stack := s' |}.
Proof.
  induction il; intros.
  - inv H; unfold run_vm; simpl.
    + reflexivity.
    + inv H0.
  - inv H.
    unfold run_vm; simpl.
    unfold run_vm_step. fold run_vm_step. unfold execSt.

    (*destruct a; destruct p; dependent destruction x'; inv H0; inv H0; simpl in *. *)
    dependent destruction x'; inv H0; inv H0; simpl in *.

    (* pose (IHil cs' (hhc (hashEv e) e) e'). simpl in *. *)
    destruct a.
    Check prim_ev.
    pose (IHil cs' (prim_ev p e) e' s s'). simpl in *. 

    concludes.
    Check foo.   
    assert    ( st_trace (fold_left run_vm_step vm_list0
                        {| st_ev := prim_ev p e; st_trace := prim_trace n p; st_stack := s |}) =
    prim_trace n p ++ st_trace (fold_left run_vm_step vm_list0
                                         {| st_ev := prim_ev p e; st_trace := []; st_stack := s |})) as H2.
    apply foo.
    apply st_congr;
      try (eapply trace_irrel; eassumption).
    eapply stack_irrel; eassumption.
    
    rewrite H2. simpl.
    assert ( run_vm vm_list0 {| st_ev := prim_ev p e; st_trace := []; st_stack := s |} =
             (fold_left run_vm_step vm_list0 {| st_ev := prim_ev p e; st_trace := []; st_stack := s |})) as H3.
    { auto. }
    rewrite <- H3.
    rewrite e0. simpl. auto.
Defined.


Lemma vm_multi_trans : forall x y z tr tr',
  vm_multi x y tr ->
  vm_multi y z tr' ->
  vm_multi x z (tr ++ tr').
Proof.
  apply refl_trans_1n_trace_trans.
Defined.

Lemma run_implies_multi: forall il tr e e' s s',
    run_vm il {| st_ev := e; st_trace := []; st_stack := s |} = {| st_ev := e'; st_trace := tr; st_stack := s' |} ->
    vm_multi (mk_config e il s) (mk_config e' [] s') tr.
Proof. 
  induction il; intros.
  - inv H; unfold run_vm; simpl.
    econstructor.
  - 
    unfold run_vm in H.
    assert (a :: il = [a]++il) as H0. auto.
    rewrite H0 in *.
    rewrite fold_left_app in H. simpl in H. unfold run_vm_step in H. fold run_vm_step in H.

    
    unfold run_vm in IHil.   
    destruct a.
    Check prim_trace.
    monad_unfold.
    unfold run_vm_step in H. fold run_vm_step in H.

    assert (
       st_trace ( fold_left run_vm_step il
        {| st_ev := prim_ev p e; st_trace := prim_trace n p; st_stack := s |}) =
        st_trace ({| st_ev := e'; st_trace := tr; st_stack := s' |})
      ).
    { congruence. }

    assert (
      st_ev (fold_left run_vm_step il
        {| st_ev := prim_ev p e; st_trace := prim_trace n p; st_stack := s |}) =
      st_ev ({| st_ev := e'; st_trace := tr; st_stack := s' |})).
    { congruence. }

    simpl in *.
         
    assert (st_trace (fold_left run_vm_step il
                                {| st_ev := e; st_trace := prim_trace n p; st_stack := s |}) =
            (prim_trace n p) ++ st_trace (fold_left run_vm_step il {| st_ev := e; st_trace := []; st_stack := s |})).
    apply foo.

    assert (st_trace
         (fold_left run_vm_step il
                    {| st_ev := e; st_trace := prim_trace n p; st_stack := s |}) =
            st_trace
         (fold_left run_vm_step il
                    {| st_ev := prim_ev p e; st_trace := prim_trace n p; st_stack := s |})).
    eapply ev_irrel.
    rewrite <- H4 in H1.
    rewrite H3 in H1.
    rewrite <- H1.
    
    econstructor.
    econstructor.
    simpl.
    eapply IHil.

    apply st_congr.
    eapply trace_irrel.
    monad_unfold.

    apply H.
    eapply stack_irrel; eauto.
    eapply ev_irrel.
Defined.


Lemma run_iff_multi: forall il tr e e' s s',
run_vm il {| st_ev := e; st_trace := []; st_stack := s |} = {| st_ev := e'; st_trace := tr; st_stack := s' |} <->
vm_multi (mk_config e il s) (mk_config e' [] s') tr.
Proof.
  intros.
  split.
  - apply run_implies_multi.
  - apply multi_implies_run.
Defined.
*)

(*
Lemma ha : forall e e' e'' s s' s'' il1 il2 resl tr1 tr2,
  vm_multi (mk_config e  (il1 ++ il2) s) (mk_config e' il2 s') tr1 ->
  vm_multi (mk_config e' il2 s') (mk_config e'' resl s'') tr2  ->
  vm_multi (mk_config e  (il1 ++ il2) s) (mk_config e'' resl s'') (tr1 ++ tr2).
Proof.
  intros.
  eapply vm_multi_trans; eauto.
Defined.
*)

(*
Lemma asas : forall i l l' tr e e' s s',
    vm_step {| vm_ev := e;  vm_list := i :: l; vm_stack := s |}
            {| vm_ev := e'; vm_list := l; vm_stack := s' |}
            tr ->
    vm_step {| vm_ev := e; vm_list := i :: l'; vm_stack := s |}
            {| vm_ev := e'; vm_list := l'; vm_stack := s' |}
            tr.
Proof.
  intros.
  inv H.
  apply do_vmStep.
Defined.
*)

Print vm_st.

(*

Lemma vm_multi_transitive:
  forall il1 il2 resl tr1 tr2 e e' e'' s s' s'',
    vm_multi (mk_config e il1 s) (mk_config e' [] s') tr1 ->
    vm_multi (mk_config e' il2 s') (mk_config e'' resl s'') tr2 ->
    vm_multi (mk_config e (il1 ++ il2) s) (mk_config e'' resl s'') (tr1 ++ tr2).     
Proof.
  intros.
  dependent induction H.
  - simpl. eauto.
  - simpl.
    rewrite <- app_assoc.
    dependent destruction x'.
    inv H.
    monad_unfold.
    (*assert ((i :: vm_list0) ++ il2 = (i::(vm_list0 ++ il2))). auto.
    rewrite H2.*)
    constructor 2 with (x':=(mk_config (st_ev res_st) (vm_list0 ++ il2) (st_stack res_st))).
    eapply asas.
    eassumption.
    eapply IHrefl_trans_1n_trace; eauto.
Defined.
 *)

Check vm_st.
Print vm_st.
Print run_vm.
(*
{ st_ev : EvidenceC;  st_stack : ev_stack;  st_trace : list Ev }

run_vm = 
fun (il : list AnnoInstr) (st : vm_st) => fold_left run_vm_step il st
     : list AnnoInstr -> vm_st -> vm_st
*)

Lemma run_transitive_done: forall il1 il2 tr1 tr2 e e' e'' s s' s'',
    run_vm il1 (mk_st e s []) = (mk_st e' s' tr1) ->
    run_vm il2 (mk_st e' s' []) = (mk_st e'' s'' tr2) ->
    run_vm (il1 ++ il2) (mk_st e s []) = (mk_st e'' s'' (tr1 ++ tr2)).
Proof.
Admitted.

(*
Lemma vm_multi_transitive_done: forall il1 il2 tr1 tr2 e e' e'' s s' s'',
    vm_multi (mk_config e il1 s) (mk_config e' [] s') tr1 ->
    vm_multi (mk_config e' il2 s') (mk_config e'' [] s'') tr2 ->
    vm_multi (mk_config e (il1 ++ il2) s) (mk_config e'' [] s'') (tr1 ++ tr2).
Proof.
  intros.
  eapply vm_multi_transitive; eauto.
Defined. 
*)

(*
Definition vm_n1_multi : step_relation vm_config Ev := refl_trans_n1_trace vm_step.

Lemma vm_n1_implies_1n : forall r r' tr,
    vm_n1_multi r r' tr -> vm_multi r r' tr.
Proof.
  intros.
  apply refl_trans_n1_1n_trace; eauto.
Defined.

Lemma vm_1n_implies_n1 : forall r r' tr,
    vm_multi r r' tr -> vm_n1_multi r r' tr.
Proof.
  intros.
  apply refl_trans_1n_n1_trace; eauto.
Defined.

Lemma vm_1n_iff_n1 : forall r r' tr,
    vm_multi r r' tr <-> vm_n1_multi r r' tr.
Proof.
  intros.
  split.
  - apply vm_1n_implies_n1.
  - apply vm_n1_implies_1n.
Defined.
*)

(*
Lemma vm_n1_multi_transitive:
  forall e e' e'' s s' s'' il1 il2 resl tr1 tr2,
    vm_n1_multi (mk_config e il1 s) (mk_config e' [] s') tr1 ->
    vm_n1_multi (mk_config e' il2 s') (mk_config e'' resl s'') tr2 ->
    vm_n1_multi (mk_config e (il1 ++ il2) s) (mk_config e'' resl s'') (tr1 ++ tr2).
Proof.
  intros.
  rewrite <- vm_1n_iff_n1 in *.
  eapply vm_multi_transitive; eauto.
Defined.
*)

(* 
Record vm_config : Type :=
  mk_config
    {vm_ev:EvidenceC ; 
      vm_stack:ev_stack ;
     vm_list:list AnnoInstr}.
 *)
(*
Lemma record_congr : forall r,
  r = 
  {| vm_ev := vm_ev r; vm_list := vm_list r; vm_stack := vm_stack r |}.
Proof.
  intros.
  destruct r.
  reflexivity.
Defined.
 *)
Check st_congr.

(*
Lemma restt : forall tr1 tr2 il il1 i e e' e'' s s' s'',
  vm_n1_multi (mk_config e il s) (mk_config e' [] s') tr1 ->
  vm_step (mk_config e' [i] s') (mk_config e'' [] s'') tr2 ->
  il1 = il ++ [i] ->
  vm_multi  (mk_config e il1 s) (mk_config e'' [] s'') (tr1 ++ tr2).
Proof.
  intros.
  subst.
  eapply vm_multi_transitive.
  rewrite <- vm_1n_iff_n1 in H.
  eapply H.
  eapply step_implies_multi.
  assumption.
Defined.
*)

Definition shaver{A} (l: list A) : list A :=
  skipn ((length l) - 1) l.

Lemma listThing{A:Type} : forall (x:A) l1 l2,
    l1 ++ l2 = x :: l2 ->
    l1 = [x].
Proof.
  intros.
  assert (x::l2 = [x]++l2). auto.
  rewrite H0 in H.
  eapply app_inv_tail; eauto.
Defined.

Lemma hh {A:Type}:
  forall (l1:list A) l2,
    l1 ++ l2 = l2 ->
    l1 = [].
Proof.
  intros.
  Search (_ ++ _ = _).
  eapply app_inv_tail.
  apply H.
Defined.

Lemma skip1{A:Type} : forall (i:A) l lr,
    i :: l = lr ->
    l = skipn 1 lr.
Proof.
  intros.
  subst. simpl. reflexivity.
Defined.

(*
Lemma traces_append_gen : forall x y il1 il2 e e' e'' s s' s'',
    vm_multi {| vm_ev := e; vm_list := il1; vm_stack := s |} {| vm_ev := e'; vm_list := []; vm_stack := s' |} x ->
    vm_multi {| vm_ev := e'; vm_list := il2; vm_stack := s' |} {| vm_ev := e''; vm_list := []; vm_stack := s'' |} y ->
    vm_multi {| vm_ev := e; vm_list := il1 ++ il2; vm_stack := s |}
             {| vm_ev := e''; vm_list := []; vm_stack := s'' |} (x ++ y).
Proof.
  intros.
  eapply vm_multi_transitive; eauto.
Defined.
*)
  
Lemma headShouldersKneesAndToes : forall A (h : A) t l1 l2,
    h :: t = l1 ++ l2 ->
    forall prefix i, t = prefix ++ i :: l2 ->
    l1 = h :: prefix ++ [i].
Proof.
  intros. subst.
  assert (H0 : i :: l2 = [i] ++ l2). reflexivity.
  rewrite H0 in H; clear H0.
  eapply app_inv_tail.
  simpl. rewrite <- app_assoc. eauto.
Defined.

(*
Theorem vm_multi_suffix : forall il1 il2 tr e e' s s',
    vm_multi {| vm_ev := e; vm_list := il1; vm_stack := s |} {| vm_ev := e'; vm_list := il2; vm_stack := s' |} tr ->
    exists prefix, il1 = prefix ++ il2.
Proof.
  dependent induction il1; destruct il2; intros.
  - exists []. reflexivity.
  - inv H. inv H0.
  - exists (a::il1). rewrite app_nil_r. reflexivity.
  - inv H.
    + exists []. reflexivity.
    + dependent destruction x'.
      assert (vm_list0 = il1).
      inv H0. reflexivity.   
      edestruct IHil1.
      rewrite H2 in H1.
      apply H1.
      rewrite H3.
      exists (a::x). reflexivity.
Defined.
*)

(*
Lemma il1_pieces' : forall i0 vm_list0 il1 il2 i tr e e' s s',
    i0 :: vm_list0 = il1 ++ il2 ->
    vm_multi {| vm_ev := e; vm_list := vm_list0; vm_stack := s |} {| vm_ev := e'; vm_list := i :: il2; vm_stack := s' |} tr ->
    exists bla, il1 = [i0] ++ bla ++ [i].
Proof.
  intros i0 vm_list0 il1 il2 i tr e e' s s' H0 H1.
  remember (vm_multi_suffix _ _ _ _ _ _ _ H1) as e2. destruct e2. exists x.
  apply headShouldersKneesAndToes with (t := vm_list0) (l2 := il2); try assumption.
Qed.
*)

(*
Lemma restl : forall i il1 il2 cs cs' e e' e'' s s' s'',
  vm_multi  (mk_config e (il1 ++ il2) s) (mk_config e' (i::il2) s') cs ->
  vm_step (mk_config e' [i] s') (mk_config e'' [] s'') cs' ->
  vm_multi  (mk_config e il1 s) (mk_config e'' [] s'') (cs ++ cs').
Proof.
  intros.
  dependent induction H.
  - assert (il1 = [i]).
    eapply listThing; eauto.
    rewrite H in *. clear x. clear H.
    eapply step_implies_multi; eauto.
  - dependent destruction x'.
    inv H.
    monad_unfold.
    rewrite <- app_assoc.

    assert (exists bla, il1 = [i0] ++ bla ++ [i]).
    eapply il1_pieces'; eauto.
    destruct_conjs.
    rewrite H3.
    rewrite H3 in H.

    assert (
        (H2 ++ [i] ++ il2) =
        vm_list0).
      {
        assert (i0::vm_list0 = [i0]++vm_list0).
        { auto. }
        rewrite H3 in H4.

        rewrite <- app_assoc in H4.
        assert (([i0] ++ (H2 ++ [i]) ++ il2) =
                i0 :: (H2 ++ [i] ++ il2)).
        {
          rewrite <- app_assoc.
          simpl. auto.
        }

        rewrite H6 in H4.
        congruence.
      } 
    rewrite <- H5 in H.

    Check asas.
    assert (([i0] ++ H2 ++ [i]) ++ il2  = i0 :: (H2 ++ [i] ++ il2)).
    {
      simpl.
      rewrite <- app_assoc.
      assert ([i]++il2 = i::il2). auto.
      rewrite H6. auto.
    }
    rewrite H6 in H.
    
    eapply vm_multi_transitive.
    eapply step_implies_multi.
    Check asas.

    eapply asas. apply H.
    eapply IHrefl_trans_1n_trace; eauto.
    rewrite <- app_assoc.
    subst. auto.
Defined.
*)

(*
Lemma restl' : forall il1 il2 tr e e' s s',
    vm_multi  (mk_config e (il1 ++ il2) s)
                 (mk_config e' il2 s') tr ->
    vm_multi  (mk_config e il1 s) (mk_config e' [] s') tr.
Proof.
  intros.
  inv H.
  - assert (il1 = []).
    { eapply hh; eauto. }
    subst.    
    econstructor.
  - rewrite vm_1n_iff_n1 in H.
    inv H.
    + assert (il1 = []).
      eapply hh; eauto.
      subst.
      econstructor.
    + dependent destruction x'0.
      assert (exists i, vm_list0 = i :: il2).
      dependent destruction vm_list0. inv H6. inv H6.
      dependent destruction x'.
      exists a. reflexivity.

      destruct_conjs.
      rewrite H5 in *.
      eapply restl.
      rewrite vm_1n_iff_n1. apply H3.
      eapply asas. eauto.
Defined.
*)

(*
Lemma fafa : forall tr i rest e e' s s',
    vm_step (mk_config e [i] s) (mk_config e' [] s') tr ->
    vm_multi (mk_config e ([i] ++ rest) s) (mk_config e' rest s') tr.
Proof.
  intros.
  assert (tr = tr ++ []). rewrite app_nil_r. auto. rewrite H0.
  econstructor.
  eapply asas. eauto.
  econstructor.
Defined.
*)

Lemma list_nil_app{A:Type} : forall (l1 l2:list A),
    [] = l1 ++ l2 ->
    l1 = [] /\ l2 = [].
Proof.
  intros.
  destruct l1.
  - simpl in H.
    split; eauto.
  - inv H.
Defined. 

Lemma first_skip{A:Type} :
  forall n (l:list A),
    (firstn n l) ++ (skipn n l) = l.
Proof.
  apply firstn_skipn.
Defined.

Lemma compile_not_empty :
  forall t,
    (instr_compiler t) <> [].
Proof.
  intros.
  induction t.
  - destruct a; simpl; congruence.
  - simpl.
    Search (_ <> []).
    destruct (instr_compiler t1).
    +  simpl. auto.
    + simpl. congruence.
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

(*
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
*)

(*
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
*)

(*
Lemma update_ev_immut_stack'{A:Type} : forall s (h:VM A) e,
    st_stack (execSt s h) = st_stack (execSt s ((put_ev e);; h)).
Proof.
Abort.
*)  (* NOT true for arbitrary h:  h could match on e to update its stack *)


(*
Ltac invv :=
  repeat (
      match goal with
      | [ H: vm_lstar _ _ (_::_) _ _ |- _ ] => inv H; doit
      | [ G: vm_step _ _ _ _ |- _ ] => inv G; doit
      end).
*)

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

(*
Lemma jj_gen : forall il1 rest tr e e' s s',
    vm_multi
      {| vm_ev := e; vm_list := il1; vm_stack := s |}
      {| vm_ev := e'; vm_list := []; vm_stack := s' |} tr ->
    
    vm_multi
      {| vm_ev := e;
         vm_list := il1 ++ rest; vm_stack := s
          |}
      {| vm_ev := e';
         vm_list := rest; vm_stack := s'
          |} tr.
Proof.
  intros il1 rest tr e e' s s' H.
  assert (rest = [] ++ rest). simpl. reflexivity.
  rewrite H0 at 2.
  assert (tr = tr ++ []). rewrite app_nil_r. auto.
  rewrite H1.
  eapply vm_multi_transitive. apply H.
  simpl. econstructor.
Defined.
*)


Lemma ev_determ : forall il e s tr1 tr1' e' s' tr2,
    fold_left run_vm_step il {| st_ev := e; st_stack := s; st_trace := tr1 |} =
    {| st_ev := e'; st_stack := s'; st_trace := tr1' |} ->
    st_ev (fold_left run_vm_step il {| st_ev := e; st_stack := s; st_trace := tr2 |}) = e'.
Proof.
  induction il; intros.
  - simpl. simpl in H. congruence.
  - simpl;
    unfold run_vm_step; fold run_vm_step;
    destruct a; simpl; monad_unfold;
    destruct p; simpl;
    eapply IHil; simpl in *; unfold run_vm_step in *; fold run_vm_step in H; simpl in *;
    unfold execSt in *; simpl in *; eassumption.
Defined.

Lemma stack_determ : forall il e s tr1 tr1' e' s' tr1'',
    fold_left run_vm_step il {| st_ev := e; st_stack := s; st_trace := tr1 |} =
    {| st_ev := e'; st_stack := s'; st_trace := tr1' |} ->
    st_stack (fold_left run_vm_step il {| st_ev := e; st_stack := s; st_trace := tr1'' |}) = s'.
Proof.
    induction il; intros.
  - simpl. simpl in H. congruence.
  - simpl;
    unfold run_vm_step; fold run_vm_step;
    destruct a; simpl; monad_unfold;
    destruct p; simpl;
    eapply IHil; simpl in *; unfold run_vm_step in *; fold run_vm_step in H; simpl in *;
      unfold execSt in *; simpl in *; eassumption.
Defined.
      
Lemma run_vm_monotonic' : forall il x x0 e s,
    st_trace (fold_left run_vm_step il
                        {| st_ev := e; st_trace := []; st_stack := s |}) = x0 ->
    st_trace (fold_left run_vm_step il
                        {| st_ev := e; st_trace := x; st_stack := s |}) = x ++ x0.
Proof.
  intros.
  rewrite foo in H. simpl in H. subst.
  rewrite foo. auto.
Defined.
    
Lemma run_vm_monotonic : forall il x x0 e e' s s',
    fold_left run_vm_step il
              {| st_ev := e; st_trace := []; st_stack := s |} =
    {| st_ev := e'; st_trace := x0; st_stack := s' |} ->
    fold_left run_vm_step il
              {| st_ev := e; st_trace := x; st_stack := s |} =
    {| st_ev := e'; st_trace := x ++ x0; st_stack := s' |}.
Proof.
  intros.
  assert (st_trace (fold_left run_vm_step il {| st_ev :=e; st_trace := x; st_stack := s |}) = x ++ x0).
  { 
    apply run_vm_monotonic'.
    assert (fold_left run_vm_step il {| st_ev := e; st_trace := []; st_stack := s |} =
            {| st_ev := e'; st_trace := x0; st_stack := s' |} ->
            st_trace (fold_left run_vm_step il {| st_ev := e; st_trace := []; st_stack := s |}) =
            st_trace ({| st_ev := e'; st_trace := x0; st_stack := s' |})).
    { congruence. }
    
  apply H0 in H.
  simpl in H. auto. }
       (*      
  assert (st_ev (fold_left run_vm_step il {| st_trace := x |}) = e').
  eapply ev_determ. eassumption. (* TODO: ev deterministic regardless of trace, stack *)
  assert (st_stack (fold_left run_vm_step il {| st_trace := x |}) = s).
  eapply stack_determ. eassumption. (* TODO stack deterministic regardless of trace, ev *)
*)

  apply st_congr; eauto.
  eapply trace_irrel; eauto.
  eapply stack_irrel; eauto.
Defined.

Ltac heee l :=
  assert (l = l ++ []) as HH; auto; rewrite HH.

(*
Ltac hee :=
      match goal with
      | |- context
              [  vm_multi
                   {| vm_ev := _; vm_list := ?x |}
                   {| vm_ev := _; vm_list := [] |} _
        ] =>  assert (x = x ++ []) as HH; auto; rewrite HH
      end.
*)
(*
Lemma exists_trace : forall t e s,
  exists tr,
  run_vm (instr_compiler t) (mk_st e s []) =
              (mk_st (eval (unanno t) e) s tr).
Proof.
  induction t; intros.
  -
    (*exists (prim_trace (fst r) (asp_instr a)).*)
    destruct a; 
      simpl in *;
      eexists; econstructor.
  - destruct (IHt1 e s).
    destruct (IHt2 (eval (unanno t1) e) s).
    eexists.
    simpl.
    eapply run_transitive_done.
    eassumption.
    eassumption.
Defined.
*)

  (*
Lemma exists_trace : forall t e s,
  exists tr,
  vm_multi (mk_config e (instr_compiler t) s)
              (mk_config (eval (unanno t) e) [] s) tr.
Proof.
  induction t; intros.
  -
    (*exists (prim_trace (fst r) (asp_instr a)).*)
    destruct a; 
      simpl in *;
      eexists;
    hee;
    repeat econstructor.
  - destruct (IHt1 e s).
    destruct (IHt2 (eval (unanno t1) e) s).
    eexists.
    simpl.
    eapply vm_multi_transitive_done.
    eassumption.
    eassumption.
Defined.
*)

(*
Lemma exists_trace_gen : forall il e,
  exists tr e',
  vm_multi (mk_config e il)
              (mk_config e' []) tr.
Proof.
  induction il; intros.
  - eexists.
    eexists.
    econstructor.
  - edestruct IHil.
    destruct_conjs.
    destruct a.
    destruct p.
    eexists. exists H.
    econstructor.
    econstructor.
    apply H0.
Defined.

(*
    destruct IHt1.
    destruct IHt2.
    destruct_conjs.
    exists (x ++ x0).
    repeat eexists.

    rewrite <- run_iff_multi.
    unfold run_vm. simpl.
    rewrite fold_left_app.

    subst.
    assert ({| st_trace := x |} =

        (fold_left run_vm_step (instr_compiler t1)
                       {| st_trace := [] |})
            ).
    {
      Check run_iff_multi.
      
      subst.
      rewrite <- run_iff_multi in H. unfold run_vm in H.
     
      congruence.
    }
    rewrite <- H1.
    Check run_iff_multi.
    
    rewrite <- run_iff_multi in H0. unfold run_vm in H0.

    apply run_vm_monotonic; eauto.
Defined.
*)
*)


(*
Lemma trace_unique : forall il tr1 tr2 e e' e'' s s',
    vm_multi {| vm_ev := e; vm_list := il; vm_stack := s |} {| vm_ev := e'; vm_list := []; vm_stack := s' |} tr1 ->
    vm_multi {| vm_ev := e; vm_list := il; vm_stack := s|} {| vm_ev := e''; vm_list := []; vm_stack := s' |} tr2 ->
    tr1 = tr2.
Proof.
  intros.
  Check run_iff_multi.
  rewrite <- run_iff_multi in *.
  simpl in *.
  rewrite H in H0. congruence.
Defined.

Lemma ev_unique : forall il tr1 tr2 e e' e'' s s',
    vm_multi {| vm_ev := e; vm_list := il; vm_stack := s |} {| vm_ev := e'; vm_list := []; vm_stack := s' |} tr1 ->
    vm_multi {| vm_ev := e; vm_list := il; vm_stack := s |} {| vm_ev := e''; vm_list := []; vm_stack := s' |} tr2 ->
    e' = e''.
Proof.
  intros.
  Check run_iff_multi.
  rewrite <- run_iff_multi in *.
  simpl in *.
  rewrite H in H0. congruence.
Defined.
*)

(*
Lemma trace_decompose' :  forall t1 t2 tr e e'',
      vm_multi
      {| vm_ev := e; vm_list := (instr_compiler t1 ++ instr_compiler t2) |}
      {| vm_ev := e''; vm_list := []; |} tr ->
      exists tr1,
        vm_multi
      {| vm_ev := e; vm_list := (instr_compiler t1 ++ instr_compiler t2) |}
      {| vm_ev := (eval (unanno t1) e); vm_list := instr_compiler t2 |} tr1 /\
        exists tr2,
          vm_multi
            {| vm_ev := (eval (unanno t1) e); vm_list := instr_compiler t2 |}
            {| vm_ev := e''; vm_list := [] |} tr2 /\
          tr = tr1 ++ tr2.
Proof. *)


(*
Lemma trace_decompose' :  forall t1 t2 tr e e'' s s'',
      vm_multi
      {| vm_ev := e; vm_list := (instr_compiler t1 ++ instr_compiler t2); vm_stack := s |}
      {| vm_ev := e''; vm_list := []; vm_stack := s'' |} tr ->
      exists tr1 e' s',
        vm_multi
      {| vm_ev := e; vm_list := (instr_compiler t1 ++ instr_compiler t2); vm_stack := s |}
      {| vm_ev := e'; vm_list := instr_compiler t2; vm_stack := s' |} tr1 /\
        exists tr2,
          vm_multi
            {| vm_ev := (eval (unanno t1) e); vm_list := instr_compiler t2; vm_stack := s' |}
            {| vm_ev := e''; vm_list := []; vm_stack := s'' |} tr2 /\
          tr = tr1 ++ tr2.
Proof.
  Check exists_trace.
  Check trace_unique.
  intros.
  edestruct exists_trace with (t := t1) (s:=s).
  destruct_conjs.
  exists x. eexists. exists s.
  split.
  Check jj_gen.
  eapply jj_gen.
  eauto.
  destruct exists_trace with (t:=t2) (e:=eval (unanno t1) e) (s:=s).
  destruct_conjs.
  exists x0.
 (* assert (H0 = eval (unanno t1) e).
  eapply multi_ev_eval; eauto.
  assert (H2 = eval (unanno t2) H0).
  eapply multi_ev_eval; eauto. *)

    assert (instr_compiler t1 ++ instr_compiler t2 = instr_compiler (alseq (0,0) t1 t2)).
  auto.
  rewrite H2 in H.
  assert (e'' = eval (unanno (alseq (0, 0) t1 t2)) e).
  {
    destruct exists_trace with (t:=(alseq (0, 0) t1 t2)) (e:=e) (s:=s).
    Check ev_unique.
    eapply ev_unique with (e:=e) (e':=e'') (e'':=eval(unanno (alseq (0,0) t1 t2)) e). apply H.
    Check stack_irrel.
    rewrite <- run_iff_multi.
    Check stack_irrel.
    eapply st_congr.
    rewrite <- run_iff_multi in H3.
    rewrite H3. simpl. auto.
    eapply stack_irrel.
    rewrite <- run_iff_multi in H.
    apply H.
    Check ev_irrel.
    eapply ev_irrel. }
  
  (*
  eapply multi_ev_eval; eauto.*)
  assert (s'' = s) as H4. {
  rewrite <- run_iff_multi in *.
  assert (
      st_stack (run_vm (instr_compiler (alseq (0, 0) t1 t2))
        {| st_ev := e; st_stack := s; st_trace := [] |}) =
      st_stack ({| st_ev := e''; st_stack := s''; st_trace := tr |})).
  { congruence. }
  simpl in H4.
  destruct exists_trace with (t:=(alseq (0, 0) t1 t2)) (e:=e) (s:=s).
  rewrite <- run_iff_multi in H5.
  erewrite stack_irrel with (s' := s) in H4; eauto. }

  split; simpl in *; subst.
  -
    eassumption.
    (*
    Check st_congr.
    Check stack_irrel.
    rewrite <- run_iff_multi in H1.
    rewrite <- run_iff_multi.
    eapply st_congr.
    eapply trace_irrel; eauto.
    
    assert ( st_stack (
                 {| st_ev := eval (unanno t1) e; st_stack := s; st_trace := [] |}) = s)
    eapply st_congr.
    
    auto. *)
  -
    
    assert (vm_multi
              {| vm_ev := e; vm_list := (instr_compiler t1 ++ instr_compiler t2); vm_stack := s |}
              {| vm_ev := eval (unanno t2) (eval (unanno t1) e); vm_list := []; vm_stack := s |} (x ++ x0)). {
  eapply traces_append_gen.
  eassumption.
  eassumption. }

    eapply trace_unique; eauto.
    Unshelve. exact mtc.
Defined.
*)

(*
Lemma trace_decompose'_gen :  forall tr il1 il2 e e'',
      vm_multi
      {| vm_ev := e; vm_list := (il1 ++ il2) |}
      {| vm_ev := e''; vm_list := []; |} tr ->
      exists tr1 e',
        vm_multi
      {| vm_ev := e; vm_list := (il1 ++ il2) |}
      {| vm_ev := e'; vm_list := il2 |} tr1 /\
        exists tr2,
          vm_multi
            {| vm_ev := e'; vm_list := il2 |}
            {| vm_ev := e''; vm_list := [] |} tr2 /\
          tr = tr1 ++ tr2.
Proof.
  intros.
  edestruct exists_trace_gen with (il:=il1).
  destruct_conjs.
  exists x. exists H0.
  split.
  Check jj_gen.
  eapply jj_gen.
  eauto.
  destruct exists_trace_gen with (il:=il2) (e:=H0).
  destruct_conjs.
  exists x0.
  split.
  subst.
  (*
  assumption.

  assert (vm_multi {| vm_list := il1 ++ il2 |}
                   {| vm_list := [] |} (x ++ x0)).
  apply traces_append_gen; auto.
  eapply trace_unique; eauto.
Defined. *)
Admitted.

*)


(*
Lemma trace_decompose :
  forall tr1 tr2 tr t1 t2 e e' e'' s,
    vm_multi
      {| vm_ev := e;  vm_list := instr_compiler t1; vm_stack := s |}
      {| vm_ev := e'; vm_list := []; vm_stack := s |} tr1 ->
    vm_multi
      {| vm_ev := e';  vm_list := instr_compiler t2; vm_stack := s |}
      {| vm_ev := e''; vm_list := []; vm_stack := s |} tr2 ->
    vm_multi
      {| vm_ev := e; vm_list := (instr_compiler t1 ++ instr_compiler t2); vm_stack := s |}
      {| vm_ev := e''; vm_list := []; vm_stack := s |} tr ->
    tr = tr1 ++ tr2.
Proof.
  intros.
  edestruct trace_decompose'. eassumption.
  destruct_conjs.
  subst.
  assert (e' = eval (unanno t1) e).
  {
    destruct exists_trace with (t:=t1) (e:=e) (s:=s).
    Check ev_unique.
    eapply ev_unique; eauto.
  }
  subst.
  assert (H3 = s) as H7.
  {
    destruct exists_trace with (t:=t1(*(alseq (0,0) t1 t2)*)) (e:=e) (s:=s).
    
    Check stack_irrel.

    Check restl'.
    assert (
        vm_multi
         {|
         vm_ev := e;
         vm_list := instr_compiler t1;
         vm_stack := s |}
         {| vm_ev := H2; vm_list := []; vm_stack := H3 |} x).
    eapply restl'; eauto.

    rewrite <- run_iff_multi in *.
(*
    assert (
         st_stack (run_vm (instr_compiler t1)
         {| st_ev := e; st_stack := s; st_trace := [] |}) =
         st_stack ({| st_ev := H2; st_stack := H3; st_trace := x |})).
    { congruence. } *)

    assert (
    st_stack (run_vm (instr_compiler t1)
         {| st_ev := e; st_stack := s; st_trace := [] |}) =
    st_stack ( {| st_ev := eval (unanno t1) e; st_stack := s; st_trace := x0 |})).
    { congruence. }
    simpl in H9.
    rewrite H7 in H8. inv H8.
    reflexivity. } 

    (*
    simpl in H9.
                                                                       
        
    assert 

        
    { congruence. }
    
    simpl in H8. rewrite <- H8.
    Check stack_irrel.
    symmetry.
    
    eapply stack_irrel; eauto.
    rewrite <- H6 in H8.
    simpl in H8. rewrite <- H8 in H6. simpl in H6.
    congruence.
    
    admit.
  } *)
  assert (tr2 = H5). {
  Check trace_unique.

                   subst.
  eapply trace_unique; eauto.
  }
  subst.
  Check restl'.

  assert (vm_multi {| vm_ev := e; vm_list := instr_compiler t1; vm_stack := s |} {| vm_ev := H2; vm_list := []; vm_stack := s |} x). {
    apply restl' with (il2:=instr_compiler t2).
   
    eauto. }
  
  assert (x = tr1).
  eapply trace_unique; eauto.
  congruence.
Defined.
*)

(*
Lemma trace_decompose_gen :
  forall tr1 tr2 tr il1 il2 e e' e'',
    vm_multi
      {| vm_ev := e;  vm_list := il1 |}
      {| vm_ev := e'; vm_list := [] |} tr1 ->
    vm_multi
      {| vm_ev := e';  vm_list := il2 |}
      {| vm_ev := e''; vm_list := [] |} tr2 ->
    vm_multi
      {| vm_ev := e; vm_list := (il1 ++ il2) |}
      {| vm_ev := e''; vm_list := [] |} tr ->
    tr = tr1 ++ tr2.
Proof.
  (*
  intros.
  edestruct trace_decompose'_gen. eassumption.
  destruct_conjs.
  rewrite H5.
  assert (x = tr1).
  Check hh.
  assert (vm_multi {| vm_list := il1 |} {| vm_list := [] |} x).
  eapply restl'; eauto.

  eapply trace_unique; eauto.

  assert (H3 = tr2).
  eapply trace_unique; eauto.
  
  congruence.
Defined. *)
Admitted.
 *)

Print vm_st.

Lemma ya :
  forall A,
    A =
    {| st_ev := st_ev A;
       st_stack := st_stack A;
       st_trace := st_trace A |}.
Proof.
  intros.
  destruct A.
  reflexivity.
Defined.

Lemma st_trace_run_vm_step : forall e e' s s' a,
    st_trace (run_vm_step {| st_ev := e; st_stack := s; st_trace := [] |} a) =
    st_trace (run_vm_step {| st_ev := e'; st_stack := s'; st_trace := [] |} a).
Proof.
  destruct a.
  destruct p; try (simpl; auto).
Defined.

Lemma st_trace_destruct' :
  forall il1 il2 e s e' s' m,
    st_trace
      (fold_left run_vm_step il2
                 (fold_left run_vm_step il1
                            {| st_ev := e; st_stack := s; st_trace := m |})) =
    m ++ 
    st_trace
      (fold_left run_vm_step il1 
                 {| st_ev := e; st_stack := s; st_trace := [] |}) ++
      st_trace
      (fold_left run_vm_step il2
                 {| st_ev := e';
                    st_stack := s';
                    st_trace := [] |}).
Proof.
  induction il1; (*destruct il1;*) try reflexivity; intros.
  - simpl.
    erewrite foo.
    erewrite ev_irrel. auto.
  - simpl.
    Check foo.
    destruct a.
    unfold run_vm_step. fold run_vm_step.
    monad_unfold.
    rewrite foo.
    rewrite <- app_assoc.
    rewrite <- IHil1.
    erewrite IHil1.
    erewrite IHil1.
    rewrite <- app_assoc.
    auto.
    Unshelve. exact mtc. exact [].
Defined.


Lemma st_trace_destruct :
  forall il1 il2 e s e' s',
    st_trace
      (fold_left run_vm_step il2
                 (fold_left run_vm_step il1
                            {| st_ev := e; st_stack := s; st_trace := [] |})) =
    st_trace
      (fold_left run_vm_step il1 
                 {| st_ev := e; st_stack := s; st_trace := [] |}) ++
      st_trace
      (fold_left run_vm_step il2
                 {| st_ev := e';
                    st_stack := s';
                    st_trace := [] |}).
Proof.
  intros.
  erewrite st_trace_destruct'.
  simpl. auto.
Defined.

  (*
  induction il1; (*destruct il1;*) try reflexivity; intros.
  - simpl.
    apply ev_irrel.
  - simpl.
    Check foo.
    destruct a.
    unfold run_vm_step. fold run_vm_step.
    monad_unfold.
    rewrite foo.
    rewrite <- app_assoc.
    rewrite <- IHil1.
    Check foo.
    
    
    rewrite app_nil_r. auto.
  - simpl.
    unfold run_vm_step. fold run_vm_step. destruct a. monad_unfold.
    unfold add_tracem. monad_unfold.
    destruct (modify_evm (prim_ev p)
              (fold_left run_vm_step il1
                         {| st_ev := e; st_stack := s; st_trace := [] |})).
    destruct o.
    + simpl.
      Check foo.
      assert (
          st_trace
            (fold_left run_vm_step il2
               {| st_ev := prim_ev p e'; st_stack := s'; st_trace := prim_trace n p |}) =
          prim_trace n p ++
       st_trace
         (fold_left run_vm_step il2
                    {| st_ev := prim_ev p e'; st_stack := s'; st_trace := [] |})).
      apply foo.
      rewrite H.
      rewrite <- foo at 3.
      rewrite <- IHil2.
    


    
    

  -  destruct a.
    destruct p; try 
                  unfold run_vm_step; fold run_vm_step; monad_unfold;
      eapply ev_irrel.

  - simpl in *.
    Check foo.
    unfold run_vm_step. fold run_vm_step. monad_unfold.
    destruct a; destruct a0. monad_unfold. unfold add_tracem.
    unfold modify. unfold add_trace. fold add_trace.
    monad_unfold. simpl. unfold modify_evm. monad_unfold. simpl.
    


    monad_unfold.
    destruct (modify_evm (prim_ev p)
              (fold_left run_vm_step il1
                 {|
                 st_ev := prim_ev p0 e;
                 st_stack := s;
                 st_trace := prim_trace n0 p0 |})).
    destruct o; simpl.
    unfold add_trace. simpl.
    destruct v.
    admit.
    simpl.
    
    reflexivity.
    admit.
    rewrite <- IHil2.
    

    simpl.
    rewrite fold_left_app.
    simpl.
    destruct a; destruct a0.
    simpl.
    rewrite <- IHil1.   
    
    
Admitted. *)

Lemma destruct_compiled_appended : forall il1 il2 tr e e'' s s'',
    run_vm
      (il1 ++ il2)
        {| st_ev := e;   st_stack := s;   st_trace := [] |} =
        {| st_ev := e''; st_stack := s''; st_trace := tr;  |} ->
    (exists tr1 e' s',
        run_vm
          (il1)
          {| st_ev := e;  st_stack := s;  st_trace := []  |} =
          {| st_ev := e'; st_stack := s'; st_trace := tr1;  |} /\
        exists tr2,
          run_vm
            (il2)
            {| st_ev := e';  st_stack := s';  st_trace := tr1 |} =
            {| st_ev := e''; st_stack := s''; st_trace := tr1 ++ tr2;  |} /\
          tr = tr1 ++ tr2).
Proof.
  intros.
  remember (run_vm (il1) {| st_ev := e; st_stack := s; st_trace := [] |}) as A.
  
  exists (st_trace A).
  exists (st_ev A).
  exists (st_stack A).
  Check st_congr.

  split.
  apply ya.
  remember (run_vm (il2)
                   {| st_ev := st_ev A; st_stack := st_stack A; st_trace := st_trace A |}) as B.
  exists (st_trace (run_vm (il2)
                      {| st_ev := st_ev A;
                         st_stack := st_stack A;
                         st_trace := [] |})).
  subst.
  unfold run_vm.
  
  rewrite <- ya.

  rewrite <- fold_left_app.
    assert (st_trace
         (fold_left run_vm_step (il2)
            (fold_left run_vm_step (il1)
                       {| st_ev := e; st_stack := s; st_trace := [] |})) =
          st_trace
                (fold_left run_vm_step (il1)
                   {| st_ev := e; st_stack := s; st_trace := [] |}) ++
              st_trace
                (fold_left run_vm_step (il2)
                   {|
                   st_ev := st_ev
                              (fold_left run_vm_step (il1)
                                 {| st_ev := e; st_stack := s; st_trace := [] |});
                   st_stack := st_stack
                                 (fold_left run_vm_step (il1)
                                    {| st_ev := e; st_stack := s; st_trace := [] |});
                   st_trace := [] |})). {


      eapply st_trace_destruct; eauto.
    }
  split.
  -
    Check trace_irrel.


    
  assert (st_trace
                (fold_left run_vm_step (il1 ++ il2)
                           {| st_ev := e; st_stack := s; st_trace := [] |}) = tr).
  { unfold run_vm in H.
    rewrite H. simpl. reflexivity.
  }
  rewrite fold_left_app in H1.
  
  rewrite <- H0.
  rewrite H1.
  assumption.
  -
    rewrite <- H0.
    symmetry.
    unfold run_vm in H.
    rewrite fold_left_app in H.
    rewrite H. 
    simpl. reflexivity.
Defined.

(*
Lemma destruct_compiled_appended : forall t1 t2 tr e e'' s s'',
    run_vm
      (instr_compiler t1 ++ instr_compiler t2)
        {| st_ev := e;   st_stack := s;   st_trace := [] |} =
        {| st_ev := e''; st_stack := s''; st_trace := tr;  |} ->
    (exists tr1 e' s',
        run_vm
          (instr_compiler t1)
          {| st_ev := e;  st_stack := s;  st_trace := []  |} =
          {| st_ev := e'; st_stack := s'; st_trace := tr1;  |} /\
        exists tr2,
          run_vm
            (instr_compiler t2)
            {| st_ev := e';  st_stack := s';  st_trace := tr1 |} =
            {| st_ev := e''; st_stack := s''; st_trace := tr1 ++ tr2;  |} /\
          tr = tr1 ++ tr2).
Proof.
  intros.
  remember (run_vm (instr_compiler t1) {| st_ev := e; st_stack := s; st_trace := [] |}) as A.
  
  exists (st_trace A).
  exists (st_ev A).
  exists (st_stack A).
  Check st_congr.

  split.
  apply ya.
  remember (run_vm (instr_compiler t2)
                   {| st_ev := st_ev A; st_stack := st_stack A; st_trace := st_trace A |}) as B.
  exists (st_trace (run_vm (instr_compiler t2)
                      {| st_ev := st_ev A;
                         st_stack := st_stack A;
                         st_trace := [] |})).
  subst.
  unfold run_vm.
  Check exists_trace.
  rewrite <- ya.

  rewrite <- fold_left_app.
    assert (st_trace
         (fold_left run_vm_step (instr_compiler t2)
            (fold_left run_vm_step (instr_compiler t1)
                       {| st_ev := e; st_stack := s; st_trace := [] |})) =
          st_trace
                (fold_left run_vm_step (instr_compiler t1)
                   {| st_ev := e; st_stack := s; st_trace := [] |}) ++
              st_trace
                (fold_left run_vm_step (instr_compiler t2)
                   {|
                   st_ev := st_ev
                              (fold_left run_vm_step (instr_compiler t1)
                                 {| st_ev := e; st_stack := s; st_trace := [] |});
                   st_stack := st_stack
                                 (fold_left run_vm_step (instr_compiler t1)
                                    {| st_ev := e; st_stack := s; st_trace := [] |});
                   st_trace := [] |})). {


      eapply st_trace_destruct; eauto.
    }
  split.
  -
    Check trace_irrel.


    
  assert (st_trace
                (fold_left run_vm_step (instr_compiler t1 ++ instr_compiler t2)
                           {| st_ev := e; st_stack := s; st_trace := [] |}) = tr).
  { unfold run_vm in H.
    rewrite H. simpl. reflexivity.
  }
  rewrite fold_left_app in H1.
  
  rewrite <- H0.
  rewrite H1.
  assumption.
  -
    rewrite <- H0.
    symmetry.
    unfold run_vm in H.
    rewrite fold_left_app in H.
    rewrite H. 
    simpl. reflexivity.
Defined.
*)

  
  







(*
Lemma destruct_compiled_appended : forall t1 t2 tr e e'' s s'',
      vm_multi
        {| vm_ev := e;  vm_list := instr_compiler t1 ++ instr_compiler t2; vm_stack := s |}
        {| vm_ev := e''; vm_list := []; vm_stack := s'' |} tr ->
    (exists tr1 e' s',
        vm_multi
          {| vm_ev := e; vm_list := instr_compiler t1; vm_stack := s |}
          {| vm_ev := e'; vm_list := []; vm_stack := s' |} tr1 /\
        exists tr2,
          vm_multi
            {| vm_ev := e'; vm_list := instr_compiler t2; vm_stack := s' |}
            {| vm_ev := e''; vm_list := []; vm_stack := s'' |} tr2 /\
          tr = tr1 ++ tr2).
Proof.
  intros.
  edestruct exists_trace with (t:=t1).
  destruct_conjs.
  exists x. exists (eval (unanno t1) e). exists s.
  split.
  - 
    eassumption.
  -
    

  edestruct exists_trace with (t:=t2) (e:= eval (unanno t1) e) (s:=s).
  destruct_conjs.
  exists x0.
  assert (instr_compiler t1 ++ instr_compiler t2 =
          (instr_compiler (alseq (0,0) t1 t2))). auto.
  
  assert (s = s'').
  {
    edestruct exists_trace with (t:=(alseq (0,0) t1 t2)) (e:=e) (s:=s).
    simpl in H3.
    rewrite <- run_iff_multi in *.
    congruence.
  }

  assert (e'' = eval (unanno t2) (eval (unanno t1) e)). {
    destruct exists_trace with (t:= (alseq (0,0) t1 t2)) (e:=e) (s:=s).
    
    subst.
    eapply ev_unique; eauto. }
    

  split.
  +


    
    rewrite H2 in H.
    

    subst. eassumption.

  + eapply trace_decompose; eauto.
    rewrite H2 in H.
    subst. eauto.
Defined.
*)

(*
Lemma destruct_compiled_appended_gen : forall il1 il2 tr e e'',
      vm_multi
        {| vm_ev := e;  vm_list := il1 ++ il2 |}
        {| vm_ev := e''; vm_list := [] |} tr ->
    (exists tr1 e',
        vm_multi
          {| vm_ev := e; vm_list := il1 |}
          {| vm_ev := e'; vm_list := [] |} tr1 /\
        exists tr2,
          vm_multi
            {| vm_ev := e'; vm_list := il2 |}
            {| vm_ev := e''; vm_list := [] |} tr2 /\
          tr = tr1 ++ tr2).
Proof.
  (*
  intros.
  destruct exists_trace_gen with (il:=il1).
  destruct_conjs.
  exists x.
  split.
  assumption.

  edestruct exists_trace_gen with (il:=il2).
  destruct_conjs.
  exists x0.
  split.
  - assumption.
  - eapply trace_decompose_gen; eauto.
Defined. *)
Admitted.
 *)



(*
Lemma restl' : forall il1 il2 tr e e' s s',
    vm_multi (il1 ++ il2)
             (mk_st e s [])
             (mk_st e' s' tr il2 s') tr ->
    vm_multi  (mk_config e il1 s) (mk_config e' [] s') tr.
Proof. *)

Lemma restl' : forall il e e' s s' x tr,
    run_vm il {| st_ev := e; st_stack := s; st_trace := x |} =
    {| st_ev := e'; st_stack := s'; st_trace := x ++ tr |} ->

    run_vm il {| st_ev := e; st_stack := s; st_trace := [] |} =
    {| st_ev := e'; st_stack := s'; st_trace := tr |}.
Proof.
  induction il; intros.
  - simpl.
    inv H.
    assert (tr = []).
    { symmetry in H3.
      rewrite <- app_nil_r in H3.
      eapply app_inv_head. eauto.
    }

    congruence.
  - simpl.
    destruct a.
    + monad_unfold.
      unfold run_vm_step in *. fold run_vm_step in *. monad_unfold.
      eapply st_congr.
      eapply trace_irrel; eauto.
      eapply stack_irrel; eauto.
      rewrite foo.
      erewrite IHil.
      assert (
          st_trace (
              run_vm il
        {|
        st_ev := prim_ev p e;
        st_stack := s;
        st_trace := x ++ prim_trace n p |}) =

          st_trace (
              {| st_ev := e'; st_stack := s'; st_trace := x ++ tr |})).
      congruence.
      rewrite foo in H0. simpl in H0.
      assert (tr =
              prim_trace n p ++
       st_trace
         (fold_left run_vm_step il
                    {| st_ev := prim_ev p e; st_stack := s; st_trace := [] |})).

      Search ((_ ++ _) = (_ ++ _)).
      rewrite <- app_assoc in H0.
      eapply app_inv_head; eauto.
      
     
      rewrite H1.
      simpl.
      reflexivity.

      assert (
          st_trace (
              run_vm il
        {|
        st_ev := prim_ev p e;
        st_stack := s;
        st_trace := x ++ prim_trace n p |}) =

          st_trace (
              {| st_ev := e'; st_stack := s'; st_trace := x ++ tr |})).
      congruence.
      eapply st_congr.
      reflexivity.
      reflexivity.
      rewrite foo.
      reflexivity.
      Unshelve.
      exact [].
Defined.



Lemma multi_ev_eval : forall t tr1 e e' s s',
    run_vm (instr_compiler t)
           {| st_ev := e; st_stack := s;  st_trace := [] |} =
           {| st_ev := e'; st_stack := s'; st_trace := tr1 |}  ->
    e' = eval (unanno t) e.
Proof.
  induction t; intros.
  - destruct a; inv H; reflexivity.
  - simpl in *.
    edestruct destruct_compiled_appended; eauto.
    destruct_conjs.
    simpl.
    eapply IHt2.
    assert (H0 = eval (unanno t1) e).
    eauto.
    subst.
    eapply restl'; eauto.
Defined.

(*
Lemma multi_ev_eval : forall t tr1 e e' s,
    vm_multi {| vm_ev := e; vm_list := (instr_compiler t); vm_stack := s |}
             {| vm_ev := e'; vm_list := []; vm_stack := s |} tr1 ->
    e' = eval (unanno t) e.
Proof.
  induction t; intros.
  - destruct a;
    inv H; inv H0;

    inv H0;
  
    inv H1; try (inv H1; reflexivity); inv H2.
  -
    edestruct destruct_compiled_appended; eauto.
    destruct_conjs.
    simpl.
     assert (H1 = s).
     { edestruct exists_trace with (t:=t1) (e:=e) (s:=s).
       rewrite <- run_iff_multi in *.
       
       congruence.
     }
    eapply IHt2.
    assert (H0 = (eval (unanno t1) e)).
    {
   
    rewrite H6 in H4.
    rewrite H6 in H2.
    eapply IHt1; eauto. }
    subst. eassumption.
Defined.
 *)

Lemma multi_stack_restore : forall t tr1 e e' s s',
    run_vm (instr_compiler t)
           {| st_ev := e; st_stack := s;  st_trace := [] |} =
           {| st_ev := e'; st_stack := s'; st_trace := tr1 |}  ->
    s = s'.
Proof.
    induction t; intros.
    - destruct a;
        inv H; try reflexivity.
    - edestruct destruct_compiled_appended; eauto.
      destruct_conjs.
      eapply IHt2.
      assert (s = H1).
      eapply IHt1; eauto.
      subst.
      eapply restl'; eauto.
Defined.
  
(*
Lemma multi_stack_restore : forall t tr1 e e' s s',
    vm_multi {| vm_ev := e; vm_list := (instr_compiler t); vm_stack := s |}
             {| vm_ev := e'; vm_list := []; vm_stack := s' |} tr1 ->
    s = s'.
Proof.
  induction t; intros.
    - destruct a;
    inv H; inv H0;

    inv H0;
  
    inv H1; try (inv H1; reflexivity); inv H2.
  -
    edestruct destruct_compiled_appended; eauto.
    destruct_conjs.
    simpl.
    eapply IHt2.
    assert (s = H1).
    eapply IHt1; eauto.
    subst. eassumption.
Defined.
*)

(*
Lemma yo : forall e'0 e' cs' s,
    refl_trans_1n_trace vm_step
                        {| vm_ev := e'0; vm_list := []; vm_stack := s |}
                        {| vm_ev := e'; vm_list := []; vm_stack := s |}
                        cs' ->
    cs' = [].
Proof.
  intros.
  inv H.
  + reflexivity.
  + inv H0.
Defined.

Ltac haa :=
      match goal with
      | [H: refl_trans_1n_trace vm_step
            {| vm_ev := _; vm_list := []; vm_stack := _ |}
            {| vm_ev := _; vm_list := []; vm_stack := _ |}
            ?cs1 |- 
        lstar (stop _ _) ?cs1 (stop _ _)]
        => assert (cs1 = []) as HH by (eapply yo; eauto);
          rewrite HH
          
       (*assert (cs' = cs' ++ []) as HH; auto; rewrite HH*)
      end.
*)

(*
  H1 : refl_trans_1n_trace vm_step {| vm_ev := e'0; vm_list := [] |} {| vm_ev := e'; vm_list := [] |}
         cs'

  lstar (stop p (aeval (aasp r CPY) p et)) cs' (stop p et)

 *)

Lemma multi_lstar : forall t tr et p e e' s s',
    run_vm (instr_compiler t)
           (mk_st e s []) =
           (mk_st e' s' tr) ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  assert (s = s').
  eapply multi_stack_restore; eauto.
  rewrite <- H0 in H.
  clear H0.
  
  generalize dependent tr.
  generalize dependent et.
  generalize dependent p.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent s.
  generalize dependent s'. 
  induction t; intros.
  - destruct a;
     simpl in *; 
      invc H;
        econstructor; try (econstructor; reflexivity).
      (*haa;
      econstructor.*)
  - simpl in *.
    econstructor.
    econstructor.
    edestruct destruct_compiled_appended; eauto.
    destruct_conjs.
    subst.
    
    assert (s = H1).
    {
      eapply multi_stack_restore; eauto.
      (*
      edestruct exists_trace with (t:=t1) (e:=e) (s:=s).
       rewrite <- run_iff_multi in *.      
       congruence. *)
    }
    eapply lstar_transitive.
    
    eapply lstar_stls.
    
    rewrite H5 in H2.
    eapply IHt1; eauto.
    eapply lstar_silent_tran.
    apply stlseqstop.
    eapply IHt2.
    exact [].
    rewrite H5 in H4.
    eapply restl'; eauto.
Defined.
  

(*
Lemma multi_lstar : forall t tr et p e e' s s',
      vm_multi (mk_config e (instr_compiler t) s)
                  (mk_config e' [] s') tr ->
      lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  assert (s = s').
  eapply multi_stack_restore; eauto.
  rewrite <- H0 in H.
  clear H0.
  generalize dependent tr.
  generalize dependent et.
  generalize dependent p.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent s.
  generalize dependent s'.
  induction t; intros.
  - destruct a;
     simpl in *; 
      invc H; invc H0;
        econstructor; try (econstructor; reflexivity);
      haa;
      econstructor.
  - simpl in *.
    econstructor.
    econstructor.
    edestruct destruct_compiled_appended; eauto.
    destruct_conjs.
    subst.
    assert (s = H1).
    {
      edestruct exists_trace with (t:=t1) (e:=e) (s:=s).
       rewrite <- run_iff_multi in *.      
       congruence.
    }
    eapply lstar_transitive.
    
    eapply lstar_stls.
    
    rewrite H5 in H2.
    eapply IHt1; eauto.
    eapply lstar_silent_tran.
    apply stlseqstop.
    eapply IHt2.
    exact [].
    rewrite H5 in H4.

    eauto.
Defined.
*)


Require Import Main.
Require Import Event_system.
Require Import Term_system.

Theorem vm_ordered : forall t tr ev0 ev1 e e' s s',
    well_formed t ->
    run_vm
      (instr_compiler t)
      (mk_st e s []) =
      (mk_st e' s' tr) ->
    prec (ev_sys t) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  eapply ordered with (p:=0) (e:=mt); eauto.
  eapply multi_lstar; eauto.
Defined.

  
(*
Theorem vm_ordered : forall t tr ev0 ev1 e e' s s',
    well_formed t ->
    vm_multi
      (mk_config e (instr_compiler t) s)
      (mk_config e' [] s') tr ->
    prec (ev_sys t) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  eapply ordered with (p:=0) (e:=mt); eauto.
  eapply multi_lstar; eauto.
Defined.
*)
(*
  (*apply vm_lstar_trace in H0; auto.*)
  apply trace_order with (t:=t); auto.
Defined. *)









    



(*

Theorem vm_ordered : forall t e e' s tr ev0 ev1,
    well_formed t ->
    vm_1n_multi'
    (mk_accum e s) (mk_accum e' s)
    (instr_compiler t) [] tr ->
    prec (ev_sys t) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  apply vm_lstar_trace in H0; auto.
  apply trace_order with (t:=t); auto.
  (*  
  intros.
  edestruct vm_smallstep with (p:=0); eauto.
  eapply ordered; eauto. *)
Defined.




Lemma vm_config_correct : forall e s t tr,
    trace t tr ->
    vm_multi (mk_vm_config e                  (instr_compiler t) s)
                (mk_vm_config (eval (unanno t) e)[]                 s)
                tr.
Proof.
  intros.
  generalize dependent e.
  generalize dependent s.
  generalize dependent tr.
  induction t; intros; simpl in *.
  - inv H.
    destruct a; eapply step_implies_lstar; econstructor.
  - inv H. 
    eapply step_implies_lstar.
    rewrite <- remote_events_axiom with (t:=t) (tr:=tr1).
    eapply reqrpy_step. assumption.
  - inv H.
    eapply vm_multi_trans with (y:=mk_vm_config (eval (unanno t1) e) (instr_compiler t2) s).
    apply jj; eauto.
    apply IHt2; eauto.
  - destruct s.
    inv H.
    assert ( (Term.split (fst r) :: tr0 ++ tr1 ++ [join (Nat.pred (snd r))]) =
             ([Term.split (fst r)] ++ tr0 ++ tr1 ++ [join (Nat.pred (snd r))])).
    auto.
    rewrite H. clear H.
    econstructor 2.
    econstructor.
    econstructor. doit.
    eapply vm_multi_transitive'.
    apply IHt1; eauto.
    assert ((tr1 ++ [join (Nat.pred (snd r))]) = [] ++ (tr1 ++ [join (Nat.pred (snd r))])). auto.
    rewrite H.
    econstructor.
    econstructor.
    econstructor.
    eapply vm_multi_transitive'.
    apply IHt2; eauto.
    apply step_implies_lstar.
    econstructor.
  - destruct s.
    inv H.
    assert ((Term.split (fst r) :: tr2 ++ [join (Nat.pred (snd r))]) =
            [(Term.split (fst r))] ++ tr2 ++ [join (Nat.pred (snd r))]). auto.
    rewrite H.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.

    rewrite hihi with (t:=t1) (tr:=tr0).
    rewrite hihi with (t:=t2) (tr:=tr1).
    assumption.
    assumption.
    assumption.
    doit.
    apply step_implies_lstar.
    rewrite para_eval_vm.
    rewrite para_eval_vm.
    econstructor.
Defined.


Lemma vm_config_deterministic : forall e e' e'' s s' s'' (*r r' r''*) tr tr' t,
    trace t tr ->
    trace t tr' ->
    (*vm_1n_multi' r r' (instr_compiler t) [] tr ->
    vm_1n_multi' r r'' (instr_compiler t) [] tr' -> 
    r' = r''. *)
    vm_multi (mk_vm_config e (instr_compiler t) s) (mk_vm_config e' [] s') tr ->
    vm_multi (mk_vm_config e (instr_compiler t) s) (mk_vm_config e'' [] s'') tr' ->
    e' = e'' /\
    s' = s''.
Proof.  
Admitted.

Lemma vm_config_correct' : forall e e' s s' t tr,
    vm_1n_multi' (mk_accum e s) (mk_accum e' s')
                 (instr_compiler t) []
                tr ->
    e' = (eval (unanno t) e) /\
    s = s'.
Proof.
  intros.
  assert (trace t tr).
  eapply vm_lstar_trace.
  Check vm_config_correct.
  assert (vm_multi
         {| cec := e; cvm_list := instr_compiler t; cvm_stack := s |}
         {| cec := eval (unanno t) e; cvm_list := []; cvm_stack := s |} tr).
  apply vm_config_correct.
  eapply vm_lstar_trace. eassumption.
  eassumption.

  assert (vm_multi
         {| cec := e; cvm_list := instr_compiler t; cvm_stack := s |}
         {| cec := eval (unanno t) e; cvm_list := []; cvm_stack := s |} tr).
  apply vm_config_correct; eauto.
  unfold vm_1n_multi' in H. doit.
  edestruct vm_config_deterministic. {
    apply H0. }
  apply H0.
  unfold vm_1n_multi'.
  apply H.
  apply H1.
  split; eauto.
Defined.
  
*)





(******* ABANDONED PROOFS ********)


(**** restIL def  *)

(*
(*
Inductive rest_il : AnnoTerm -> Plc -> Evidence -> (list AnnoInstr) -> LTS.St -> Prop :=
(*| aasp_rest : forall r a p et,
    rest_il (aasp r a) p et
            [aprimInstr (fst r) (asp_instr a)]
            (conf (aasp r a) p et)*)
| term_rest : forall t p et,
    rest_il t p et (instr_compiler t) (conf t p et)
(*| aasp_done: forall r a p et,
    rest_il (aasp r a) p et
            []
            (stop p (aeval (aasp r a) p et))*)
| done_rest : forall t p et,
    rest_il t p et [] (stop p (aeval t p et))
(*| lseq_rest : forall r t1 t2 p e,
    rest_il (alseq r t1 t2) p e
            (instr_compiler t1 ++ instr_compiler t2)
            (conf (alseq r t1 t2) p e)*)
| lseq_rest_t1 : forall r t1 t2 il st p e,
    rest_il t1 p e il st ->
    rest_il (alseq r t1 t2) p e
            (il ++ (instr_compiler t2))
            (ls st t2)
| lseq_rest_t2 : forall r t1 t2 p e,
    rest_il (alseq r t1 t2) p e
            (instr_compiler t2)
            (conf t2 p (aeval t1 p e))
(*| lseq_done: forall r t1 t2 p et,
    rest_il (alseq r t1 t2) p et
            []
            (stop p (aeval t2 p (aeval t1 p et)))*).
*)

(*
Lemma multi_lstar' : forall t tr p et il il' st st',
      vm_multi (mk_config il)
               (mk_config il') tr ->
      rest_il t p et il st ->
      rest_il t p et il' st' ->
      lstar st tr st'.
Proof.  
  induction t; intros.
  - destruct a.
    inv H0; inv H1; simpl in *.
    + 
      assert (tr = []). admit.
      rewrite H2.
      econstructor.
    + inv H. inv H2.
      assert (cs' = []). admit.
      rewrite H4.
      rewrite app_nil_r. repeat econstructor.
    + inv H. inv H2.
    + assert (tr = []). admit.
      rewrite H2.
      econstructor.
  - inv H0; inv H1.
    Focus 10.
    assert (il = []). admit.
    subst.
    simpl in *.
    assert (tr = []). admit. subst. clear H.
    assert (st = (stop p (aeval t1 p et))). admit.
    subst. inv H1. inv H0. inv H11. admit. 

    
    + admit.
    + econstructor. econstructor.
      eapply lstar_stls.
      

      eapply IHt1.
      assert (vm_multi {| vm_list := (instr_compiler t1) |} {| vm_list := il |} tr). admit.
      apply H2.
      destruct t1. econstructor.
      simpl.
      econstructor. eauto.
    + econstructor. econstructor.
      assert (tr = tr ++ []). admit.
      rewrite H2.
      eapply lstar_transitive.
      eapply lstar_stls.
      eapply IHt1.
      assert ( vm_multi {| vm_list := instr_compiler t1 |}
                        {| vm_list := [] |} tr). admit.
      apply H3.
      destruct t1. econstructor.
      simpl. econstructor; eauto.
      destruct t1; econstructor.
      econstructor. apply stlseqstop. econstructor.
    + admit.
    + admit.
    + admit.
    + admit.

    Focus 9.
      
      
      
      
      
    
      
      
      
    
Admitted.
*)


(*
Lemma multi_lstar' : forall t tr et p il' st',
      vm_multi (mk_config (instr_compiler t))
               (mk_config il') tr ->
      rest_il t p et il' st' ->
      lstar (conf t p et) tr st'.
Proof.

  (*
  intros.
  generalize dependent et.
  generalize dependent st'.
  generalize dependent p.
  induction H; intros.*)




  intros.
  generalize dependent tr.
  induction H0; intros.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - 
    
    
  dependent induction t; intros.
  -
    
    inv H0.
    +  simpl in *.
       assert (tr = []). admit.
       subst.
       econstructor.
    + inversion H0. subst.
      destruct a.
      inv H. inv H1. inv H1.
      assert (res_st = res_st1). auto.
      rewrite H3.
      
      
      rewrite H6.
      eapply lstar_transitive.
      econstructor. econstructor. econstructor.
      assert (cs' = []). admit.
      rewrite H4.
      econstructor.
  -
    inv H0; simpl in *.
    + 
      assert (tr = []).
      admit.
      rewrite H1.
      econstructor.
    + inv H0.
      econstructor. econstructor.
      assert (tr = tr ++ []). rewrite app_nil_r. auto.
      rewrite H1.
      eapply lstar_transitive.
      apply lstar_stls. eapply IHt1.
      assert (vm_multi {| vm_list := instr_compiler t1 |}
                       {| vm_list := il |} tr). admit.
      apply H2. eauto.
      econstructor.
    +
      assert (vm_multi {| vm_list := instr_compiler t1 |}
                       {| vm_list := [] |} tr). admit.

      econstructor. econstructor.
      assert (tr = tr ++ []). rewrite app_nil_r. auto.
      rewrite H2.
      eapply lstar_transitive.
      eapply lstar_stls.
      eapply IHt1. eauto. destruct t1; econstructor.
      econstructor.  eapply stlseqstop.
      econstructor.
    +
      admit
      
      
      
    
      
      admit.
  -
    inv H0.
  
Admitted.
*)

(*
Lemma multi_lstar : forall t tr et p,
      vm_multi (mk_config (instr_compiler t))
                  (mk_config []) tr ->
      lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  eapply multi_lstar'.
  apply H.
  destruct t; econstructor.
  destruct t; econstructor.
Defined.*)
*)






(**** old lstar trace *)



(*
Lemma vm_lstar_trace: forall e e' s s' t tr,
    well_formed t -> 
    vm_1n_multi (mk_config e (instr_compiler t) s)
                (mk_config e' [] s')
                tr ->
    trace t tr.
Proof.
  intros.
  apply lstar_trace with (p:=0) (e:=mt).
  - eauto.
  - eapply multi_lstar. apply H0.
Defined.
*)

(*
Lemma vm_lstar_trace: forall r r' t tr,
    (*well_formed t -> *)
    vm_1n_multi' r r'
             (instr_compiler t) []
             tr ->
    trace t tr.
Proof.
  intros.
  induction H using refl_trans_1n_trace_n1_ind.
  admit.
  intros.
  (*assert (tr <> []). admit.*)
  generalize dependent r.
  generalize dependent r'.
  generalize dependent tr.
  induction t; intros.
  - destruct a; simpl.
    + simpl.
      inv H.
      inv H1. inv H0. inv H7. simpl. econstructor. inv H0. inv H8. inv H.
    + admit.
    +
      admit.
    +
      admit.
    + admit.
      (*
      inv H2.
      * simpl. econstructor.
      * inv H.
    + simpl.
      inv H.
      inv H1. inv H8.
      inv H2.
      * simpl. econstructor.
      * inv H.
    + simpl.
      inv H.
      inv H1. inv H8.
      inv H2.
      * simpl. econstructor.
      * inv H.
    + simpl.
      inv H.
      inv H1. inv H8.
      inv H2.
      * simpl. econstructor.
      * inv H.
    + simpl.
      inv H.
      inv H1. inv H8.
      inv H2.
      * simpl. econstructor.
      * inv H. *)
  - admit. (*inv H.
    dependent destruction x'.
    inv H1. inv H10.
    inv H2.
    simpl. rewrite app_nil_r.
    
    econstructor.
    eapply IHt.
    admit.
    admit. (* TODO: are these two axioms?? *)
    inv H. *)
  - simpl in H.
    (* rewrite multi'_iff_comp in H.
    dependent induction H. *)
    edestruct destr_app_compile; eauto.
    destruct_conjs.
    rewrite H4.
    econstructor; eauto.
    (*
    
    
    + admit.
    + admit.
    + 
      econstructor.
      
      eapply IHt1. 
      Search (_ ++ _ = _ ++ _).


    inv H.
    + congruence.
    + 
      
    simpl in H1.
    econstructor.
    
    edestruct destr_app_compile in H; eauto; destruct_conjs.
    subst.
    econstructor.
    eapply IHt1; eauto.
    + unfold not. intros.
      subst.
      inv H2.
      ++ admit. (* TODO: compile not empty lemma *)
      ++ dependent destruction x'.
         inv H9.
      * admit.
      * admit.

    
    + eapply IHt2; eauto.
      {
      unfold not. intros.
      subst.
      inv H4.
      * admit.
      * admit. } *)
  - simpl in H.
    destruct s.
    inv H.
    inv H0.
    inv H7. doit.
    (*admit.
    
    inv H8. doit.

    assert (
        refl_trans_1n_trace vm_step'
         {|
         cec := e1;
         cvm_list := instr_compiler t1 ++
                     abesr :: instr_compiler t2 ++ [ajoins (Nat.pred (snd r))];
         cvm_stack := e2 :: vm_stack r0 |}
         {| cec := ec r'; cvm_list := []; cvm_stack := vm_stack r' |} cs'
        =
        vm_1n_multi' (mk_accum e1 (e2 :: vm_stack r0)) r'
                     (instr_compiler t1 ++
                                     abesr :: instr_compiler t2 ++ [ajoins (Nat.pred (snd r))])
                     []
                     cs').
    auto.
    rewrite H in H2. clear H.   *)                

    edestruct destr_app_compile' in H1.
        assert (
        refl_trans_1n_trace vm_step'
         {|
         cec := e1;
         cvm_list := instr_compiler t1 ++
                     abesr :: instr_compiler t2 ++ [ajoins (Nat.pred (snd r))];
         cvm_stack := e2 :: vm_stack r0 |}
         {| cec := ec r'; cvm_list := []; cvm_stack := vm_stack r' |} cs'
        =
        vm_1n_multi' (mk_accum e1 (e2 :: vm_stack r0)) r'
                     (instr_compiler t1 ++
                                     abesr :: instr_compiler t2 ++ [ajoins (Nat.pred (snd r))])
                     []
                     cs').
        auto.
        rewrite <- H. eauto.
        
    destruct_conjs. doit.
    assert (trace t1 x).
    {
      eapply IHt1.
      eassumption.
    }
    clear H1.
    inv H3. doit.
    inv H1. doit.
    inv H10. doit.

    assert ( refl_trans_1n_trace vm_step'
         {|
         cec := er;
         cvm_list := instr_compiler t2 ++ [ajoins (Nat.pred (snd r))];
         cvm_stack := e :: vm_stack r'2 |}
         {| cec := ec r'; cvm_list := []; cvm_stack := vm_stack r' |} cs'0
             =
             vm_1n_multi' (mk_accum er (e :: vm_stack r'2))
                          r'
                          (instr_compiler t2 ++ [ajoins (Nat.pred (snd r))])
                          []
                          cs'0).
    auto.
    rewrite H1 in H6. clear H1. doit.

    edestruct destr_app_compile'' in H6; eauto.
    destruct_conjs.
    assert (trace t2 x0).
    {
      eapply IHt2; eauto.
    }
    rewrite H7.
    inv H4. doit.
    inv H9. doit. inv H14. doit. simpl in *.
    dependent destruction H1. doit.
    simpl in *.
    assert (cs' = []).
    {
    inv H10.
    + eauto.
    + inv H1. }
    rewrite H1.
    econstructor; eauto. 
  -
Admitted.
 *)




(** Misc ***)


(*
Lemma asdd {A:Type} : forall l (v:A) il1 il2,
    l ++ [v] = il1 ++ il2 ->
    (il2 = [] /\ l ++ [v] = il1) \/
    (*(il1 = [] /\ l ++ [v] = il2) \/*)
    (il2 = [v] /\ l = il1) \/
    (exists n, (il1 = firstn n l) /\ (il2 = (skipn n l) ++ [v])).
Proof.
Admitted.*)


(*
Axiom hihi : forall t tr,
    trace t tr -> (parallel_vm_events (instr_compiler t) = tr).

Axiom hihi' : forall t tr,
    (parallel_vm_events (instr_compiler t) = tr) -> trace t tr.
*)


(*
Lemma cross_relation e t s :
  forall (P : vm_config -> list Ev -> Prop),
    P (mk_config e (instr_compiler t) s) [] ->
    (forall st st' tr ev,
        vm_multi (mk_config e (instr_compiler t) s)
                    st tr ->
        P st tr ->
        (*vm_step (mk_accum (cec st) (vm_stack st)) i st' ev ->*)
        vm_step st st' ev ->
        P st' (tr ++ ev)) ->
    forall st tr,
      vm_multi (mk_config e (instr_compiler t) s) st tr ->
      P st tr.
Proof using.
  intros.
  find_apply_lem_hyp refl_trans_1n_n1_trace.
  prep_induction H1.
  induction H1; intros; subst; eauto.
  eapply H3; eauto.
  - apply refl_trans_n1_1n_trace. auto.
  - eapply IHrefl_trans_n1_trace; auto.
Defined.
*)
  
(*
Lemma cross_relation e t s :
  forall (P : vm_config -> list Ev -> Prop),
    P (mk_vm_config e (instr_compiler t) s) [] ->
    (forall st st' tr ev i,
        vm_1n_multi (mk_vm_config e (instr_compiler t) s) st tr ->
        P st tr ->
        vm_step (mk_accum (cec st) (cvm_stack st)) i st' ev ->
        P (mk_vm_config (ec st') (tail (cvm_list st)) (vm_stack st')) (tr ++ ev)) ->
    forall st tr,
      vm_1n_multi (mk_vm_config e (instr_compiler t) s) st tr ->
      P st tr.
Proof using.
  intros.
  find_apply_lem_hyp refl_trans_1n_n1_trace.
  prep_induction H1.
  induction H1; intros; subst; eauto.
  dependent destruction x''.
  inv H.
  apply H3.
  eapply H3; eauto.
  - apply refl_trans_n1_1n_trace. auto.
  - apply IHrefl_trans_n1_trace; auto.
Qed.
*)

(*
Lemma t_prop e t s :
  forall st tr,
    vm_multi (mk_config e (instr_compiler t) s) st tr ->
    True.
Proof.
  apply cross_relation; trivial.
Defined.
Check lstar.
*)

(*
Inductive st_to_instr : LTS.St -> list AnnoInstr -> Prop :=
| stop_st: forall p e, st_to_instr (stop p e) []
| conf_st: forall p e annt, st_to_instr (conf annt p e) (instr_compiler annt)
| rem_st: forall p q st, st_to_instr (rem p q st) []
| ls_st: forall st il1 annt,
    st_to_instr st il1 ->
    st_to_instr (ls st annt) (il1 ++ (instr_compiler annt))
| bsl_st: forall st il1 annt p n e,
    st_to_instr st il1 ->
    st_to_instr (bsl n st annt p e) ((il1 ++ (instr_compiler annt)))
| bsr_st: forall st il n e,
    st_to_instr st il ->
    st_to_instr (bsr n e st) il
| bp_st: forall n st1 st2,
    st_to_instr (bp n st1 st2) [].

Lemma trying : forall e e' s s' tr l l' st st',
  vm_1n_multi (mk_config e l s)
              (mk_config e' l' s') tr ->
  st_to_instr st l ->
  st_to_instr st' l' ->
  lstar st tr st'.
Proof.
  intros.
  induction st.
  - inv H0. inv H. inv H1. admit. admit. admit. inv H1. admit. admit. inv H1. admit. admit.
Abort.
*)

    
    

(*
Lemma multi_lstar_intermed: forall e e' s s' t tr et p l st,
  vm_1n_multi (mk_config e (instr_compiler t) s)
              (mk_config e' l s') tr ->
  st_to_instr st l ->
  lstar (conf t p et) tr st.
Proof.
  intros.
  generalize dependent tr.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent p.
  generalize dependent et.
  generalize dependent l.
  generalize dependent st.
  induction t; intros.
  - admit.
  - admit.
  -
    induction H.
    econstructor. econstructor. eapply IHt1.

    
    simpl in *.
    inv H.
    admit.
    econstructor.
    econstructor.
    econstructor
    
    simpl in *.
    
    


Lemma multi_lstar: forall e e' s s' t tr et p l,
      vm_1n_multi (mk_config e (instr_compiler t) s)
                  (mk_config e' l s') tr ->
      exists st',
        lstar (conf t p et) tr st'.
Proof.
Admitted.

Lemma multi_lstar' : forall e e' s s' t tr et p,
      vm_1n_multi (mk_config e (instr_compiler t) s)
                  (mk_config e' [] s') tr ->
      lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  edestruct multi_lstar with (p:=p) (et:=et).
  apply H.
 *)



(**** multi' proofs *****)

(*
Lemma restl : forall r r' r'' il1 il2 i cs cs',
    vm_1n_multi' r r' (il1 ++ il2) (i::il2) cs /\
    vm_step r' i r'' cs' ->
    vm_1n_multi' r r'' il1 [] (cs ++ cs').
Proof.
  intros.
  destruct H.
  eapply restt with (il:=shave_r il1).
  unfold vm_1n_multi' in H.
  rewrite <- vm_n1_iff_1n in H.
  inv H.
  admit.

  dependent destruction x'.
  inv H2.
Admitted.
 *)

(*
Lemma restt : forall r r' r'' il il1 tr1 tr2 i,
  vm_n1_multi' r r' il [] tr1 ->
  vm_step r' i r'' tr2 ->
  il1 = il ++ [i] ->
  vm_1n_multi' r r'' il1 [] (tr1 ++ tr2).
Proof.
  intros.
  rewrite H1.
  eapply vm_1n_multi_transitive'.
  unfold vm_n1_multi' in H.
  rewrite vm_n1_iff_1n in H.
  eapply H.
  apply step_implies_lstar.
  cut (vm_step r' i r'' tr2). repeat rewrite <- record_congr. auto.
  assumption.
Defined.*)

(*
Definition vm_n1_multi' (acc1:vm_accum) (acc2:vm_accum) (el_in:list AnnoInstr) (el_out:list AnnoInstr) (tr:list Ev) :=
  vm_n1_multi (mk_vm_config (ec acc1) el_in (vm_stack acc1))
              (mk_vm_config (ec acc2) el_out (vm_stack acc2))
              tr.

Lemma vm_n1_multi_transitive':
  forall r r' r'' il1 il2 resl tr1 tr2,
    vm_n1_multi' r r' il1 [] tr1 ->
    vm_n1_multi' r' r'' il2 resl tr2 ->
    vm_n1_multi' r r'' (il1 ++ il2) resl (tr1 ++ tr2).*)




(*
Lemma vm_1n_multi_transitive': 
  forall r r' r'' il1 il2 resl tr1 tr2,
    vm_1n_multi' r r' il1 [] tr1 ->
    vm_1n_multi' r' r'' il2 resl tr2 ->
    vm_1n_multi' r r'' (il1 ++ il2) resl (tr1 ++ tr2).
Proof.
  intros.
  (*unfold vm_1n_multi'. *)
  eapply vm_1n_multi_transitive'; eauto.
Defined.*)

(*
Lemma vm_1n_multi_transitive'_done: forall r r' r'' il1 il2 tr1 tr2,
    vm_1n_multi' r r' il1 [] tr1 ->
    vm_1n_multi' r' r'' il2 [] tr2 ->
    vm_1n_multi' r r'' (il1 ++ il2) [] (tr1 ++ tr2).
Proof.
  intros.
  eapply vm_1n_multi_transitive; eauto.
Defined.
 *)


(*
Lemma ffff_gen_helperrr : forall r r' il1 il1' il2 tr,
  (il1 <> []) ->
  vm_1n_multi' r r' il1 il1' tr ->
  vm_1n_multi' r r' (il1 ++ il2) (il1' ++ il2) tr.
Proof. (*
  intros.
  induction H0 using refl_trans_1n_trace_n1_ind.*)


  (*
  inv H0.
  - assert (r = r'). admit. rewrite H0.
    econstructor.
  - 
    dependent destruction x'.
    inv H1.
    Lemma afaf : forall r r' i l' cs,
        vm_step r i r' cs -> 
    vm_step' (mk_vm_config (ec r) (i::l') (vm_stack r))
             (mk_vm_config (ec r') l'     (vm_stack r'))
             cs.
    Proof.
    Admitted.
    assert ((i :: cvm_list0) ++ il2 = i :: (cvm_list0 ++ il2)). auto.
    rewrite H0.
    econstructor.

    apply afaf.  rewrite <- record_congr in H9. apply H9. clear H0. clear H9.
*)

    (*
    assert (cs' = [] ++ cs').(* rewrite app_nil_r.*) auto.

    rewrite H0.
    eapply vm_1n_multi_transitive.
    econstructor.
    
  ============================
  vm_step'
    {|
    cec := ec r;
    cvm_list := (i :: cvm_list0) ++ il2;
    inv H9
    eapply vm_1n_multi_transitive' *)  
Admitted.
*)





(******** Old vm_step: *******)

(*
Inductive vm_step: vm_accum -> AnnoInstr -> vm_accum -> (list Ev) -> Prop :=
| prim_step: forall r i a, vm_step r (aprimInstr i a) (update_ev (prim_ev a (ec r)) r) (prim_trace i a)
| split_step: forall r i sp1 sp2,
    let e1 := splitEv sp1 (ec r) in
    let e2 := splitEv sp2 (ec r) in
    let r' := update_ev e1 r in
    let r'' := push_stackr e2 r' in
    (*let r''' := add_trace [Term.split i] r'' in *)
    vm_step r (asplit i sp1 sp2) r'' [Term.split i]
| joins_step: forall r i,
    (*let (er,r') := pop_stackr r in *)
    let e := (ec r) in
    let er := (fst (pop_stackr r)) in
    let r' := (snd (pop_stackr r)) in
    let r'' := update_ev (ssc er e) r' in
    (*let r''' := add_trace [Term.join i] r'' in*)
    vm_step r (ajoins i) r'' [Term.join i]
| joinp_step: forall r i,
    (*let (er,r') := pop_stackr r in *)
    let e := (ec r) in
    let er := (fst (pop_stackr r)) in
    let r' := (snd (pop_stackr r)) in
    let r'' := update_ev (ppc e er) r' in
    (*let r''' := add_trace [Term.join i] r'' in*)
    vm_step r (ajoinp i) r'' [Term.join i]
| besr_step: forall r,
    let e := (ec r) in
    let popped_r := pop_stackr r in
    let er := fst (popped_r) in (*(fst (pop_stackr r)) in*)
    let r' := snd (popped_r) (*(snd (pop_stackr r))*) in
    let r'' := update_ev er r' in
    let r''' := push_stackr e r'' in
    vm_step r (abesr) r''' []
| reqrpy_step: forall r rg q annt,
    let e := (ec r) in
    let r' := update_ev (toRemote (unanno annt) q e) r in
    let reqi := (fst rg) in
    let rpyi := Nat.pred (snd rg) in
    let newTrace :=
        [req reqi q (unanno annt)] ++ (remote_events annt) ++ [rpy rpyi q] in     
    (*let r'' := add_trace newTrace r' in*)
    vm_step r (areqrpy rg q annt) r' newTrace
| bep_step: forall r rg1 rg2 il1 il2 tr,
    let e := (ec r) in
    let er := (fst (pop_stackr r)) in
    let r' := (snd (pop_stackr r)) in
    let res1 := parallel_att_vm_thread il1 e in
    let res2 := parallel_att_vm_thread il2 er in
    let el1 := parallel_vm_events il1 in
    let el2 := parallel_vm_events il2 in
    let r'' := update_ev res1 r' in
    let r''' := push_stackr res2 r'' in
    shuffle el1 el2 tr ->
    vm_step r (abep rg1 rg2 il1 il2) r''' tr.

Check step_relation.
Print step_relation.

Record vm_config : Type := mk_vm_config
                            { cec:EvidenceC ;
                              cvm_list:(list AnnoInstr) ;
                              cvm_stack:ev_stackc }.

Inductive vm_step' : vm_config -> vm_config -> list Ev -> Prop  :=
| doStep : forall e e' s s' i l tr,
    vm_step (mk_accum e s) i (mk_accum e' s') tr ->
    vm_step' (mk_vm_config e ([i] ++ l) s) (mk_vm_config e' l s') tr.*)








(*
Lemma ffff : forall r t tr r3 il2, (* TODO: il1 must be compiled for stack restore *)
    let il1 := (instr_compiler t) in
    vm_1n_multi' r r3
             (il1 ++ il2) []
             tr ->
   exists r' tr1,
      vm_1n_multi' r r'
               il1 []
               tr1 /\
     exists tr2,
      vm_1n_multi' r' r3
               il2 []
               tr2 (*/\
      tr = tr1 ++ tr2*).
     (*skipn (length tr0) tr3 = tr1 ++ tr2*)
Proof.
  intros.
  eapply ffff_gen.
  apply compile_not_empty.
  eauto.
Defined.
 *)



(* 
Lemma destr_app_compile : forall r0 r' t1 t2 tr r,
    vm_1n_multi' r0 r' (instr_compiler (alseq r t1 t2)) [] tr
    -> (exists tr1 r_mid,
          vm_1n_multi' r0 r_mid (instr_compiler t1) [] tr1 /\
          exists tr2,
            vm_1n_multi' r_mid r' (instr_compiler t2) [] tr2 /\
            tr = tr1 ++ tr2).
Proof. (*
  intros.
  induction H using refl_trans_1n_trace_n1_ind.
  admit. *)



(*
  intros.
  dependent induction t1.
  admit.
  apply IHn.*)


(*
  intros.
  dependent destruction r0.
  (*destruct all_t with (t:= t1) (e:=ec0) (s:=vm_stack0).*)
  destruct_conjs.
  assert (vm_1n_multi' {| ec := ec0; vm_stack := vm_stack0 |}
                       {| ec := (eval (unanno t1) ec0); vm_stack := vm_stack0 |} (instr_compiler t1) [] x).
  apply vm_config_correct. eauto.
    
  
  exists x.
  exists (mk_accum (eval (unanno t1) ec0) vm_stack0).

  split.
  eassumption. clear H2.
  destruct all_t with (t:= t2) (e:=eval (unanno t1) ec0) (s:=vm_stack0).
  destruct_conjs.

  assert ( vm_1n_multi'
             {| ec := (eval (unanno t1) ec0); vm_stack := vm_stack0 |}
             {| ec := (eval (unanno t2) (eval (unanno t1) ec0)); vm_stack := vm_stack0 |}
             (instr_compiler t2) []
             x0).
  apply vm_config_correct. eauto.

  assert (tr = x ++ x0).

  eapply aa; eauto.


  
  assert ( vm_1n_multi' {| ec := ec0; vm_stack := vm_stack0 |}
                        {| ec := eval (unanno (alseq r t1 t2)) ec0; vm_stack := vm_stack0 |}
                        
                        (instr_compiler (alseq r t1 t2 )) [] tr).
  
  eapply vm_config_correct.
  {
  rewrite H9.
  econstructor; eauto. }
  exists x0.
  
  split.

  assert (r' = {|
         ec := eval (unanno t2) (eval (unanno t1) ec0);
         vm_stack := vm_stack0 |}).
  simpl in H8.
  admit. (* TODO: vm_config_deterministic *)
  subst.
  eassumption.
  eassumption. *)
Admitted.

Lemma destr_app_compile': forall r0 r' t1 t2 tr n,
    vm_1n_multi' r0 r' (instr_compiler t1 ++
                         abesr :: instr_compiler t2 ++ [ajoins n]) [] tr
    -> (exists tr1 r_mid,
          vm_1n_multi' r0 r_mid (instr_compiler t1) [] tr1 /\
          exists tr2,
            vm_1n_multi' r_mid r' (abesr :: instr_compiler t2 ++ [ajoins n]) [] tr2 /\
            tr = tr1 ++ tr2).
Proof.
  intros.
Admitted.

Lemma destr_app_compile'': forall r0 r' t2 tr n,
    vm_1n_multi' r0 r' (instr_compiler t2 ++ [ajoins n]) [] tr
    -> (exists tr1 r_mid,
          vm_1n_multi' r0 r_mid (instr_compiler t2) [] tr1 /\
          exists tr2,
            vm_1n_multi' r_mid r' ([ajoins n]) [] tr2 /\
            tr = tr1 ++ tr2).
Proof.
Admitted.
*)





(*
Lemma ffff_gen :forall r r3 tr il1 il2,
    il1 <> [] ->
    vm_1n_multi' r r3
           (il1 ++ il2) []
           tr ->
  exists r' tr1,
    vm_1n_multi' r r'
             il1 []
             tr1 /\
    exists tr2,
      vm_1n_multi' r' r3
               il2 []
               tr2 (*/\
      tr = tr1 ++ tr2*).
Proof.
  intros.
  apply ffff_another_helper in H0; eauto.
  (*apply ffff_gen_helper in H0; eauto.*)
  destruct_conjs.
  exists H0. exists H1.
  split.
  - inv H2.
    admit.
    inv H5.
    assert (il1 = [i] \/
            exists n, il1 = [i] ++ (firstn n l)).
    admit.
    destruct H1.
    + 
    subst. assert (l = il2). admit.
    assert (cs' = []). admit. subst.
    rewrite app_nil_r.
    apply step_implies_lstar; eauto.
    assert (ec H0 = e'). admit.
    assert (vm_stack H0 = s'). admit.
    subst.
    eauto.
    + destruct_conjs.
      subst.
      econstructor.
      econstructor. apply H10.
      assert (l = (firstn H1 l) ++ il2). admit.
      rewrite H2 in H6.
      Check ffff_gen_helper'.
      dependent destruction H0. simpl in *.
      cut ( vm_1n_multi'
              {| ec := e'; vm_stack := s' |} {| ec := ec0; vm_stack := vm_stack0 |} (firstn H1 l) [] cs'). auto.
      eapply ffff_gen_helper'; eauto.
Admitted.


Lemma ffff_gen_helper'' : forall r r' il1 il2 tr,
  (il1 <> []) ->
  vm_1n_multi' r r' il1 [] tr ->
  vm_1n_multi' r r' (il1 ++ il2) il2 tr.
Proof.
  intros.
  cut (vm_1n_multi' r r' (il1 ++ il2) ([] ++ il2) tr). simpl; auto.
  eapply ffff_gen_helperrr; eauto.
Defined.


*)


(*
    (*eapply ffff_gen_helper'; eauto.*)
  - exists H3.
    eauto.
Defined.*)

(*
Proof.
  intros.
  apply ffff_gen_helper in H0.
  destruct_conjs.
  exists H0. exists H1.
  split.
  - eapply ffff_gen_helper'; eauto.
  - exists H3.
    eauto.
  - eassumption.
Defined.*)










(* OLD STACK RESTORE PROOF:  

  (*
  intros.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent l.
  generalize dependent l'.
  generalize dependent s.
  generalize dependent s'.
  
  induction t; intros.
  - destruct a; try (inv_vm_lstar; reflexivity).
  - inv_vm_lstar. reflexivity.

  - simpl in H.

    eapply ffff in H.
    destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H0. 
    assert (s = x1). eapply IHt1; eauto.
    assert (x1 = s'). eapply IHt2; eauto. congruence.
    econstructor.

  -
    simpl in H.
    destruct s.
    inv H.
    inv H4.
    apply ffff (*with (il2:= (abesr :: instr_compiler t2 ++ [ajoins (Nat.pred (snd r))])) (il1:=instr_compiler t1)*) in H5.
    destruct H5. destruct H. destruct H. destruct H. destruct H0. destruct H0.
    assert (vm_stack r'' = x1). eapply IHt1; eauto.
    (*assert (
        (abesr :: instr_compiler t2 ++ [ajoins (Nat.pred (snd r))])
        = ([abesr] ++ instr_compiler t2 ++ [ajoins (Nat.pred (snd r))])).
    trivial.
    rewrite H3 in H0. *)
    inv H0.
    inv H7.
   (* inv H8.*)
    apply ffff (*with (il2:= instr_compiler t2 ++ [ajoins (Nat.pred (snd r))]) (il1:=[abesr])*) in H8.
    destruct H8. destruct H0. destruct H0. destruct H0. destruct H2. destruct H2.
    
    (*apply ffff with (il2:=[ajoins (Nat.pred (snd r))]) (il1:=instr_compiler t2) in H4.  destruct H4. destruct H0. destruct H0. destruct H0. destruct H2. destruct H2.*)
    inv H2. inv H8. (*inv H10.*)
    assert (push_stackc e6 (vm_stack r'2) = x4).
    eapply IHt2; eauto.
    subst.
    inv H9.
    eauto.

    (*
    assert (x5 = x8). eapply IHt2; eauto. inv H10. inv H2. inv H10.
    assert (vm_stack r'' = push_stackc e2 s0).
    assert (vm_stack r'0 = vm_stack {| ec := e; vm_trace := l; vm_stack := s0 |}). eauto. eauto. 
    rewrite H2 in *.
    assert (vm_stack r'''0 = s').

    eapply ssss; eauto.
      
    subst.
    assert (vm_stack r''0 = x8).
    eapply ssss; eauto.
    
    subst. clear H11. clear H0. clear H.
    clear H12.
    assert (r'4 = r'5). eauto.
    eauto.
    (*
    subst.
    assert (vm_stack r'' = e2 :: s0). eauto.
    rewrite H0 in *.
    assert (vm_stack r'2 = s0). eauto.
    assert (vm_stack r''0 = e6::s0). eauto.
    assert (vm_stack r'5 = s0). assumption.
    rewrite <- H8.
    rewrite <- H.
    assert (vm_stack r''1 = vm_stack r'''0). eauto.
    rewrite <- H9.

    apply update_ev_immut_stack. *)
    econstructor.
    econstructor.
    econstructor. *)
    econstructor.
    econstructor.

  - simpl in H.
    destruct s.
    inv H. inv H5. inv H4.
    inv H3. inv H6.
    inv H4. inv H3.
   (* assert (vm_stack r'0 = vm_stack r''1).
    eapply update_ev_immut_stack.
    rewrite H. *)
    eauto.
Defined. *)

    (*
    unfold att_vm' in H.
    destruct s.
    simpl in H.
    rewrite fold_left_app in H.
    simpl in H.
    rewrite fold_left_app in H.
    simpl in H.
    (* unfold push_stack in H. *)  (* TODO:  why does this step of evaluation prohibit destructing the let later on?? *)
    
    unfold vm_prim at 3 in H. (*unfold push_stack in H. *)
    unfold vm_prim at 1 in H.

    remember (fold_left (vm_prim p) (instr_compiler t1 p)
                            (splitEv s e, push_stack (splitEv s1 e) s0)).
    destruct p0.

    remember (pop_stack e3).
    destruct p0.

    remember ((fold_left (vm_prim p) (instr_compiler t2 p)
                             (e4, push_stack e2 e5))).
    destruct p0.

    assert (e7 = e2 :: e5).
    apply IHt2 with (e:=e4) (e0:=e6) (p:=p).
    assumption.
    rewrite H0 in H. unfold pop_stack in H.
    inversion H. subst.

    assert (e3 = splitEv s1 e :: s0).
    apply IHt1 with (e:=splitEv s e) (e0:=e2) (p:=p).
    apply Heqp0.
    rewrite H0 in Heqp1.
    unfold pop_stack in Heqp1. inversion Heqp1. reflexivity.

  - simpl in H.
    destruct s in H.
    simpl in H.

    assert (parallel_att_vm_thread (instr_compiler t1 p) (splitEv s e) = 
                att_vm (instr_compiler t1 p) p (splitEv s e)).
    apply par_vm_thread.

    assert (parallel_att_vm_thread (instr_compiler t2 p) (splitEv s1 e) = 
            att_vm (instr_compiler t2 p) p (splitEv s1 e)).
    apply par_vm_thread.
    
    rewrite H0 in H.
    rewrite H1 in H.
    congruence.
*)

(* OLD LEMMAS/DEFINITIONS: *)

(*
Lemma fasd :
  lstar st (tr1 ++ tr2)
  lstar (rem (snd r) p (conf t n (et_fun p e)))
    (remote_events t ++ [rpy rpyi n]) (stop p (aeval t n (et_fun p e)))*)
 *)

(*
    Lemma fart : forall r' r'' l l' tr,
        tr <> [] ->
        vm_lstar r' r'' l l' tr -> l <> l'.
    Proof.
      intros.
      induction H0.
      - eauto.
      - 
        
      generalize dependent H.
      dependent induction H0; intros.
      - auto.
      - admit.
      
    Admitted.

    eapply fart; eauto.
    
 *)


(*
Definition add_trace (el:list Ev) (x:vm_accum) : vm_accum :=
  let old_trace := vm_trace x in
  let new_trace := old_trace ++ el in
  mk_accum (ec x) (new_trace) (vm_stack x). *)

(*
Inductive wf_instr_seq : list AnnoInstr -> Prop :=
| compile_wf: forall t, wf_instr_seq (instr_compiler t)
(*| concat_wf: forall t1 t2, wf_instr_seq (instr_compiler t1 ++ instr_compiler t2)*)
| bseq_wf: forall j t,
   (* wf_instr_seq il1 ->
    wf_instr_seq il2 -> *)
    wf_instr_seq ([abesr] ++ (instr_compiler t) ++ [ajoins j]). *)

(*| joins_wf: forall j,
    wf_instr_seq [ajoins j].*)
(*
| joinp_wf: forall j,
| bpar_wf: forall i j sp1 sp2 r1 r2 il1 il2,
    wf_instr_seq il1 ->
    wf_instr_seq il2 ->
    wf_instr_seq ([asplit i sp1 sp2] ++ [abep r1 r2 il1 il2] ++ [ajoinp j]).*)
(*
| bseq2_wf: forall t2 i,
    wf_instr_seq (instr_compiler t2 ++ [ajoins i])
| bseq3_wf: forall t2 i,
    wf_instr_seq ([abesr] ++ instr_compiler t2 ++ [ajoins i]).*)

(*
Lemma t_completes : forall r t, exists r',
      vm_lstar r r' (instr_compiler t) [].
Proof.
Admitted.
 *)

(*
Lemma ssss : forall e tr s r,
    vm_lstar r {| ec := e; vm_stack := s |} [] [] tr ->
    vm_stack r = s.
Proof.
  intros.
  inv H.
  simpl. reflexivity.
Defined. *)






(* Alternate multistep relation:  

Inductive vm_comp_multi : vm_accum -> vm_accum -> list AnnoInstr -> list AnnoInstr -> list Ev -> Prop :=
| vm_lstar_refl: forall r l, vm_comp_multi r r l l []
| vm_lstar_step: forall r r' i tr,
    vm_step r i r' tr ->
    vm_comp_multi r r' [i] [] tr
| vm_lstar_comp: forall r r' r'' tr1 tr2 resl t1 t2 il1 il2,
    il1 = instr_compiler t1 ->
    il2 = instr_compiler t2 ->
    vm_comp_multi r r' il1 [] tr1 ->
    vm_comp_multi r' r'' il2 resl tr2 ->
    vm_comp_multi r r'' (il1 ++ il2) resl (tr1 ++ tr2).

Lemma multi'_iff_comp : forall r r' l l' tr,
    vm_1n_multi' r r' l l' tr <-> vm_comp_multi r r' l l' tr.
Proof.
Admitted.

*)