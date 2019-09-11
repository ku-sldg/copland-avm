Require Import More_lists Preamble Term Trace LTS Instr Event_system Term_system.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.

Set Nested Proofs Allowed.

(** * EvidenceC Stack *)
Definition ev_stackc := list EvidenceC.
Definition empty_stackc : ev_stackc := [].

Definition push_stackc (e:EvidenceC) (s:ev_stackc) : ev_stackc :=
  (e :: s).

Definition pop_stackc (s:ev_stackc) : (EvidenceC*ev_stackc) :=
  match s with
  | e :: s' => (e,s')
  | _ => (mtc,empty_stackc) (* TODO: will this be expressive enough? *)
  end.

Record vm_accum : Type := mk_accum
                            { ec:EvidenceC ;
                              (*vm_trace:(list Ev) ;*)
                              vm_stack:ev_stackc }.

Definition update_ev (e:EvidenceC) (x:vm_accum) : vm_accum :=
  mk_accum e (vm_stack x).

Definition push_stackr (e:EvidenceC) (x:vm_accum) : vm_accum :=
  mk_accum (ec x) (push_stackc e (vm_stack x)).

Definition pop_stackr (x:vm_accum) : (EvidenceC*vm_accum) :=
  let (er,s') := pop_stackc (vm_stack x) in
  (er,mk_accum (ec x) (s')).

Definition remote_events (t:AnnoTerm) : (list Ev).
Admitted.

Definition prim_trace (i:nat) (a:Prim_Instr) : (list Ev) :=
  match a with
  | copy => [Term.copy i]
  | kmeas asp_id q A => [Term.kmeas i asp_id q A]
  | umeas asp_id A => [Term.umeas i asp_id A]
  | sign => [Term.sign i]
  | hash => [Term.hash i]
  end.
Check update_ev.

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

Definition parallel_att_vm_thread (li:list AnnoInstr) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_vm_events (li:list AnnoInstr) : list Ev.
Admitted.

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

Inductive vm_lstar: vm_accum -> vm_accum -> list AnnoInstr -> list AnnoInstr -> list Ev -> Prop :=
| vm_lstar_refl: forall r, vm_lstar r r [] [] []
| vm_lstar_tran: forall i l l' r r' r'' tr1 tr2,
    vm_step r i r' tr1 -> vm_lstar r' r'' l l' tr2 -> vm_lstar r r'' (i::l) l' (tr1 ++ tr2).
Hint Resolve vm_lstar_refl.

Lemma vm_lstar_trans : forall r r' r'' il il' il'' tr1 tr2,
  vm_lstar r r' il il' tr1 ->
  vm_lstar r' r'' il' il'' tr2 ->
  vm_lstar r r'' il il'' (tr1 ++ tr2).
Proof.
  intros.
  generalize dependent r''.
  generalize dependent il''.
  induction H; intros.
  - inv H0. econstructor.
    (*simpl.
    econstructor; eauto.*)
  - rewrite <- app_assoc.
    eapply vm_lstar_tran.
    apply H.
    eauto.
Defined.

Lemma ha : forall r r' r'' il1 il2 resl tr1 tr2,
  vm_lstar r r' (il1 ++ il2) il2 tr1 ->
  vm_lstar r' r'' il2 resl tr2 ->
  vm_lstar r r'' (il1 ++ il2) resl (tr1 ++ tr2).
Proof.
  intros.
  eapply vm_lstar_trans; eauto.
Defined.



Lemma vm_lstar_transitive:
  forall (*e s*) r r' r'' il1 il2 resl tr1 tr2,
    (*let r := (mk_accum e [] s) in*)
    vm_lstar r r' il1 [] tr1 ->
    vm_lstar r' r'' il2 resl tr2 -> 
    vm_lstar r r'' (il1 ++ il2) resl (tr1 ++ tr2).
Proof.
  intros.
  dependent induction H.
  - simpl. eauto.
  - simpl.
    rewrite <- app_assoc.
    econstructor. eassumption.
    eauto.
Defined.

Require Import Coq.Program.Equality.
Lemma vm_lstar_transitive_done:
  forall (*e s*) r r' r'' il1 il2 tr1 tr2,
    (*let r := (mk_accum e [] s) in*)
    vm_lstar r r' il1 [] tr1 ->
    vm_lstar r' r'' il2 [] tr2 -> 
    vm_lstar r r'' (il1 ++ il2) [] (tr1 ++ tr2).
Proof.
  intros.
  dependent induction H.
  - simpl. eauto.
  - simpl.
    rewrite <- app_assoc.
    econstructor. eassumption.
    eauto.
Defined.
    
Inductive vm_rlstar: vm_accum -> vm_accum -> list AnnoInstr -> list AnnoInstr -> list Ev -> Prop :=
| vm_rlstar_refl: forall r, vm_rlstar r r [] [] []
| vm_rlstar_tran: forall r r' r'' i il tr1 tr2,
    vm_rlstar r r' il [] tr1 -> vm_step r' i r'' tr2 ->
    vm_rlstar r r'' (il ++ [i]) [] (tr1 ++ tr2).
Hint Resolve vm_rlstar_refl.


Lemma vm_rlstar_transitive : forall r r' r'' il1 il2 resl tr1 tr2,
    vm_rlstar r r' il1 [] tr1 ->
    vm_rlstar r' r'' il2 resl tr2 -> 
    vm_rlstar r r'' (il1 ++ il2) resl (tr1 ++ tr2).
Proof.
  intros.
  dependent induction H0.
  - rewrite app_nil_r. rewrite app_nil_r. auto.
  - apply IHvm_rlstar in H. 
    rewrite app_assoc.
    rewrite app_assoc.
    eapply vm_rlstar_tran; eauto.
Defined.
  
Lemma vm_rlstar_lstar : forall r r' l resl tr,
    vm_rlstar r r' l resl tr -> vm_lstar r r' l resl tr.
Proof.
  intros.
  induction H; auto.
  - eapply vm_lstar_transitive. eauto.
    cut (vm_lstar r' r'' [i] [] (tr2 ++ [])). rewrite app_nil_r; eauto.
    econstructor; eauto.
Defined.

Lemma vm_lstar_rlstar : forall r r' l resl tr,
    vm_lstar r r' l resl tr -> vm_rlstar r r' l resl tr.
Proof.
  intros.
  dependent induction H.
  - econstructor.
  - cut (vm_rlstar r r'' ([i] ++ l) l' (tr1 ++ tr2)). simpl; auto.
    apply vm_rlstar_transitive with (r':=r').
    cut (vm_rlstar r r' ([] ++ [i]) [] ([] ++ tr1)). simpl; auto.
    econstructor; eauto.
    eauto.
Defined.

Lemma vm_rlstar_iff_lstar : forall r r' l resl tr,
    vm_lstar r r' l resl tr <-> vm_rlstar r r' l resl tr.
Proof.
  intros.
  split.
  - apply vm_lstar_rlstar.
  - apply vm_rlstar_lstar.
Defined.

Ltac inv_vm_lstar :=
  repeat (
      match goal with
      | [ H: vm_lstar _ _ _ _ _ |- _ ] => inv H; simpl
      | [ G: vm_step _ _ _ _ |- _ ] => inv G; simpl
      end).  

Lemma ffff_gen_helper' : forall r r' il1 il2 tr,
  vm_lstar r r' (il1 ++ il2) il2 tr ->
  vm_lstar r r' il1 [] tr.
Proof.
  intros.
  rewrite vm_rlstar_iff_lstar in H.
  dependent induction H.
  - assert (il1 = []). rewrite app_nil_r in x. auto.
    subst. auto.
  - rewrite app_nil_r in x.
    rewrite <- x.
    rewrite vm_rlstar_iff_lstar.
    eapply vm_rlstar_transitive. eassumption.
    cut (vm_rlstar r' r'' ([] ++ [i]) [] ([] ++ tr2)). simpl; auto.
    eapply vm_rlstar_tran; eauto.
Defined.

Lemma fafa : forall r r' tr i rest,
    vm_step r i r' tr ->
    vm_lstar r r' ([i] ++ rest) rest tr.
Proof.
  intros.
  cut (vm_lstar r r' ([i] ++ rest) rest (tr++[])). rewrite app_nil_r. auto.
  econstructor. eassumption.
  Admitted.

Lemma ffff_gen_helperrr : forall r r' il1 il1' il2 tr,
  (il1 <> []) ->
  vm_lstar r r' il1 il1' tr ->
  vm_lstar r r' (il1 ++ il2) (il1' ++ il2) tr.
Proof.
  intros.
  rewrite vm_rlstar_iff_lstar in H0.
  generalize dependent il2.
  (* generalize dependent H.*)
  inv H0; intros.
  - congruence.
  - rewrite <- app_assoc.
    eapply vm_lstar_transitive.
    rewrite <- vm_rlstar_iff_lstar in H1.
    eassumption.
    apply fafa. eassumption.
Defined.

Lemma ffff_gen_helper'' : forall r r' il1 il2 tr,
  (il1 <> []) ->
  vm_lstar r r' il1 [] tr ->
  vm_lstar r r' (il1 ++ il2) il2 tr.
Proof.
  intros.
  cut (vm_lstar r r' (il1 ++ il2) ([] ++ il2) tr). simpl; auto.
  eapply ffff_gen_helperrr; eauto.
Defined.

Lemma asdd {A:Type} : forall l (v:A) il1 il2,
    l ++ [v] = il1 ++ il2 ->
    (il2 = [] /\ l ++ [v] = il1) \/
    (*(il1 = [] /\ l ++ [v] = il2) \/*)
    (il2 = [v] /\ l = il1) \/
    (exists n, (il1 = firstn n l) /\ (il2 = (skipn n l) ++ [v])).
Proof.
Admitted.

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

Lemma step_implies_lstar : forall r r' i tr,
    vm_step r i r' tr ->
    vm_lstar r r' [i] [] tr.
Proof.
  intros.
  cut (vm_lstar r r' ([i]++[]) [] (tr ++ [])). simpl. rewrite app_nil_r. eauto.
  eapply vm_lstar_tran; eauto.
Defined.


Lemma first_skip{A:Type} :
  forall n (l:list A),
    l = (firstn n l) ++ (skipn n l).
Proof.
Admitted.

Lemma ffff_another_helper :forall r r3 tr il1 il2 resl,
    il1 <> [] ->
    vm_lstar r r3
             (il1 ++ il2) resl
             tr ->
    exists r' tr1,
      vm_lstar r r'
               (il1 ++ il2) il2
               tr1 /\
      exists tr2,
        vm_lstar r' r3
                 il2 resl
                 tr2 (*/\
                       tr = tr1 ++ tr2*).
Proof.
  intros.
  rewrite vm_rlstar_iff_lstar in H0.
  dependent induction H0.
  - apply list_nil_app in x. destruct x.
    subst.
    eexists. eexists.
    split.
    econstructor.
    eexists.
    econstructor.
  - apply asdd in x.
    destruct x.
    + destruct H2. subst.
      exists r''. exists (tr1 ++ tr2).
      rewrite vm_rlstar_iff_lstar.
      split.
      * rewrite app_nil_r.
        eapply vm_rlstar_tran.
        eassumption.
        eassumption.
      * eexists. econstructor.
    + destruct H2.
      * destruct H2.
        subst.
        exists r'. exists (tr1).
        split. 
        -- apply ffff_gen_helper''.
           eassumption.
           rewrite vm_rlstar_iff_lstar.
           eauto.
        (*
          Check vm_rlstar_transitive.
          (* vm_rlstar r r' il1 [] tr1 ->
       vm_rlstar r' r'' il2 resl tr2 -> vm_rlstar r r'' (il1 ++ il2) resl (tr1 ++ tr2) *)
          eapply vm_rlstar_transitive. eassumption.
          (*vm_rlstar r r'' (il1 ++ il2) resl (tr1 ++ tr2)*)
          
          cut (vm_rlstar r' r' ([] ++ [i]) [i] ([] ++ [])). auto.
          eapply vm_rlstar_transitive. econstructor.
          admit.*)
          (*
          cut (
          rewrite <- vm_rlstar_iff_lstar in H.
          eapply ffff_gen_helper''. eassumption.*)
        -- exists tr2.
           apply step_implies_lstar; eauto.

      * destruct H2.
        destruct H2.
        (*destruct (IHvm_rlstar il1 (skipn x il)).*)
        destruct (IHvm_rlstar (skipn x il) il1).
        -- assumption.
        -- rewrite H2.
           eapply first_skip.    
        -- destruct H4. destruct H4. destruct H5.
           apply ffff_gen_helper' in H4.
           exists x0. exists x1.
           split.
           ++ apply ffff_gen_helper''; eauto.
           ++ rewrite H3.
              exists (x2 ++ tr2).
              Check ffff_gen_helper'.
              rewrite vm_rlstar_iff_lstar.
              eapply vm_rlstar_transitive; eauto.
              rewrite vm_rlstar_iff_lstar in H5.
              eauto.
              rewrite <- vm_rlstar_iff_lstar.
              eapply step_implies_lstar; eauto.
Defined.

Lemma ffff_gen_helper :forall r r3 tr il1 il2,
    (il1 <> []) ->
  vm_lstar r r3
           (il1 ++ il2) []
           tr ->
  exists r' tr1,
    vm_lstar r r'
             (il1 ++ il2) il2
             tr1 /\
    exists tr2,
      vm_lstar r' r3
               il2 []
               tr2 (*/\
      tr = tr1 ++ tr2*).
Proof.
  intros.
  eapply ffff_another_helper; eauto.
Defined.

Lemma ffff_gen :forall r r3 tr il1 il2,
    il1 <> [] ->
    vm_lstar r r3
           (il1 ++ il2) []
           tr ->
  exists r' tr1,
    vm_lstar r r'
             il1 []
             tr1 /\
    exists tr2,
      vm_lstar r' r3
               il2 []
               tr2 (*/\
      tr = tr1 ++ tr2*).
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
Defined.

Lemma compile_not_empty :
  forall t,
    (instr_compiler t) <> [].
Proof.
Admitted.

Lemma ffff : forall r t tr r3 il2, (* TODO: il1 must be compiled for stack restore *)
    let il1 := (instr_compiler t) in
    vm_lstar r r3
             (il1 ++ il2) []
             tr ->
   exists r' tr1,
      vm_lstar r r'
               il1 []
               tr1 /\
     exists tr2,
      vm_lstar r' r3
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

Lemma lstar_stls :
  forall st0 st1 t tr,
    lstar st0 tr st1 -> lstar (ls st0 t) tr (ls st1 t).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Qed.

Lemma fasd : forall st st' tr p r,
    lstar st tr
          st' ->
    lstar (rem r p st) tr (rem r p st').
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.

Lemma update_ev_immut_stack : forall s e,
    vm_stack s = vm_stack (update_ev e s).
Proof.
  intros.
  simpl. reflexivity.
Defined.

Ltac doit :=
  unfold push_stackr in * ;
  unfold push_stackc in * ;
  unfold update_ev in * ;
  unfold pop_stackr in *;
  simpl in *.
    
Ltac invv :=
  repeat (
      match goal with
      | [ H: vm_lstar _ _ (_::_) _ _ |- _ ] => inv H; doit
      | [ G: vm_step _ _ _ _ |- _ ] => inv G; doit
      end).

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

Lemma vm_config_correct : forall e e' s s' t tr,
    vm_lstar (mk_accum e s) (mk_accum e' s')
             (instr_compiler t) []
             tr ->
    e' = (eval (unanno t) e) /\
    s = s'.
Proof.
  intros.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent tr.
  induction t; intros.
  - destruct a; inv_vm_lstar; (split; auto).
  - simpl.
    inv H. inv H4.
    inv H7.
    split; eauto.
  - simpl.
    simpl in H.
    apply ffff_gen in H.
    destruct_conjs.
    destruct H. 
    edestruct IHt2. eassumption.
    edestruct IHt1. eassumption.
    subst. split; reflexivity.
    apply compile_not_empty.
  - simpl in H. destruct s.
    invv.
    apply ffff_gen in H7.
    destruct_conjs.
    dependent destruction r''.
    dependent destruction H7.
    destruct IHt1 with (tr:=H) (s:=e2 :: s0) (s':=vm_stack0) (e:=splitEv s e) (e':=ec0).
    apply H0.                  
    invv.
    dependent destruction r'''.
    invv.
    apply ffff_gen in H12.
    destruct_conjs.
    dependent destruction H12.   
    destruct IHt2 with (tr:=H1) (s:=e0 :: s0) (s':=vm_stack0) (e:=splitEv s1 e) (e':=ec0).
    apply H2.
    invv.
    dependent destruction r''1.
    invv.
    inv H14.
    invv.
    split.
    eapply ssc_inv.
    eauto. eauto. reflexivity.
    apply compile_not_empty.
    apply compile_not_empty.
  - simpl in H. destruct s.
    invv.
    dependent destruction r''.
    inv H9.
    split; eauto.
    rewrite para_eval_vm.
    rewrite para_eval_vm.
    eauto.
Defined.

Lemma stack_restore_vm : forall e e' s s' t tr,
    vm_lstar (mk_accum e s) (mk_accum e' s')
             (instr_compiler t) [] tr ->
    s = s'.
Proof.
  intros.
  edestruct vm_config_correct; eauto.
Defined.

Lemma vm_ev_stack_deterministic : forall r r' r'' il il' tr tr',
  vm_lstar r r' il il' tr ->
  vm_lstar r r'' il il' tr' ->
  vm_stack r' = vm_stack r'' /\
  ec r' = ec r''.
Proof.
Admitted.

Lemma vm_lstar_trace: forall r r' t tr,
    (*well_formed t -> *)
    vm_lstar r r'
             (instr_compiler t) []
             tr ->
    trace t tr.
Proof.
Admitted.

Theorem vm_ordered : forall t e e' s tr ev0 ev1,
    well_formed t ->
    vm_lstar
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