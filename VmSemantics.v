Require Import More_lists Preamble Term Trace LTS Instr Event_system Term_system.

Require Import List.
Import ListNotations.

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
(*
Definition add_trace (el:list Ev) (x:vm_accum) : vm_accum :=
  let old_trace := vm_trace x in
  let new_trace := old_trace ++ el in
  mk_accum (ec x) (new_trace) (vm_stack x). *)

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

Definition parallel_att_vm_thread (li:list AnnoInstr) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_vm_events (li:list AnnoInstr) : list Ev.
Admitted.

Inductive vm_step: vm_accum -> AnnoInstr -> vm_accum -> (list Ev) -> Prop :=
| prim_step: forall r i a, vm_step r (aprimInstr i a) r (prim_trace i a)
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
    let er := (fst (pop_stackr r)) in
    let r' := (snd (pop_stackr r)) in
    let r'' := push_stackr e r' in
    vm_step r (abesr) r'' []
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
  induction H.
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
  induction H.
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
  induction H0.
  - 
    repeat rewrite app_nil_r. assumption.
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
  induction H.
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

    
  
(*
Theorem vm_bigstep: forall e e' s t tr p,
  well_formed t ->
  vm_lstar
    (mk_accum e [] s)
    (mk_accum e' tr s)
    (instr_compiler t)
    [] ->
  trace t tr /\ (et_fun p e' = typeof (unanno t) p (et_fun p e)).
Proof.
Admitted. *)

Ltac inv_vm_lstar :=
  repeat (
      match goal with
      | [ H: vm_lstar _ _ _ _ _ |- _ ] => inv H; simpl
      | [ G: vm_step _ _ _ _ |- _ ] => inv G; simpl
      end).
(*
Inductive wf_instr_seq : list AnnoInstr -> Prop :=
| compile_wf: forall t, wf_instr_seq (instr_compiler t)
(*| concat_wf: forall t1 t2, wf_instr_seq (instr_compiler t1 ++ instr_compiler t2)*)
| bseq_wf: forall j t,
   (* wf_instr_seq il1 ->
    wf_instr_seq il2 -> *)
    wf_instr_seq ([abesr] ++ (instr_compiler t) ++ [ajoins j])
| joins_wf: forall j,
    wf_instr_seq [ajoins j].
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

Lemma t_completes : forall r t, exists r',
      vm_lstar r r' (instr_compiler t) [].
Proof.
Admitted.
*)

 (*
 
Lemma eee : forall il1 il2 r1 r3,
  vm_lstar r1 r3
           (il1 ++ il2) [] ->
  exists r2,
    vm_lstar r1 r2
             (il1 ++ il2) il2.
Proof.
  intros.
  dependent induction H
  - eexists. assert (il1 = []). admit. assert (il2 = []). admit.
    subst. econstructor.
  -
  *)  
    
  

(*
Lemma ffff : forall e e'' s'' s t tr0 tr3 il2, (* TODO: il1 must be compiled for stack restore *)
    wf_instr_seq il2 -> 
    let il1 := (instr_compiler t) in
    let r := (mk_accum e tr0 s) in
    let r3 := (mk_accum e'' tr3 s'') in
    vm_lstar r r3
             (il1 ++ il2) [] ->
   exists e' tr1 s',
      let r' := (mk_accum e' tr1 s') in
      vm_lstar r r'
               il1 [] /\
     exists tr2,
      let r'' := (mk_accum e'' tr2 s'') in
      vm_lstar (mk_accum e' [] s') r''
               il2 [] /\
     skipn (length tr0) tr3 = tr1 ++ tr2.
Proof.
  (*
  intros.
  generalize dependent e.
  generalize dependent e''.
  generalize dependent s.
  generalize dependent s''.
  generalize dependent tr0.
  generalize dependent tr3.
  (*generalize dependent il1.
  generalize dependent t. *)
  dependent induction H; intros.
  - edestruct t_completes 
  eexists. eexists. eexists.
  destruct t_completes with (r:={| ec := e; vm_trace := tr0; vm_stack := s |}) (t:=t).
  split.
  destruct x.
  apply H.
  - destruct a.
    + inv H0. inv H5. simpl in H6.
      exists e. exists (tr0 ++ [Term.copy (fst r)]). exists s.
      (*assert (il1 = il1 ++ []). trivial. rewrite H0.*)
      split.
      * eapply vm_lstar_tran.
        econstructor.
        econstructor.
      * exists (skipn (S (length tr0)) tr3).
        split.
        --
          inv H6. inv H. admit.
          econstructor.
        
        eapply vm_lstar_tran.



      inv H5. simpl in H6.
      eexists. eexists. eexists.
      split.
      * econstructor. econstructor. econstructor.
      * eexists.
        split.
        -- simpl. inv H6. simpl. econstructor.
        
  - edestruct IHt; eauto.
  - edestruct IHt2; eauto.
  - edestruct IHt2; eauto.
  - edestruct IHt2; eauto.
    
    
    
  - destruct a.
    inv H.
    * repeat eexists.
      econstructor. econstructor. econstructor.
      inv H0. inv H4. inv H5
    + eexists. eexists. eexists. eexists. simpl in il1.
      econstructor. econstructor. econstructor.
      eexists. eexists.
      inv H.
      *  *)
  
  (*
  intros.
  induction H.
  admit.
  admit.
  admit.
  inv H0.*)
Admitted. *)
(*
  - 
  simpl.
  eexists. eexists. eexists.
  split.
  + inv H.
    admit. admit. admit. admit.
  + inv H.
    eexists. admit.
    eexists. admit.
    eexists. admit.
    eexists. admit.
  - inv H.
    eexists. eexists. eexists.
    split.
    + admit.
    + admit.
    + eexists. eexists. eexists.
      split.
      admit.
      eexists. admit.
    + eexists. eexists. eexists.
      split.
      admit.
      eexists. admit.
    + eexists. eexists. eexists.
      split.
      admit.
      eexists.
      admit.

(*
    assert ((instr_compiler t1) = []).
    admit.
    rewrite H.
    eapply vm_lstar_refl.
  + eexists.
    assert ((instr_compiler t2) = []).
    admit.
    rewrite H.
    eapply vm_lstar_refl.
  - subst.

    eexists. eexists. eexists.
    split.
    + edestruct IHvm_lstar.
    
    

    apply vm_lstar_transitive in H.
Admitted. *) *)

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

Lemma ssss : forall e tr s r,
    vm_lstar r {| ec := e; vm_stack := s |} [] [] tr ->
    vm_stack r = s.
Proof.
  intros.
  inv H.
  simpl. reflexivity.
Defined.

(*
Lemma vm_config_correct : forall e s t tr,
    vm_lstar (mk_accum e s) (mk_accum (eval (unanno t) e) s)
             (instr_compiler t) [] tr.
Proof.
  intros.
  generalize dependent e.
  generalize dependent s.
  generalize dependent tr. 

  
Admitted. *)

Lemma vm_config_correct : forall e e' s s' t tr,
    vm_lstar (mk_accum e s) (mk_accum e' s')
             (instr_compiler t) []
             tr ->
    e' = (eval (unanno t) e) /\
    s = s'.
Proof.
Admitted.


Lemma vm_ev_stack_deterministic : forall r r' r'' il il' tr tr',
  vm_lstar r r' il il' tr ->
  vm_lstar r r'' il il' tr' ->
  vm_stack r' = vm_stack r'' /\
  ec r' = ec r''.
Proof.
Admitted.
  
Lemma stack_restore_vm : forall e e' s s' t tr,
    vm_lstar (mk_accum e s) (mk_accum e' s')
             (instr_compiler t) [] tr ->
    s = s'.
Proof.
  intros.
  edestruct vm_config_correct; eauto.
Defined.

(*
Lemma vm_trace_correct : forall r r' tr t,
    vm_lstar r r' 
             (instr_compiler t) []
             tr ->
  trace t tr.
Admitted. *)

Lemma vm_lstar_trace: forall r r' t tr,
    well_formed t ->
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



(* Abandoned vm_smallstep proof: 

Theorem vm_smallstep: forall e e' s t tr n et,
  (*well_formed t ->*)
  vm_lstar
    (mk_accum e s) (mk_accum e' s)
    (instr_compiler t) [] tr ->
  lstar (conf t n et) tr (stop n (aeval t n et)).
  (*/\ (et_fun p e' = typeof (unanno t) p (et_fun p e)).*)
Proof.
  intros.
  (*generalize dependent p.*)
  generalize dependent tr.
  generalize dependent et.
  generalize dependent n.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent s.
  
  induction t; intros.
  - destruct a; try (simpl; inv_vm_lstar; repeat econstructor).
  - inv_vm_lstar.
    eapply lstar_tran.
    econstructor.
    eapply lstar_transitive.
    eapply lstar_transitive.
    apply fasd.
    eapply IHt.
    admit. (* TODO: make this an axiom? *)

    eapply lstar_tran.
    apply stattstop.
    econstructor.
    econstructor.
  - simpl in H.

    apply ffff with (il2:=instr_compiler t2) in H. 
    destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H0.
    (*destruct H0.*)

    eapply lstar_silent_tran. econstructor. simpl in H1.
    rewrite H1.
    eapply lstar_transitive. eapply lstar_stls.
    

    eapply IHt1. assert (s = x1).
    eapply stack_restore_vm. apply H.
    subst.
    eassumption.
    
    eapply lstar_silent_tran.
    apply stlseqstop.
    eapply IHt2. assert (x1 = s).
    eapply stack_restore_vm. eassumption.
    subst.
    apply H0.
    econstructor.
  - simpl in H. destruct s.
    inv H. inv H4.
    

    apply ffff with (*(il1:=instr_compiler t1)*) (il2:=abesr :: instr_compiler t2 ++ [ajoins (Nat.pred (snd r))]) in H5.
    destruct H5. destruct H. destruct H. destruct H. destruct H0. destruct H0.

    (*
    assert (
        (abesr :: instr_compiler t2 ++ [ajoins (Nat.pred (snd r))])
        = ([abesr] ++ instr_compiler t2 ++ [ajoins (Nat.pred (snd r))])).
    trivial.
    rewrite H2 in H0. *)
    inv H0. inv H6.

    apply ffff with (*(il1:=[abesr])*) (il2:=[ajoins (Nat.pred (snd r))]) in H7. destruct H7. destruct H0. destruct H0. destruct H0. destruct H2. destruct H2.
    inv H2. inv H8.
    eapply lstar_silent_tran. econstructor.

    inv H0.
    destruct H2. destruct H0.
    apply ffff with (il1:=instr_compiler t2) (il2:=[ajoins (Nat.pred (snd r))]) in H0.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H3. destruct H3.
    inv H3.

    inv H11. inv H7.
    simpl in *.
    eapply lstar_transitive.
    econstructor. econstructor. econstructor.

    
    admit.
    inv H4. admit.

    inv_vm_lstar.

    eapply lstar_silent_tran.
    econstructor.



    eapply lstar_stls.
    
    
    






























    
  - simpl.
    inv_vm_lstar.
    econstructor.
    econstructor.
    eapply lstar_transitive.
    + 
      (*remember (remote_events t) as HH. *)
      assert ((remote_events t) = (remote_events t) ++ []).
      admit.
      rewrite H.
      eapply lstar_transitive with (st1:=(rem (snd r) p (stop n (aeval t n (et_fun n e))))).
      specialize IHt with (tr:=remote_events t).
     assert (lstar (conf t n (et_fun n e)) (remote_events t)
                   (stop n (aeval t n (et_fun n e)))).
     {
       apply IHt.
       admit. (* TODO: Axiom?? *)
     }

     Lemma rem_congr : forall t n e p (r:(nat*nat)),
         lstar (conf t n (et_fun n e)) (remote_events t)
         (stop n (aeval t n (et_fun n e))) ->
  lstar (rem (snd r) p (conf t n (et_fun p e))) (remote_events t)
        (rem (snd r) p (stop n (aeval t n (et_fun n e)))).
    Admitted.

     apply rem_congr.
     eauto.
     econstructor.
    + eapply lstar_tran.
      eapply stattstop.
      apply lstar_refl.
      
    
     
       
    destruct HH.
    * econstructor.
    * simpl.
      econstructor
      

      simpl.
      eapply lstar_transitive.
      econstructor.
    *
      
    eapply stattstop.
    econstructor.
    econstructor.
    destruct (remote_events t).
    + 
    eapply lstar_tran.
    remember (et_fun p e).
    remember (unanno t).
    subst.
    remember (range t).
    eapply statt.
    econstructor.
    simpl.
      
    
Admitted.
*)





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

      (*
Lemma fasd :
  lstar st (tr1 ++ tr2)
  lstar (rem (snd r) p (conf t n (et_fun p e)))
    (remote_events t ++ [rpy rpyi n]) (stop p (aeval t n (et_fun p e)))*)
*)