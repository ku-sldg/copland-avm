Require Import Term.
(*Require Import MonadCOP.*)
Require Import Event_system.
Require Import Term_system.
Require Import Trace.
Require Import LTS.
Require Import Main.
Require Import More_lists.
Require Import Preamble.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.


(** * VM Instructions *)

Inductive Prim_Instr: Set :=
| copy: Prim_Instr
| kmeas: ASP_ID -> Plc -> (list Arg) -> Prim_Instr
| umeas: ASP_ID -> (list Arg) -> Prim_Instr
| sign: Prim_Instr
| hash: Prim_Instr.

Inductive Instr: Set :=
| primInstr: Prim_Instr -> Instr
| split: SP -> SP -> Instr
| joins: Instr
| joinp: Instr
| reqrpy: Plc -> Term -> Instr
| besr : Instr
| bep: (list Instr) -> (list Instr) -> Instr.

Inductive AnnoInstr: Set :=
| aprimInstr: nat -> Prim_Instr -> AnnoInstr
| asplit: nat -> SP -> SP -> AnnoInstr
| ajoins: nat -> AnnoInstr
| ajoinp: nat -> AnnoInstr
| abesr : AnnoInstr
| areqrpy: Range -> Plc -> AnnoTerm -> AnnoInstr
| abep: Range -> Range -> (list AnnoInstr) -> (list AnnoInstr) -> AnnoInstr.


(* 
Definition invokeKIM (i:ASP_ID) (q:Plc) (args:list Arg) : BS.
Admitted.

Definition invokeUSM (i:ASP_ID) (args:list Arg) : BS.
Admitted.

Definition signEv (e:EvidenceC) : BS.
Admitted.

Definition hashEv (e:EvidenceC) : BS.
Admitted.

Definition toRemote (t:Term) (pTo:Plc) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_att_vm_thread (li:list Instr) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_eval_thread (t:Term) (p:Plc) (e:EvidenceC) : EvidenceC.
Admitted.
*)

(*
Inductive Effect: Set :=
| copye: nat -> EvidenceC -> Effect
| kmease: nat -> ASP_ID -> Plc -> (list Arg) -> Effect
| umease: nat -> ASP_ID -> (list Arg) -> Effect
| signe: nat -> EvidenceC -> Effect
| hashe: nat -> EvidenceC -> Effect
| reqe: nat -> Plc -> Term -> Effect
| rpye: nat -> Plc -> Evidence -> Effect
| splite: nat -> SP -> SP -> EvidenceC -> Effect
| vm_threade: nat -> (nat*nat) -> (list Instr) -> EvidenceC -> Effect
| joine: nat -> EvidenceC -> EvidenceC -> Effect.

Definition EffectTrace := (list Effect).
Definition EffSys := EvSys Effect.

Fixpoint eff_Sys (t:AnnoTerm) (p:Plc) (e:Evidence) : EffSys.

Definition eve x :=
  match x with
  | copye i _  => i
  | kmease i _ _ _ => i
  | umease i _ _ => i
  | signe i _ => i
  | hashe i _ => i
  | reqe i _ _ => i
  | rpye i _ _ => i
  | splite i _ _ _ => i
  | vm_threade i _ _ _ => i
  | joine i _ _ => i
  end.

Check es_size.
Print well_structured.
Print well_structured_range.

Check (ev (copye *)

(*
Theorem ordered_effects:
  forall t p effs e effs ev0 ev1,
    well_formed t ->
    well_formed_sys t p effs ev_sys ->
    (*lstar (conf t p e) tr (stop p (aeval t p e)) ->*)
    (att_vm (instr_compiler t p) p e) effs (aeval t p e) ->
    prec (ev_sys t p e) ev0 ev1 ->
    earlier effs effs(ev ev0) effs(ev ev1). *)

(*
Scheme mutual_ind_A := Induction for Instr Sort Prop
  with mutual_ind_B := Induction for nat Sort Prop. *)
(*
Fixpoint eq_ev_dec :
  forall x y: Instr, {x = y} + {x <> y}
  with asdfdsa :   forall x y: (list Instr), {x = y} + {x <> y}.*)
Require Import Coq.Program.Equality.


Theorem eq_ev_dec :   forall x y: Instr, {x = y} + {x <> y}.
Proof.
Admitted.
(*
  intros.
  generalize dependent y.
  dependent induction x;
    intros; destruct y; try (left; reflexivity); try (right; congruence).
  SearchAbout "eq_dec".
  -
  destruct (PeanoNat.Nat.eq_dec n n1);
    destruct (PeanoNat.Nat.eq_dec n0 n2);
    destruct (eq_ln_dec l l0); try (left; congruence); try (right; congruence).
  - 
  destruct (PeanoNat.Nat.eq_dec n n0);
    destruct (eq_ln_dec l l0); try (left; congruence); try (right; congruence).
  - destruct (PeanoNat.Nat.eq_dec n n1);
    destruct (PeanoNat.Nat.eq_dec n0 n2);
    destruct (eq_term_dec t t0); try (left; congruence); try (right; congruence).
    - destruct (eq_sp_dec s s1);
    destruct (eq_sp_dec s0 s2);
    try (left; congruence); try (right; congruence).
    -
Admitted.*)
Hint Resolve eq_ev_dec.

Definition eq_li_dec:
  forall x y: (list Instr), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.
Hint Resolve eq_li_dec.


(** * Instruction Compiler *)
Definition asp_instr (a:ASP) : Prim_Instr :=
  match a with
  | CPY => copy
  | KIM i p args => kmeas i p args
  | USM i args => umeas i args
  | SIG => sign
  | HSH => hash
  end.

Check anno.

Fixpoint instr_compiler (t:AnnoTerm) : (list AnnoInstr) :=
  match t with
  | aasp r a => [aprimInstr (fst r) (asp_instr a)]

    
  | aatt r q t' => [areqrpy r q t']

               
  | alseq _ t1 t2 =>
    let tr1 := instr_compiler t1 in
    let tr2 := instr_compiler t2 in
    tr1 ++ tr2
      
  | abseq r (sp1,sp2) t1 t2 =>
    let tr1 := instr_compiler t1 in
    let tr2 := instr_compiler t2 in
    let i := Nat.pred (snd r) in
    [asplit (fst r) sp1 sp2] ++ tr1 ++ [abesr] ++ tr2 ++ [ajoins i]
                             
  | abpar r (sp1,sp2) t1 t2 =>
    (*let splEv := [split sp1 sp2] in*)
    let tr1 := instr_compiler t1 in
    let tr2 := instr_compiler t2 in
    let tr := [abep (range t1) (range t2) tr1 tr2] in
    let i := Nat.pred (snd r) in
    [asplit (fst r) sp1 sp2] ++ tr ++ [ajoinp i] 
  end.

Definition termx := (bpar (ALL,ALL) (asp CPY) (asp SIG)).
Definition termy := bpar (NONE,NONE) termx termx.

Compute (instr_compiler (annotated termy)).

(** * Place-holder axioms for IO operations *)
Definition invokeKIM (i:ASP_ID) (q:Plc) (args:list Arg) : BS.
Admitted.

Definition invokeUSM (i:ASP_ID) (args:list Arg) : BS.
Admitted.

Definition signEv (e:EvidenceC) : BS.
Admitted.

Definition hashEv (e:EvidenceC) : BS.
Admitted.

Definition toRemote (t:Term) (pTo:Plc) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_att_vm_thread (li:list AnnoInstr) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_eval_thread (t:Term) (p:Plc) (e:EvidenceC) : EvidenceC.
Admitted.


(** * Eval function definition *)
Definition splitEv (sp:SP) (e:EvidenceC) : EvidenceC :=
  match sp with
  | ALL => e
  | NONE => mtc
  end.

Definition eval_asp (a:ASP) (p:Plc) (e:EvidenceC) : EvidenceC :=
  match a with
  | CPY => e
  | KIM i q args =>
    let bs := invokeKIM i q args in
    (kkc i args q bs e)
  | USM i args =>
    let bs := invokeUSM i args in
    (uuc i args bs e)
  | SIG =>
    let bs := signEv e in
    (ggc e bs)
  | HSH =>
    let bs := hashEv e in
    (hhc bs e)
  end.

Fixpoint eval (t:Term) (p:Plc) (e:EvidenceC) : EvidenceC :=
  match t with
  | asp a => eval_asp a p e
  | att q t1 => toRemote t1 q e
  | lseq t1 t2 =>
    let e1 := eval t1 p e in
    eval t2 p e1
  | bseq (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := eval t1 p e1 in
    let e2' := eval t2 p e2 in
    (ssc e1' e2')
  | bpar (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := parallel_eval_thread t1 p e1 in
    let e2' := parallel_eval_thread t2 p e2 in
    (ppc e1' e2')
  end.

Axiom toRemType : forall p n e et t,
    ET p e et -> 
    ET p (toRemote t n e) (typeof t n et).

Axiom splitType : forall p e et s0,
  ET p e et ->
  ET p (splitEv s0 e) (sp s0 et).

Axiom par_eval_thread : forall t p e,
    parallel_eval_thread t p e = eval t p e.

Theorem eval_typeof : forall p e et t,
  ET p e et ->
  ET p (eval t p e) (typeof t p et).
Proof.
  intros.
  generalize dependent p.
  generalize dependent e.
  generalize dependent et.
  induction t; intros; try (simpl;auto;reflexivity).
  - destruct a; try simpl; eauto.
  - simpl. apply toRemType; auto.
  - simpl. remember s. destruct s0.
    econstructor.
    + apply IHt1. simpl.
      apply splitType. auto.
    + apply IHt2. simpl. apply splitType. auto.
  - simpl. remember s. destruct s0.
    econstructor; rewrite par_eval_thread.
    + apply IHt1. simpl.
      apply splitType. auto.
    + apply IHt2. simpl. apply splitType. auto.
Defined.

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

(** * Evidence Stack *)
Definition ev_stack := list Evidence.
Definition empty_stack : ev_stack := [].

Definition push_stack (e:Evidence) (s:ev_stack) : ev_stack :=
  (e :: s).

Definition pop_stack (s:ev_stack) : (Evidence*ev_stack) :=
  match s with
  | e :: s' => (e,s')
  | _ => (mt,empty_stack) (* TODO: will this be expressive enough? *)
  end.

Record vm_accum : Type := mk_accum
                            { ec:EvidenceC ;
                              vm_trace:(list Ev) ;
                              vm_stack:ev_stackc }.

Definition add_trace (el:list Ev) (x:vm_accum) : vm_accum :=
  let old_trace := vm_trace x in
  let new_trace := old_trace ++ el in
  mk_accum (ec x) (new_trace) (vm_stack x).

Definition update_ev (e:EvidenceC) (x:vm_accum) : vm_accum :=
  mk_accum e (vm_trace x) (vm_stack x).

Definition push_stackr (e:EvidenceC) (x:vm_accum) : vm_accum :=
  mk_accum (ec x) (vm_trace x) (push_stackc e (vm_stack x)).

Definition pop_stackr (x:vm_accum) : (EvidenceC*vm_accum) :=
  let (er,s') := pop_stackc (vm_stack x) in
  (er,mk_accum (ec x) (vm_trace x) (s')).

Definition prim_trace (i:nat) (a:Prim_Instr) : (list Ev) :=
  match a with
  | copy => [Term.copy i]
  | kmeas asp_id q A => [Term.kmeas i asp_id q A]
  | umeas asp_id A => [Term.umeas i asp_id A]
  | sign => [Term.sign i]
  | hash => [Term.hash i]
  end.
(*
    | reqrpy _ pTo t =>
      (toRemote t pTo e,s) *)

Definition remote_events (t:AnnoTerm) : (list Ev).
Admitted.

Inductive vm_step: vm_accum -> AnnoInstr -> vm_accum -> Prop :=
| prim_step: forall r i a, vm_step r (aprimInstr i a) (add_trace (prim_trace i a) r)
| split_step: forall r i sp1 sp2,
    let e1 := splitEv sp1 (ec r) in
    let e2 := splitEv sp2 (ec r) in
    let r' := update_ev e1 r in
    let r'' := push_stackr e2 r' in
    let r''' := add_trace [Term.split i] r'' in
    vm_step r (asplit i sp1 sp2) r'''
| joins_step: forall r i,
    (*let (er,r') := pop_stackr r in *)
    let e := (ec r) in
    let er := (fst (pop_stackr r)) in
    let r' := (snd (pop_stackr r)) in
    let r'' := update_ev (ssc er e) r' in
    let r''' := add_trace [Term.join i] r'' in
    vm_step r (ajoins i) r'''
| joinp_step: forall r i,
    (*let (er,r') := pop_stackr r in *)
    let e := (ec r) in
    let er := (fst (pop_stackr r)) in
    let r' := (snd (pop_stackr r)) in
    let r'' := update_ev (ppc e er) r' in
    let r''' := add_trace [Term.join i] r'' in
    vm_step r (ajoinp i) r'''
| besr_step: forall r,
    let e := (ec r) in
    let er := (fst (pop_stackr r)) in
    let r' := (snd (pop_stackr r)) in
    let r'' := push_stackr e r' in
    vm_step r (abesr) r''
| reqrpy_step: forall r rg q annt,
    let e := (ec r) in
    let r' := update_ev (toRemote (unanno annt) q e) r in
    let reqi := (fst rg) in
    let rpyi := Nat.pred (snd rg) in
    let newTrace :=
        [req reqi q (unanno annt)] ++ (remote_events annt) ++ [rpy rpyi q] in     
    let r'' := add_trace newTrace r' in
    vm_step r (areqrpy rg q annt) r''

 (* | bep evs1 evs2 =>
      let (er,s') := pop_stack s in
      let res1 := parallel_att_vm_thread evs1 e in
      let res2 := parallel_att_vm_thread evs2 er in
      (res1, push_stack res2 s')  (* TODO: ret some kind of "wait handle" evidence instead? *) *)
| bep_step: forall r rg1 rg2 il1 il2,
    let e := (ec r) in
    let er := (fst (pop_stackr r)) in
    let r' := (snd (pop_stackr r)) in
    let res1 := parallel_att_vm_thread il1 e in
    let res2 := parallel_att_vm_thread il2 er in
    let r'' := update_ev res1 r' in
    let r''' := push_stackr res2 r'' in
    vm_step r (abep rg1 rg2 il1 il2) r'''.
    
Definition vm_prim (ep:vm_accum) (instr:AnnoInstr) : vm_accum :=
  let e := ec ep in
  let s := vm_stack ep in
  let tr := vm_trace ep in
  match instr with
  (*| aprimInstr r a => 


    (*
    | copy => let new_tr := tr ++ [copy ] in
             mk_accum e new_tr s *)

       (*               
    | kmeas i q args =>
      let bs := invokeKIM i q args in
      ((kkc i args q bs e),s)
        
    | umeas i args =>
      let bs := invokeUSM i args in
      ((uuc i args bs e),s)
    | sign =>
      let bs := signEv e in
      ((ggc e bs),s)
    | hash =>
      let bs := hashEv e in
      ((hhc bs e),s)
    | reqrpy _ pTo t =>
      (toRemote t pTo e,s)
    | split sp1 sp2 =>
      let e1 := splitEv sp1 e in
      let e2 := splitEv sp2 e in
      (e1, push_stack e2 s) (*(sp e1 e2)*)
    | besr =>
      let (er,s') := pop_stack s in
      let s'' := push_stack e s' in
      (er,s'')             
    | joins =>
      let (er,s') := pop_stack s in
      (ssc er e,s')              
    | joinp =>
      let (er,s') := pop_stack s in
      (ppc e er,s') (* TODO: invoke "wait on evidence" commands here? *)
    | bep evs1 evs2 =>
      let (er,s') := pop_stack s in
      let res1 := parallel_att_vm_thread evs1 e in
      let res2 := parallel_att_vm_thread evs2 er in
      (res1, push_stack res2 s')  (* TODO: ret some kind of "wait handle" evidence instead? *)
*)
 *)
    | _ => mk_accum mtc [] []
  end.

Lemma vm_step_iff_vm_prim : forall r i r',
    vm_step r i r' <-> vm_prim r i = r'.
Admitted.


Inductive vm_lstar: vm_accum -> vm_accum -> list AnnoInstr -> list AnnoInstr -> Prop :=
| vm_lstar_refl: forall r, vm_lstar r r [] []
| vm_lstar_tran: forall i l r r' r'',
    vm_step r i r' -> vm_lstar r' r'' l [] -> vm_lstar r r'' (i::l) [].

Check annotated. Check vm_trace. Check typeof.

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
      | [ H: vm_lstar _ _ _ _ |- _ ] => inv H; simpl
      | [ G: vm_step _ _ _ |- _ ] => inv G; simpl
      end).

Lemma ffff : forall e e'' s'' s tr0 tr3 il1 il2, (* TODO: il1 must be compiled for stack restore *)
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
               il2 []  /\
     skipn (length tr0) tr3 = tr1 ++ tr2.
Proof.
Admitted.

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
Admitted.

Lemma ssss : forall e tr s r,
    vm_lstar r {| ec := e; vm_trace := tr; vm_stack := s |} [] [] ->
    vm_stack r = s.
Proof.
Admitted.

Lemma stack_restore_vm : forall e e' l l' s s' t,
    vm_lstar (mk_accum e l s) (mk_accum e' l' s')
             (instr_compiler t) [] ->
    s = s'.
Proof.


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
    apply ffff in H.
    destruct H. destruct H. destruct H. destruct H. destruct H0.
    destruct H0. 
    assert (s = x1). eapply IHt1; eauto.
    assert (x1 = s'). eapply IHt2; eauto. congruence.

  -
    simpl in H.
    destruct s.
    inv H.
    inv H4.
    apply ffff in H5.
    destruct H5. destruct H. destruct H. destruct H. destruct H0. destruct H0.
    assert (vm_stack r'' = x1). eapply IHt1; eauto.
    assert (
        (abesr :: instr_compiler t2 ++ [ajoins (Nat.pred (snd r))])
        = ([abesr] ++ instr_compiler t2 ++ [ajoins (Nat.pred (snd r))])).
    admit.
    rewrite H3 in H0.
    apply ffff in H0.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H4. destruct H4.
    inv H0.
    apply ffff in H4. destruct H4. destruct H0. destruct H0. destruct H0. destruct H2. destruct H2.
    assert (x5 = x8). eapply IHt2; eauto. inv H10. inv H2. inv H10.
    subst.
    assert (vm_stack r'' = push_stackc e2 s0).
    assert (vm_stack r'0 = vm_stack {| ec := e; vm_trace := l; vm_stack := s0 |}).
    apply update_ev_immut_stack. unfold vm_stack at 2 in H2.
    rewrite <- H2.
    reflexivity.
    rewrite H2 in *.
    assert (vm_stack r'''0 = s').


    eapply ssss; eauto.
    
    subst.
    assert (vm_stack r''0 = x8).
    eapply ssss; eauto.
    subst. clear H11. clear H0. clear H.
    clear H12.
    assert (r'4 = r'5). eauto.
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
    



    apply update_ev_immut_stack.

  -
    
    
    




    
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







  











  


      (*
Lemma fasd :
  lstar st (tr1 ++ tr2)
  lstar (rem (snd r) p (conf t n (et_fun p e)))
    (remote_events t ++ [rpy rpyi n]) (stop p (aeval t n (et_fun p e)))*)
      
Theorem vm_smallstep: forall e e' s t tr n et,
  (*well_formed t ->*)
  vm_lstar
    (mk_accum e [] s)
    (mk_accum e' tr s)
    (instr_compiler t)
    [] ->
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




    apply fasd.
    eapply IHt.
    admit. (* TODO: make this an axiom? *)

    eapply lstar_tran.
    apply stattstop.
    econstructor.
  - simpl in H.



    apply ffff in H.
    destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H0.
    destruct H0.

    eapply lstar_silent_tran. econstructor.
    rewrite H1.
    eapply lstar_transitive. eapply lstar_stls.
    

    eapply IHt1. assert (s = x1).



    eapply stack_restore_vm. apply H.

    
    subst.
    eassumption.

    



    eapply lstar_silent_tran.
    apply stlseqstop.
    eapply IHt2. assert (x1 = x3).
    eapply stack_restore_vm. eassumption.
    subst.
    apply H0.
  -
    
    
    
    subst.
    
    apply H.

    edestruct ffff in H.
    inv H. 
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

Theorem vm_ordered : forall t e e' s tr ev0 ev1,
    well_formed t ->
    vm_lstar
    (mk_accum e [] s)
    (mk_accum e' tr s)
    (instr_compiler t)
    [] ->
    prec (ev_sys t) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  edestruct vm_smallstep with (p:=0); eauto.
  eapply ordered; eauto.
Qed.


(** * Primitive VM Operations *)

Definition exec_asp (n:nat) (p:Plc) (e:EvidenceC) (a:ASP) : (EvidenceC*Ev) :=
  match a with
  | CPY => (e,Term.copy n p (typeof (asp CPY) p e))
  | _ => (mtc,Term.copy n p (typeof e))
  end.
    
  | kmeas: ASP_ID -> Plc -> (list Arg) -> Prim_Instr
  | umeas: ASP_ID -> (list Arg) -> Prim_Instr
  | sign: Prim_Instr
  | hash: Prim_Instr
  | split: SP -> SP -> Prim_Instr
  | joins: Prim_Instr
  | joinp: Prim_Instr.




(** * Attestation VM run function *)
Definition att_vm' (is:list Instr) (p:Plc) (ep:EvidenceC*ev_stack) : (EvidenceC*ev_stack) :=
  fold_left (vm_prim p) is ep.

Definition att_vm (is:list Instr) (p:Plc) (e:EvidenceC) : (EvidenceC) :=
  fst (att_vm' is p (e,[])).

(** * Reasonable axioms for remote/parallel components *)
Axiom remote_vm : forall t n e,
    toRemote t n e = att_vm (instr_compiler t n) n e.

Axiom par_vm_thread : forall t p e,
  parallel_att_vm_thread (instr_compiler t p) e = att_vm (instr_compiler t p) p e.




(** * Lemmas *)
Lemma att_vm'_distributes : forall is1 is2 p ep,
    (att_vm' (is1 ++ is2) p ep) =
    (att_vm' is2 p
             (att_vm' is1 p ep)).
Proof.
  intros.
  unfold att_vm'.
  apply fold_left_app.
Defined.

Lemma fst_inv{A B:Type} : forall (p:A*B) (p':A*B), p = p' -> fst p = fst p'.
Proof.
  intros.
  congruence.
Defined.

Lemma snd_inv{A B:Type} : forall (p:A*B) (p':A*B), p = p' -> snd p = snd p'.
Proof.
  intros.
  congruence.
Defined.

Lemma ssc_inv : forall e1 e1' e2 e2', e1 = e1' -> e2 = e2' -> ssc e1 e2 = ssc e1' e2'.
Proof.
  congruence.
Defined.

Lemma stack_restore' : forall e0 e1 t p s e,
    ((e0, e1) = att_vm' (instr_compiler t p) p (e, s)) ->
    e1 = s.
Proof.
  intros.
  generalize dependent p.
  generalize dependent s.
  generalize dependent e0.
  generalize dependent e1.
  generalize dependent e.
  
  induction t; intros.
  - destruct a; try (cbv in H; congruence).
  - simpl in H.
    
    rewrite remote_vm in H. unfold att_vm in H.
    congruence.
  - simpl in H.
    unfold att_vm' in H.
    rewrite fold_left_app in H.

    remember (att_vm' (instr_compiler t1 p) p (e, s)).
    destruct p0.
    assert (e3 = s). apply IHt1 with (p:=p) (e:=e) (e0:=e2).
    apply Heqp0.

    rewrite <- H0.
        
    remember (att_vm' (instr_compiler t2 p) p (e2, e3)).
    destruct p0.

    unfold att_vm' in Heqp0. 

    rewrite <- Heqp0 in H.

    unfold att_vm' in Heqp1.

    rewrite <- Heqp1 in H.

    apply IHt2 with (e:=e2) (e0:=e4) (p:=p).
    assert (e1 = e5). congruence. subst.
    assumption.
  -
    simpl in H.
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
Defined.

Lemma stack_restore : forall s t p e,
    snd (att_vm' (instr_compiler t p) p (e, s)) = s.
Proof.
  intros.
  remember ((att_vm' (instr_compiler t p) p (e, s))).
  destruct p0.
  simpl. eapply stack_restore'. eassumption.
Defined.

Lemma nil_stack_restore : forall t p e,
    snd (att_vm' (instr_compiler t p) p (e,[])) = [].
Proof.
  intros.
  apply stack_restore.
Defined.

Lemma stack_irrel : forall e p t e2 e2', (* starting stack irrelevant *)
    fst (fold_left (vm_prim p) (instr_compiler t p) (e,e2)) =
    fst (fold_left (vm_prim p) (instr_compiler t p) (e,e2')).
Proof.
  intros.
  generalize dependent p.
  generalize dependent e.
  generalize dependent e2.
  generalize dependent e2'.
  induction t; intros; try reflexivity.
  - destruct a; try reflexivity.
  - simpl.
    rewrite fold_left_app.
    rewrite fold_left_app.
    remember ((fold_left (vm_prim p) (instr_compiler t1 p) (e, e2))).
    destruct p0.
    remember ((fold_left (vm_prim p) (instr_compiler t1 p) (e, e2'))).
    destruct p0.
    assert (e0 = e3).
    
    remember (IHt1 e2' e2 e p).
    rewrite surjective_pairing in Heqp0. rewrite e5 in Heqp0.
    inversion Heqp0.
    rewrite surjective_pairing in Heqp1. inversion Heqp1.
    subst. reflexivity.

    subst.
    apply IHt2.
  - simpl.
    destruct s.
    simpl.
    rewrite fold_left_app. rewrite fold_left_app. simpl.
    unfold vm_prim at 5.
    unfold vm_prim at 2.

    remember (fold_left (vm_prim p) (instr_compiler t1 p)
                        (splitEv s e, push_stack (splitEv s0 e) e2)).
    destruct p0.

    remember (fold_left (vm_prim p) (instr_compiler t1 p)
                        (splitEv s e, push_stack (splitEv s0 e) e2')).
    destruct p0.

    assert (e0 = e3).
    rewrite surjective_pairing in Heqp0.
    inversion Heqp0.

    rewrite surjective_pairing in Heqp1. inversion Heqp1.
    apply IHt1.
    subst.

    rewrite fold_left_app.
    rewrite fold_left_app.
    simpl.
    unfold vm_prim at 1.
    unfold vm_prim at 2.

    remember (fold_left (vm_prim p) (instr_compiler t2 p)
                        (let (er, s') := pop_stack e1 in (er, push_stack e3 s'))).
    destruct p0.

    remember (fold_left (vm_prim p) (instr_compiler t2 p)
                        (let (er, s') := pop_stack e4 in (er, push_stack e3 s'))).
    destruct p0.

    assert (e0 = e6).
    remember (pop_stack e4).
    remember (pop_stack e1).
    destruct p0.
    destruct p1.

    assert (e4 = push_stack (splitEv s0 e) e2').
    
    apply stack_restore' with (e0:=e3) (t:=t1) (p:=p) (e:=splitEv s e).
    assumption.

    assert (e1 =  push_stack (splitEv s0 e) e2).
    eapply stack_restore'. eassumption.
    assert (e8 = e10).
    subst. unfold push_stack in *. unfold pop_stack in *. congruence.
    subst.

    rewrite surjective_pairing in Heqp3.
    inversion Heqp3.
    rewrite (IHt2 (push_stack e3 e11) (push_stack e3 e9)).

    rewrite surjective_pairing in Heqp2. inversion Heqp2.
    reflexivity. subst.

    destruct (pop_stack e1).
    destruct (pop_stack e4).
    unfold push_stack in *.
    assert (e5 = (e3 :: e8)).

    eapply stack_restore'. unfold att_vm'. apply Heqp2.

    subst.
    assert (e7 = e3 :: e10).
    eapply stack_restore'. apply Heqp3.
    subst. reflexivity.

  - simpl.
    destruct s.
    simpl. reflexivity.
Defined.



Lemma att_vm_distributive' : forall e p t1 t2,
    let il1 := (instr_compiler t1 p) in
    let il2 := (instr_compiler t2 p) in
    fst (fold_left (vm_prim p) il2 (fst (fold_left (vm_prim p) il1 (e, [])), [])) =
    fst (fold_left (vm_prim p) il2 (fold_left (vm_prim p) il1 (e, []))).
Proof.
  intros.
  destruct ((fold_left (vm_prim p) il1 (e, []))).
  simpl.
  apply stack_irrel.
Defined.

(*
Lemma compile_att_vm : forall il1 il2 p e,
    att_vm il2 p (att_vm il1 p e) =
    att_vm (il1 ++ il2) p e. *)

Lemma att_vm_distributive : forall t1 t2 p e,
    let il1 := (instr_compiler t1 p) in
    let il2 := (instr_compiler t2 p) in
    att_vm il2 p (att_vm il1 p e) =
    att_vm (il1 ++ il2) p e.
Proof.
  intros.
  unfold att_vm.
  unfold att_vm'.
  rewrite fold_left_app.
  apply att_vm_distributive'.
Defined.


(** * Theorems *)
Theorem vm_eval : forall (t:Term) (p:Plc) (e:EvidenceC),
    eval t p e = att_vm (instr_compiler t p) p e.
Proof.
  intros.
  generalize dependent p.
  generalize dependent e.
  induction t; intros.
  - destruct a; try reflexivity.
  - simpl.
    cbv. reflexivity.
  - simpl.
    unfold att_vm.
    unfold att_vm'.
    rewrite fold_left_app.
    unfold att_vm in *.
    rewrite (IHt1 e p).
    rewrite (IHt2 (fst (att_vm' (instr_compiler t1 p) p (e, [])))).
    apply att_vm_distributive'.

  - destruct s.
    simpl.
    unfold att_vm. simpl.
    rewrite (IHt1 (splitEv s e) p).

    unfold att_vm'. 
    rewrite fold_left_app.
    simpl.
    rewrite fold_left_app.
    simpl.
    unfold vm_prim at 1.

    unfold vm_prim at 2.

    unfold att_vm.
    unfold att_vm'.

    rewrite (IHt2 (splitEv s0 e) p).
    unfold att_vm. unfold att_vm'.

    remember (fold_left (vm_prim p) (instr_compiler t1 p) (splitEv s e, push_stack (splitEv s0 e)[])) as HH.
    destruct HH.
    remember (pop_stack e1) as HHHH.
    destruct HHHH.
    remember (fold_left (vm_prim p) (instr_compiler t2 p) (e2, push_stack e0 e3)) as HHH.
    destruct HHH.
    remember (pop_stack e5) as J.
    destruct J.
    
    simpl.
    assert (e1 = [(splitEv s0 e)]).

    unfold push_stack in *.

    eapply stack_restore'.
    apply HeqHH.

    unfold push_stack in HeqHH.
    subst. unfold pop_stack in HeqHHHH.
    assert (e2 = (splitEv s0 e)). congruence.
    subst.
    assert (e3 = []). congruence.
    subst. clear HeqHHHH.
    unfold push_stack in *.
    assert (e5 = [e0]).
    eapply stack_restore'. apply HeqHHH.

    subst.
    unfold pop_stack in HeqJ.
    assert (e0 = e6). congruence. subst.
    clear HeqJ.

    apply ssc_inv.
    rewrite <- stack_irrel with (e2:=[(splitEv s0 e)]).
    rewrite <- HeqHH. reflexivity.

    rewrite <- stack_irrel with (e2:=[e6]).
    rewrite <- HeqHHH. reflexivity.
  -
    simpl.
    destruct s.
    unfold att_vm.
    unfold att_vm'.
    simpl.
    rewrite par_eval_thread.
    rewrite par_eval_thread.
    rewrite par_vm_thread.
    rewrite par_vm_thread.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Defined.

Theorem vm_typeof : forall (t:Term) (p:Plc) (e:EvidenceC) et,
    ET p e et ->
    ET p (att_vm (instr_compiler t p) p e) (typeof t p et).
Proof.
  intros.
  rewrite <- vm_eval.
  apply eval_typeof; auto.
Qed.

  

(*Set Nested Proofs Allowed.*)