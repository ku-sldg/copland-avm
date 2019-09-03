Require Import Term.
(*Require Import MonadCOP.*)

Require Import List.
Import ListNotations.


(** * VM Instructions *)

Inductive Instr: Set :=
| copy: Instr
| kmeas: ASP_ID -> Plc -> (list Arg) -> Instr
| umeas: ASP_ID -> (list Arg) -> Instr
| sign: Instr
| hash: Instr
| reqrpy: Plc -> Plc -> Term -> Instr
| split: SP -> SP -> Instr
| besr : Instr
| bep: (list Instr) -> (list Instr) -> Instr
| joins: Instr
| joinp: Instr.

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
Definition asp_instr (t:ASP) (p:Plc) : Instr :=
  match t with
  | CPY => copy
  | KIM i p args => kmeas i p args
  | USM i args => umeas i args
  | SIG => sign
  | HSH => hash
  end.

Fixpoint instr_compiler (t:Term) (p:Plc) : (list Instr) :=
  match t with
  | asp a => [asp_instr a p]
  | att q t' => [reqrpy p q t']
  | lseq t1 t2 =>
    let tr1 := instr_compiler t1 p in
    let tr2 := instr_compiler t2 p in
    tr1 ++ tr2
  | bseq (sp1,sp2) t1 t2 =>
    let splEv := split sp1 sp2 in
    let tr1 := instr_compiler t1 p in
    let tr2 := instr_compiler t2 p in
    [splEv] ++ tr1 ++ [besr] ++ tr2 ++ [joins]
  | bpar (sp1,sp2) t1 t2 =>
    let splEv := [split sp1 sp2] in
    let tr1 := instr_compiler t1 p in
    let tr2 := instr_compiler t2 p in
    let tr := [bep tr1 tr2] in
    splEv ++ tr ++ [joinp]
  end.

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

Definition parallel_att_vm_thread (li:list Instr) (e:EvidenceC) : EvidenceC.
Admitted.

Definition vm_prim_thread (i:Instr) (p:Plc) (e:EvidenceC) : EvidenceC.
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
    (kkc i args q p bs e)
  | USM i args =>
    let bs := invokeUSM i args in
    (uuc i args p bs e)
  | SIG =>
    let bs := signEv e in
    (ggc p e bs)
  | HSH =>
    let bs := hashEv e in
    (hhc p bs)
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

(** * EvidenceC Stack *)
Definition ev_stack := list EvidenceC.
Definition empty_stack : ev_stack := [].

Definition push_stack (e:EvidenceC) (s:ev_stack) : ev_stack :=
  (e :: s).

Definition pop_stack (s:ev_stack) : (EvidenceC*ev_stack) :=
  match s with
  | e :: s' => (e,s')
  | _ => (mtc,empty_stack) (* TODO: will this be expressive enough? *)
  end.

(** * Primitive VM Operations *)
Definition vm_prim (p:Plc) (ep:EvidenceC*ev_stack) (instr:Instr)
  :(EvidenceC * ev_stack) :=
  let (e,s) := ep in
    match instr with
    | copy => (e,s)
    | kmeas i q args =>
      let bs := invokeKIM i q args in
      ((kkc i args q p bs e),s)
    | umeas i args =>
      let bs := invokeUSM i args in
      ((uuc i args p bs e),s)
    | sign =>
      let bs := signEv e in
      ((ggc p e bs),s)
    | hash =>
      let bs := hashEv e in
      ((hhc p bs),s)
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
    end.


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

Axiom par_eval_thread : forall t p e,
    parallel_eval_thread t p e = eval t p e.


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

(*Set Nested Proofs Allowed.*)