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
(*| besl: Instr -> Instr
| besr: Instr -> Instr*)
| besr : Instr
| bep: (list Instr) -> (list Instr) -> Instr
| joins: Instr
| joinp: Instr.

Definition eq_ev_dec:
  forall x y: Instr, {x = y} + {x <> y}.
Proof.
  intros.
  generalize dependent y.
  induction x;
    intros; destruct y; try (left; reflexivity); try (right; congruence).
  SearchAbout "eq_dec".
  destruct (PeanoNat.Nat.eq_dec n n1);
    destruct (PeanoNat.Nat.eq_dec n0 n2);
    destruct (eq_ln_dec l l0); try (left; congruence); try (right; congruence).
  destruct (PeanoNat.Nat.eq_dec n n0);
    destruct (eq_ln_dec l l0); try (left; congruence); try (right; congruence).
  destruct (PeanoNat.Nat.eq_dec n n1);
    destruct (PeanoNat.Nat.eq_dec n0 n2);
    destruct (eq_term_dec t t0); try (left; congruence); try (right; congruence).
    destruct (eq_sp_dec s s1);
    destruct (eq_sp_dec s0 s2);
    try (left; congruence); try (right; congruence).
    (*
    destruct (IHx y); try (left; congruence); try (right; congruence).
    destruct (IHx y); try (left; congruence); try (right; congruence).*)
    admit.
Admitted.
Hint Resolve eq_ev_dec.

Definition eq_li_dec:
  forall x y: (list Instr), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.
Hint Resolve eq_li_dec.

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
    (*let evalL := map besl tr1 in
    let evalR := map besr tr2 in *)
    [splEv] ++ tr1 ++ [besr] ++ tr2 ++ [joins]
  | bpar (sp1,sp2) t1 t2 =>
    let splEv := [split sp1 sp2] in
    let tr1 := instr_compiler t1 p in
    let tr2 := instr_compiler t2 p in
    let tr := [bep tr1 tr2] in
    splEv ++ tr ++ [joinp]
  end.



Definition invokeKIM (i:ASP_ID) (q:Plc) (args:list Arg) : BS.
Admitted.

Definition invokeUSM (i:ASP_ID) (args:list Arg) : BS.
Admitted.

Definition signEv (e:Evidence) : BS.
Admitted.

Definition hashEv (e:Evidence) : BS.
Admitted.

Definition toRemote (t:Term) (pTo:Plc) (e:Evidence) : Evidence.
Admitted.

Definition parallel_att_vm_thread (li:list Instr) (e:Evidence) : Evidence.
Admitted.

Definition vm_prim_thread (i:Instr) (p:Plc) (e:Evidence) : Evidence.
Admitted.

Definition parallel_eval_thread (t:Term) (p:Plc) (e:Evidence) : Evidence.
Admitted.

Definition splitEv (sp:SP) (e:Evidence) : Evidence :=
  match sp with
  | ALL => e
  | NONE => mt
  end.

Definition eval_asp (a:ASP) (p:Plc) (e:Evidence) : Evidence :=
  match a with
  | CPY => e
  | KIM i q args =>
    let bs := invokeKIM i q args in
    (kk i args q p bs e)
  | USM i args =>
    let bs := invokeUSM i args in
    (uu i args p bs e)
  | SIG =>
    let bs := signEv e in
    (gg p e bs)
  | HSH =>
    let bs := hashEv e in
    (hh p bs)
  end.

Fixpoint eval (t:Term) (p:Plc) (e:Evidence) : Evidence :=
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
    (ss e1' e2')
  | bpar (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := parallel_eval_thread t1 p e1 in
    let e2' := parallel_eval_thread t2 p e2 in
    (pp e1' e2')
  end.

Definition ev_stack := list Evidence.
Definition empty_stack : ev_stack := [].

Definition push_stack (e:Evidence) (s:ev_stack) : ev_stack :=
  (e :: s).

Definition pop_stack (s:ev_stack) : (Evidence*ev_stack) :=
  match s with
  | e :: s' => (e,s')
  | _ => (mt,empty_stack) (* TODO: will this be expressive enough? *)
  end.


Definition vm_prim (p:Plc) (ep:Evidence*ev_stack) (instr:Instr)
  :(Evidence * ev_stack) :=
  let (e,s) := ep in
    match instr with
    | copy => (e,s)
    | kmeas i q args =>
      let bs := invokeKIM i q args in
      ((kk i args q p bs e),s)
    | umeas i args =>
      let bs := invokeUSM i args in
      ((uu i args p bs e),s)
    | sign =>
      let bs := signEv e in
      ((gg p e bs),s)
    | hash =>
      let bs := hashEv e in
      ((hh p bs),s)
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
      (ss er e,s') (* TODO: better choice than mt? *)
                 
    | joinp =>
      let (er,s') := pop_stack s in
      (pp e er,s') (* TODO: invoke "wait on evidence" commands here? *)
    | bep evs1 evs2 =>
      let (er,s') := pop_stack s in
      let res1 := parallel_att_vm_thread evs1 e in
      let res2 := parallel_att_vm_thread evs2 er in
      (res1, push_stack res2 s')  (* TODO: ret some kind of "wait handle" evidence instead? *)
    end.
(*
Definition vm_prim (p:Plc) (ep:Evidence*Evidence) (instr:Instr)
  : (Evidence*Evidence) :=
  vm_prim' p (fst ep) (snd ep) instr. *)
(*
Fixpoint fold {A B : Type} (f:A -> B -> A) (a:A) (bs:list B) : A :=
  match bs with
  | [] => a
  | (x::xs) => fold f (f a x) xs
  end.*)

Lemma fst_inv{A B:Type} : forall (p:A*B) (p':A*B), p = p' -> fst p = fst p'.
Proof.
  intros.
  congruence.
Defined.

Lemma fst_val{A B:Type} : forall (a:A) (b:B), fst (a,b) = a.
Proof.
  intros. simpl. reflexivity.
Defined.

Lemma pair_inv{A B:Type} : forall (a a':A) (b b':B), (a,b) = (a',b') -> a = a'.
Admitted.

Lemma ss_inv : forall e1 e1' e2 e2', e1 = e1' -> e2 = e2' -> ss e1 e2 = ss e1' e2'.
Admitted.



Set Nested Proofs Allowed.

  
Definition att_vm' (is:list Instr) (p:Plc) (ep:Evidence*ev_stack) : (Evidence*ev_stack) :=
  fold_left (vm_prim p) is ep.

Definition att_vm (is:list Instr) (p:Plc) (e:Evidence) : (Evidence) :=
  fst (att_vm' is p (e,[])).

Axiom remote_vm : forall t n e,
    toRemote t n e = att_vm (instr_compiler t n) n e.

Axiom rem_vm : forall t p e s,
    (toRemote t p e, s) = att_vm' (instr_compiler t p) p (e, s).

Axiom par_vm_thread : forall t p e,
  parallel_att_vm_thread (instr_compiler t p) e = att_vm (instr_compiler t p) p e.

Axiom par_eval_thread : forall t p e,
    parallel_eval_thread t p e = eval t p e.

(*
Lemma fads : forall e0 e1 e e2 p t,
    (e0,e1) = fold_left (vm_prim p) (instr_compiler t p) (e, e2) ->
    (e1 = e2).
Proof.
Admitted. *)

Lemma hi : forall e0 e1 t p s e,
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
    (* unfold push_stack in H. *)
    
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
  simpl. eapply hi. eassumption.
Defined.

Lemma afsd : forall e p t e2 e2', (* starting stack irrelevant *)
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
    (*assert (e4 = e1).*)

    (* Lemma hi : forall e0 e1 t p s e,
    ((e0, e1) = att_vm' (instr_compiler t p) p (e, s)) ->
    e1 = s. *)

    assert (e4 = push_stack (splitEv s0 e) e2').
    
    
    apply hi with (e0:=e3) (t:=t1) (p:=p) (e:=splitEv s e).
    assumption.

    assert (e1 =  push_stack (splitEv s0 e) e2).
    eapply hi. eassumption.
    assert (e8 = e10).
    subst. unfold push_stack in *. unfold pop_stack in *. congruence.
    subst.

    rewrite surjective_pairing in Heqp3.
    inversion Heqp3.
    rewrite (IHt2 (push_stack e3 e11) (push_stack e3 e9)).

    rewrite surjective_pairing in Heqp2. inversion Heqp2.
    reflexivity. subst.
    
   

(*
    
    subst. congruence.

    (*assert (e4 = e1).*)
    





    unfold push_stack in *.
    assert (e4 = splitEv s0 e :: e2'). admit.
    subst.
    assert (e1 = splitEv s0 e :: e2). admit.
    subst.
    unfold pop_stack in Heqp2.
    unfold pop_stack in Heqp3. *)

    destruct (pop_stack e1).
    destruct (pop_stack e4).
    unfold push_stack in *.
    assert (e5 = (e3 :: e8)).

    eapply hi. unfold att_vm'. apply Heqp2.

    subst.
    assert (e7 = e3 :: e10).
    eapply hi. apply Heqp3.
    subst. reflexivity.

  - simpl.
    destruct s.
    simpl. reflexivity.
Defined. 

Theorem vm_eval : forall (t:Term) (p:Plc) (e:Evidence),
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
    apply fst_inv.

    unfold att_vm'.
    assert (snd (fold_left (vm_prim p) (instr_compiler t1 p) (e, [])) = []).
      
    apply stack_restore.
    rewrite <- H at 2.

    rewrite <- surjective_pairing. reflexivity.

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

    eapply hi.
    apply HeqHH.

    unfold push_stack in HeqHH.
    subst. unfold pop_stack in HeqHHHH.
    assert (e2 = (splitEv s0 e)). congruence.
    subst.
    assert (e3 = []). congruence.
    subst. clear HeqHHHH.
    unfold push_stack in *.
    assert (e5 = [e0]).
    eapply hi. apply HeqHHH.

    subst.
    unfold pop_stack in HeqJ.
    assert (e0 = e6). congruence. subst.
    clear HeqJ.

    apply ss_inv.
    rewrite <- afsd with (e2:=[(splitEv s0 e)]).
    rewrite <- HeqHH. reflexivity.

    rewrite <- afsd with (e2:=[e6]).
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

Lemma asdf : forall is1 is2 p ep,
        (att_vm' (is1 ++ is2) p ep) =
        (att_vm' is2 p
                 (att_vm' is1 p ep)).
Proof.
  intros.
  unfold att_vm'.
  apply fold_left_app.
Defined.

Lemma snd_inv{A B:Type} : forall (p:A*B) (p':A*B), p = p' -> snd p = snd p'.
Proof.
  intros.
  congruence.
Defined.

Lemma exists_ev : forall t p e er t1 t2 sp t1' t2' sp', exists e',
      t <> bseq sp t1 t2 ->
      t <> bpar sp' t1' t2' ->
      att_vm' (instr_compiler t p) p (e,er) = (e',er).
Proof.
  intros.
  generalize dependent p.
  generalize dependent e.
  generalize dependent er.
  generalize dependent t1'.
  generalize dependent t2'.
  generalize dependent t1.
  generalize dependent t2.
  generalize dependent sp.
  generalize dependent sp'.
  
  induction t; intros; try (eexists; reflexivity).
  - destruct a; try (eexists; reflexivity).
      
  - destruct (IHt1 sp sp' t2 t3 t2' t1' er e p).
    destruct (IHt2 sp sp' t2 t3 t2' t1' er x p).
    eexists.
    simpl.

    unfold att_vm'.
    rewrite fold_left_app.
    assert ((att_vm' (instr_compiler t1 p) p (e,er)) = (fold_left (vm_prim p) (instr_compiler t1 p) (e, er))).
    unfold att_vm'. reflexivity.
    intros.
    rewrite <- H1.
    rewrite H.
    assert ((att_vm' (instr_compiler t2 p) p (x,er)) = (fold_left (vm_prim p) (instr_compiler t2 p) (x, er))).
    unfold att_vm'. reflexivity.
    rewrite <- H2. rewrite H0. reflexivity.
  - 
    (*destruct (IHt2 x p). *)
    eexists.
    simpl.
    unfold att_vm'.

    unfold fold_left at 1. 


    destruct s. simpl. fold (fold_left (vm_prim p) (instr_compiler t1 p ++ besr :: instr_compiler t2 p ++ [joins]) (splitEv s e, splitEv s0 e)).
    fold (att_vm' (instr_compiler t1 p ++ besr :: instr_compiler t2 p ++ [joins]) p (splitEv s e, splitEv s0 e)). unfold att_vm'.  Check fold_left_app.

    pose (l2 := besr :: instr_compiler t2 p ++ [joins]).
    rewrite fold_left_app.
    destruct (IHt1 (splitEv s0 e) (splitEv s e) p).
    unfold att_vm' in H. rewrite H.

    simpl.

    rewrite fold_left_app. simpl. destruct (IHt2 x (splitEv s0 e) p). unfold att_vm' in H0. rewrite H0. simpl. reflexivity.



    
    apply fold_left_app with (l' := besr :: instr_compiler t2 p ++ [joins]).


                         (  (fix fold_left (l : list Instr) (a0 : Evidence * Evidence) {struct l} :
     Evidence * Evidence :=
     match l with
     | [] => a0
     | b :: t => fold_left t (vm_prim p a0 b)
     end) (instr_compiler t1 p ++ besr :: instr_compiler t2 p ++ [joins])
    (splitEv s e, splitEv s0 e)).
    
    
    + eexists. reflexivity.

Lemma right_mt : forall t p e,
    snd (att_vm' (instr_compiler t p) p (e,mt)) = mt.
Proof.
  intros.
  destruct (exists_ev t p e).
  rewrite H.
  trivial.
Defined.

  intros.
  generalize dependent p.
  generalize dependent e.
  induction t; intros; try reflexivity.
  - destruct a; try reflexivity.
  - simpl.
    rewrite <- (IHt2 (snd (att_vm' (instr_compiler t1 p) p (e, mt))) p) at 2.
    rewrite <- (IHt1 e p) at 3.
    rewrite (IHt1 e p) at 2.
    apply snd_inv.
    unfold att_vm' at 1.
    rewrite fold_left_app.
    unfold att_vm'.
    unfold att_vm' in IHt1. rewrite IHt1.
    assert ((fold_left (vm_prim p) (instr_compiler t1 p) (e, mt)) = (mt,mt)).
    
    admit.
    congruence.
    



    apply asdf.
  - simpl.
    
    


    
    
  

    snd (vm_prim' p e mt instr) = mt.
Proof.
  intros.
  induction instr; try reflexivity.
  - simpl

(*
Lemma asdf : forall e,
IdentityMonad.unIdent
  (ReaderMonad.runReaderT (vm_prim e copy) empty_cop_env) = e.
Proof.
  intros. simpl.
Admitted. *)

Lemma compile_att_vm : forall il1 il2 p e,
    att_vm il2 p (att_vm il1 p e) =
    att_vm (il1 ++ il2) p e.
Proof.
Admitted.
(*
  att_vm (instr_compiler t2 p) p (att_vm (instr_compiler t1 p) p e) =
  att_vm (instr_compiler t1 p ++ instr_compiler t2 p) p e *)
  
Theorem eval_vm : forall (t:Term) (p:Plc) (e:Evidence),
    eval t p e = att_vm (instr_compiler t p) p e.
Proof.
  intros.
  generalize dependent p.
  generalize dependent e.
                            
  induction t; intros; try (reflexivity).
  
  + 
    destruct a; try (cbv; reflexivity).
  + simpl. rewrite (IHt2 (eval t1 p e)).
    rewrite (IHt1 e).
    apply compile_att_vm.
  + simpl. destruct s. simpl
    destruct (instr_compiler t1 p);
      destruct (instr_compiler t2 p).
  - admit.
  - admit.

  - admit.
  - simpl.
    
    
    
    

    simpl. rewrite (IHt n).



    
  + unfold eval
    
    
  + destruct env. simpl.
    
  - simpl. destruct env.

    simpl. unfold empty_cop_env.
    assert (p = 0). admit. congruence
    unfold instr_compiler. unfold asp_instr.
    unfold att_vm. unfold foldM_COP. unfold eval. unfold eval_asp_cop


  simpl.
  unfold runCOP at 1. simpl. unfold runCOP at 1.
  simpl.
  unfold runCOP. simpl. unfold ReaderMonad.runReaderT.
  unfold vm_prim
  destruct empty_cop_env. simpl. unfold vm_prim.
  destruct runReaderT.
  destruct env
  simpl. unfold vm_prim
  
  
