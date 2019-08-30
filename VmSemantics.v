Require Import Term.
Require Import Instr.

Require Import List.
Import ListNotations.

Inductive vm_primR : Plc -> (Evidence*ev_stack) -> Instr -> (Evidence*ev_stack) -> Prop :=
| vcopy : forall p ep, vm_primR p ep copy ep
| vkmeas : forall i p q args e s,
    let bs := invokeKIM i q args in
    vm_primR p (e,s) (kmeas i q args) ((kk i args q p bs e),s)
| vumeas : forall i p args e s,
    let bs := invokeUSM i args in
    vm_primR p (e,s) (umeas i args) ((uu i args p bs e),s)
| vsign : forall p e s,
    let bs := signEv e in
    vm_primR p (e,s) sign ((gg p e bs),s)
| vhash : forall p e s,
    let bs := hashEv e in
    vm_primR p (e,s) hash ((hh p bs),s)
| vreqrpy : forall p e pTo pFrom s t,
    vm_primR p (e,s) (reqrpy pFrom pTo t) (toRemote t pTo e,s)
| vsplit : forall p sp1 sp2 e s,
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    vm_primR p (e,s) (Instr.split sp1 sp2) (e1, push_stack e2 s)
(*| vbesr : forall p e s,
    let (er,s') := pop_stack s in
    let s'' := push_stack e s' in
    (vm_primR p (e,s) besr (er,s'')).*)
| vbesr : forall p e s,
    vm_primR p (e,s) besr ((fst(pop_stack s)), (push_stack e (snd(pop_stack s))))
| vjoins : forall p e (s:ev_stack),
    (*let (er,s') := pop_stack s in
    vm_primR p (e,s) joins (ss er e,s')*)
    vm_primR p (e,s) joins (ss (fst(pop_stack s)) e,snd(pop_stack s))
| vjoinp : forall p e (s:ev_stack),
    vm_primR p (e,s) joinp (pp e (fst(pop_stack s)), snd(pop_stack s))
| vbep : forall p e s evs1 evs2,
    let res1 := parallel_att_vm_thread evs1 e in
    let res2 := parallel_att_vm_thread evs2 (fst(pop_stack s)) in
    vm_primR p (e,s) (bep evs1 evs2) (res1, push_stack res2 (snd(pop_stack s))).

Lemma vm_primR_implies_vm_prim : forall p i ep1 ep2,
    vm_primR p ep1 i ep2 -> vm_prim p ep1 i = ep2.
Proof.
  intros.
  induction H; try (destruct ep); try (destruct s); reflexivity.
Defined.

Lemma vm_prim_implies_vm_primR : forall p i ep1 ep2,
    vm_prim p ep1 i = ep2 -> vm_primR p ep1 i ep2.
Proof.
Admitted.

Lemma vm_prim_iff_vm_primR : forall p i ep1 ep2,
    vm_prim p ep1 i = ep2 <-> vm_primR p ep1 i ep2.
Proof.
  intros.
  split.
  - apply vm_prim_implies_vm_primR.
  - apply vm_primR_implies_vm_prim.
Defined.

    



Inductive att_vm'R : Plc -> (list Instr) -> (list Instr) -> (Evidence*ev_stack) -> (Evidence*ev_stack) -> Prop :=
| att_vm'R_nil : forall p ep,
    att_vm'R p [] [] ep ep
| att_vm'R_step : forall p i is ep ep',
    vm_primR p ep i ep' ->
    att_vm'R p (i::is) is ep ep'
| att_vm'R_trans : forall p is is' is'' ep ep' ep'',
    att_vm'R p is is' ep ep' ->
    att_vm'R p is' is'' ep' ep'' ->
    att_vm'R p is is'' ep ep''.

Definition att_vmR (p:Plc) (is:list Instr) (e:Evidence) (e':Evidence) : Prop :=
  att_vm'R p is [] (e,[]) (e',[]).

Require Import Coq.Program.Equality.
Set Nested Proofs Allowed.

Lemma pairf{A B:Type} : forall (p:A*B) e' v,
    p = (e', v) -> fst p = e'.
Proof.
  intros.
  subst. simpl. reflexivity.
Defined.

Lemma asdf : forall p e i e',
    vm_primR p (e, []) i (e', []) -> fst (vm_prim p (e, []) i) = e'.
Proof.
  intros.
  Check vm_prim_iff_vm_primR.
  rewrite <- vm_prim_iff_vm_primR in H.
  eapply pairf. eassumption.
Defined.

Lemma fdsa : forall p is is' e ep' e',
    att_vm'R p is is' (e, []) ep' -> 
    att_vm'R p is' [] ep' (e', []) ->
    fst (att_vm' is p (e, [])) = e'.
Proof.
Admitted.

Theorem att_vmR_implies_att_vm : forall p e e' is,
    att_vmR p is e e' -> att_vm is p e = e'.
Proof.
  intros.
  inversion H.
  - cbv. reflexivity.
  - unfold att_vm. unfold att_vm'. unfold fold_left.
    apply asdf; assumption.
    
  - unfold att_vm.
    subst.
    eapply fdsa; eassumption.
Defined.

    
    
    
  
      
    
  