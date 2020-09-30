Require Import List.
Import ListNotations.

Definition snoc : list nat -> nat -> list nat :=
  fun l n => l ++ [n].

Theorem foo : forall l m,
  fold_left snoc l m = m ++ l.
Proof.
  induction l as [|h t IH]; simpl; intro m.
  - rewrite app_nil_r. reflexivity.
  - unfold snoc; fold snoc.
    assert (m ++ h :: t = (m ++ [h]) ++ t).
    { rewrite <- app_assoc. reflexivity. }
    rewrite H.
    apply IH.
Qed.

Lemma fold_monotonic_gen : forall prefix ns tr l,
    fold_left snoc ns l = tr ->
    fold_left snoc ns prefix = prefix ++ (skipn (length l) tr).
Proof.
  intros prefix ns tr l H.
  rewrite foo in H. subst.
  assert (skipn (length l) (l ++ ns) = ns).
  Search skipn.
  admit.
  rewrite H.
  rewrite foo. reflexivity.
Admitted.

  
 
Lemma fold_monotonic' : forall prefix ns tr,
  fold_left snoc ns [] = tr ->
  fold_left snoc ns prefix = prefix ++ tr.
Proof.
  intros.
  assert (tr = (skipn (length ([]:list nat)) tr)).
  auto.
  rewrite H0.
  apply fold_monotonic_gen. assumption.
Defined.

Lemma fold_monotonic : forall prefix ns tr,
  fold_left snoc ns [] = tr ->
  fold_left snoc ns prefix = prefix ++ tr.
Proof.
  intros prefix ns tr H.
  rewrite foo in H. rewrite app_nil_l in H. subst.
  rewrite foo. reflexivity.
Qed.




Inductive Instr : Set :=
| hash : Instr.

Inductive AnnoInstr : Type :=
| aprimInstr: nat -> Instr -> AnnoInstr.

Fixpoint instr_compiler (t:AnnoTerm) : (list AnnoInstr) :=
  match t with
  | aasp r a => [aprimInstr (fst r) (asp_instr a)]  
(*  | aatt r q t' => [areqrpy r q t']      *)        
  | alseq _ t1 t2 =>
    let tr1 := instr_compiler t1 in
    let tr2 := instr_compiler t2 in
    tr1 ++ tr2 

