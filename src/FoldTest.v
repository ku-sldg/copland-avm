Require Import List.
Import ListNotations.

Check fold_left.

Definition f : list nat -> nat -> list nat :=
  fun l (n:nat) => (l ++ [n]).

Lemma fold_monotonic : forall prefix ns tr,
  fold_left f ns [] = tr ->
  fold_left f ns prefix = (prefix ++ tr).
Proof.

  (*
  intros.
  generalize dependent tr.
  generalize dependent prefix.
  induction ns; intros; simpl in *.
  - inversion H; subst. rewrite app_nil_r. trivial.
  - 
    rewrite <- IHns.
    unfold f. simpl. fold f.*)
Abort.

    
    
  
  
