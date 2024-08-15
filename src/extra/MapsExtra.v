(*
Lemma map_get_get : forall (k:nat) (v:EvidenceTC) l',
    map_get ((k,v) :: l') k = Some v.
Proof.
  intros.
  simpl.
  break_match; eauto.
  rewrite PeanoNat.Nat.eqb_refl in Heqb. congruence.
Defined.

Lemma map_get_get_2 : forall (k:nat) (v:EvidenceTC) k' v' l',
    k <> k' ->
    map_get ((k',v') :: (k,v) :: l') k = Some v.
Proof.
  intros; simpl.
  break_if;
    dohtac; tauto.
Defined.
*)
