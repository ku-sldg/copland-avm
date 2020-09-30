(*


Author:  Adam Petz, ampetz@ku.edu
*)

Theorem app_inj_l: forall A (l1 l2 suf : list A),
    l1 ++ suf = l2 ++ suf -> l1 = l2.
Proof.
  Admitted.
  
Lemma headShouldersKneesAndToes : forall A (h : A) t l1 l2,
    h :: t = l1 ++ l2 ->
    forall prefix i, t = prefix ++ i :: l2 ->
    l1 = h :: prefix ++ [i].
Proof.
  intros. subst.
  assert (H0 : i :: l2 = [i] ++ l2). reflexivity.
  rewrite H0 in H; clear H0.
  apply app_inj_l with (suf := l2).
  simpl. rewrite <- app_assoc. auto.
Qed.

Theorem vm_multi_suffix : forall il1 il2 tr,
    vm_multi {| vm_list := il1 |} {| vm_list := il2 |} tr ->
    exists prefix, il1 = prefix ++ il2.
Proof.
(*  intros il1 il2 tr H. inversion H.
  - exists []. reflexivity.
  - subst. Print refl_trans_1n_trace. Print vm_step.
*)
  intros il1 il2 tr H. dependent induction H.
  - exists []. reflexivity.
  - apply IHrefl_trans_1n_trace.
    + admit.
    + reflexivity.
Admitted.

Lemma il1_pieces' : forall i0 vm_list0 il1 il2 i tr,
    i0 :: vm_list0 = il1 ++ il2 ->
    vm_multi {| vm_list := vm_list0 |} {| vm_list := i :: il2 |} tr ->
    exists bla, il1 = [i0] ++ bla ++ [i].
Proof.
  intros i0 vm_list0 il1 il2 i tr H0 H1.
  remember (vm_multi_suffix _ _ _ H1) as e. destruct e. exists x.
  apply headShouldersKneesAndToes with (t := vm_list0) (l2 := il2); try assumption.
Qed.
