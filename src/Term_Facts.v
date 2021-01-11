Require Import List.
Import List.ListNotations.

Require Import Coq.Arith.Even.

Lemma both_args_even: forall a b,
    Nat.even a = true ->
    Nat.even b = true ->
    Nat.even (a + b) = true.
Proof.
Admitted.

Definition get_available_locs (n:nat): list nat.
Admitted.

Axiom num_locs: forall n l,
    get_available_locs n = l ->
    length l = n.

Axiom unique_locs: forall n l,
  get_available_locs n = l ->
  NoDup l.

Fixpoint make_pairs' (l:list nat) (pl:list (nat*nat)): option (list (nat*nat)) :=
  match l with
  | [] => Some pl
  | x :: y :: l' => make_pairs' l' (pl ++ [(x,y)])
  | _ => None (* TODO: handle error case with option type? *)
  end.
    
Definition make_pairs (l:list nat): option (list (nat*nat)) :=
  make_pairs' l [].

Compute (make_pairs [1; 2; 3; 4]).
Compute (make_pairs' [7;8;9;10] [(1,2); (3,4)]).

Lemma even_list_struc{A:Type}: forall n (ls:list A),
    length ls = n ->
    Coq.Arith.Even.even n ->
    ls = [] \/ exists x y ls', ls = x :: y :: ls' /\ (Coq.Arith.Even.even (length ls')).
Proof.
Admitted.

Check even_ind.
(*
even_ind
     : forall P : nat -> Prop, P 0 -> (forall n : nat, odd n -> P (S n)) -> forall n : nat, even n -> P n
 *)

Print even_ind.

Definition even_list_ind{A:Type}
  : forall P : list A -> Prop, P [] ->
                    (forall ls x y, even (length ls) -> P ls -> P (x :: y :: ls)) ->
                    (forall ls, even (length ls) -> P ls).
Admitted.

(*
Lemma start_irrel: forall ls ls' ls'' H0,
    even (length ls) ->
    make_pairs' ls ls' = Some H0 ->
    exists ps, make_pairs' ls ls'' = Some ps.
Proof.
Admitted.
 *)

Check even_ind.

(*
Theorem even_ind :
  forall (P : nat -> Prop),
    P O ->
    (forall n, even n -> P n -> P (S (S n))) ->
    forall n, even n -> P n.
Proof.
  (*
Proof.
  intros P HO HSS.
  fix self 1.
  intros n.
  destruct n as [| [| n']].
  - intro; apply HO.
  - discriminate.
  - intros H. apply HSS.
    + apply H.
    + apply self.
      apply H.
Qed.
   *)
  
  intros P HO HSS.
  fix self 1.
  intros n.
  destruct n as [| [| n']].
  - intro; apply HO.
  -
    intros.
    eauto.
  -
    eauto.
Admitted.
*)


Lemma cumul: forall ls ps H0,
    Coq.Arith.Even.even (length ls) ->
    make_pairs' ls ps = Some H0 ->
    exists lss,
    H0 = ps ++ lss.
    (*
    make_pairs' ls (p :: ps) = Some (p :: H0). *)
Proof.

  (*
  apply even_ind.
  intros ps H0 p ls H.
  generalize dependent ls.
  apply even_list_ind.
  intros.
  generalizeEverythingElse ls.
  apply even_list_ind.
  -
    cbn in *.
  intros.
  pose (even_list_struc (length ls) ls).
  repeat concludes.
  induction o.
  -
    subst.
    cbn in *.
    eauto.
    congruence.
  -
    destruct_conjs.
    subst.
    cbn in *.
*)
Admitted.

Lemma make_pairs_succeeds: forall ps ls,
  (*length ls = n -> *)
  Coq.Arith.Even.even (length ls) ->
  exists ps',
  make_pairs' ls ps = Some ps'.
Proof.
  (*
  apply even_list_ind.
  -
    cbn.
    eauto.
  -
    intros.
    destruct_conjs.
    unfold make_pairs in *.
    cbn.
    pose (cumul ls ps H0).
    repeat concludes.
    destruct_conjs.
    subst.

    exists ((ps ++ [(x, y)]) ++ e).
    


    
    pose cumul.
    pose (e ls ps H0).
    repeat concludes.
    destruct_conjs.
    exists (H0 ++ [(x,y)]).

    eapply cumul; eauto.
Defined.

    
    
    pose (even_list_struc (length ls) ls).
    repeat concludes.
    destruct o.
    +
      subst.
      cbn.
      eauto.
    +
      destruct_conjs.
      rewrite H4 in *.
      cbn in *.

      Lemma make_pairs'_cumul: forall ls ps H0,
        make_pairs' ls ps = Some H0 ->
        exists rest, H0 = ps ++ rest.
      Proof.
      Admitted.

      assert (exists rest, H0 = [(H1,H2)] ++ rest).
      {
        eapply make_pairs'_cumul; eauto.
      }

      destruct_conjs.
      subst
      
      

      eapply start_irrel; eauto.
Defined.

      
      cbv
      
    
    
  intros n ls len.
  rewrite <- len.
  generalize dependent ls.
  apply even_list_ind.
  apply even_ind.
  intros.
  generalize dependent ls.
  apply even_ind.
  intros ls n len.
  Check even_ind.
  apply even_ind.
*)
Admitted.
