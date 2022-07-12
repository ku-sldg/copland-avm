Require Import List.
Import List.ListNotations.

Definition even_nat_ind :
  forall (P : nat -> Prop),
  P 0 ->
  P 1 ->
  (forall n, P n -> P (S (S n))) ->
  forall n, P n :=
    fun P => fun P0 => fun P1 => fun P_plus_2 =>
      fix f n := match n with
                 | 0 => P0
                 | 1 => P1
                 | S (S n) => P_plus_2 n (f n)
                 end.

Lemma both_args_even: forall a b,
    Nat.even a = true ->
    Nat.even b = true ->
    Nat.even (a + b) = true.
Proof.
  induction a using even_nat_ind; simpl; intros; auto; try discriminate.
Qed.

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

(*
Compute (make_pairs [1; 2; 3; 4]).
Compute (make_pairs' [7;8;9;10] [(1,2); (3,4)]).
*)

Lemma even_list_struc{A:Type}: forall n (ls:list A),
    length ls = n ->
    Nat.even n = true ->
    ls = [] \/ exists x y ls', ls = x :: y :: ls' /\ (Nat.even (length ls') = true).
Proof.
  induction n using even_nat_ind; simpl; intros; auto.
  - left. destruct ls; simpl in *; auto; congruence.
  - discriminate.
  - right. destruct ls.
    * discriminate.
    * destruct ls.
      ** discriminate.
      ** specialize IHn with ls.
         assert (length ls = n). { 
          inversion H. auto.
         }
         apply (IHn H1) in H0.
         destruct H0.
        *** exists a, a0, []. split; subst; auto.
        *** destruct H0 as [x' [y' Hl]]. 
            destruct Hl as [ls' [Hl1 Hl2]].
            subst.
            exists a, a0, (x' :: y' :: ls'); split; subst; auto.
Qed.

(*
Check even_ind.
(*
even_ind
     : forall P : nat -> Prop, P 0 -> (forall n : nat, odd n -> P (S n)) -> forall n : nat, even n -> P n
 *)
*)


Definition even_list_ind'{A:Type}
  : forall (P : list A -> Prop), 
  P [] -> (* base case*)
  (forall x, P [x]) -> (* base case 2 *)
  (* (forall ls, Nat.even (length ls) = true -> P ls) -> *)
  (forall ls x y, P ls -> P (x :: y :: ls)) ->
  (forall ls, P ls) :=
    fun P => fun P0 => fun P1 => fun Pc2 =>
      fix f l := match l with
                  | [] => P0
                  | [x] => P1 x
                  | h1 :: h2 :: l' => Pc2 l' h1 h2 (f l')
                  end.

Definition even_list_ind{A:Type}
  : forall (P : list A -> Prop), 
  P [] -> (* base case*)
                    (forall ls x y, Nat.even (length ls) = true -> P ls -> P (x :: y :: ls)) ->
                    (forall ls, Nat.even (length ls) = true -> P ls).
Proof.
  induction ls using even_list_ind'; intros; auto.
  - discriminate.
Qed.

(*
Lemma start_irrel: forall ls ls' ls'' H0,
    even (length ls) ->
    make_pairs' ls ls' = Some H0 ->
    exists ps, make_pairs' ls ls'' = Some ps.
Proof.
Admitted.
 *)

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
    Nat.even (length ls) = true ->
    make_pairs' ls ps = Some H0 ->
    exists lss,
    H0 = ps ++ lss.
    (*
    make_pairs' ls (p :: ps) = Some (p :: H0). *)
Proof.
  induction ls using even_list_ind'; simpl; intros; auto.
  - exists nil. rewrite app_nil_r. injection H1. auto.
  - discriminate.
  - specialize IHls with (ps ++ [(x,y)]) H0.
    apply (IHls H) in H1. 
    destruct H1.
    exists ([(x,y)] ++ x0). rewrite app_assoc in *.
    auto.
Qed.
  
Lemma make_pairs_succeeds: forall ls,
  (*length ls = n -> *)
  Nat.even (length ls) = true ->
  forall ps,
  exists ps',
  make_pairs' ls ps = Some ps'.
Proof.
  induction ls using even_list_ind'; simpl; intros; auto.
  - exists ps. auto.
  - discriminate.
Qed.
