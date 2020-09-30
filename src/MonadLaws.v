(*
Proofs of monad laws for the general state monad in GenStMonad.v.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import GenStMonad.

Require Import StructTactics.

Lemma monad_left_id : forall S A B (a:A)(f:A -> (GenStMonad.St S) B) (s:S),
    (bind (ret a) f) s = (f a s).
Proof.
  intros.
  unfold ret.
  unfold bind.
  simpl.
  destruct (f a s).
  reflexivity.
Qed.

Lemma monad_right_id : forall S A (m:St S A) (s:S),
    bind m (ret) s = m s.
Proof.
  intros.
  unfold ret.
  unfold bind.
  destruct (m s).
  destruct o; auto.
Qed.

Lemma monad_right_id' : forall S (m:St S unit) (s:S),
    (m ;; (ret tt)) s = m s.
Proof.
  intros.
  unfold ret.
  unfold bind.
  destruct (m s).
  break_match; auto.
  destruct u; auto.
Defined.

Lemma monad_comp : forall A B C S (m: St S A) (k:A -> St S B) (h:B -> St S C) (s:S),
    bind m (fun x => (bind (k x) h)) s = (bind (bind m k) h) s.
Proof.
  intros.
  unfold bind.
  destruct (m s).
  destruct o.
  - destruct (k a s0).
    destruct o.
    + destruct (h b s1).
      reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma gasd{A B:Type} : forall (act:St A B) (act2:St A B) st,
    (act ;; ret tt ;; act2) st =
    (act ;; act2) st.
Proof.
  intros.
  unfold ret.
  cbn.
  unfold bind.
  remember (act st) as ooo.
  destruct ooo.
  destruct o.
  - break_let. reflexivity.
  - reflexivity.
Defined.

Lemma fafa{A B:Type} : forall (act act2 act3: St A B) st,
    ((act;; ret tt;; act2);;
     act3) st =
    ((act;; act2);;
     act3) st.
Proof.
  intros.
  rewrite <- monad_comp.
  rewrite <- monad_comp.
  unfold ret.
  unfold bind.
  remember (act st) as oo.
  destruct oo.
  destruct o.
  remember (act2 a) as ooo.
  destruct ooo.
  destruct o.
  break_let.
  reflexivity.
  reflexivity.
  reflexivity.
Defined.

Lemma hlhl{A B:Type} : forall (act act2 act3 act4 : St A B) st,
    ((act;; act2;; act3);;
     act4) st =
    (((act;; act2);; act3);;
     act4) st.
Proof.
  intros.
  unfold bind.
  remember (act st) as ooo.
  destruct ooo.
  destruct o.
  - remember (act2 a) as ooo.
    destruct ooo.
    destruct o.
    + remember (act3 a0) as ooo.
      destruct ooo.
      destruct o.
      ++ remember (act4 a1) as ooo.
         destruct ooo.
         reflexivity.
      ++ reflexivity.
    + reflexivity.
  - reflexivity.
Defined.

Lemma hghg{A B:Type} : forall (act act2 act3 act4 act5 : St A B) st,
    (((act;; act2;; act3);; act5);;
     act4) st =
    ((act;; act2;; act3);; act5;; act4) st.
Proof.
  intros.
  unfold bind.
  remember (act st) as ooo.
  destruct ooo.
  destruct o.
  - remember (act2 a) as ooo.
    destruct ooo.
    destruct o.
    + remember (act3 a0) as ooo.
      destruct ooo.
      destruct o.
      ++ remember (act5 a1) as ooo.
         destruct ooo.
         destruct o.
         +++
           remember (act4 a2) as ooo.
           destruct ooo.
           destruct o.
           reflexivity.
         
         reflexivity.
         +++ reflexivity.
      ++ reflexivity.
    + reflexivity.
  - reflexivity.
Defined.
