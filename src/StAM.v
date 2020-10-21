(*
Record representing the AM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Maps StructTactics Term.
Require Import Coq.Arith.EqNat.

Require Import List.
Import ListNotations.

Definition BS := nat.

Definition eqbPair{A B:Type}`{H:EqClass A}`{H':EqClass B} (p1:A*B) (p2:A*B) : bool :=
  match (p1,p2) with
  | ((a1,b1), (a2,b2)) => andb (eqb a1 a2) (eqb b1 b2)
  end.

Search beq_nat_true.
Check beq_nat_true.

Lemma beq_pair_true{A B:Type}`{H:EqClass A}`{H':EqClass B} : forall (p1 p2:(A*B)),
    eqbPair p1 p2 = true -> p1 = p2.
Proof.
  intros.
  unfold eqbPair in *.
  repeat break_let.
  assert (a = a0).
  {
    assert (eqb a a0 = true).
    {
      destruct (eqb a a0); try solve_by_inversion.
    }
    Check beq_nat_true.
    eapply eqb_leibniz; eauto.
  }
  
  assert (b = b0).
  {
        assert (eqb b b0 = true).
        {
          destruct (eqb b b0); try reflexivity.
          cbv in *.
          repeat break_let.
          break_if; solve_by_inversion.     
        }
    eapply eqb_leibniz; eauto.
  }
  subst.
  reflexivity.
Defined.

                                                             


Instance pair_EqClass{A B:Type}`{H:EqClass A}`{H':EqClass B} : EqClass (A*B) :=
  { eqb:= eqbPair;
    eqb_leibniz := beq_pair_true }.

Definition asp_map := MapC (Plc * ASP_ID) ASP_ID.
Definition sig_map := MapC Plc ASP_ID.

(* Specific AM monad state *)
Record AM_St : Type := mkAM_St
                         { am_nonceMap : MapC nat BS;
                           am_nonceId : nat;
                           st_aspmap : asp_map;
                           st_sigmap : sig_map(*;
                           checked : list nat*) }.

Definition empty_amst :=
  mkAM_St [] 0 [] [].
                                         
