Require Import Maps StructTactics.

Require Import Coq.Arith.EqNat.



Definition eqbPair{A B:Type}`{H:EqClass A}`{H':EqClass B} (p1:A*B) (p2:A*B) : bool :=
  match (p1,p2) with
  | ((a1,b1), (a2,b2)) => andb (eqb a1 a2) (eqb b1 b2)
  end.

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
