Require Import Term_Defs_Core Manifest (*Copland_AC*) Manifest_Admits.
Require Import AbstractedTypes EqClass Eqb_Evidence.


Require Import StructTactics.
Require Import Lists.List.
Import ListNotations.



Definition Environment : Type :=  Plc -> (option Manifest).

Definition e_empty : Environment := (fun _ => None).
  
Definition e_update (m : Environment) (x : Plc) (v : (option Manifest)) :=
  fun x' => if eq_plc_dec x x' then v else m x'.

  
(* A System is all attestation managers in the enviornement *)
Definition System := list Environment.

(*
Definition can_measure_target (pol:AC_Policy) (tplc:Plc) (targid:TARG_ID): bool :=
  pol READ (targ_obj tplc targid).
  *)
Definition can_measure_target (pol:PolicyT) (tplc:Plc) (targid:TARG_ID) : bool 
  := true.






(* Helper lemma for proving equivalence of propositional vs boolean list membership.  TODO:  consider moving this somewhwere else? *)
Lemma existsb_eq_iff_In: forall `{H : EqClass ID_Type} l a,
    existsb (eqb a) l = true <-> In a l.
Proof.
  intros.
  split.
  -
    generalizeEverythingElse l.
    induction l; intros; simpl in *.
    +
      solve_by_inversion.
    +
      Search "||".
      (*
Bool.orb_prop: forall a b : bool, (a || b)%bool = true -> a = true \/ b = true
       *)
      find_apply_lem_hyp Bool.orb_prop.
      destruct H0.
      ++
        left.
        symmetry.
        apply eqb_leibniz.
        eassumption.
      ++
        right.
        eauto.
  -
    generalizeEverythingElse l.
    induction l; intros; simpl in *.
    +
      solve_by_inversion.
    +
      destruct H0.
      ++
        subst.
        assert (eqb a0 a0 = true).
        {
          apply eqb_leibniz.
          auto.
        }
        find_rewrite.
        eauto.
      ++
        assert (existsb (eqb a0) l = true) by eauto.
        find_rewrite.
        simpl.
 
        apply Bool.orb_true_r.
Qed.
