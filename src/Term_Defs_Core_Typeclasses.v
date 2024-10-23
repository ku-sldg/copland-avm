Require Import EqClass Term_Defs_Core.

Require Import StructTactics.

Definition eqb_ASP_PARAMS `{EqClass ASP_ID, EqClass ASP_ARGS, EqClass Plc, EqClass TARG_ID}
    (a1 a2 : ASP_PARAMS) : bool :=
  let '(asp_paramsC a1 la1 p1 t1) := a1 in
  let '(asp_paramsC a2 la2 p2 t2) := a2 in
  (eqb a1 a2) && (eqb la1 la2) && (eqb p1 p2) && (eqb t1 t2).

Global Instance EqClass_ASP_PARAMS `{EqClass ASP_ID, EqClass ASP_ARGS, EqClass Plc, EqClass TARG_ID} : EqClass ASP_PARAMS.
eapply Build_EqClass with (eqb := eqb_ASP_PARAMS).
induction x; destruct y; ff;
repeat rewrite Bool.andb_true_iff in *; ff;
repeat rewrite eqb_eq in *; ff.
Defined.

Fixpoint eqb_EvidenceT `{EqClass N_ID, EqClass ASP_PARAMS, EqClass Plc} (e1 e2 : EvidenceT) : bool :=
  match e1, e2 with
  | mt_evt, mt_evt => true
  | nonce_evt i, nonce_evt i' => eqb i i'
  | asp_evt p par e, asp_evt p' par' e' =>
    (eqb p p') && (eqb par par') && (eqb_EvidenceT e e')
  | left_evt e, left_evt e' => eqb_EvidenceT e e'
  | right_evt e, right_evt e' => eqb_EvidenceT e e'
  | split_evt e1 e2, split_evt e1' e2' =>
    eqb_EvidenceT e1 e1' && eqb_EvidenceT e2 e2'
  | _, _ => false
  end.

Global Instance EqClass_EvidenceT `{EqClass N_ID, EqClass Plc, EqClass ASP_PARAMS} : EqClass EvidenceT.
eapply Build_EqClass with (eqb := eqb_EvidenceT).
induction x, y; simpl in *; ff;
repeat rewrite Bool.andb_true_iff in *; ff;
repeat rewrite eqb_eq in *; ff;
try erewrite IHx in *; ff;
try erewrite IHx1, IHx2 in *; ff.
Defined.