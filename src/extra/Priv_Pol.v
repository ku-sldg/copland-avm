Require Import Term_Defs Term Eqb_Evidence.

Require Import StructTactics.

Require Import PeanoNat Coq.Program.Tactics.


(*
Inductive EvSubT: Evidence -> Evidence -> Prop :=
| evsub_refl_t : forall e : Evidence, EvSubT e e
| uuSubT: forall e e' i tid l tpl,
    EvSubT e e' ->
    EvSubT e (uu i l tpl tid e')
| ggSubT: forall e e' p,
    EvSubT e e' ->
    EvSubT e (gg p e')
| nnSubT: forall e e' i,
    EvSubT e e' ->
    EvSubT e (nn i e').
*)

Inductive req_evidence: AnnoTerm -> Plc -> Plc -> Evidence -> Evidence -> Prop :=
| is_req_evidence: forall annt t pp p q i e e',
    events annt pp e (req i p q t e') ->
    req_evidence annt pp q e e'.

Fixpoint check_req (t:AnnoTerm) (pp:Plc) (q:Plc) (e:Evidence) (e':Evidence): bool :=
  match t with
  | aatt r rp t' => (eqb_evidence e e' && (Nat.eqb q rp)) || (check_req t' rp q e e')
  | alseq r t1 t2 => (check_req t1 pp q e e') || (check_req t2 pp q (aeval t1 pp e) e')
  | abseq r s t1 t2 =>
    (check_req t1 pp q (splitEv_T_l s e) e') || (check_req t2 pp q (splitEv_T_r s e) e')
  | abpar r s t1 t2 =>
    (check_req t1 pp q (splitEv_T_l s e) e') || (check_req t2 pp q (splitEv_T_r s e) e')
  | _ => false
  end.

Lemma req_implies_check: forall t pp q e e',
    req_evidence t pp q e e' -> check_req t pp q e e' = true.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a.
    +
      cbn.
      inversion H.
      solve_by_inversion.
    +
      cbn.
      inversion H.
      solve_by_inversion.
    +     
      cbn.
      inversion H.
      solve_by_inversion.
    +     
      cbn.
      inversion H.
      solve_by_inversion.
  -
    
    invc H.
    invc H0; subst; cbn.
    +
      rewrite Bool.orb_true_iff.
      left.
      rewrite Bool.andb_true_iff.
      split.
      ++
        rewrite eqb_eq_evidence.
        tauto.
      ++
        apply Nat.eqb_refl.
    +
      rewrite Bool.orb_true_iff.
      right.
      eapply IHt.
      econstructor.
      eassumption.
  -
    cbn.
    invc H.
    invc H0.
    +
      rewrite Bool.orb_true_iff.
      left.
      eapply IHt1.
      econstructor.
      eassumption.
    +
      rewrite Bool.orb_true_iff.
      right.
      eapply IHt2.
      econstructor.
      eassumption.
  -
    cbn.
    invc H.
    invc H0.
    +
      rewrite Bool.orb_true_iff.
      left.
      eapply IHt1.
      econstructor.
      eassumption.
    +
      rewrite Bool.orb_true_iff.
      right.
      eapply IHt2.
      econstructor.
      eassumption.
  -
    cbn.
    invc H.
    invc H0.
    +
      rewrite Bool.orb_true_iff.
      left.
      eapply IHt1.
      econstructor.
      eassumption.
    +
      rewrite Bool.orb_true_iff.
      right.
      eapply IHt2.
      econstructor.
      eassumption.  
Defined.

Lemma check_implies_req: forall t pp q e e',
    check_req t pp q e e' = true -> req_evidence t pp q e e'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      cbn; try solve_by_inversion.
  -
    cbn in *.
      rewrite Bool.orb_true_iff in H.
      destruct H.
      +
        rewrite Bool.andb_true_iff in H.
        destruct_conjs.
        econstructor.
        rewrite eqb_eq_evidence in *.

        apply EqNat.beq_nat_true in H0.
        subst.
        eauto.
      +
        
        assert (req_evidence t n q e e') by eauto.
        invc H0.
        econstructor.
        econstructor.
        eassumption.
  -
    cbn in *. 
    rewrite Bool.orb_true_iff in H.
    destruct_conjs.
    destruct H.
    +
      assert (req_evidence t1 pp q e e') by eauto.
      invc H0.
      econstructor.
      apply evtslseql.
      eassumption.
    +
      assert (req_evidence t2 pp q (aeval t1 pp e) e') by eauto.
      invc H0.
      econstructor.
      apply evtslseqr.
      eassumption.
  -
    cbn in *.
    rewrite Bool.orb_true_iff in H.
    destruct_conjs.
    destruct H.
    +
      assert (req_evidence t1 pp q (splitEv_T_l s e) e') by eauto.
      invc H0.
      econstructor.
      apply evtsbseql.
      eassumption.
    +
      assert (req_evidence t2 pp q (splitEv_T_r s e) e') by eauto.
      invc H0.
      econstructor.
      apply evtsbseqr.
      eassumption.
  -
    cbn in *.
    rewrite Bool.orb_true_iff in H.
    destruct_conjs.
    destruct H.
    +
      assert (req_evidence t1 pp q (splitEv_T_l s e) e') by eauto.
      invc H0.
      econstructor.
      apply evtsbparl.
      eassumption.
    +
      assert (req_evidence t2 pp q (splitEv_T_r s e) e') by eauto.
      invc H0.
      econstructor.
      apply evtsbparr.
      eassumption.
Defined.


(*

(* priv_pol p e --> allow place p to receive evidence with shape e *)
Definition priv_pol := Plc -> Evidence -> Prop.

Check priv_pol.

Definition satisfies_policy (t:AnnoTerm) (pp:Plc) (ee:Evidence)
           (q:Plc) (es:Evidence) (pol:priv_pol) :=
  req_evidence t pp ee q es -> (pol q es).

Definition test_term: Term := att 1 (asp CPY).
Definition test_term_anno := annotated test_term.
Compute test_term_anno.

Definition test_init_evidence := uu 1 [] 42 442 mt.
Definition test_init_evidence2 := uu 2 [] 42 442 mt.

Definition test_pol (p:Plc) (e:Evidence) :=
  match (p,e) with
  | (1, (uu 1 [] 42 442 mt)) => False
  | _ => True
  end.
    
    

Example test_term_satisfies_test_pol: forall pp ee q,
    satisfies_policy test_term_anno pp ee q mt test_pol.
Proof.
  intros.
  cbn.
  unfold test_init_evidence.
  unfold satisfies_policy.
  intros.
  unfold test_pol.
  cbv.
  intros.
  invc H.
  inv H1.
  auto.
  invc H1.
  auto.
  solve_by_inversion.
Qed.
*)
