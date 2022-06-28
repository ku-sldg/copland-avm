(*
Experiments in stating "disclosure" properties of the CVM.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Anno_Term_Defs Term LTS Cvm_Impl Cvm_St Trace Main.

Require Import CvmSemantics Appraisal_Evidence Eqb_Evidence Auto.

Require Import StructTactics.

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.

Inductive discloses_to_remote: Ev -> (Plc*Evidence) -> Prop :=
| at_disclose: forall i p q t e,
    discloses_to_remote (req i p q t e) (q,e).

Inductive discloses_to_asp: Ev -> (Plc*ASP_ID*Evidence) -> Prop :=
| asp_disclose: forall i p asp_id args tpl tid e,
    discloses_to_asp
      (umeas i p (asp_paramsC asp_id args tpl tid) e)
      (p,asp_id,e).

Definition splitEv_mt (sp:SP) (e:Evidence) : Evidence :=
  match sp with
  | ALL => e
  | NONE => mt
  end.

Fixpoint term_discloses_to_remote (t:Term) (p:Plc) (e:Evidence) (r:(Plc*Evidence)) : bool :=
  match t with
  | att q t' => (Nat.eqb q (fst r)) && (eqb_evidence e (snd r)) ||
               (term_discloses_to_remote t' q e r)
  | lseq t1 t2 => (term_discloses_to_remote t1 p e r) ||
                 (term_discloses_to_remote t2 p (eval t1 p e) r)
  | bseq (sp1,sp2) t1 t2 => (term_discloses_to_remote t1 p (splitEv_mt sp1 e) r) ||
                           (term_discloses_to_remote t2 p (splitEv_mt sp2 e) r)
  | bpar (sp1,sp2) t1 t2 => (term_discloses_to_remote t1 p (splitEv_mt sp1 e) r) ||
                           (term_discloses_to_remote t2 p (splitEv_mt sp2 e) r)
  | _ => false
  end.

Lemma term_remote_disclosures_correct_events: forall t p e r annt ev,
    term_discloses_to_remote t p e r = false -> 
    annoP annt t ->
    events annt p e ev ->
    ~ (discloses_to_remote ev r).
Proof.
  intros.
  unfold not in *; intros.
  generalizeEverythingElse t.
  induction t; ff; intros.
  -
    invc H0.
    destruct_conjs.
    destruct a; ff.
    repeat find_inversion.
    invc H1.
    invc H2.
    invc H1.
    invc H2.
    invc H1.
    invc H2.
    invc H1.
    invc H2.
    invc H2.
    invc H1.
  -
    invc H0.
    destruct_conjs.
    invc H4.
    break_let.
    invc H6; simpl in *.
    rewrite Bool.orb_false_iff in H.
    destruct_conjs.


    (*
    
    assert ( andb (Nat.eqb p p1) (eqb_evidence e e0) = false).
    admit.
    assert (term_discloses_to_remote t p e (p1, e0) = false).
    admit. *)
    invc H1.
    +
    simpl in *.
    invc H2.
    rewrite PeanoNat.Nat.eqb_refl in H.
    assert (eqb_evidence e0 e0 = true).
    {
      apply eqb_eq_evidence. auto. }
    rewrite H1 in *.
    invc H.
    +
      eapply IHt.
      eassumption.
      econstructor. repeat eexists. eassumption.
      eassumption.
      eassumption.
    +
      simpl in *.
      solve_by_inversion.
  -

    rewrite Bool.orb_false_iff in H.
    destruct_conjs.

    (*
    
    assert (term_discloses_to_remote t1 p e r = false).
    admit.
    assert (term_discloses_to_remote t2 p (eval t1 p e) r = false).
    admit. *)
    invc H0.
    destruct_conjs.
    invc H5.
    repeat break_let.
    find_inversion.

    invc H1.
    + (* t1 case *)
      eapply IHt1.
      eassumption.
      econstructor. repeat eexists. eassumption.
      eassumption.
      eassumption.
    + (* t2 case *)
      eapply IHt2.
      eassumption.
      econstructor. repeat eexists. eassumption.
      
      assert (eval t1 p e = aeval a p e).
      {
        erewrite eval_aeval.
        rewrite Heqp1.
        simpl. tauto.
      }
      rewrite H1.
      eassumption.
      eassumption.
  -
    rewrite Bool.orb_false_iff in H.
    destruct_conjs.
    (*
    assert (term_discloses_to_remote t1 p (splitEv_mt s0 e) r = false).
    admit.
    assert (term_discloses_to_remote t2 p (splitEv_mt s1 e) r = false).
    admit.
     *)
    

    invc H0.
    destruct_conjs.
    invc H5.
    repeat break_let.
    ff.
    invc H1; ff.
    + (* t1 case *)
      destruct s0.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
    + (* t2 case *)
      destruct s0.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
  -
    rewrite Bool.orb_false_iff in H.
    destruct_conjs.
    (*
    assert (term_discloses_to_remote t1 p (splitEv_mt s0 e) r = false).
    admit.
    assert (term_discloses_to_remote t2 p (splitEv_mt s1 e) r = false).
    admit.
     *)
    

    invc H0.
    destruct_conjs.
    invc H5.
    repeat break_let.
    ff.
    invc H1; ff.
    + (* t1 case *)
      destruct s0.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
    + (* t2 case *)
      destruct s0.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
Qed.


Definition term_discloses_to_remotes (rs: list (Plc*Evidence)) (t:Term) (p:Plc) (e:Evidence) : bool :=
  existsb (term_discloses_to_remote t p e) rs.

Definition filter_remote_disclosures (rs: list (Plc*Evidence)) (p:Plc) (e:Evidence) (ts:list Term):
  list Term := filter (fun t => negb (term_discloses_to_remotes rs t p e)) ts.

Lemma hii{A:Type} : forall (f:A->bool) ls,
    existsb f ls = false ->
    forallb (fun r => negb (f r)) ls = true.
Proof.
  intros.
  generalizeEverythingElse ls.
  induction ls; intros.
  -
    ff.
  -
    ff.
    rewrite Bool.orb_false_iff in H.
    destruct_conjs.
    
    assert (negb (f a) = true).
    {
      rewrite H. tauto.
    }
    assert (forallb (fun r : A => negb (f r)) ls = true).
    eapply IHls. eassumption.
    rewrite H1. rewrite H2. tauto.
Qed.

Lemma filter_remote_disclosures_correct_events: forall rs p e ts ts' t annt r ev,
  filter_remote_disclosures rs p e ts = ts' ->
  In t ts ->
  annoP annt t ->
  events annt p e ev ->
  In r rs ->
  In t ts' -> 
  ~ (discloses_to_remote ev r).
(*  ~ (In t ts'). *)
Proof.
  Check term_remote_disclosures_correct_events.
  (*
     : forall (t : Term) (p : Plc) (e : Evidence) (r : Plc * Evidence) (annt : AnnoTerm) (ev : Ev),
       term_discloses_to_remote t p e r = false ->
       annoP annt t -> events annt p e ev -> ~ discloses_to_remote ev r
   *)
  Check filter_In.
  (*
     : forall (A : Type) (f : A -> bool) (x : A) (l : list A), In x (filter f l) <-> In x l /\ f x = true
   *)
  intros.
  unfold filter_remote_disclosures in *.

  eapply term_remote_disclosures_correct_events.
  3: { eassumption. }
  2: { eassumption. }

  rewrite <- H in H4. clear H.
  rewrite filter_In in H4.
  destruct_conjs. clear H.
  unfold term_discloses_to_remotes in *.
  Check existsb_exists.
  (*
     : forall (A : Type) (f : A -> bool) (l : list A),
       existsb f l = true <-> (exists x : A, In x l /\ f x = true)
   *)

  
  assert ((existsb (term_discloses_to_remote t p e) rs) = false).
  {
    rewrite <- Bool.negb_true_iff.
    eassumption.
  }
  clear H4.

  assert (forall x, In x rs -> term_discloses_to_remote t p e x = false).
  {
    intros.
    assert (forallb (fun r => negb (term_discloses_to_remote t p e r)) rs = true).
    {
      eapply hii.
      eassumption.
    }
    rewrite forallb_forall in H5.
      Search negb.
  (*
Bool.negb_false_iff: forall b : bool, negb b = false <-> b = true
Bool.negb_true_iff: forall b : bool, negb b = true <-> b = false
   *)
      rewrite <- Bool.negb_true_iff.
      eapply H5.
      eassumption.
  }

  eapply H4. eassumption.
Qed.

Lemma lts_refines_events: forall t p e tr ev,
  well_formed_r_annt t ->
  lstar (conf t p e) tr (stop p (aeval t p e)) ->
  In ev tr ->
  events t p e ev.
Proof.
  intros.
  eapply trace_events; eauto.
  eapply lstar_trace; eauto.
Qed.

(*
Lemma events_refines_lts: forall t p e tr ev,
    events t p e ev ->
    In ev tr ->
    lstar (conf t p e) tr (stop p (aeval t p e)).
Proof.
Admitted.
*)

Lemma filter_remote_disclosures_correct_cvm:
  forall rs p e ts ts' t annt r ev atp i i' bits bits' e' cvm_tr p',
  filter_remote_disclosures rs p e ts = ts' ->
  In t ts ->
  
  (* anno_parP atp t -> *)
  term_to_coreP t atp ->
  annoP_indexed annt t i i' ->
  copland_compileP atp
                   (mk_st (evc bits e) [] p i)
                   (Some tt)
                   (mk_st (evc bits' e') cvm_tr p' i') ->

  In ev cvm_tr ->
  
  In r rs ->
  In t ts' -> 
  ~ (discloses_to_remote ev r).
 (*  ~ (In t ts'). *)
Proof.
  intros.
  assert (events annt p e ev).
  {
    eapply lts_refines_events.
    -
      invc H2.
      eapply anno_well_formed_r.
      eassumption.
    -
      eapply cvm_refines_lts_events.
      +
        eassumption.
      +
        eassumption.
      +
        eassumption.
        
    -
      eassumption. 
  }
  
  eapply filter_remote_disclosures_correct_events; eauto.
  invc H2.
  econstructor.
  repeat eexists. eassumption.
Qed.




(* Start ASP disclosures definitions and facts *)


Fixpoint term_discloses_to_asp (t:Term) (p:Plc) (e:Evidence) (r:(Plc*ASP_ID*Evidence)) : bool :=
  match t with
  | asp (ASPC (asp_paramsC x _ _ _)) =>
    let '(rp,ri,re) := r in
    (Nat.eqb p rp) && (eqb_aspid x ri) && (eqb_evidence e re)
    
  | att q t' => (* (Nat.eqb q (fst r)) && (eqb_evidence e (snd r)) || *)
               (term_discloses_to_asp t' q e r)
  | lseq t1 t2 => (term_discloses_to_asp t1 p e r) ||
                 (term_discloses_to_asp t2 p (eval t1 p e) r)
  | bseq (sp1,sp2) t1 t2 => (term_discloses_to_asp t1 p (splitEv_mt sp1 e) r) ||
                           (term_discloses_to_asp t2 p (splitEv_mt sp2 e) r)
  | bpar (sp1,sp2) t1 t2 => (term_discloses_to_asp t1 p (splitEv_mt sp1 e) r) ||
                           (term_discloses_to_asp t2 p (splitEv_mt sp2 e) r)
  | _ => false
  end.


Lemma term_asp_disclosures_correct_events: forall t p e r annt ev,
    term_discloses_to_asp t p e r = false -> 
    annoP annt t ->
    events annt p e ev ->
    ~ (discloses_to_asp ev r).
Proof.
  intros.
  unfold not in *; intros.
  generalizeEverythingElse t.
  induction t; ff; intros.
  -
    invc H0.
    destruct_conjs.
    destruct a; ff.
    
    invc H1.
    invc H2.
    invc H1.
    invc H2.
    invc H1.
    invc H2.
    rewrite PeanoNat.Nat.eqb_refl in H.
     assert (eqb_evidence e0 e0 = true).
    {
      apply eqb_eq_evidence. auto. }
    rewrite H0 in *; clear H0.
    assert (eqb_aspid a0 a0 = true).
    {
      apply eqb_eq_aspid. auto.
    }
    rewrite H0 in *; clear H0.
    invc H.

    invc H1.
    invc H2.
    invc H1.
    invc H2.

  -
    invc H0.
    destruct_conjs.
    invc H4.
    break_let.
    invc H6; simpl in *.
    (*
    rewrite Bool.orb_false_iff in H.
    destruct_conjs. *)


    (*
    
    assert ( andb (Nat.eqb p p1) (eqb_evidence e e0) = false).
    admit.
    assert (term_discloses_to_remote t p e (p1, e0) = false).
    admit. *)
    invc H1.
    +
    simpl in *.
    invc H2.

    (*
    rewrite PeanoNat.Nat.eqb_refl in H.
    assert (eqb_evidence e0 e0 = true).
    {
      apply eqb_eq_evidence. auto. }
    rewrite H1 in *.
    invc H. *)
    +
      eapply IHt.
      eassumption.
      econstructor. repeat eexists. eassumption.
      eassumption.
      eassumption.
    +
      simpl in *.
      solve_by_inversion.
  -

    rewrite Bool.orb_false_iff in H.
    destruct_conjs.

    (*
    
    assert (term_discloses_to_remote t1 p e r = false).
    admit.
    assert (term_discloses_to_remote t2 p (eval t1 p e) r = false).
    admit. *)
    invc H0.
    destruct_conjs.
    invc H5.
    repeat break_let.
    find_inversion.

    invc H1.
    + (* t1 case *)
      eapply IHt1.
      eassumption.
      econstructor. repeat eexists. eassumption.
      eassumption.
      eassumption.
    + (* t2 case *)
      eapply IHt2.
      eassumption.
      econstructor. repeat eexists. eassumption.
      
      assert (eval t1 p e = aeval a0 p e).
      {
        erewrite eval_aeval.
        rewrite Heqp1.
        simpl. tauto.
      }
      rewrite H1.
      eassumption.
      eassumption.
  -
    rewrite Bool.orb_false_iff in H.
    destruct_conjs.
    (*
    assert (term_discloses_to_remote t1 p (splitEv_mt s0 e) r = false).
    admit.
    assert (term_discloses_to_remote t2 p (splitEv_mt s1 e) r = false).
    admit.
     *)
    

    invc H0.
    destruct_conjs.
    invc H5.
    repeat break_let.
    ff.
    invc H1; ff.
    + (* t1 case *)
      destruct s0.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
    + (* t2 case *)
      destruct s0.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
  -
    rewrite Bool.orb_false_iff in H.
    destruct_conjs.
    (*
    assert (term_discloses_to_remote t1 p (splitEv_mt s0 e) r = false).
    admit.
    assert (term_discloses_to_remote t2 p (splitEv_mt s1 e) r = false).
    admit.
     *)
    

    invc H0.
    destruct_conjs.
    invc H5.
    repeat break_let.
    ff.
    invc H1; ff.
    + (* t1 case *)
      destruct s0.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
    + (* t2 case *)
      destruct s0.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
Qed.





(*
Definition term_discloses_to_remotes (rs: list (Plc*Evidence)) (t:Term) (p:Plc) (e:Evidence) : bool :=
  existsb (term_discloses_to_remote t p e) rs.

Definition filter_remote_disclosures (rs: list (Plc*Evidence)) (p:Plc) (e:Evidence) (ts:list Term):
  list Term := filter (fun t => negb (term_discloses_to_remotes rs t p e)) ts.
*)


Definition term_discloses_to_asps (ls: list (Plc*ASP_ID*Evidence)) (t:Term) (p:Plc) (e:Evidence) : bool :=
  existsb (term_discloses_to_asp t p e) ls.

Definition filter_asp_disclosures (ls: list (Plc*ASP_ID*Evidence)) (p:Plc) (e:Evidence) (ts:list Term):
  list Term := filter (fun t => negb (term_discloses_to_asps ls t p e)) ts.





Lemma filter_asp_disclosures_correct_events: forall rs p e ts ts' t annt r ev,
  filter_asp_disclosures rs p e ts = ts' ->
  In t ts ->
  annoP annt t ->
  events annt p e ev ->
  In r rs ->
  In t ts' -> 
  ~ (discloses_to_asp ev r).
(*  ~ (In t ts'). *)
Proof.
  intros.
  unfold filter_asp_disclosures in *.

  eapply term_asp_disclosures_correct_events.
  3: { eassumption. }
  2: { eassumption. }

  rewrite <- H in H4. clear H.
  rewrite filter_In in H4.
  destruct_conjs. clear H.
  unfold term_discloses_to_asps in *.
  Check existsb_exists.
  (*
     : forall (A : Type) (f : A -> bool) (l : list A),
       existsb f l = true <-> (exists x : A, In x l /\ f x = true)
   *)

  
  assert ((existsb (term_discloses_to_asp t p e) rs) = false).
  {
    rewrite <- Bool.negb_true_iff.
    eassumption.
  }
  clear H4.

  assert (forall x, In x rs -> term_discloses_to_asp t p e x = false).
  {
    intros.
    assert (forallb (fun r => negb (term_discloses_to_asp t p e r)) rs = true).
    {
      eapply hii.
      eassumption.
    }
    rewrite forallb_forall in H5.
      Search negb.
  (*
Bool.negb_false_iff: forall b : bool, negb b = false <-> b = true
Bool.negb_true_iff: forall b : bool, negb b = true <-> b = false
   *)
      rewrite <- Bool.negb_true_iff.
      eapply H5.
      eassumption.
  }

  eapply H4. eassumption.
Qed.




Lemma filter_asp_disclosures_correct_cvm:
  forall rs p e ts ts' t annt r ev atp i i' bits bits' e' cvm_tr p',
  filter_asp_disclosures rs p e ts = ts' ->
  In t ts ->
  
  anno_parP atp t ->
  annoP_indexed annt t i i' ->
  copland_compileP atp
                   (mk_st (evc bits e) [] p i)
                   (Some tt)
                   (mk_st (evc bits' e') cvm_tr p' i') ->

  In ev cvm_tr ->
  
  In r rs ->
  In t ts' -> 
  ~ (discloses_to_asp ev r).
 (*  ~ (In t ts'). *)
Proof.
  intros.
  assert (events annt p e ev).
  {
    eapply lts_refines_events.
    -
      invc H2.
      eapply anno_well_formed_r.
      eassumption.
    -
      eapply cvm_refines_lts_event_ordering.
      +
        eassumption.
      +
        eassumption.
      +
        eassumption.
        
    -
      eassumption. 
  }
  
  eapply filter_asp_disclosures_correct_events; eauto.
  invc H2.
  econstructor.
  repeat eexists. eassumption.
Qed.








  



(*

(* Helper relation for "discloses" relation *)
Inductive asp_discloses: ASP -> Plc -> Evidence -> (Plc * Evidence) -> Prop :=
| cpy_dis: forall p e,
    asp_discloses CPY p e (p,e)
| asp_dis: forall p e args,
    asp_discloses (ASPC args) p e (p, (uu args p e))
| sig_dis: forall p e,
    asp_discloses SIG p e (p, (gg p e))
| hsh_dis: forall p e,
    asp_discloses HSH p e (p, (hh p e)).


(* Relation that specifies evidence disclosure.  Technically, it specifies the 
   TYPE of evidence disclosed to each place. 

   Parameters--  discloses t p e (q,e') says: executing phrase t at place p 
   with initial evidence type e discloses evidence type e' to place q.

   For example:

   discloses (att q t) p e (q,e) states that evidence of type e is disclosed
   to place q.  

*)
Inductive discloses: Term -> Plc -> Evidence -> (Plc * Evidence) -> Prop :=
| asp_discl: forall a p e v,
    asp_discloses a p e v ->
    discloses (asp a) p e v
| att_discl: forall t p q e v,
    discloses t q e v ->
    discloses (att q t) p e v
| lseq_discl_l: forall t1 t2 p e v,
    discloses t1 p e v ->
    discloses (lseq t1 t2) p e v
| lseq_discl_r: forall t1 t2 p e v,
    discloses t2 p (eval t1 p e) v ->
    discloses (lseq t1 t2) p e v
| bseq_discl_l: forall t1 t2 p e v sp2,
    discloses t1 p e v ->
    discloses (bseq (ALL, sp2) t1 t2) p e v
| bseq_discl_r: forall t1 t2 p e v sp1,
    discloses t2 p e v ->
    discloses (bseq (sp1, ALL) t1 t2) p e v
| bpar_discl_l: forall t1 t2 p e v sp2,
    discloses t1 p e v ->
    discloses (bpar (ALL, sp2) t1 t2) p e v
| bpar_discl_r: forall t1 t2 p e v sp1,
    discloses t2 p e v ->
    discloses (bpar (sp1, ALL) t1 t2) p e v.

*)
              
  
                                               
