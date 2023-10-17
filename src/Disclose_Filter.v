Require Import Term_Defs Anno_Term_Defs Term LTS Cvm_Impl Cvm_St Trace Main ConcreteEvidence.

Require Import CvmSemantics Appraisal_Evidence Eqb_Evidence Auto AbstractedTypes EqClass Helpers_CvmSemantics (* Disclose_Gen *) External_Facts Axioms_Io.

Require Import StructTactics.

Require Import ErrorStMonad_Coq.

Require Import Coq.Program.Tactics PeanoNat Lia.

Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)




Fixpoint orb_list (l:list bool) : bool :=
  match l with
  | nil => false
  | b::l => orb b (orb_list l)
  end.

Definition orb_list_alt (l:list bool) : bool := existsb (fun b => b) l.

Lemma orb_list_alt_eq : forall (l:list bool),
    orb_list l = orb_list_alt l.
Proof.
  intros.
  induction l; trivial.
Qed.

Definition term_discloses_to_remote_list (t:Term) (p:Plc) (e:Evidence) (l: list (Plc*Evidence)) : bool :=
  let bool_list := map (term_discloses_to_remote t p e) l in
  orb_list bool_list.

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
    +
    invc H1.
    invc H2.
    +
    invc H1.
    invc H2.
    +
      
    invc H1.
    invc H2.
    +
      
    invc H1.
    invc H2.
    +
      
    invc H2.
    invc H1.
    +
      invc H1.
      invc H2.
      
  - (* @ case *)
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

    assert (eqb_plc p1 p1 = true).
    {
      apply eqb_plc_refl.
    }
    assert (eqb_evidence e0 e0 = true).
    {
      apply eqb_evidence_refl.
    }
    repeat find_rewrite.
    simpl in *.
    solve_by_inversion.
    
    

    (*
    
    solve_by_inversion.
    
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
  (*In t ts -> *)
  annoP annt t ->
  events annt p e ev ->
  In r rs ->
  In t ts' -> 
  ~ (discloses_to_remote ev r).
(*  ~ (In t ts'). *)
Proof.

  (*
  Check term_remote_disclosures_correct_events.
   *)
  (*
     : forall (t : Term) (p : Plc) (e : Evidence) (r : Plc * Evidence) (annt : AnnoTerm) (ev : Ev),
       term_discloses_to_remote t p e r = false ->
       annoP annt t -> events annt p e ev -> ~ discloses_to_remote ev r
   *)

  (*
  Check filter_In.
   *)
  
  (*
     : forall (A : Type) (f : A -> bool) (x : A) (l : list A), In x (filter f l) <-> In x l /\ f x = true
   *)
  intros.
  unfold filter_remote_disclosures in *.

  eapply term_remote_disclosures_correct_events.
  3: { eassumption. }
  2: { eassumption. }

  rewrite <- H in H3. clear H.
  rewrite filter_In in H3.
  destruct_conjs. clear H.
  unfold term_discloses_to_remotes in *.

  (*
  Check existsb_exists.
   *)
  
  (*
     : forall (A : Type) (f : A -> bool) (l : list A),
       existsb f l = true <-> (exists x : A, In x l /\ f x = true)
   *)

  
  assert ((existsb (term_discloses_to_remote t p e) rs) = false).
  {
    rewrite <- Bool.negb_true_iff.
    eassumption.
  }
  clear H3.

  assert (forall x, In x rs -> term_discloses_to_remote t p e x = false).
  {
    intros.
    assert (forallb (fun r => negb (term_discloses_to_remote t p e r)) rs = true).
    {
      eapply hii.
      eassumption.
    }
    rewrite forallb_forall in H4.
    rewrite <- Bool.negb_true_iff.
    eapply H4.
    eassumption.
  }

  eapply H3. eassumption.
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
  forall rs p e ts ts' t annt r ev atp i i' bits bits' e' cvm_tr p' ac ac',
    filter_remote_disclosures rs p e ts = ts' ->
    In t ts' -> 
    term_to_coreP t atp ->
    annoP_indexed annt t i i' ->
    build_cvmP atp
                     (mk_st (evc bits e) [] p i ac)
                     (resultC tt)
                     (mk_st (evc bits' e') cvm_tr p' i' ac') ->
    
    In ev cvm_tr ->
    In r rs ->
    ~ (discloses_to_remote ev r).
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





(*



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

  term_to_coreP t atp ->
  (*anno_parP atp t -> *)
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
  
  eapply filter_asp_disclosures_correct_events; eauto.
  invc H2.
  econstructor.
  repeat eexists. eassumption.
Qed.


 *)