Require Import Defs Term_Defs List_Facts AnnoFacts.
Require Import Preamble More_lists StructTactics Term_Facts.

Require Import Compare_dec Coq.Program.Tactics.

Require Import Lia.

Require Import List.
Import List.ListNotations.

Set Nested Proofs Allowed.

Lemma wf_lseq_pieces: forall r lr t1 t2,
    well_formed (alseq r lr t1 t2) ->
    well_formed t1 /\ well_formed t2.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Lemma wf_at_pieces: forall t r lr locs p,
    well_formed (aatt locs r lr p t) ->
    well_formed_r t.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Lemma wf_bseq_pieces: forall r lr s t1 t2,
    well_formed (abseq r lr s t1 t2) ->
    well_formed t1 /\ well_formed t2.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Lemma wf_bpar_pieces: forall r lr (*xlocs*) ylocs s t1 t2,
    well_formed (abpar r lr (*xlocs*) ylocs s t1 t2) ->
    well_formed t1 /\ well_formed t2.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Ltac do_wf_pieces :=
  match goal with
  | [H: well_formed (alseq _ _ _ _) |- _] =>
    (edestruct wf_lseq_pieces; eauto)
  | [H: well_formed (aatt _ _ _ _ ?t) |- _] =>   
    assert (well_formed t)
      by (eapply wf_at_pieces; eauto)
  | [H: well_formed (abseq _ _ _ _ _) |- _] =>
    (edestruct wf_bseq_pieces; eauto)
  | [H: well_formed (abpar _ _ _ _ _ _) |- _] =>
    (edestruct wf_bpar_pieces; eauto)     
  end.

Lemma well_formed_range_r:
  forall t,
    well_formed_r t ->
    snd (range t) = fst (range t) + esize t.
Proof.
    induction t;
    try (intros H; simpl; inv H; simpl;
         repeat find_apply_hyp_hyp; lia).
Defined.

Lemma well_formed_range:
  forall t,
    well_formed t ->
    snd (range t) = fst (range t) + esize t.
Proof.
  induction t;
    try (intros H; simpl; inv H; simpl;
    repeat find_apply_hyp_hyp; lia).
  -
    intros H.
    inv H.
    eapply well_formed_range_r.
    econstructor; eauto.
Defined.

Lemma well_formed_lrange:
  forall t,
    well_formed t ->
    length (lrange t) >= anss t.
Proof.
  induction t; intros H;
    try (simpl; inv H; simpl; repeat concludes; lia).

Lemma esize_nonempty: forall t, esize t > 0.
Proof.
  intros.
  induction t; intros;
    try (destruct a);
    (cbn; lia).
Defined.

Lemma wf_mono: forall t,
    well_formed t ->
    snd (range t) > fst (range t).
Proof.
  intros.
  rewrite well_formed_range.
  pose (esize_nonempty t).
  lia.
  eauto.
Defined.

Ltac do_mono :=
  (* let asdff := eapply anno_mono; eauto in *)
  match goal with
  | [H: anno _ ?x _ _ = Some (?y,_) |- _] => assert_new_proof_by (y > x) ltac:(eapply anno_mono; eauto)
  end.

Lemma asp_lrange_irrel: forall a i l l2 a0 a1 n n' b,
    anno (asp a) i l b = Some (n, a0) ->
    anno (asp a) i l2 b= Some (n',a1) ->
    a0 = a1.
Proof.
  intros.
  destruct a; ff.
Defined.

(*
Ltac list_facts :=
  do_firstn_skipn_len;
  do_anno_some_fact;
  do_firstn_factt;
  do_firstn_skipn;
  nodup_list_firstn;
  nodup_list_skipn;
  do_nodup_firstn;
  do_nodup_skipn;
  do_nodup_contra.
 *)
Locate list_facts.

Ltac wf_hammer :=
  ff;
  do_nodup;
  try (eapply anno_well_formed_r; eauto; tauto);
  repeat do_mono;
  repeat erewrite anno_range;
  try tauto;
  try lia;
  eauto;
  tauto.

Lemma nodup_lrange: forall t i ls n a,
    NoDup ls ->
    anno t i ls true = Some (n, a) ->
    NoDup (lrange a).
Proof.
  induction t; intros;
    do_nodup.
Defined.

Lemma anno_firstn_nss: forall t i ls n a,
    anno t i (firstn (nss t) ls) true = Some (n, a) ->
    (length (firstn (nss t) ls) = nss t).
Proof.
  intros.
  eapply firstn_factt.
  eapply anno_some_fact; eauto.
Defined.

Lemma anno_well_formed:
  forall t i j ls t',
    length ls = nss t ->
    NoDup ls ->
    anno t i ls true = Some (j, t') ->
    well_formed t'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    ff.
  -
    ff.
    econstructor;
      wf_hammer.
  -
    ff.
    list_facts.

    econstructor;
      try (wf_hammer);
      try (eauto; tauto).

    assert (list_subset (firstn (nss t1) ls) ls).
    {
      eapply firstn_subset; eauto.
    }

    unfold list_subset in *.
    
    eapply incl_tran; try eassumption;
      eapply anno_lrange'; eauto.

    assert (list_subset (skipn (nss t1) ls) ls).
    {
      eapply skipn_subset; eauto.
    }

    unfold list_subset in *.

    eapply incl_tran; try eassumption;
      eapply anno_lrange'; eauto.

    assert (list_subset (lrange a) (firstn (nss t1) ls)).
    {
      eapply anno_lrange'; eauto.
    }

    assert (list_subset (lrange a0) (skipn (nss t1) ls)).
    {
      eapply anno_lrange'; eauto.
    }

    eapply nodup_append.

    assert (NoDup (firstn (nss t1) ls)).
    {
      eapply nodup_firstn; eauto.
    }
    
    eapply nodup_lrange; eassumption.

    assert (NoDup (skipn (nss t1) ls)).
    {
      eapply nodup_skipn; eauto.
    }

    eapply nodup_lrange; eassumption.

    unfold disjoint_lists.
    intros.

    ff.

    assert (NoDup (firstn (nss t1) ls ++ skipn (nss t1) ls)) by congruence.
    ff'.
    repeat find_apply_hyp_hyp.
    list_facts.

  -
    ff.
    list_facts.

    econstructor;
      try (wf_hammer);
      try (eauto; tauto).

    assert (list_subset (firstn (nss t1) ls) ls).
    {
      eapply firstn_subset; eauto.
    }

    unfold list_subset in *.
    
    eapply incl_tran; try eassumption;
      eapply anno_lrange'; eauto.

    assert (list_subset (skipn (nss t1) ls) ls).
    {
      eapply skipn_subset; eauto.
    }

    unfold list_subset in *.

    eapply incl_tran; try eassumption;
      eapply anno_lrange'; eauto.

    assert (list_subset (lrange a) (firstn (nss t1) ls)).
    {
      eapply anno_lrange'; eauto.
    }

    assert (list_subset (lrange a0) (skipn (nss t1) ls)).
    {
      eapply anno_lrange'; eauto.
    }

    eapply nodup_append.

    assert (NoDup (firstn (nss t1) ls)).
    {
      eapply nodup_firstn; eauto.
    }
    
    eapply nodup_lrange; eassumption.

    assert (NoDup (skipn (nss t1) ls)).
    {
      eapply nodup_skipn; eauto.
    }

    eapply nodup_lrange; eassumption.

    unfold disjoint_lists.
    intros.


    ff'.
    repeat find_apply_hyp_hyp.
    assert (NoDup (firstn (nss t1) ls ++ skipn (nss t1) ls)) by congruence.
    list_facts.
  -

    ff.
    list_facts.

    econstructor;
      try (wf_hammer; tauto);
      try (ff'; eauto; tauto).

    +
    assert (list_subset (firstn (nss t1) l0) l0).
    {
      eapply firstn_subset; eauto.
    }

    unfold list_subset in *.
    eapply incl_tran; eauto.
    

    eapply anno_lrange'; eauto.
    repeat right; eauto.

    +
    assert (list_subset (skipn (nss t1) l0) l0).
    {
      eapply skipn_subset; eauto.
    }

    unfold list_subset in *.
    eapply incl_tran; eauto.
    
    eapply anno_lrange'; eauto.
    repeat right; eauto.
    
    +
      ff'.
    assert ( (n1 :: n2 (*:: n3 :: n4*) :: lrange a ++ lrange a0) =
             [n1 ; n2 (*; n3 ; n4*)] ++ (lrange a ++ lrange a0)) as HH.
    tauto.
    rewrite HH; clear HH.

    assert (list_subset (lrange a0) (skipn (nss t1) l0))
      by (eapply anno_lrange'; eauto).

    assert (list_subset (lrange a) (firstn (nss t1) l0))
          by (eapply anno_lrange'; eauto).

    eapply nodup_append.
    ++
      do_nodup.
    ++
      eapply nodup_append.
      +++
        eapply nodup_lrange.
        2: { eassumption. }
        eassumption.
      +++
        eapply nodup_lrange.
         2: { eassumption. }
        eassumption.       
      +++
        unfold disjoint_lists; intros.
        
        assert (NoDup (firstn (nss t1) l0 ++ skipn (nss t1) l0)) by congruence.
        ff'.
        repeat find_apply_hyp_hyp.
        list_facts.
    ++
      unfold disjoint_lists; intros.

      assert (list_subset (lrange a) l0).
      {  
        assert (list_subset (firstn (nss t1) l0) l0).
        {
          eapply firstn_subset.
        }
        
        unfold list_subset in *.
        eapply incl_tran; eauto.
      }
   
      assert (list_subset (lrange a0) l0).
      {

        assert (list_subset (skipn (nss t1) l0) l0).
        {
          eapply skipn_subset.
        }

        unfold list_subset in *.
        eapply incl_tran; eauto.
      }
      
      assert (list_subset ((lrange a) ++ (lrange a0)) l0).
      {
        eapply list_subset_app; eauto.
      }

      assert (In x l0) by ff'.
      
      do_nodup.      
Defined.

Lemma anno_well_formed':
  forall t ls,
    length ls = nss t ->
    NoDup ls ->
    well_formed (annotated t ls).
Proof.
  intros.
  edestruct anno_some with (t := t) (i:=0).
  eassumption.
  destruct x.
  (*
  destruct p. *)
  unfold annotated.
  unfold anno'.
  simpl.
  rewrite H1.
  simpl.
  eapply anno_well_formed.
  eassumption.
  eassumption.
  eassumption.
Defined.

(** Eval for annotated terms. *)

Fixpoint aeval t p e :=
  match t with
  | aasp _ _ x => eval (asp x) p e
  | aatt _ _ _ q x => aeval x q e
  | alseq _ _ t1 t2 => aeval t2 p (aeval t1 p e)
  | abseq _ _ s t1 t2 => ss (aeval t1 p ((splitEv_T (fst s)) e))
                         (aeval t2 p ((splitEv_T (snd s)) e)) 
  | abpar _ _ _ s t1 t2 => pp (aeval t1 p ((splitEv_T (fst s)) e))
                         (aeval t2 p ((splitEv_T (snd s)) e))
  end. 

(*
Lemma eval_aeval:
  forall t p e i loc,
    eval t p e = aeval (snd (snd ((anno t i loc)))) p e.
Proof.
  induction t; intros; simpl; auto;
    repeat expand_let_pairs; simpl;
      try (repeat jkjk; auto;congruence);
      try (repeat jkjk'; auto).
Defined.
*)

(** This predicate specifies when a term, a place, and some initial
    evidence is related to an event.  In other words, it specifies the
    set of events associated with a term, a place, and some initial
    evidence. *)

Inductive events: AnnoTerm -> Plc -> Ev -> Prop :=
| evtscpy:
    forall r lr i p,
      fst r = i ->
      events (aasp r lr CPY) p (copy i p)
| evtsusm:
    forall i id args r lr p,
      fst r = i ->
      events (aasp r lr (ASPC id args)) p (umeas i p id args)
| evtssig:
    forall r lr i p,
      fst r = i ->
      events (aasp r lr SIG) p (sign i p) 
| evtshsh:
    forall r lr i p,
      fst r = i ->
      events (aasp r lr HSH) p (hash i p)
| evtsattreq:
    forall r lr q t i p req_loc rpy_loc,
      fst r = i ->
      events (aatt r lr (req_loc, rpy_loc) q t) p (req i req_loc p q (unanno t))
| evtsatt:
    forall r lr q t ev p locs,
      events t q ev ->
      events (aatt r lr locs q t) p ev
| evtsattrpy:
    forall r lr q t i p req_loc rpy_loc,
      snd r = S i ->
      events (aatt r lr (req_loc, rpy_loc) q t) p (rpy i rpy_loc p q)
| evtslseql:
    forall r lr t1 t2 ev p,
      events t1 p ev ->
      events (alseq r lr t1 t2) p ev
| evtslseqr:
    forall r lr t1 t2 ev p,
      events t2 p ev ->
      events (alseq r lr t1 t2) p ev
| evtsbseqsplit:
    forall r lr i s t1 t2 p,
      fst r = i ->
      events (abseq r lr s t1 t2) p
             (Term_Defs.split i p)
| evtsbseql:
    forall r lr s t1 t2 ev p,
      events t1 p ev ->
      events (abseq r lr s t1 t2) p ev
| evtsbseqr:
    forall r lr s t1 t2 ev p,
      events t2 p ev ->
      events (abseq r lr s t1 t2) p ev
| evtsbseqjoin:
    forall r lr i s t1 t2 p,
      snd r = S i ->
      events (abseq r lr s t1 t2) p
             (join i p)

| evtsbparsplit:
    forall r lr i s t1 t2 p (*xi xi'*) yi yi',
      fst r = i ->
      events (abpar r lr (*(xi,xi')*) (yi,yi') s t1 t2) p
             (splitp i (*xi*) yi p)
| evtsbparl:
    forall r lr s t1 t2 ev p (*xlocs*) ylocs,
      events t1 p ev ->
      events (abpar r lr (*xlocs*) ylocs s t1 t2) p ev
| evtsbparr:
    forall r lr s t1 t2 ev p (*xlocs*) ylocs,
      events t2 p ev ->
      events (abpar r lr (*xlocs*) ylocs s t1 t2) p ev
| evtsbparjoin:
    forall r lr i s t1 t2 p (*xi xi'*) yi yi',
      snd r = S i ->
      events (abpar r lr (*(xi,xi')*) (yi,yi') s t1 t2) p
             (* TODO: fix joinp event *)
             (joinp i (*(xi')*) yi' (yi') p).
Hint Constructors events : core.

(*
Lemma events_range_r:
  forall t v p,
    well_formed_r t ->
    events t p v ->
    fst (range t) <= ev v < snd (range t).
Proof.
    (*
  intros t v p H H0.
  pose proof H as G.
  apply well_formed_range_r in G.
  rewrite G.
  clear G.
  induction H0; inv H; simpl in *; auto;
    try (repeat find_apply_hyp_hyp;
         repeat (find_apply_lem_hyp well_formed_range); lia).
     *)
Admitted.
 *)

Ltac inv_wfr :=
  match goal with
  | [H: well_formed_r _ |- _] => inv H
  end.

Lemma events_range:
  forall t v p,
    well_formed_r t ->
    events t p v ->
    fst (range t) <= ev v < snd (range t).
Proof.
  
  intros t v p H H0.
  pose proof H as G.
  apply well_formed_range_r in G.
  rewrite G.
  clear G.
  induction H0;
    try (inv_wfr; simpl in *; auto;
         repeat find_apply_hyp_hyp;
         repeat (find_apply_lem_hyp well_formed_range_r); lia).
Defined.

Lemma at_range:
  forall x r i,
    S (fst r) = fst x ->
    snd r = S (snd x) ->
    fst r <= i < snd r ->
    i = fst r \/
    fst x <= i < snd x \/
    i = snd x.
Proof.
  intros.
  pose proof lt_dec i (S (fst r)) as G.
  destruct G as [G|G]; [left; lia| right].
  pose proof lt_dec i (snd x) as F.
  destruct F as [F|F]; [left; lia| right].
  lia.
Qed.

Lemma lin_range:
  forall x y i,
    snd x = fst y ->
    fst x <= i < snd y ->
    fst x <= i < snd x \/
    fst y <= i < snd y.
Proof.
  intros.
  pose proof lt_dec i (snd x) as G.
  destruct G; lia.
Qed.

Lemma bra_range:
  forall x y r i,
    S (fst r) = fst x ->
    snd x = fst y ->
    snd r = S (snd y) ->
    fst r <= i < snd r ->
    i = fst r \/
    fst x <= i < snd x \/
    fst y <= i < snd y \/
    i = snd y.
Proof.
  intros.
  pose proof lt_dec i (S (fst r)) as G.
  destruct G as [G|G]; [left; lia| right].
  pose proof lt_dec i (snd x) as F.
  destruct F as [F|F]; [left; lia| right].
  pose proof lt_dec i (snd y) as E.
  destruct E; lia.
Qed.

(** Properties of events. *)

Lemma events_range_event:
  forall t p i,
    well_formed_r t ->
    fst (range t) <= i < snd (range t) ->
    exists v, events t p v /\ ev v = i.
Proof.
  intros t p i H; revert i; revert p.
  induction H; intros; simpl in *.
  - destruct x; eapply ex_intro; split; auto;
      (*destruct r as [j k];*) simpl in *; lia.
  - find_eapply_lem_hyp at_range; eauto.
    (*eapply at_range in H2; eauto. *)

    Ltac dest_range :=
      match goal with
      | [H: (nat * nat) |- _] => destruct H
      end.

     Ltac dest_lrange :=
       match goal with
       | [H: LocRange |- _] => destruct H
       end.

     Ltac do_lin_range :=
      match goal with
      | [H: snd _ = fst _,
            H': fst _ <= ?n < snd _
         |- _] =>
        apply lin_range with (i:=n) in H; eauto
      end.

     Ltac do_bra_range :=
      match goal with
      | [H: snd _ = fst _,
            H': fst ?x <= ?n < snd ?x
         |- _] =>
        apply bra_range with (i:=n) (r:=x) in H; eauto
      end.

     repeat dest_range;
    
        
    (* destruct r; destruct locs. *)
    repeat destruct_disjunct; subst; eauto.
    (* + eapply ex_intro; split; auto. *)

    + 
      find_eapply_hyp_hyp.
      (*apply IHwell_formed with (p:=p) in H2. *)
      destruct_conjs.
      eauto.
      (*
      destruct H2 as [v].
      destruct H2; subst.
      exists v; split; eauto. 
    + eapply ex_intro; split.
      apply evtsattrpy; auto.
      * rewrite H1; auto.
      * simpl; auto.
      *)
      
  -

    do_lin_range;       
    (*eapply lin_range with (i:=i) in H2; *) eauto;
    repeat destruct_disjunct;
      try lia;
      try (find_eapply_hyp_hyp; eauto;
        destruct_conjs;
        eauto).
  -
     do_bra_range;
    (* apply bra_range with (i:=i) (r:=r) in H2; *) eauto;
      repeat destruct_disjunct; subst;
        try lia;
        try (find_eapply_hyp_hyp; eauto;
             destruct_conjs;
             eauto; tauto).
      

    + eapply ex_intro; split; try (auto; eauto;tauto).
    + eapply ex_intro; split; try (eauto; auto; tauto).

  -
    repeat dest_range;
      do_bra_range;
      (*
    destruct xlocs; destruct ylocs.
    apply bra_range with (i:=i) (r:=r) in H2; *) eauto;
      repeat destruct_disjunct; subst;
        try lia;
        try (find_eapply_hyp_hyp; eauto;
             destruct_conjs;
             eauto; tauto).

    + eapply ex_intro; split; auto.
    + eapply ex_intro; split; eauto.
Qed.

Ltac events_event_range :=
  repeat match goal with
         | [ H: events _ _ _ |- _ ] =>
           apply events_range in H; auto
         end; lia.

Ltac aba :=
  match goal with
  | [H: events _ _ _, H': events _ _ _ |- _] => inv H; inv H'
  end.

Ltac wfr :=
  match goal with
  | [(*H: AnnoTerm,*) H': well_formed_r ?HH |- _] => pose_new_proof (well_formed_range_r HH H')
  end.

Lemma events_injective:
  forall t p v1 v2,
    well_formed_r t ->
    events t p v1 ->
    events t p v2 ->
    ev v1 = ev v2 ->
    v1 = v2.
Proof.
  intros.
  generalizeEverythingElse H.
  (*
  intros t p v1 v2 H; revert v2; revert v1;
    revert p. *)
  induction H; intros;
    try (
        repeat wfr;
        aba; simpl in *; subst; auto;
        try (events_event_range; tauto);
        try (find_eapply_hyp_hyp; eauto);
        eauto).
Qed.

(*
repeat find_apply_lem_hyp well_formed_range.

find_apply_lem_hyp well_formed_range.
find_apply_lem_hyp well_formed_range
apply well_formed_range in G.
apply well_formed_range in G0.
Check well_formed_range.
 *)


Inductive splitEv_T_R : SP -> Evidence -> Evidence -> Prop :=
| spAll: forall e, splitEv_T_R ALL e e
| spNone: forall e, splitEv_T_R NONE e mt.

Inductive evalR : Term -> Plc -> Evidence -> Evidence -> Prop :=
| evalR_asp: forall a p e,
    evalR (asp a) p e (eval_asp a p e)
| evalR_att: forall t1 q e e' p,
    evalR t1 q e e' ->
    evalR (att q t1) p e e'
| evalR_lseq: forall t1 t2 p e e' e'',
    evalR t1 p e e' ->
    evalR t2 p e' e'' ->
    evalR (lseq t1 t2) p e e''
| evalR_bseq: forall s e e1 e2 e1' e2' p t1 t2,
    splitEv_T_R (fst s) e e1 ->
    splitEv_T_R (snd s) e e2 ->
    evalR t1 p e1 e1' ->
    evalR t2 p e2 e2' ->
    evalR (bseq s t1 t2) p e (ss e1' e2')
| evalR_bpar: forall s e e1 e2 e1' e2' p t1 t2,
    splitEv_T_R (fst s) e e1 ->
    splitEv_T_R (snd s) e e2 ->
    evalR t1 p e1 e1' ->
    evalR t2 p e2 e2' ->
    evalR (bpar s t1 t2) p e (pp e1' e2').

Ltac jkjke :=
  match goal with
  | [H: _ |-  _ ] => erewrite H; eauto
  end.
Ltac kjkj :=
  match goal with
  | [H: evalR ?t ?p ?e ?e' |- _] => assert_new_proof_by (eval t p e = e') eauto
  end.


Ltac do_split :=
  match goal with
  | [H: Split |- _] => destruct H
  end.
      
Ltac do_sp :=
  match goal with
  | [H: SP |- _] => destruct H
  end.

Lemma eval_iff_evalR: forall t p e e',
    evalR t p e e' <-> eval t p e = e'.
Proof.
  split.
  - (* -> case *)
    intros.
    generalize dependent p.
    generalize dependent e.
    generalize dependent e'.

    induction t; intros;
      try (
          inv H;
          simpl;
          repeat kjkj;
          

          try (do_split;
               repeat do_sp);
          try (inv H3; inv H4; reflexivity);
          repeat jkjk;
          eauto).

  (*try (
    inv H;
    simpl;
    repeat kjkj). *)
    
 (*         
    + destruct a; solve_by_inversion.
    + 
      inv H. simpl.
      eauto.
    + inv H.

      simpl.
      repeat kjkj.
      eauto.
      (*
      repeat jkjk.
      eauto. *)

    
    +
      inv H.
      simpl.
      repeat kjkj.

      do_split;
        do_sp;
        try (inv H3; inv H4; reflexivity).
    +
      inv H.
      simpl.
      repeat kjkj.
      
      do_split;
        do_sp;
        try (inv H3; inv H4; reflexivity).
*)
    

  - (* <- case *)
    intros.
    generalize dependent p.
    generalize dependent e.
    generalize dependent e'.

    induction t; intros;
      inv H;
      try (destruct a);
      try (do_split; repeat do_sp);
      repeat econstructor; eauto.
Defined.

