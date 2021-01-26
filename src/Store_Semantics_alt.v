Require Import Defs Term_Defs Term StructTactics Event_system Term_system.

Require Import Lia Coq.Program.Tactics Coq.Program.Equality Coq.Arith.EqNat.

Require Import List.
Import List.ListNotations.

Set Nested Proofs Allowed.

(* 
(ev_sys_remote t p q) represents (abstractly) the events that occur 
at place q, originated by a request from place p for q to execute t *)
Definition ev_sys_remote (t:Term) (p:Plc) (q:Plc): EvSys Ev.
Admitted.
        
Fixpoint ev_sys (t: AnnoTerm) p: EvSys Ev :=
  match t with
  | aasp (i, j) lr x => leaf (i, j) (asp_event i x p)
  | aatt (i, j) lr (req_loc,rpy_loc) q x =>
    before (i, j)
      (leaf (i, S i) (req i req_loc p q (unanno x)))
      (before (S i, j)
              (* (ev_sys x q) *)
              (ev_sys_remote (unanno x) p q)
              (leaf (pred j, j) (rpy (pred j) rpy_loc p q)))
  | alseq r lr x y => before r (ev_sys x p)
                          (ev_sys y p)
  | abseq (i, j) lr s x y =>
    before (i, j)
           (leaf (i, S i)
                 (Term_Defs.split i p))
           (before (S i, j)
                   (before (S i, (pred j))
                           (ev_sys x p)
                           (ev_sys y p))
                   (leaf ((pred j), j)
                   (join (pred j) p)))
  | abpar (i, j) lr (xi,xi') (yi,yi') s x y =>
    before (i, j)
           (leaf (i, S i)
                 (splitp i xi yi p))
           (before (S i, j)
                   (merge (S i, (pred j))
                          (ev_sys x p)
                          (ev_sys y p))
                   (leaf ((pred j), j)
                   (joinp (pred j) xi' yi' p)))
  end.

(*
Definition remote_event: Term -> Plc -> Ev.
Admitted.
*)


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
             (*
| evtsatt:
    forall r lr q t (*ev*) p locs,
      events (aatt r lr locs q t) p (remote_event (unanno t) p)
      (*events t q ev -> 
      events (aatt r lr locs q t) p ev
       *)
*)
      
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
    forall r lr i s t1 t2 p xi xi' yi yi',
      fst r = i ->
      events (abpar r lr (xi,xi') (yi,yi') s t1 t2) p
             (splitp i xi yi p)
| evtsbparl:
    forall r lr s t1 t2 ev p xlocs ylocs,
      events t1 p ev ->
      events (abpar r lr xlocs ylocs s t1 t2) p ev
| evtsbparr:
    forall r lr s t1 t2 ev p xlocs ylocs,
      events t2 p ev ->
      events (abpar r lr xlocs ylocs s t1 t2) p ev
| evtsbparjoin:
    forall r lr i s t1 t2 p xi xi' yi yi',
      snd r = S i ->
      events (abpar r lr (xi,xi') (yi,yi') s t1 t2) p
             (joinp i (xi') (yi') p).
Hint Constructors events : core.


Inductive store_event: Ev -> Plc -> Loc -> Prop :=
| put_event: forall i x p q t, store_event (req i x p q t) p x
| put_event_spl: forall i xi yi p, store_event (splitp i xi yi p) p xi
| put_event_spr: forall i xi yi p, store_event (splitp i xi yi p) p yi
| get_event: forall i x p q, store_event (rpy i x p q) p x
| get_event_joinpl: forall i xi yi p, store_event (joinp i xi yi p) p xi
| get_event_joinpr: forall i xi yi p, store_event (joinp i xi yi p) p yi.

(*
Lemma wf_mono_locs: forall t,
    well_formed t ->
    fst (lrange t) <= snd (lrange t).
Proof.
  intros.
  rewrite Term.well_formed_lrange; eauto.
  lia.
Defined.
*)

Ltac inv_wf :=
  match goal with
  | [H: well_formed (aasp _ _ _) |- _] =>
    invc H
  | [H: well_formed (alseq _ _ _ _) |- _] =>
    invc H
  | [H: well_formed (aatt _ _ _ _ ?t) |- _] =>   
    invc H
  | [H: well_formed (abseq _ _ _ _ _) |- _] =>
    invc H
  | [H: well_formed (abpar _ _ _ _ _ _ _) |- _] =>
    invc H
  end.

Ltac inv_ev :=
  match goal with
  | [H: events (aasp _ _ _) _ _ |- _] =>
    invc H
  | [H: events (alseq _ _ _ _) _ _ |- _] =>
    invc H
  | [H: events (aatt _ _ _ _ _) _ _ |- _] =>   
    invc H
  | [H: events (abseq _ _ _ _ _) _ _ |- _] =>
    invc H
  | [H: events (abpar _ _ _ _ _ _ _) _ _ |- _] =>
    invc H
  end.

Ltac inv_ev' :=
  match goal with
  | [H: events (aasp _ _ _) _ _ |- _] =>
    inv H
  | [H: events (alseq _ _ _ _) _ _ |- _] =>
    inv H
  | [H: events (aatt _ _ _ _ _) _ _ |- _] =>   
    inv H
  | [H: events (abseq _ _ _ _ _) _ _ |- _] =>
    inv H
  | [H: events (abpar _ _ _ _ _ _ _) _ _ |- _] =>
    inv H
  end.

Ltac inv_ev2 :=
  match goal with
  | [H: events _ _ _,
     H': events _ _ _ |- _] =>
    invc H; invc H'
  end.

Ltac inv_ev2' :=
  match goal with
  | [H: events _ _ _,
     H': events _ _ _ |- _] =>
    inv H; inv H'
  end.

Ltac inv_se :=
  match goal with
  | [H: store_event (?C _) (*(req _ _ _ _ _)*) _ _ |- _] =>
    invc H
         (*
  | [H: events (alseq _ _ _ _) _ _ |- _] =>
    invc H
  | [H: events (aatt _ _ _ _ _) _ _ |- _] =>   
    invc H
  | [H: events (abseq _ _ _ _ _) _ _ |- _] =>
    invc H
  | [H: events (abpar _ _ _ _ _ _ _) _ _ |- _] =>
    invc H *)
  end.

Ltac inv_store_ev2 :=
  match goal with
  | [H: store_event _ _ _,
     H': store_event _ _ _ |- _] =>
    invc H; invc H'
  end.

Lemma nodup_contra': forall ls ls' (loc:nat),
    NoDup (ls ++ ls') ->
    In loc ls ->
    In loc ls' ->
    False.
Proof.
  intros.
  generalizeEverythingElse ls.

  (*
  generalize dependent H0.
  generalize dependent H1.
  generalize dependent loc.
  dependent induction H; intros.
   *)
  induction ls; destruct ls'; intros.
  -
    solve_by_inversion.
  -
    solve_by_inversion.
  -
    solve_by_inversion.
  -
    invc H0;
      invc H1;
      try solve_by_inversion.
    +
      invc H.
      unfold not in *.
      eapply H2.
      assert (ls ++ loc :: ls' = ls ++ (loc :: ls')).
      tauto.
      
      eapply in_or_app.
      right.
      simpl.
      tauto.
    +
      invc H.
      unfold not in *.
      eapply H3.
      eapply in_or_app.
      right.
      right.
      eassumption.
    +
      eapply IHls with (ls' := (loc :: ls')).

      invc H.
      eassumption.
      eassumption.
      econstructor.
      tauto.
    +
      invc H.
      unfold not in *.

      assert (NoDup (ls ++ ls')).
      {
        eapply NoDup_remove_1; eauto.
      }

      eauto.
Defined.

Lemma in_app: forall ls ls' (loc:nat),
    In loc ls ->
    In loc (ls ++ ls').
Proof.
  intros.
  eapply in_or_app; eauto.
Defined.

Lemma in_app2: forall ls ls' (loc:nat),
    In loc ls' ->
    In loc (ls ++ ls').
Proof.
  intros.
  eapply in_or_app; eauto.
Defined.

Ltac in_app_facts :=
  match goal with
  | [H: In ?loc (lrange ?t1),
        H': well_formed ?t1,
            H'': well_formed ?t2 |- _] =>
    try
      (assert_new_proof_by
         (In loc ((lrange t1) ++ (lrange t2)))
         ltac:(eapply in_app; eauto));
    try (assert_new_proof_by
           (In loc ((lrange t2) ++ (lrange t1)))
           ltac:(eapply in_app2; eauto))
  end.

Ltac nodup_contra_auto :=
  match goal with
  | [H: In ?loc ?ls,
        H': In ?loc ?ls',
            H'': NoDup (?ls ++ ?ls') |- _] =>
    exfalso; eapply nodup_contra'; eauto
  end.


Lemma event_in_lrange: forall t p ev loc,
    well_formed t ->
    events t p ev ->
    store_event ev p loc ->
    In loc (lrange t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      inv_ev;
      ff.
  -
    
    inv_wf.

    (*
    clear H12.
    clear H11.
     *)
    
    

    inv_ev'; ff.


    

    (*
    ff;
      inv_ev.
    +
      ff.
      (*
      assert (In req_loc l). admit.
      ff.
       *)
      
      (*
      inv H1.
      admit. *)
    +
      ff.
      (*
      assert (In rpy_loc l). admit.
      ff.
       *)
      
      (*
      ff.
      inv H1. *)
     *)
    
  -
    ff.
    inv_wf.
    (*
    clear H11.
    clear H12. *)
    inv_ev.
    +

      assert (In loc (lrange t1)) by eauto.

      (*

      assert (list_subset (lrange t1) l). admit.
       *)
      
      unfold list_subset in *.
      eauto.

      (*

      assert (l = (lrange t1) ++ (lrange t2)).
      admit.

      subst;
      in_app_facts; eauto. *)
    +
      assert (In loc (lrange t2)) by eauto.

      (*

      assert (list_subset (lrange t2) l). admit. *)
      unfold list_subset in *.
      eauto.

      
      (*

      assert (l = (lrange t1) ++ (lrange t2)).
      admit.

      subst;
        in_app_facts; eauto.
       *)
      

  -
    ff.
    inv_wf.
    (*
    clear H12. *)
    inv_ev;
      try solve_by_inversion.
    +
      assert (In loc (lrange t1)) by eauto.

      (*

      assert (list_subset (lrange t1) l). admit. *)
      unfold list_subset in *.
      eauto.

      (*

      assert (l = (lrange t1) ++ (lrange t2)).
      admit.

      subst;
      in_app_facts; eauto. *)
    +
      assert (In loc (lrange t2)) by eauto.

      (*

      assert (list_subset (lrange t2) l). admit.
       *)
      
      unfold list_subset in *.
      eauto.

      
      (*
      assert (l = (lrange t1) ++ (lrange t2)).
      admit.

      subst;
        in_app_facts; eauto.
       *)
      
  -
    ff.
    inv_wf.

    (*
    clear H19.
    clear H15.
    clear H16.
    clear H17.
    clear H18.
     *)
    
    

    
    inv_ev';
      try solve_by_inversion;
      try (eauto; tauto);
      try (ff; congruence).
    +
      ff.
      unfold list_subset in *.
      ff.
      repeat inv_se;
        ff'.
        
      
      (*
      
      assert (list_subset [xi; xi'; yi; yi'] l). admit.
      unfold list_subset in *.

      ff.
       *)

      (*
    +
      
      assert (list_subset (lrange t1) l). admit.
       
      
      unfold list_subset in *.
      eauto.

    +
      assert (list_subset (lrange t2) l). admit.
      unfold list_subset in *.
      eauto.
*)
    +

      (*
      assert (list_subset [xi; xi'; yi; yi'] l). admit.
       *)
      
      unfold list_subset in *.
      ff.

      repeat inv_se;
        ff'.
          
      ++
        repeat (find_apply_hyp_hyp').
        tauto.
Defined.

Ltac t_in_lrange :=
  match goal with
  | [H: events ?t ?p ?ev,
        H': store_event ?ev ?p ?loc |- _] =>
    assert_new_proof_by (In loc (lrange t)) ltac:(eapply event_in_lrange; eauto)
  end.

Lemma unique_store_event_locs: forall t p ev ev' loc,
    well_formed t ->
    events t p ev ->
    events t p ev' ->
    store_event ev p loc ->
    store_event ev' p loc ->
    ev = ev'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    inv_wf;
      inv_ev2;
      eauto.
  -
    inv_wf;
      inv_ev2;
       try (assert (req_loc = rpy_loc) by 
               (repeat inv_se; congruence));
          repeat inv_se;
          ff; congruence.
 
  -
    inv_wf.
    (*
    clear H13.
    clear H14.
     *)
    
    
    inv_ev2;
      try solve_by_inversion;
      try eauto;
      try (
           (* unfold list_subset in *;  *)
           repeat t_in_lrange;
           nodup_contra_auto; tauto).
 
  -
    inv_wf.
    inv_ev2;
      try solve_by_inversion;
      try eauto;
      try (
          repeat t_in_lrange;
          nodup_contra_auto; tauto).
  -
          Ltac nodup_inv :=
        repeat 
        match goal with
        | [H: NoDup (_::_) |- _] => invc H
        end.
    inv_wf.
    
    (* clear H21. *)
    (*clear H17; clear H18; clear H19; clear H20. *)
    inv_ev2;
      try solve_by_inversion;
      try (ff; congruence);
      try (eauto; tauto);
      try (repeat inv_se;
           repeat t_in_lrange;
           try in_app_facts;
           ff;
           nodup_inv;
           ff;
           try nodup_contra_auto;
           tauto).
Defined.

(*
Lemma evsys_reps: forall t p ev,
  ev_in ev (ev_sys t p) ->
  ev_in ev (Term_system.ev_sys t p).
Proof.
Admitted.

Lemma events_reps: forall t p ev,
  events t p ev ->
  Term.events t p ev.
Proof.
Admitted.
*)

Definition store_event_evsys es p loc := exists ev, store_event ev p loc /\ ev_in ev es.

Inductive store_conflict: Plc -> EvSys Ev -> Prop :=
| store_conflict_merge: forall r p es1 es2 loc,
    store_event_evsys es1 p loc ->
    store_event_evsys es2 p loc ->
    store_conflict p (merge r es1 es2)
| store_conflict_before_l: forall r p es1 es2,
    store_conflict p es1 ->
    store_conflict p (before r es1 es2)
| store_conflict_before_r: forall r p es1 es2,
    store_conflict p es2 ->
    store_conflict p (before r es1 es2).


Axiom ev_sys_iff_remote: forall t n p0,
    (ev_sys t n = ev_sys_remote (unanno t) p0 n).

Axiom no_nested_at_store_conflict: forall t p q,
    not (store_conflict p (ev_sys_remote t p q)).

Axiom events_remote: forall t p q ev n n' l loc loc',
    ev_in ev (ev_sys_remote (unanno t) p q) ->
    events (aatt (n, n') l (loc, loc') q t) p ev.

Lemma evsys_events:
  forall t p ev,
    well_formed_r t ->
    ev_in ev (ev_sys t p) <-> events t p ev.
Proof.
    split; revert p; induction t; intros; inv H; simpl in *;
    repeat break_let; simpl in *.
  - inv H0; auto; destruct a; simpl; auto.
  - destruct p.
    rewrite H8 in H0; simpl in H0.
    repeat find_inversion.
    inv H0; auto.

    inv H3; auto. inv H3; auto.
    +
      apply events_remote; eauto.
    +
      inv H4; auto.
  - inv H0; auto.
    
  - rewrite H10 in H0; simpl in H0.

    inv H0.

    inv H3.
    auto.

    inv H3.

    inv H3.

    auto.

    inv H4.
    auto.

   

    inv H5.

    auto.
    auto.

    inv H5.

    inv H5.

    auto.

    inv H4.
    inv H4.

    auto.
    
  - destruct p; destruct p0.
    rewrite H12 in H0; simpl in H0.
    inv H0; auto. inv H3; auto. inv H3; auto. inv H4; auto. inv H4; auto.
  - inv H0; auto.
  - rewrite H8; simpl.
    inv H0; auto.
    simpl in *.
    (*
    rewrite H11 in H8. *)
    assert (snd (range t) = i) by lia.
    subst.
    auto.
    (*
    apply Nat.succ_inj in H13; subst; auto. *)
  - inv H0; auto.
  - rewrite H10; simpl.
    inv H0; auto.
    simpl in H13.

    assert (snd (range t2) = i) by lia.
    subst.
    auto.

    
    (*
    rewrite H12 in H10. 
    apply Nat.succ_inj in H10; subst; auto. *)
    
  - rewrite H12; simpl.
    inv H0; auto.
    simpl in *.
    assert (snd (range t2) = i) by lia.
    subst.
    auto.

    (*
    rewrite H15 in H12.
    apply Nat.succ_inj in H12; subst; auto. *)

Qed.

Lemma wf_implies_wfr: forall t,
    well_formed t ->
    well_formed_r t.
Proof.
  induction t; intros.
  -
    destruct a; ff.
  -
    ff.
  -
    ff.
  -
    ff.
  -
    ff.
Defined.

Lemma unique_store_events': forall t p ev1 ev2 loc,
    well_formed t ->
    ev_in ev1 (ev_sys t p) ->
    ev_in ev2 (ev_sys t p) -> 
    store_event ev1 p loc ->
    store_event ev2 p loc ->
    ev1 <> ev2 ->
    False.
Proof.
  intros.
  assert (ev1 = ev2).
  {
    eapply unique_store_event_locs;
      try eassumption.
    Locate evsys_events.
    eapply evsys_events; eauto.
    eapply wf_implies_wfr; eauto.
    eapply evsys_events; eauto.
    eapply wf_implies_wfr; eauto.
  }
  congruence.
Defined.

Lemma unique_store_events_corollary: forall t p ev1 ev2 loc,
    well_formed t ->
    ev_in ev1 (ev_sys t p) -> 
    store_event ev1 p loc ->
    store_event ev2 p loc ->
    ev1 <> ev2 ->
    not (ev_in ev2 (ev_sys t p)).
Proof.
  intros.
  unfold not; intros.
  eapply unique_store_events'.
  eassumption.
  apply H0.
  apply H4.
  eassumption.
  eassumption.
  eassumption.
Defined.

Lemma unique_events': forall r es1 es2 ev1 ev2,
    well_structured ev (merge r es1 es2) ->
    ev_in ev1 es1 ->
    ev_in ev2 es2 ->
    ev ev1 <> ev ev2.
Proof.
  intros.
  inv H.
  assert (fst (es_range es1) <= ev ev1 < snd (es_range es1)).
  {
    eapply ws_evsys_range; eauto.
  }

  assert (fst (es_range es2) <= ev ev2 < snd (es_range es2)).
  {
    eapply ws_evsys_range; eauto.
  }

  lia.
Defined.

Lemma unqev: forall ev1 ev2,
  ev ev1 <> ev ev2 ->
  ev1 <> ev2.
Proof.
  intros.
  unfold not; intros.
  subst.
  solve_by_inversion.
Defined.

Lemma unique_events: forall r es1 es2 ev1 ev2,
    well_structured ev (merge r es1 es2) ->
    ev_in ev1 es1 ->
    ev_in ev2 es2 ->
    ev1 <> ev2.
Proof.
  intros.
  eapply unqev.
  eapply unique_events';
    eauto.
Defined.

Lemma  evsys_range
  : forall (t : AnnoTerm) (p : nat), es_range (ev_sys t p) = range t.
Proof.
  induction t; intros; simpl; auto;
    repeat break_let; simpl; auto.
Qed.

(*
Lemma ws_remote: forall t p0 ev n,
    well_structured ev (ev_sys t p0) ->
    well_structured ev (ev_sys_remote (unanno t) p0 n).
Proof.
Admitted.
*)

Lemma well_structured_evsys:
  forall t p,
    well_formed_r t ->
    well_structured ev (ev_sys t p).
Proof.
  induction t; intros; inv H; simpl;
    repeat break_let; destruct r as [i k];
      simpl in *; subst; auto.
  - apply ws_leaf_event; auto;
      destruct a; simpl; auto.
  - apply ws_before; simpl; auto.
    rewrite H6.

    assert (ev_sys t n = ev_sys_remote (unanno t) p0 n) as HH.
    {
      eapply ev_sys_iff_remote.
    }
    rewrite <- HH.

    apply ws_before; simpl; auto; rewrite evsys_range; auto.
    
  - apply ws_before; auto; repeat rewrite evsys_range; auto.
    
  - repeat (apply ws_before; simpl in *; auto; repeat rewrite evsys_range; auto).
    
  - repeat (apply ws_before; simpl in *; auto; repeat rewrite evsys_range; auto).
    repeat (apply ws_merge; simpl in *; auto; repeat rewrite evsys_range; auto).
Qed.

Theorem no_store_conflicts: forall t p sys,
    well_formed t ->
    sys = ev_sys t p ->
    not (store_conflict p sys).
Proof.
  unfold not; intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      cbn in *;
      repeat break_let;
      subst;
      solve_by_inversion.
  -
    destruct p.
    destruct r.

    (*
    assert (p0 <> n). admit.
     *)
    

    


    
    ff.
    subst.
    invc H1; ff.
    invc H3; ff.

    

    pose
      no_nested_at_store_conflict.
    unfold not in *.
    eauto.
  -
    ff.
    subst.
    invc H1;
      do_wf_pieces.
  -

      cbn in *;
      repeat break_let;
      subst.
    inv H1.
    +
      solve_by_inversion.
    +
      inv H3.
      ++
        inv H4;
          do_wf_pieces.
      ++
        solve_by_inversion.
  - assert (well_structured ev sys).
    {
      rewrite H0.
      eapply well_structured_evsys; eauto.
      eapply wf_implies_wfr; eauto.
      (*
      rewrite H0.
      eapply well_structured_evsys.
      eassumption. *)
    }
    
    cbn in *;
      repeat break_let;
      subst.
    inv H1;
      try solve_by_inversion.
    +
      inv H4;
        try solve_by_inversion.
      ++       
        inv H5;
          try solve_by_inversion.
        +++
          unfold store_event_evsys in *.
          destruct_conjs.

          assert (ev_in H7 (merge (S n, Nat.pred n0) (ev_sys t1 p1) (ev_sys t2 p1))).
          {
            eauto.
          }
          
          assert (ev_in H9 (merge (S n, Nat.pred n0) (ev_sys t1 p1) (ev_sys t2 p1))).
          {
            eauto.
          }

          eapply unique_store_events' with (ev1:=H7) (ev2:=H9) (t:=(abpar (n, n0) l (n1,n2) (n3,n4) s t1 t2)) (p:=p1) (loc:=loc);
            try eassumption;
            try (simpl; eauto; tauto).
          ++++  
            inv H2.
            inv H16.
            eapply unique_events; eauto.
Defined.

FAILHERE



    




      
    
    
  


(*

Create HintDb lr.

Lemma rpy_events_lrange (t:AnnoTerm) : forall p i p1 q loc,
    well_formed t ->
    events t p (rpy i loc p1 q) ->
    fst (lrange t) <= loc < snd (lrange t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
      try (
        cbn in *;
        inv_wf;
        inv_ev;
        simpl in *; subst;
        try lia;
        repeat (find_eapply_hyp_hyp);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia).
Defined.
Hint Resolve rpy_events_lrange : lr.

Lemma req_events_lrange (t:AnnoTerm) : forall p i p1 q t0 loc,
    well_formed t ->
    events t p (req i loc p1 q  t0) ->
    fst (lrange t) <= loc < snd (lrange t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try (
        cbn in *;
        inv_wf;
        inv_ev;
        simpl in *; subst;
        try lia;
        repeat (find_eapply_hyp_hyp);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia).
Defined.
Hint Resolve req_events_lrange : lr.

Lemma splitp_l_events_lrange (t:AnnoTerm) : forall p i p0 yi loc,
    well_formed t ->
    events t p (splitp i loc yi p0) ->
    fst (lrange t) <= loc < snd (lrange t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try (
        cbn in *;
        inv_wf;
        inv_ev;
        simpl in *; subst;
        try lia;
        repeat (find_eapply_hyp_hyp);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia).
Defined.
Hint Resolve splitp_l_events_lrange : lr.

Lemma splitp_r_events_lrange (t:AnnoTerm) : forall p i p0 xi loc,
    well_formed t ->
    events t p (splitp i xi loc p0) ->
    fst (lrange t) <= loc < snd (lrange t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try (
        cbn in *;
        inv_wf;
        inv_ev;
        simpl in *; subst;
        try lia;
        repeat (find_eapply_hyp_hyp);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia).
Defined.
Hint Resolve splitp_r_events_lrange : lr.

Lemma joinp_l_events_lrange (t:AnnoTerm) : forall p p0 i yi loc,
    well_formed t ->
    events t p (joinp i loc yi p0) ->
    fst (lrange t) <= loc < snd (lrange t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try (
        cbn in *;
        inv_wf;
        inv_ev;
        simpl in *; subst;
        try lia;
        repeat (find_eapply_hyp_hyp);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia).
Defined.
Hint Resolve joinp_l_events_lrange : lr.

Lemma joinp_r_events_lrange (t:AnnoTerm) : forall p p0 i xi loc,
    well_formed t ->
    events t p (joinp i xi loc p0) ->
    fst (lrange t) <= loc < snd (lrange t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try (
        cbn in *;
        inv_wf;
        inv_ev;
        simpl in *; subst;
        try lia;
        repeat (find_eapply_hyp_hyp);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia).
Defined.
Hint Resolve joinp_r_events_lrange : lr.

Lemma store_events_lrange (t:AnnoTerm) : forall p ev loc,
    well_formed t ->
    events t p ev ->
    store_event ev loc ->
    fst (lrange t) <= loc < snd (lrange t).
Proof.
  intros.
  inv H1;
    eauto with lr.
Defined.
*)

Ltac pose_store_events :=
  match goal with
  | [H: events _ _ ?ev,
        H': Loc |- _] =>
    assert_new_proof_by (store_event ev H') econstructor
  end.

(*
Ltac pose_new_lrange :=
  match goal with
  | [H: well_formed ?t,
        H': events ?t ?p ?ev,
            H'': store_event ?ev ?loc
     |- _] =>
    pose_new_proof (store_events_lrange t p ev loc H H' H'')
  end.
*)

Ltac pose_lrange_facts :=
  repeat pose_store_events
  (*repeat pose_new_lrange; 
  repeat find_eapply_lem_hyp wf_mono_locs*) .

Ltac dest_lrange :=
  match goal with
  | [H: LocRange |- _] => destruct H
  end.

Create HintDb rl.

Set Nested Proofs Allowed.

Lemma store_event_locs: forall t p ev loc,
    store_event ev loc ->
    events t p ev ->
    well_formed t ->
    In loc (lrange t).
Proof.
Admitted.

(* TODO:  check nodup_contra call sites *)
Lemma nodup_contra: forall (x (*y*): nat) ls ls',
    In x ls  ->
    In x (* y *) ls' ->
    NoDup (ls ++ ls') ->
    False.
Proof.
Admitted.

Lemma unique_req_locs: forall t p i i0 loc q q0 t0 t1,
    well_formed t ->
    events t p (req i  loc p q t0) ->
    events t p (req i0 loc p q0 t1) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    inv_wf.
    inv_ev2.
  -

    invc H.

    invc H0.
    invc H1.

    ff.
  -
    ff.

    inv H.

    invc H0.
    +
      invc H1.
      ++
        eauto.
      ++
        eauto.



        assert (In loc (lrange t1)).
        {
          eapply store_event_locs; eauto.
          econstructor.
        }

        assert (In loc (lrange t2)).
        {
          eapply store_event_locs; eauto.
          econstructor.
        }

        (* TODO:  NoDup ((lrange t1) ++ (lrange t2)) as part of well_formed? *)
        assert (NoDup ((lrange t1) ++ (lrange t2))).
        {
          admit.
        }

        eauto.

        exfalso.
        eapply nodup_contra.
        apply H0.
        apply H1.
        eassumption.
    +
      invc H1.
      ++
                assert (In loc (lrange t1)).
        {
          eapply store_event_locs; eauto.
          econstructor.
        }

        assert (In loc (lrange t2)).
        {
          eapply store_event_locs; eauto.
          econstructor.
        }

        (* TODO:  NoDup ((lrange t1) ++ (lrange t2)) as part of well_formed? *)
        assert (NoDup ((lrange t1) ++ (lrange t2))).
        {
          admit.
        }

        eauto.

        exfalso.
        eapply nodup_contra.
        apply H0.
        apply H1.
        eassumption.

      ++

        assert (In loc t2
        
        
        
        
      
      
          
        
        
        
        

        ff.
        

        
      ff.

    
    

    

    ff.

    invc H0.
    ff.
    +
      ff.
      invc H1.
      ++
        eauto.
      ++
        
        
        
    


    
    inv_wf.
    inv_ev2; try eauto.

    admit.

    
    inv_ev2;
      try eauto.

    ff.
    
    
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_req_locs : rl.

Lemma unique_req_splitp_l_locs:
  forall (t : AnnoTerm) (p i i0 loc p0 p1 q yi : nat) (t0: Term),
    well_formed t ->
    events t p (req i loc p0 q t0) ->
    events t p (splitp i0 loc yi p1) -> i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_req_splitp_l_locs : rl.

Lemma unique_req_splitp_r_locs:
  forall (t : AnnoTerm) (p i i0 loc p0 p1 q xi : nat) (t0: Term),
    well_formed t ->
    events t p (req i loc p0 q t0) ->
    events t p (splitp i0 xi loc p1) -> i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_req_splitp_r_locs: rl.

Lemma unique_req_rpy_locs
  : forall (t : AnnoTerm) (p i i0 loc p0 p1 q q0 : nat) (t0: Term),
    well_formed t ->
    events t p (req i loc p0 q t0) ->
    events t p (rpy i0 loc p1 q0) -> i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_req_rpy_locs: rl.

Lemma unique_splitp_splitp_ll_locs:
  forall (t : AnnoTerm) (p i i0 loc p0 p1 yi yi0 : nat),
    well_formed t ->
    events t p (splitp i  loc yi  p0) ->
    events t p (splitp i0 loc yi0 p1) -> i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_splitp_splitp_ll_locs: rl.

Lemma unique_splitp_splitp_rl_locs:
  forall (t : AnnoTerm) (p i i0 loc p0 p1 yi yi0 : nat),
    well_formed t ->
    events t p (splitp i0 loc yi0 p1) ->
    events t p (splitp i  yi loc  p0) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_splitp_splitp_rl_locs: rl.

Lemma unique_rpy_splitp_l_locs:
  forall (t : AnnoTerm) (p i i0 loc p0 p1 q yi : nat),
    well_formed t ->
    events t p (rpy i loc p0 q) ->
    events t p (splitp i0 loc yi p1) -> i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_rpy_splitp_l_locs: rl.

Lemma unique_splitp_splitp_rr_locs:
  forall (t : AnnoTerm) (p i i0 loc p0 p1 xi xi0 : nat),
    well_formed t ->
    events t p (splitp i  xi loc  p0) ->
    events t p (splitp i0 xi0 loc p1) -> i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_splitp_splitp_rr_locs: rl.

Lemma unique_rpy_splitp_r_locs:
  forall (t : AnnoTerm) (p i i0 loc p0 p1 q xi : nat),
    well_formed t ->
    events t p (rpy i loc p0 q) ->
    events t p (splitp i0 xi loc p1) -> i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_rpy_splitp_r_locs: rl.

Lemma unique_rpy_locs
  : forall (t : AnnoTerm) (p i i0 loc p0 p1 q q0 : nat),
    well_formed t ->
    events t p (rpy i  loc p0 q) ->
    events t p (rpy i0 loc p1 q0) -> i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_rpy_locs: rl.

Lemma unique_splitpl_joinpl_locs
  : forall (t : AnnoTerm) (p i i0 loc p1 q0 yi yi' : nat),
    well_formed t ->
    events t p (splitp i loc yi p1) ->
    events t p (joinp i0 loc yi' q0) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_splitpl_joinpl_locs: rl.

Lemma unique_req_joinpl_locs
  : forall (t : AnnoTerm) (p i i0 loc p0 q q0 yi : nat) t0,
    well_formed t ->
    events t p (req i loc p0 q t0) ->
    events t p (joinp i0 loc yi q0) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_req_joinpl_locs: rl.

Lemma unique_splitpr_joinpl_locs
  : forall (t : AnnoTerm) (p i i0 loc p1 q0 xi yi : nat),
    well_formed t ->
    events t p (splitp i xi loc p1) ->
    events t p (joinp i0 loc yi q0) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_splitpr_joinpl_locs: rl.

Lemma unique_rpy_joinpl_locs
  : forall (t : AnnoTerm) (p i i0 loc p0 q q0 yi : nat),
    well_formed t ->
    events t p (rpy i loc p0 q) ->
    events t p (joinp i0 loc yi q0) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_rpy_joinpl_locs: rl.

Lemma unique_joinpl_joinpl_locs
  : forall (t : AnnoTerm) (p i i0 loc p1 q0 yi yi' : nat),
    well_formed t ->
    events t p (joinp i  loc yi p1) ->
    events t p (joinp i0 loc yi' q0) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_joinpl_joinpl_locs: rl.

Lemma unique_req_joinpr_locs
  : forall (t : AnnoTerm) (p i i0 loc p0 q q0 xi : nat) t0,
    well_formed t ->
    events t p (req i loc p0 q t0) ->
    events t p (joinp i0 xi loc q0) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_req_joinpr_locs: rl.

Lemma unique_splitpl_joinpr_locs
  : forall (t : AnnoTerm) (p i i0 loc p1 q0 yi xi : nat),
    well_formed t ->
    events t p (splitp i loc yi p1) ->
    events t p (joinp i0 xi loc q0) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_splitpl_joinpr_locs: rl.

Lemma unique_splitpr_joinpr_locs
  : forall (t : AnnoTerm) (p i i0 loc p1 q0 xi xi' : nat),
    well_formed t ->
    events t p (splitp i xi loc p1) ->
    events t p (joinp i0 xi' loc q0) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_splitpr_joinpr_locs: rl.

Lemma unique_rpy_joinpr_locs
  : forall (t : AnnoTerm) (p i i0 loc p0 q q0 xi : nat),
    well_formed t ->
    events t p (rpy i loc p0 q) ->
    events t p (joinp i0 xi loc q0) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_rpy_joinpr_locs: rl.

Lemma unique_joinpl_joinpr_locs
  : forall (t : AnnoTerm) (p i i0 loc p1 q0 xi yi : nat),
    well_formed t ->
    events t p (joinp i  xi loc p1) ->
    events t p (joinp i0 loc yi q0) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_joinpl_joinpr_locs: rl.

Lemma unique_joinpr_joinpr_locs
  : forall (t : AnnoTerm) (p i i0 loc p1 q0 xi xi' : nat),
    well_formed t ->
    events t p (joinp i  xi  loc p1) ->
    events t p (joinp i0 xi' loc q0) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    dest_lrange; simpl in *;
      try (pose_lrange_facts;    
           lia).
Defined.
Hint Resolve unique_joinpr_joinpr_locs: rl.


Ltac flip a :=
  try (eapply a;
       eauto; tauto);
  try (symmetry;
       eapply a;
       eauto; tauto);
  tauto.

Ltac dorl' a b c d e f g h i j k l m n o p q r s t u :=
    first
      [ flip a
      | flip b
      | flip c
      | flip d
      | flip e
      | flip f
      | flip g
      | flip h
      | flip i
      | flip j
      | flip k
      | flip l
      | flip m
      | flip n
      | flip o
      | flip p
      | flip q
      | flip r
      | flip s
      | flip t
      | flip u
      ].

Ltac dorl :=
  dorl'
    unique_req_locs
    unique_req_splitp_l_locs
    unique_req_splitp_r_locs
    unique_req_rpy_locs
    unique_req_joinpl_locs
    unique_splitp_splitp_ll_locs
    unique_splitp_splitp_rl_locs
    unique_rpy_splitp_l_locs
    unique_splitpl_joinpl_locs
    unique_splitp_splitp_rr_locs
    unique_rpy_splitp_r_locs
    unique_splitpr_joinpl_locs
    unique_rpy_locs
    unique_rpy_joinpl_locs
    unique_joinpl_joinpl_locs
    unique_req_joinpr_locs
    unique_splitpl_joinpr_locs
    unique_splitpr_joinpr_locs
    unique_rpy_joinpr_locs
    unique_joinpl_joinpr_locs
    unique_joinpr_joinpr_locs.
    
Lemma unique_store_events: forall t p ev1 ev2 loc,
  well_formed t ->
  events t p ev1 ->
  events t p ev2 ->
  store_event ev1 loc ->
  store_event ev2 loc ->
  ev1 = ev2.
Proof.
  intros.
  eapply events_injective; eauto.
  invc H2;
    invc H3;
    simpl;
    try dorl.
Defined.

Lemma unique_store_events': forall t p ev1 ev2 loc,
    well_formed t ->
    ev_in ev1 (ev_sys t p) ->
    ev_in ev2 (ev_sys t p) -> 
    store_event ev1 loc ->
    store_event ev2 loc ->
    ev1 <> ev2 ->
    False.
Proof.
  intros.
  assert (ev1 = ev2).
  {
    eapply unique_store_events;
      try eassumption.
    eapply evsys_events; eauto.
    eapply evsys_events; eauto.
  }
  congruence.
Defined.

Definition store_event_evsys es loc := exists ev, store_event ev loc /\ ev_in ev es.

Inductive store_conflict: EvSys Ev -> Prop :=
| store_conflict_merge: forall r es1 es2 loc,
    store_event_evsys es1 loc ->
    store_event_evsys es2 loc ->
    store_conflict (merge r es1 es2)
| store_conflict_before_l: forall r es1 es2,
    store_conflict es1 ->
    store_conflict (before r es1 es2)
| store_conflict_before_r: forall r es1 es2,
    store_conflict es2 ->
    store_conflict (before r es1 es2).

Lemma unique_events': forall r es1 es2 ev1 ev2,
    well_structured ev (merge r es1 es2) ->
    ev_in ev1 es1 ->
    ev_in ev2 es2 ->
    ev ev1 <> ev ev2.
Proof.
  intros.
  inv H.
  assert (fst (es_range es1) <= ev ev1 < snd (es_range es1)).
  {
    eapply ws_evsys_range; eauto.
  }

  assert (fst (es_range es2) <= ev ev2 < snd (es_range es2)).
  {
    eapply ws_evsys_range; eauto.
  }

  lia.
Defined.

Lemma unqev: forall ev1 ev2,
  ev ev1 <> ev ev2 ->
  ev1 <> ev2.
Proof.
  intros.
  unfold not; intros.
  subst.
  solve_by_inversion.
Defined.

Lemma unique_events: forall r es1 es2 ev1 ev2,
    well_structured ev (merge r es1 es2) ->
    ev_in ev1 es1 ->
    ev_in ev2 es2 ->
    ev1 <> ev2.
Proof.
  intros.
  eapply unqev.
  eapply unique_events';
    eauto.
Defined.



Definition store_event_evsys es loc := exists ev, store_event ev loc /\ ev_in ev es.

Inductive store_conflict: EvSys Ev -> Prop :=
| store_conflict_merge: forall r es1 es2 loc,
    store_event_evsys es1 loc ->
    store_event_evsys es2 loc ->
    store_conflict (merge r es1 es2)
| store_conflict_before_l: forall r es1 es2,
    store_conflict es1 ->
    store_conflict (before r es1 es2)
| store_conflict_before_r: forall r es1 es2,
    store_conflict es2 ->
    store_conflict (before r es1 es2).

Theorem no_store_conflicts: forall t p sys,
    well_formed t ->
    sys = ev_sys t p ->
    not (store_conflict sys).
Proof.
  unfold not; intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      cbn in *;
      repeat break_let;
      subst;
      solve_by_inversion.
  -
    cbn in *;
      repeat break_let;
      subst.
    inv H1.
    +
      solve_by_inversion.
    +
      inv H2;
        try solve_by_inversion;
        try inv_wf; eauto.
      
  -
    cbn in *;
      repeat break_let;
      subst.
    inv H1;
      do_wf_pieces.
  -
    cbn in *;
      repeat break_let;
      subst.
    inv H1.
    +
      solve_by_inversion.
    +
      inv H2.
      ++
        inv H3;
          do_wf_pieces.
      ++
        solve_by_inversion.
  -
    
    assert (well_structured ev sys).
    {
      rewrite H0.
      eapply well_structured_evsys.
      eassumption.
    }
    
    cbn in *;
      repeat break_let;
      subst.
    inv H1;
      try solve_by_inversion.
    +
      inv H3;
        try solve_by_inversion.
      ++       
        inv H4;
          try solve_by_inversion.
        +++
          unfold store_event_evsys in *.
          destruct_conjs.

          assert (ev_in H6 (merge (S n, Nat.pred n0) (ev_sys t1 p1) (ev_sys t2 p1))).
          {
            eauto.
          }
          
          assert (ev_in H8 (merge (S n, Nat.pred n0) (ev_sys t1 p1) (ev_sys t2 p1))).
          {
            eauto.
          }

          eapply unique_store_events' with (ev1:=H6) (ev2:=H8) (t:=(abpar (n, n0) l (n1,n2) (n3,n4) s t1 t2)) (p:=p1) (loc:=loc);
            try eassumption;
            try (simpl; eauto; tauto).
          ++++  
            inv H2.
            inv H16.
            eapply unique_events; eauto.
Defined.
