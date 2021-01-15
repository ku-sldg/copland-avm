
(* Extra Lemmas not needed at present *)
(*
Lemma unique_store_events: forall t p tr ev1 ev2 loc,
  well_formed t ->
  Trace.trace t p tr ->
  In ev1 tr ->
  In ev2 tr ->
  store_event ev1 loc ->
  store_event ev2 loc ->
  ev1 <> ev2 ->
  False.
Proof.
  intros.
  assert (ev1 = ev2).
  {
    eapply store_events_injective;
      try eassumption;
      try (eapply Trace.trace_events; eassumption).
  }
  congruence.
Defined.
 *)

(*
Lemma noDup_store_events: forall t p ev loc tr,
  well_formed t ->
  store_event ev loc ->
  Trace.trace t p tr ->
  In ev tr ->
  NoDup ev.
 *)

(*
Inductive store_event_evsys: EvSys Ev -> Loc -> Prop :=
| inevsys_leaf: forall r ev loc,
    store_event ev loc ->
    store_event_evsys (leaf r ev) loc
| inevsys_before_l: forall r es1 es2 loc,
    store_event_evsys es1 loc ->
    store_event_evsys (before r es1 es2) loc
| inevsys_before_r: forall r es1 es2 loc,
    store_event_evsys es2 loc ->
    store_event_evsys (before r es1 es2) loc
| inevsys_merge_l: forall r es1 es2 loc,
    store_event_evsys es1 loc ->
    store_event_evsys (merge r es1 es2) loc
| inevsys_merge_r: forall r es1 es2 loc,
    store_event_evsys es2 loc ->
    store_event_evsys (merge r es1 es2) loc.
Hint Constructors store_event_evsys: core.
 *)

(*
Lemma alt_store_event_evsys: forall es loc,
    store_event_evsys es loc <-> store_event_evsys es loc.
Proof.
  intros.
  unfold store_event_evsys.
  split.
  -
    generalizeEverythingElse es.
    induction es; intros loc H;
      inv H;
      try (eauto; tauto);
      try ( try (edestruct IHes1; [eauto | destruct_conjs; eauto]; tauto);
            try (edestruct IHes2; [eauto | destruct_conjs; eauto]; tauto)
          ).
  -
    generalizeEverythingElse es.
    induction es; intros loc H;
      destruct H as [x [xx H1]];
      inv H1; eauto.
Defined.
*)

(*
Lemma aff: forall es1 loc,
    store_event_evsys es1 loc ->
    exists ev, store_event ev loc /\ ev_in ev es1.
Proof.
  intros.
  unfold store_event_evsys in *.
  eauto.
Defined.

  intros.
  induction H;
    try eauto;
    try (
        edestruct IHstore_event_evsys;
        destruct_conjs;
        exists x;
        split; eauto).
Defined.
 *)
    
(*

Inductive top_level_at: (*Plc ->*) Loc -> AnnoTerm -> Prop :=
(*| top_at_rec: forall r p q loc t',
          top_level_at q loc t' ->
          top_level_at p loc (aatt r q t') *)
| top_at_l: forall q t' loc loc2,
    top_level_at loc (aatt (loc,loc2) q t')
| top_at_r: forall q t' loc loc2,
    top_level_at (pred loc2) (aatt (loc,loc2) q t')
| top_lseq_l: forall r loc t1 t2,
    top_level_at loc t1 ->
    top_level_at loc (alseq r t1 t2)
| top_lseq_r: forall r loc t1 t2,
    top_level_at loc t2 ->
    top_level_at loc (alseq r t1 t2)
| top_bseq_l: forall r s loc t1 t2,
    top_level_at loc t1 ->
    top_level_at loc (abseq r s t1 t2)
| top_bseq_r: forall r s loc t1 t2,
    top_level_at loc t2 ->
    top_level_at loc (abseq r s t1 t2)
| top_bpar_l: forall r s loc t1 t2,
    top_level_at loc t1 ->
    top_level_at loc (abpar r s t1 t2)
| top_bpar_r: forall r s loc t1 t2,
    top_level_at loc t2 ->
    top_level_at loc (abpar r s t1 t2).

Lemma store_event_facts: forall loc t p,
    store_event_evsys (ev_sys t p) loc ->
    top_level_at loc t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
    
      inv H;
        repeat break_let;
        try solve_by_inversion;
        inv H0; inv H1.
  -
    cbn in *.
    repeat break_let.
    invc H.
    +
      invc H4.
      invc H2.
      econstructor.
    +
      invc H4.
      invc H2.
      econstructor.
  -
    cbn in *.
    invc H.
    +
      econstructor.
      eauto.
    +
      eapply top_lseq_r.
      eauto.
  -
    cbn in *.
    repeat break_let.
    invc H.
    +
      invc H4.
      invc H2.
    +
      invc H4.
      ++
        invc H3.
        +++
          econstructor.
          eauto.
        +++
          eapply top_bseq_r.
          eauto.
      ++
        invc H3.
        invc H2.
  -
    cbn in *.
    repeat break_let.
    invc H.
    +
      invc H4.
      invc H2.
    +
      invc H4.
      ++
        invc H3.
        +++
          econstructor.
          eauto.
        +++
          eapply top_bpar_r.
          eauto.
      ++
        invc H3.
        invc H2.
Defined.

Lemma wf_att_fact: forall x y q t',
    well_formed (aatt (x, y) q t') ->
    x > (Nat.pred y) ->
    False.
Proof.
  intros.
  inv H.
  simpl in *.
  lia.
Defined.

Lemma good_par : forall r s p t1 t2 loc,
    well_formed (abpar r s t1 t2) ->
    store_event_evsys (ev_sys t1 p) loc ->
    store_event_evsys (ev_sys t2 p) loc ->
    False.
Proof.
  intros.
  eapply store_event_facts in H0.
  eapply store_event_facts in H1.
  inv H.
  Check anno_mono.
  inv H0; inv H1; cbn in *.

  invc H0; invc H1;
    try lia.

  invc H0; invc H1;
    try lia.

  eapply wf_att_fact.
  apply H7.
  lia.

  rewrite <- H3 in *.
  subst.
  invc H7.
  simpl in *.
  lia.


  

  invc H6.
  simpl in *.
  subst.

  invc H0; try lia.
  pose (wf_mono t' H12).
  simpl in *.
  subst.
  rewrite <- H13 in *.
  rewrite H14 in *.
  simpl in *.
  destruct (range t') eqn:hey.
  simpl in *.
  subst.
  destruct r.
  simpl in *.
  subst.
  destruct r0.
  simpl in *.
  subst.
  clear H1.
  invc H7.
  subst.

  simpl in *.
  subst.
  pose (wf_mono t1 H4).
  subst.
  rewrite H8 in *.
  subst.
  rewrite <- H6 in *; clear H6.
  rewrite <- H8 in *; clear H8.
  
  subst.
  admit.
  
Admitted.

 *)

(*


Theorem no_store_conflicts: forall t p,
    well_formed t ->
    not (store_conflict (ev_sys t p)).
Proof.
  Print ev_sys.
  unfold not; intros.
  generalize dependent p.
  induction t; intros.
  -
    destruct a;
      try (inv H0; repeat break_let; solve_by_inversion).
  -
    cbn in *.
    repeat break_let.
    invc H0.
    +
      solve_by_inversion.
    +
      solve_by_inversion.
  -
    inv H.
    invc H0; eauto.
  -
    inv H.
    invc H0;
      repeat break_let;
      try solve_by_inversion.
    +
      invc H1.
      solve_by_inversion.
    +
      invc H1.
      invc H2.
      ++
        invc H1; eauto.
      ++
        solve_by_inversion.
  -
    inv H.
    invc H0;
      repeat break_let;
      try solve_by_inversion.
    +
      invc H1.
      solve_by_inversion.
    +
      invc H1.
      invc H2; try solve_by_inversion.
      invc H1.
      
      eapply good_par; eauto.
Defined.
  
  *)
