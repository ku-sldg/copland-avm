Require Import Term StructTactics Event_system Term_system.

Require Import Lia Coq.Program.Tactics.


Inductive store_event: Ev -> Loc -> Prop :=
| put_event: forall i x p q t, store_event (req i x p q t) x
| put_event_spl: forall i xi yi p, store_event (splitp i xi yi p) xi
| put_event_spr: forall i xi yi p, store_event (splitp i xi yi p) yi
| get_event: forall i x p q, store_event (rpy i x p q) x
| get_event_joinpl: forall i xi yi p, store_event (joinp i xi yi p) xi
| get_event_joinpr: forall i xi yi p, store_event (joinp i xi yi p) yi.

Lemma wf_mono_locs: forall t,
    well_formed t ->
    fst (lrange t) <= snd (lrange t).
Proof.
  intros.
  rewrite Term.well_formed_lrange; eauto.
  lia.
Defined.

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
(*
Ltac inv_wf :=
  match goal with
  | [H: well_formed _ |- _] =>
    invc H
  end.
 *)


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

Ltac pose_store_events :=
  match goal with
  | [H: events _ _ ?ev,
        H': Loc |- _] =>
    assert_new_proof_by (store_event ev H') econstructor
  end.

Ltac pose_new_lrange :=
  match goal with
  | [H: well_formed ?t,
        H': events ?t ?p ?ev,
            H'': store_event ?ev ?loc
     |- _] =>
    pose_new_proof (store_events_lrange t p ev loc H H' H'')
  end.

Create HintDb rl.

Lemma unique_req_locs: forall t p i i0 loc p0 p1 q q0 t0 t1,
    well_formed t ->
    events t p (req i loc p0 q t0) ->
    events t p (req i0 loc p1 q0 t1) ->
    i = i0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    inv_wf;
    inv_ev2;
    try eauto;
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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
    destruct l; simpl in *;
      try (
          repeat pose_store_events;
          repeat pose_new_lrange;
          repeat find_eapply_lem_hyp wf_mono_locs;    
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

(*
Ltac dorl' a b c d e f g h i j k l:=
    first
      [ flip a
      | ( eapply b;
          eauto; tauto)
      | ( eapply c;
          eauto; tauto)
      | ( eapply d;
          eauto; tauto)
      | ( eapply e;
          eauto; tauto)
      | ( eapply f;
          eauto; tauto)
      | ( eapply g;
          eauto; tauto)
      | ( eapply h;
          eauto; tauto)
      | ( eapply i;
          eauto; tauto)
      | ( eapply j;
          eauto; tauto)
      | ( eapply k;
          eauto; tauto)
      | ( eapply l;
          eauto; tauto)
      ].
*)

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

Definition store_event_evsys' es loc := exists ev, store_event ev loc /\ ev_in ev es.

Inductive store_conflict: EvSys Ev -> Prop :=
| store_conflict_merge: forall r es1 es2 loc,
    store_event_evsys' es1 loc ->
    store_event_evsys' es2 loc ->
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
      repeat break_let.
    inv H0.
    inv H1.
    +
      solve_by_inversion.
    +
      inv H3.
      ++
        inv H.
        eauto.
      ++
        solve_by_inversion.
        
  -
    cbn in *.
    inv H0.
    inv H1.
    +
      inv H.
      eauto.
    +
      inv H.
      eauto.
  -
    cbn in *;
      repeat break_let.
    inv H0.
    inv H1.
    +
      solve_by_inversion.
    +
      inv H3.
      ++
        inv H4;
          inv H; eauto.
      ++
        solve_by_inversion.
  -
    assert (well_structured ev sys).
    {
      rewrite H0.
      eapply well_structured_evsys.
      eassumption.
    }
    
    
    cbn in H0.
    repeat break_let.
    inv H0.
    inv H1.
    +
      solve_by_inversion.
    +
      inv H4.
      ++

        (*
        remember ((merge (S n, Nat.pred n0) (ev_sys t1 p) (ev_sys t2 p))) as xxx.
         *)
        
         
        
        
        inv H5;
          try solve_by_inversion.

        unfold store_event_evsys' in *.
        destruct_conjs.

        (*
        assert (exists ev, store_event ev loc /\ ev_in ev (ev_sys t1 p1)).
        {
          unfold store_event_evsys' in *.
          eauto
          eapply aff; eauto.
        }
        assert (exists ev, store_event ev loc /\ ev_in ev (ev_sys t2 p1)).
        {
          eapply aff; eauto.
        }
        destruct_conjs.
         *)

        

        
        assert (ev_in H7 (merge (S n, Nat.pred n0) (ev_sys t1 p1) (ev_sys t2 p1))).
        {
          eauto.
        }
        
          

        assert (ev_in H9 (merge (S n, Nat.pred n0) (ev_sys t1 p1) (ev_sys t2 p1))).
        {
          eauto.
        }

        

        

        eapply unique_store_events' with (ev1:=H7) (ev2:=H9) (t:=(abpar (n, n0) l (n1,n2) (n3,n4) s t1 t2)) (p:=p1) (loc:=loc).
        eassumption.
        cbn.
        apply ein_beforer.
        apply ein_beforel.
        apply ein_mergel.
        inv H5.
        eassumption.
        
        cbn.
        apply ein_beforer.
        apply ein_beforel.
        apply ein_merger.
        inv H5.
        eassumption.

        eassumption.
        eassumption.

        

       

        inv H2.
        inv H17.

        eapply unique_events; eauto.
      ++
        solve_by_inversion.
Defined.     










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
    store_event_evsys es loc <-> store_event_evsys' es loc.
Proof.
  intros.
  unfold store_event_evsys'.
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
    store_event_evsys' es1 loc ->
    exists ev, store_event ev loc /\ ev_in ev es1.
Proof.
  intros.
  unfold store_event_evsys' in *.
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
