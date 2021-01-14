(*
Proofs about the Copland Virtual Machine implementation, linking it to the Copland reference semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import More_lists Term ConcreteEvidence LTS Event_system Term_system Main.
Require Import GenStMonad MonadVM MonadVMFacts Maps StructTactics Auto.
Require Import Axioms_Io Impl_vm External_Facts Helpers_VmSemantics.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics Coq.Program.Equality.
Require Import Coq.Arith.Peano_dec Lia.

Set Nested Proofs Allowed.

Inductive store_event: Ev -> Loc -> Prop :=
| put_event: forall i x p q t, store_event (req i x p q t) x
| put_event_spl: forall i xi yi p, store_event (splitp i xi yi p) xi
| put_event_spr: forall i xi yi p, store_event (splitp i xi yi p) yi
| get_event: forall i x p q, store_event (rpy i x p q) x
| get_event_joinpl: forall i xi yi p, store_event (joinp i xi yi p) xi.

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
    inv H
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

Print HintDb lr.
(*
Hint Resolve aff : coree.
*)

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

(*

  -
    destruct a;
      cbn in *;
      try solve_by_inversion.
  -
    
    inv_wf;
      inv_ev;
      simpl in *; subst;
        repeat (find_eapply_hyp_hyp);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia.
  -
    inv_wf;
      inv_ev;
      simpl in *; subst;
        repeat (find_eapply_hyp_hyp);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia.
  -
    inv_wf;
      inv_ev;
      simpl in *; subst;
        repeat (find_eapply_hyp_hyp);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia.
  -
    inv_wf;
      inv_ev;
      simpl in *; subst;
        repeat (find_eapply_hyp_hyp);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia.
    
    
    

  -
    cbn in *.
    
    inv_wf;
      inv_ev;
      try (
    
      simpl in *;
      repeat find_eapply_hyp_hyp;
      subst;
      repeat (find_eapply_lem_hyp wf_mono_locs);
      lia).

    simpl in *.
    find_eapply_hyp_hyp.
    repeat find_eapply_lem_hyp wf_mono_locs.
    lia.

    
      
      simpl in *; (* subst; *)
      try (find_eapply_hyp_hyp);
      subst;
        try find_eapply_lem_hyp wf_mono_locs;
        lia.
    

  -
    inv H.
    inv H0.
    +
      simpl in *.
      assert (fst (lrange t1) <= loc < snd (lrange t1)) by eauto.
      subst.
      assert (fst (lrange t2) <= snd (lrange t2)).
      {
        eapply wf_mono_locs; eauto.
      }
      lia.
    +
      simpl in *.
      
      assert (fst (lrange t2) <= loc < snd (lrange t2)) by eauto.

      assert (fst (lrange t1) <= snd (lrange t1)).
      {
        eapply wf_mono_locs; eauto.
      }
      lia.
  -
    inv H.
    inv H0.
    +
      simpl in *.
      
      assert (fst (lrange t1) <= loc < snd (lrange t1)) by eauto.
      subst.
      assert (fst (lrange t2) <= snd (lrange t2)).
      {
        eapply wf_mono_locs; eauto.
      }
      lia.
    +
      simpl in *.
      assert (fst (lrange t2) <= loc < snd (lrange t2)) by eauto.

      assert (fst (lrange t1) <= snd (lrange t1)).
      {
        eapply wf_mono_locs; eauto.
      }
      lia.
  -
    inv H.
    inv H0.
    +
      simpl in *.
      
      assert (fst (lrange t1) <= loc < snd (lrange t1)) by eauto.
      subst.

      assert (fst (lrange t2) <= snd (lrange t2)).
      {
        eapply wf_mono_locs; eauto.
      }
      lia.
    +
      simpl in *.
      assert (fst (lrange t2) <= loc < snd (lrange t2)) by eauto.

      assert (fst (lrange t1) <= snd (lrange t1)).
      {
       eapply wf_mono_locs; eauto.
      }
      lia.
Defined.
*)

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
    


(*

  -
    cbn in *.
    inv_wf;
    inv_ev.
    +
      simpl in *.
      subst.
      lia.
    +
      assert (fst (lrange t) <= loc < snd (lrange t)).
      {
        eauto.
      }
      
      assert (snd (lrange t) <= snd l).
      {
        lia.
      }
      lia.


    
    inv_wf;
      inv_ev;
      simpl in *; subst;
        repeat (find_eapply_hyp_hyp);
        repeat find_eapply_lem_hyp wf_mono_locs.
    +
      assert (snd (lrange t) <= snd l).
      {
        lia.
      }
      simpl in *; subst;
        repeat (find_eapply_hyp_hyp);
        repeat find_eapply_lem_hyp wf_mono_locs.
      
      
      
      admit.
    +
      lia.
      
     
    
    
  -
    destruct a;
      cbn in *;
      try solve_by_inversion.
  -
    cbn in *.
    inv H.
    inv H0.
    +
      simpl in *.
      subst.
      lia.
    +
      assert (fst (lrange t) <= loc < snd (lrange t)).
      {
        eauto.
      }
      
      assert (snd (lrange t) <= snd l).
      {
        lia.
      }
      lia.
  -
    inv H.
    inv H0.
    +
      simpl in *.
      assert (fst (lrange t1) <= loc < snd (lrange t1)) by eauto.
      subst.
      assert (fst (lrange t2) <= snd (lrange t2)).
      {
        eapply wf_mono_locs; eauto.
      }
      lia.
    +
      simpl in *.
      
      assert (fst (lrange t2) <= loc < snd (lrange t2)) by eauto.

      assert (fst (lrange t1) <= snd (lrange t1)).
      {
        eapply wf_mono_locs; eauto.
      }
      lia.
  -
    inv H.
    inv H0.
    +
      simpl in *.
      
      assert (fst (lrange t1) <= loc < snd (lrange t1)) by eauto.
      subst.
      assert (fst (lrange t2) <= snd (lrange t2)).
      {
        eapply wf_mono_locs; eauto.
      }
      lia.
    +
      simpl in *.
      assert (fst (lrange t2) <= loc < snd (lrange t2)) by eauto.

      assert (fst (lrange t1) <= snd (lrange t1)).
      {
        eapply wf_mono_locs; eauto.
      }
      lia.
  -
    inv H.
    inv H0.
    +
      simpl in *.
      
      assert (fst (lrange t1) <= loc < snd (lrange t1)) by eauto.
      subst.

      assert (fst (lrange t2) <= snd (lrange t2)).
      {
        eapply wf_mono_locs; eauto.
      }
      lia.
    +
      simpl in *.
      assert (fst (lrange t2) <= loc < snd (lrange t2)) by eauto.

      assert (fst (lrange t1) <= snd (lrange t1)).
      {
       eapply wf_mono_locs; eauto.
      }
      lia.
Defined.
*)

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


(*
  
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try(
    inv_wf;
    inv_ev2;
    (* inv_ev; *)
    try eauto;
        destruct l; simpl in *;
        do 2 (find_eapply_lem_hyp store_events_lrange);
        try econstructor;
        eauto;
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia).
  Unshelve.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
Defined.
*)

(*

  -
    destruct a;
      try solve_by_inversion.

  -
    inv_wf;
      inv_ev;
      inv_ev;
      try eauto;
      try (
          destruct l; simpl in *;
          find_eapply_lem_hyp req_events_lrange;
          eauto;
          lia).
  -
    
    +
      inv_ev.
      ++
        eauto.
      ++
        destruct l; simpl in *.

        find_eapply_lem_hyp req_events_lrange;
          eauto;
          lia.
  
    
    




    
  -
    inv_wf.
    inv_ev.
    +
      inv_ev.
      ++
        eauto.
      ++
        destruct l; simpl in *.

        find_eapply_lem_hyp req_events_lrange;
          eauto;
          lia.
        (*

        assert (fst (lrange t) <= loc < snd (lrange t)).
        {
          eapply req_events_lrange; eauto.    
        }
        lia. *)
        
    +
      inv_ev.
      ++
        destruct l; simpl in *.
        do 2 (find_eapply_lem_hyp req_events_lrange);
          eauto;
          lia.
        (*
         assert (fst (lrange t) <= loc < snd (lrange t)).
        {
         eapply req_events_lrange; eauto.
        }
        lia. *)
      ++
        eauto.
  -
    inv H.
    invc H0;
      invc H1;
      try eauto.
    +
      destruct l; simpl in *.

      do 2 (find_eapply_lem_hyp req_events_lrange; eauto);
        eauto; lia.

      (*

      assert (fst (lrange t2) >= snd (lrange t1)).
      {
        admit.
      }
      lia. *)
    +
       destruct l; simpl in *.

      do 2 (find_eapply_lem_hyp req_events_lrange; eauto);
        eauto; lia.
      
  -
    inv H.
    invc H0;
      invc H1;
      try eauto.
    +
       destruct l; simpl in *.

      do 2 (find_eapply_lem_hyp req_events_lrange; eauto);
        eauto; lia.
    +
       destruct l; simpl in *.

      do 2 (find_eapply_lem_hyp req_events_lrange; eauto);
        eauto; lia.
  -
    inv H.
    invc H0;
      invc H1;
      try eauto.
    +
       destruct l; simpl in *.

      do 2 (find_eapply_lem_hyp req_events_lrange; eauto);
        eauto; lia.
    +
       destruct l; simpl in *.

      do 2 (find_eapply_lem_hyp req_events_lrange; eauto);
        eauto; lia.
Defined.
*)

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



(*
  
  intros.
  generalizeEverythingElse t.

  induction t; intros;
    try(
        inv_wf;
        inv_ev2;
        (*inv_ev; *)
        try eauto;
        destruct l; simpl in *;

        do 2(
             find_eapply_lem_hyp store_events_lrange;
             try econstructor;
             eauto);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia).
  Unshelve.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  exact (asp CPY).
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
Defined.
*)

    (*
  -
    inv_wf;
      inv_ev2;
      try eauto;
      destruct l; simpl in *;
        do 2(
      find_eapply_lem_hyp store_events_lrange;
      try econstructor;
      eauto);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia.

    +
      do 2 (
      find_eapply_lem_hyp store_events_lrange;
      try econstructor;
      eauto);
      lia.
      
    +
      do 2(
      find_eapply_lem_hyp store_events_lrange;
      try econstructor;
      eauto);
      lia.
    +
      do 2(
      find_eapply_lem_hyp store_events_lrange;
      try econstructor;
      eauto);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia.
      
      find_eapply_lem_hyp store_events_lrange;
        try econstructor;
        eauto.
      repeat find_eapply_lem_hyp wf_mono_locs.
      lia.
    +
      do 2(
      find_eapply_lem_hyp store_events_lrange;
      try econstructor;
      eauto).
      lia.
      
      
    

      
      clear H11.
      clear H12.
      clear H13.
      clear H14.
      rewrite <- H22 in *; clear H22.
      admit.
    +
      find_eapply_lem_hyp store_events_lrange;
      try econstructor;
      eauto.
      find_eapply_lem_hyp store_events_lrange;
      try econstructor;
      eauto.
      lia.
      

      
      lia.
      
      
      

    




    
    lia.
    lia.

     do 2(
         find_eapply_lem_hyp store_events_lrange;
         try econstructor;
         eauto).
     lia.
      do 2(
         find_eapply_lem_hyp store_events_lrange;
         try econstructor;
         eauto).
      lia.

       do 2(
         find_eapply_lem_hyp store_events_lrange;
         try econstructor;
         eauto).
       lia.
        do 2(
         find_eapply_lem_hyp store_events_lrange;
         try econstructor;
         eauto).
        lia.
         do 2(
         find_eapply_lem_hyp store_events_lrange;
         try econstructor;
         eauto).
         lia.


          do 2(
         find_eapply_lem_hyp store_events_lrange;
         try econstructor;
         eauto).
          lia.
          lia.
          lia.
          lia.

           do 2(
         find_eapply_lem_hyp store_events_lrange;
         try econstructor;
         eauto).
           lia.

           find_eapply_lem_hyp store_events_lrange;
             try eauto;
             try econstructor.
           find_eapply_lem_hyp store_events_lrange
             try eauto;
             try econstructor

            do 2(
         find_eapply_lem_hyp store_events_lrange;
         try econstructor;
         eauto).

            subst.
            simpl in *.
            

      try eauto.
    econstructor.
    lia.

    find_eapply_lem_hyp store_events_lrange;
      try eauto.
    Focus 2.
    econstructor.

    find_eapply_lem_hyp store_events_lrange;
      try eauto.
    Focus 2.
    econstructor.
    lia.

    
    
    
    eassumption.
    Focus 2.
    Print store_event.
    apply put_event_spl.
    
    econstructor
      eauto
    









  
  induction t; intros;
    try(
    inv_wf;
    inv_ev2;
    (*inv_ev; *)
    try eauto;
    destruct l; simpl in *;
    do 2 (find_eapply_lem_hyp store_events_lrange);
    try econstructor;
    eauto;
    lia).
  
    - inv_wf;
      inv_ev;
      inv_ev;
      try eauto;
      destruct l; simpl in *.
      +
         do 1 (find_eapply_lem_hyp store_events_lrange;
           try econstructor;
           eauto).
         lia.
      +
        do 1 (find_eapply_lem_hyp store_events_lrange;
           try econstructor;
           eauto).
        subst.
        simpl in *.
        
        do 1 (find_eapply_lem_hyp store_events_lrange;
           try econstructor;
           eauto).
         lia.
         lia.
        
        
      
      
      
      

Defined.



  
Admitted.
*)

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



(*
  
    intros.
  generalizeEverythingElse t.

  induction t; intros;
    try(
        inv_wf;
        inv_ev2;
        (*inv_ev; *)
        try eauto;
        destruct l; simpl in *;

        do 2(
             find_eapply_lem_hyp store_events_lrange;
             try econstructor;
             eauto);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia).
  Unshelve.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  exact (asp CPY).
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
Defined.
*)

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



(*

  
  intros.
  generalizeEverythingElse t.

  induction t; intros;
    try(
        inv_wf;
        inv_ev2';
        (*inv_ev; *)
        try eauto;
        destruct l; simpl in *;

        do 2(
             find_eapply_lem_hyp store_events_lrange;
             try econstructor;
             eauto);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia).
  Unshelve.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  exact (asp CPY).
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  exact (asp CPY).
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  exact (asp CPY).
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
Defined.
*)

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
 (*
    try(
        inv_wf;
        inv_ev2;
        (*inv_ev; *)
        try eauto;
        destruct l; simpl in *;

        do 2(
             find_eapply_lem_hyp store_events_lrange;
             try econstructor;
             eauto);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia).
  Unshelve.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  exact (asp CPY).
    eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  exact (asp CPY).
    eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  exact (asp CPY).
    eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  exact (asp CPY). *)
Defined.


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

          
(*





  -
    (*
    assert (fst (lrange t1) <= i0 < snd (lrange t1)).
    {
      admit.
    }
     *)

    Check store_events_lrange.
    (*
store_events_lrange
     : forall (t : AnnoTerm) (p : nat) (ev : Ev) (loc : nat),
       well_formed t -> 
       events t p ev -> 
       store_event ev loc -> 
       fst (lrange t) <= loc < snd (lrange t)
     *)



    repeat pose_store_events.

    
        


    repeat pose_new_lrange.
    lia.

    pose_new_proof (store_events_lrange H7).
    pose_new_lrange.
        

    find_apply_lem_hyp_new store_events_lrange.

    edestruct H;
      try eauto;
      try econstructor.
    
    econstructor.
    eassumption.
    eassumption.
    econstructor.
      try econstructor;
      eauto.
    eassumption.

    pose (H p (splitp i yi loc p0) loc).
    repeat concludes.

    destruct a.
    

    assert (fst (lrange t1) <= loc < snd (lrange t1)).
    {
      admit.
    }

    (*
    assert (fst (lrange t2) <= i < snd (lrange t2)).
    {
      admit.
    }
     *)
    

    assert (fst (lrange t2) <= loc < snd (lrange t2)).
    {
      admit.
    }
    lia.

    
    
    do 2(
         find_eapply_lem_hyp store_events_lrange;
         try econstructor;
         eauto).
    repeat find_eapply_lem_hyp wf_mono_locs.
    assert (n <= n0).
    lia.
    subst.
    
    
    
    

    
    
  



  

  induction t; intros;
    try(
        inv_wf;
        inv_ev2;
        (*inv_ev; *)
        try eauto;
        destruct l; simpl in *;

        do 2(
             find_eapply_lem_hyp store_events_lrange;
             try econstructor;
             eauto);
        repeat find_eapply_lem_hyp wf_mono_locs;
        lia).
  Unshelve.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  exact (asp CPY).
    eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  exact (asp CPY).
Admitted.
*)

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

Lemma store_events_injective: forall t p ev1 ev2 loc,
  well_formed t ->
  events t p ev1 ->
  events t p ev2 ->
  store_event ev1 loc ->
  store_event ev2 loc ->
  ev1 = ev2.
Proof.
  intros.
  Locate events_injective.
  eapply events_injective; eauto.
  invc H2;
    invc H3;
    simpl.
  -
    eapply unique_req_locs; eauto.
  -
    eapply unique_req_splitp_l_locs; eauto.
  - 
    eapply unique_req_splitp_r_locs; eauto.
  -
    eapply unique_req_rpy_locs; eauto.
  -
    eapply unique_req_joinpl_locs; eauto.
  -
    symmetry.
    eapply unique_req_splitp_l_locs; eauto.
  -
    eapply unique_splitp_splitp_ll_locs; eauto.
  -
    symmetry.
    eapply unique_splitp_splitp_rl_locs; eauto.
  -
    symmetry.
    eapply unique_rpy_splitp_l_locs; eauto.
  -
    eapply unique_splitpl_joinpl_locs; eauto. 
  -
    symmetry.
    eapply unique_req_splitp_r_locs; eauto.
  -
    eapply unique_splitp_splitp_rl_locs; eauto.
  -
    eapply unique_splitp_splitp_rr_locs; eauto.
  -
    symmetry.
    eapply unique_rpy_splitp_r_locs; eauto.
  -
    eapply unique_splitpr_joinpl_locs; eauto.
  -
    symmetry.
    eapply unique_req_rpy_locs; eauto.
  -
    eapply unique_rpy_splitp_l_locs; eauto.
  -
    eapply unique_rpy_splitp_r_locs; eauto.
  -                                           
    eapply unique_rpy_locs; eauto.
  -
    eapply unique_rpy_joinpl_locs; eauto.
  -
    symmetry.
    eapply unique_req_joinpl_locs; eauto.
  -
    symmetry.
    eapply unique_splitpl_joinpl_locs; eauto.
  -
    symmetry.
    eapply unique_splitpr_joinpl_locs; eauto.
  -
    symmetry.
    eapply unique_rpy_joinpl_locs; eauto.
  -
    eapply unique_joinpl_joinpl_locs; eauto.
    

Defined.


    
    
    




(*

  
  -
    assert (i = loc).
    {
      eapply req_same_as_evid; eauto.
    }

    assert (i0 = loc).
    {
      eapply req_same_as_evid; eauto.
    }

    subst.
    simpl.
    tauto.
  -
    assert (i = loc).
    {
      eapply req_same_as_evid; eauto.
    }

    assert (i0 = loc).
    {
      eapply rpy_same_as_evid; eauto.
    }

    subst.
    simpl.
    tauto.
  -
    assert (i = loc).
    {
      eapply rpy_same_as_evid; eauto.
    }

    assert (i0 = loc).
    {
      eapply req_same_as_evid; eauto.
    }

    subst.
    simpl.
    tauto.
  -
    assert (i = loc).
    {
      eapply rpy_same_as_evid; eauto.
    }

    assert (i0 = loc).
    {
      eapply rpy_same_as_evid; eauto.
    }

    subst.
    simpl.
    tauto.
Defined.
 *)



  
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

Lemma unique_store_events': forall t p ev1 ev2 loc,
    well_formed t ->
    (*
  Trace.trace t p tr ->
  In ev1 tr ->
  In ev2 tr -> 
  *)
  ev_in ev1 (Term_system.ev_sys t p) ->
  ev_in ev2 (Term_system.ev_sys t p) -> 
  store_event ev1 loc ->
  store_event ev2 loc ->
  ev1 <> ev2 ->
  False.
Proof.
  intros.
  assert (ev1 = ev2).
  {
    eapply store_events_injective;
      try eassumption.
    eapply evsys_events; eauto.
    eapply evsys_events; eauto.
  }
  congruence.
Defined.


(*
Lemma noDup_store_events: forall t p ev loc tr,
  well_formed t ->
  store_event ev loc ->
  Trace.trace t p tr ->
  In ev tr ->
  NoDup ev.
*)

  


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
  Check ev.
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

(*

Lemma evsys_reps_refine: forall ev t p,
  ev_in ev (VmSemantics.ev_sys t p) ->
  ev_in ev (Term_system.ev_sys t p).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      cbn in *;
        repeat break_let;
      inv H;
      eauto.
  -
    cbn in *;
      repeat break_let.
    inv H; eauto.
  -
    cbn in *.
    inv H; eauto.
  -
    cbn in *;
      repeat break_let.
    inv H.
    +
      eauto.
    +
      inv H2.
      ++
        inv H3; eauto.
      ++
        inv H3; eauto.
  -
    cbn in *;
      repeat break_let.
    inv H.
    +
      eauto.
    +
      inv H2.
      ++
        inv H3; eauto.
      ++
        inv H3; eauto.
Defined.
*)
  
(*
Axiom evsys_reps: (ev_sys = Term_system.ev_sys).
*)

(*
Lemma evsys_tr_in:
  forall t p tr ev0,
    well_formed t ->
    Trace.trace t p tr ->
    ev_in ev0 (VmSemantics.ev_sys t p) ->
    In ev0 tr.
Proof.
  intros.
  (*
  rewrite evsys_reps in *. *)
  eapply Trace.evsys_tr_in; try eauto.
  eapply evsys_reps_refine; eauto.
Defined.
 *)

Create HintDb coree.

Print HintDb coree.
(*
Hint Resolve aff : coree.
*)

Lemma aff: forall es1 loc,
    store_event_evsys es1 loc ->
    exists ev, store_event ev loc /\ ev_in ev es1.
Proof.
  intros.
  induction H.
  -
    exists ev.
    split; eauto.
  -
    edestruct IHstore_event_evsys.
    destruct_conjs.
    exists x.
    split; eauto.
  -
    edestruct IHstore_event_evsys.
    destruct_conjs.
    exists x.
    split; eauto.
  -
    edestruct IHstore_event_evsys.
    destruct_conjs.
    exists x.
    split; eauto.
  -
    edestruct IHstore_event_evsys.
    destruct_conjs.
    exists x.
    split; eauto.
Defined.
Hint Resolve aff : coree.

Print HintDb coree.

Ltac eautoo := eauto with coree.

Theorem no_store_conflicts: forall t p sys,
    well_formed t ->
    sys = Term_system.ev_sys t p ->
    not (store_conflict sys).
Proof. (* with eautoo. *)
  Print Hint.
  Print HintDb core.
  Print ev_sys.
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
    (*
    rewrite evsys_reps in *. *)
    
    
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

        assert (exists ev, store_event ev loc /\ ev_in ev (Term_system.ev_sys t1 p1)).
        {
          eauto...
          eautoo.
          (*
          eapply aff; eauto.
           *)
          
        }
        assert (exists ev, store_event ev loc /\ ev_in ev (Term_system.ev_sys t2 p1)).
        {
          eapply aff; eauto.
        }
        destruct_conjs.

        
        assert (ev_in H0 (merge (S n, Nat.pred n0) (Term_system.ev_sys t1 p1) (Term_system.ev_sys t2 p1))).
        {
          eauto.
          (*
          apply ein_mergel.
          eauto. *)
        }
        
          

        assert (ev_in H6 (merge (S n, Nat.pred n0) (Term_system.ev_sys t1 p1) (Term_system.ev_sys t2 p1))).
        {
          eauto.
          (*
          apply ein_merger.
          eauto. *)
        }

        

        

        eapply unique_store_events' with (ev1:=H0) (ev2:=H6) (t:=(abpar (n, n0) l (n1,n2) (n3,n4) s t1 t2)) (p:=p1) (loc:=loc).
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
        inv H19.



        eapply unique_events; eauto.
      ++
        solve_by_inversion.

Defined.     
      
    


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



Lemma st_trace_irrel : forall t tr1 tr1' tr2 tr2' e e' e'' p p' p'' o o' o'',
    well_formed t ->
    copland_compile t
           {| st_ev := e;  st_trace := tr1; st_pl := p;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p'; st_store := o' |}) ->

    copland_compile t
           {| st_ev := e;  st_trace := tr2; st_pl := p;  st_store := o  |} =
    (Some tt, {| st_ev := e''; st_trace := tr2'; st_pl := p''; st_store := o'' |}) ->
    
    e' = e'' /\ p' = p'' /\ o' = o''.
Proof.
  intros.

  assert (st_ev
      (execSt (copland_compile t)
              {| st_ev := e;  st_trace := tr2; st_pl := p;  st_store := o  |}) = e').
  eapply trace_irrel_ev; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_pl
            (execSt (copland_compile t)
                    {| st_ev := e;  st_trace := tr2; st_pl := p;  st_store := o  |}) = p').
  eapply trace_irrel_pl; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_store
            (execSt (copland_compile t)
                    {| st_ev := e;  st_trace := tr2; st_pl := p;  st_store := o  |}) = o').
  eapply trace_irrel_store; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.
  repeat split; congruence.
Defined.

Lemma st_trace_cumul' : forall t m k e p o v,
    well_formed t ->
    copland_compile t
               {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |} =
    (Some tt, v) -> 
    st_trace
      ( execSt (copland_compile t)
               {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |}) =
    m ++
      st_trace
          (execSt (copland_compile t)
                  {| st_ev := e; st_trace := k; st_pl := p; st_store := o |}).
Proof.
  
  induction t; intros.
  -
    destruct r.
    destruct a;
      simpl;
      repeat rewrite app_assoc;
      reflexivity.
  -
    repeat (df; dohtac; df).
    repeat rewrite app_assoc.
    reflexivity.
  -
    df.
    annogo.
    do_wf_pieces.
    dosome.
    do_asome.
    subst.
    df.
    dohi.
    assert (
        StVM.st_trace
          (snd (copland_compile t1 {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |}))
        =
        m ++
          StVM.st_trace
          (snd (copland_compile t1 {| st_ev := e; st_trace := k; st_pl := p; st_store := o |}))).
    eapply IHt1; eauto.
    repeat subst'.
    simpl in *.
    subst.
    assert (
        StVM.st_trace
          (snd (copland_compile t2
           {| st_ev := st_ev0; st_trace := m ++ st_trace0; st_pl := st_pl0; st_store := st_store0 |})) =
        m ++
          StVM.st_trace
          (snd (copland_compile t2
           {| st_ev := st_ev0; st_trace := st_trace0; st_pl := st_pl0; st_store := st_store0 |}))) as HH.
    eapply IHt2; eauto.
    repeat (subst'; simpl in * ).
    eauto.
  - (* abseq case *)
    annogo.
        
    do_wf_pieces.
    df.
    dosome.

    do_asome.
    subst.
    df.
    annogo.
    df.
    dohi.

    assert (
        StVM.st_trace
           (snd (copland_compile t1 {| st_ev := splitEv s0 e; st_trace := m ++ (k ++ [Term.split n p]); st_pl := p; st_store := o |})) =
         m ++
         StVM.st_trace
         (snd (copland_compile t1 {| st_ev := splitEv s0 e; st_trace := k ++ [Term.split n p]; st_pl := p; st_store := o |}))).
    {
      rewrite <- app_assoc in *. (*Heqp4. *)
      eapply IHt1; eauto.
    }
    subst'.
    df.
    rewrite app_assoc in *.
    subst'.
    df.  
    subst.

    assert (
         StVM.st_trace (snd (copland_compile t2{| st_ev := splitEv s1 e; st_trace := m ++ st_trace0; st_pl := st_pl0; st_store := st_store0 |})) =
         m ++ StVM.st_trace (snd (copland_compile t2 {| st_ev := splitEv s1 e; st_trace := st_trace0; st_pl := st_pl0; st_store := st_store0 |}))
      ).
    eapply IHt2; eauto.
    subst'.
    df.
    tauto.  
  -
    do_wf_pieces.
    repeat (df; dohtac; df).
    repeat (rewrite app_assoc).
    tauto.
Defined.

(* Instance of st_trace_cumul' where k=[] *)
Lemma st_trace_cumul : forall t m e p o v,
    well_formed t ->
    copland_compile t
               {| st_ev := e; st_trace := m; st_pl := p; st_store := o |} =
    (Some tt, v) -> 
    
    st_trace
      (execSt (copland_compile t)
              {| st_ev := e; st_trace := m; st_pl := p; st_store := o |}) =
    m ++
      st_trace
      (execSt (copland_compile t)
                     {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}).
Proof.
  intros.
  assert (m = m ++ []) as HH by (rewrite app_nil_r; auto).
  rewrite HH at 1.
  eapply st_trace_cumul'; eauto.
  rewrite app_nil_r.
  eauto.
Defined.

Lemma suffix_prop : forall t e e' tr tr' p p' o o',
    well_formed t ->
    copland_compile t
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p;
             st_store := o |} =
    (Some tt, {|
      st_ev := e';
      st_trace := tr';
      st_pl := p';
      st_store := o' |}) ->
    exists l, tr' = tr ++ l.
Proof.
  intros.
  assert (st_trace
            (execSt (copland_compile t)
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p;
             st_store := o |}) =
    st_trace ({|
      st_ev := e';
      st_trace := tr';
      st_pl := p';
      st_store := o' |})) as H00.
  df.
  congruence.
  simpl in H00.
  eexists.
  rewrite <- H00.
  erewrite st_trace_cumul.
  eauto.
  eauto.
  eauto.
Defined.

Ltac do_suffix name :=
  match goal with
  | [H': copland_compile ?t
         {| st_ev := _;st_trace := ?tr; st_pl := _; st_store := _ |} =
         (Some tt,
          {| st_ev := _; st_trace := ?tr'; st_pl := _; st_store := _ |}),
         H2: well_formed ?t |- _] =>
    assert_new_proof_as_by
      (exists l, tr' = tr ++ l)
      ltac:(eapply suffix_prop; [apply H2 | apply H'])
             name
  end.

Lemma alseq_decomp : forall r lr t1' t2' e e'' p p'' o o'' tr,
    well_formed (alseq r lr t1' t2') ->
    copland_compile (alseq r lr t1' t2') {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p''; st_store := o'' |}) ->

    exists e' tr' p' o',
      copland_compile t1' {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
      (Some  tt, {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |}) /\
      exists tr'',
        copland_compile t2' {| st_ev := e'; st_trace := []; st_pl := p'; st_store := o' |} =
        (Some tt, {| st_ev := e''; st_trace := tr''; st_pl := p''; st_store := o'' |}) /\
        tr = tr' ++ tr''.     
Proof.
  intros.  
  do_wf_pieces.
  df.
  dosome.
  annogo.
  exists st_ev. exists st_trace. exists st_pl. exists st_store.
  split.
  reflexivity.
  destruct
    (copland_compile t2'
                {| st_ev := st_ev; st_trace := []; st_pl := st_pl; st_store := st_store |}) eqn:hey.
  vmsts.
  do_asome.
  subst.
  annogo.

  exists st_trace0.
  dohi.
  
  split.
  reflexivity.

  pose st_trace_cumul.
  specialize st_trace_cumul with (t:= t2') (m:=st_trace) (e:=st_ev) (p:= st_pl)
                      (o:=st_store)
                      (v:={| st_ev := st_ev0; st_trace := tr; st_pl := st_pl0; st_store := st_store0 |}).
  intros.
  repeat concludes.
  df.
  subst'.
  df.
  tauto. 
Defined.

Lemma restl : forall t e e' x tr p p' o o',
    well_formed t ->
    copland_compile t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |}) ->

    copland_compile t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}).
Proof.
  intros.
  
  assert (
      st_trace (run_cvm t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |}) =
      st_trace ({| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |})).
  {
    unfold run_cvm. 
    monad_unfold.
    subst'.
    simpl.
    reflexivity.
  }
  
  unfold run_cvm in *.
  assert (
   st_ev
     (execSt
        (copland_compile t)
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) = e').
  eapply trace_irrel_ev; eauto.

  assert (
   st_pl
     (execSt
        (copland_compile t)
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) = p').
  eapply trace_irrel_pl; eauto.

  assert (
   st_store
     (execSt
        (copland_compile t)
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) = o').
  eapply trace_irrel_store; eauto.

  assert (
      (execSt
         (copland_compile t)
         {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) =
      {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}).
  {
    eapply st_congr; eauto.
    erewrite st_trace_cumul in H1.
    eapply app_inv_head.
    eauto.
    eauto.
    eauto.
  }
  
  destruct (copland_compile t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) eqn:aa.
  simpl in *.
  vmsts.
  simpl in *.
  repeat find_inversion.
  do_asome.
  df.
  tauto.
Defined.

Ltac do_restl :=
  match goal with
  | [H: copland_compile ?t
        {| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_store := ?o |} =
        (Some tt,
         {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_pl := ?p'; st_store := ?o' |}),
        H2: well_formed ?t |- _] =>
    assert_new_proof_by
      (copland_compile t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
       (Some tt,
        {| st_ev := e'; st_trace := x; st_pl := p'; st_store := o' |}))
      ltac:(eapply restl; [apply H2 | apply H])
  end.

Lemma cvm_refines_lts_evidence : forall t tr tr' e e' p p' o o' es e's,
    well_formed t ->
    copland_compile t (mk_st e tr p o) = (Some tt, (mk_st e' tr' p' o')) ->
    Ev_Shape e es ->
    Term.eval (unanno t) p es = e's ->
    Ev_Shape e' e's.
Proof.
  induction t; intros.
  -
    destruct a;
      try (
          df;
          eauto).
  -
    do_wf_pieces.
    repeat (df; dohtac; df).    
    annogo.
    eapply IHt.
    eassumption.
    eapply copland_compile_at; eauto.
    eassumption.
    reflexivity.
  -
    do_wf_pieces.
    do_suffix blah.
    destruct_conjs.
    subst.

    edestruct alseq_decomp.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.
    destruct_conjs.
    df.
    dosome.
    
    eapply IHt2.
    + eassumption.
    + eassumption.
    + eapply IHt1.
      ++ eassumption.
      ++ eassumption.
      ++ eassumption.      
      ++ reflexivity.
    +
      repeat do_pl_immut.
      subst.
      congruence.     
  -
    do_wf_pieces.
    df.
    repeat break_match;
      try solve_by_inversion;
      try (df; tauto).
    +
      df.
      annogo.
      simpl in *.
      do_suffix blah.
      do_suffix blah'.
      destruct_conjs; subst.
      repeat do_restl.
      
      econstructor.
      destruct s0.
      ++
        eapply IHt1; eauto.
      ++
        simpl in *.
        eapply IHt1; eauto.
      ++
        destruct s1.
        +++
          simpl.
          repeat do_pl_immut.
          subst.
          eapply IHt2; eauto.
        +++
          simpl.
          repeat do_pl_immut.
          subst.
          eapply IHt2; eauto.      
  -
    do_wf_pieces.
    repeat (df; dohtac; df).
    econstructor.
    destruct s0.
    +
      simpl.
      eapply IHt1.
      apply H3.     
      eapply copland_compile_par.
      eassumption.
      eassumption.
      tauto.
    +
      simpl.
      eapply IHt1.
      eassumption.
      eapply copland_compile_par.
      eassumption.
      econstructor.
      tauto.
    +
      destruct s1.
      ++
        simpl.
        eapply IHt2.
        eassumption.
        eapply copland_compile_par.
        eassumption.
        eassumption.
        tauto.
      ++
        simpl.
        eapply IHt2.
        eassumption.
        eapply copland_compile_par.
        eassumption.
        econstructor.
        eauto.
        Unshelve.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
Defined.
   
Lemma cvm_refines_lts_event_ordering : forall t tr et e e' p p' o o',
    well_formed t ->
    copland_compile t (mk_st e [] p o) = (Some tt, (mk_st e' tr p' o')) ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros t tr et e e' p p' o o' H.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    destruct a;
      df;
      econstructor; try (econstructor; reflexivity).
  - (* aatt case *)
    do_wf_pieces.
    destruct r.
    repeat (df; dohtac; df).
    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    cbn.
    eapply IHt; eauto.
    apply copland_compile_at.
    eassumption.
    econstructor.
    apply stattstop.
    econstructor.
  -  
    do_wf_pieces.  
    edestruct alseq_decomp; eauto.
    destruct_conjs.         
    econstructor.
    econstructor.
    subst.
    eapply lstar_transitive.
    eapply lstar_stls.
    df.
    eapply IHt1.
    eassumption.
    eassumption.
    eapply lstar_silent_tran.
    apply stlseqstop.
    df.
    repeat do_pl_immut.
    subst.   
    eapply IHt2; eauto.    
  -    
    do_wf_pieces.
    destruct r; destruct s.
    df.
    vmsts.
    dosome.
    df.

    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat do_pl_immut.
    subst.
    repeat rewrite <- app_assoc.

    eapply lstar_tran.
    econstructor.
    simpl.

    eapply lstar_transitive.
    simpl.

    eapply lstar_stbsl.  
     
    eapply IHt1.
    eassumption.
    eassumption.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
        
    eapply IHt2.
    eassumption.
    eassumption.

    econstructor.
    eapply stbsrstop.
    econstructor.
  -
    destruct s; destruct r; destruct l.
    repeat (df; dohtac; df).
    econstructor.
    (*
    assert (n1 = fst (range t1)).
    {
      rewrite Heqr.
      eauto.
    }
    assert (n3 = fst (range t2)).
    {
      rewrite Heqr0.
      eauto.
    }
    subst. *)
    econstructor.
    eapply lstar_transitive.
    simpl.
    apply bpar_shuffle.
    econstructor.
    (*
    assert (n2 = snd (range t1)).
    {
      rewrite Heqr.
      eauto.
    }
    assert (n4 = snd (range t2)).
    {
      rewrite Heqr0.
      eauto.
    }
    subst.
     *)
    
    
    apply stbpstop.
    econstructor.     
    Unshelve.
    exact mtc.
    eauto. 
Defined.

Lemma cvm_refines_lts_event_ordering_corrolary : forall t tr et e e' p p' o o',
    well_formed t -> 
    copland_compile t (mk_st e [] p o) = (Some tt, (mk_st e' tr p' o')) ->
    st_trace (run_cvm t
                     (mk_st e [] p o)) = tr ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  destruct (copland_compile t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) eqn:hi.
  simpl in *.
  vmsts.
  simpl in *.
  apply cvm_refines_lts_event_ordering with (t:=t) (tr:=tr) (e:=e) (p:=p) (o:=o) (e':=st_ev) (p':=st_pl) (o':=st_store); eauto.
  destruct o0.
  dunit.
  rewrite hi.
  unfold run_cvm in *.
  monad_unfold.
  rewrite hi in *.
  simpl in *.
  subst.
  reflexivity.
  solve_by_inversion.
Defined.

Theorem cvm_respects_event_system' : forall t tr ev0 ev1 e e' o o',
    well_formed t -> 
    copland_compile 
      t
      (mk_st e [] 0 o) =
      (Some tt, (mk_st e' tr 0 o')) ->
    prec (Term_system.ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  eapply ordered with (p:=0) (e:=mt); eauto.
  eapply cvm_refines_lts_event_ordering; eauto.
Defined.

Theorem cvm_respects_event_system : forall t tr ev0 ev1 e e' o o' t',
    t = annotated t' -> 
    copland_compile
      t
      (mk_st e [] 0 o) =
      (Some tt, (mk_st e' tr 0 o')) ->
    prec (Term_system.ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  assert (well_formed t).
  unfold annotated in H.
    subst.
    eapply anno_well_formed; eauto.
    eapply ordered with (p:=0) (e:=mt); eauto.
    eapply cvm_refines_lts_event_ordering; eauto.
Defined.
