Require Import EqClass Maps Term_Defs Auto.

Require Import List.
Require Import Lists.List.
Import ListNotations.

Require Import Lia Coq.Arith.PeanoNat.

Require Import StructTact.StructTactics.

Set Nested Proofs Allowed.

Require Import MSets.

Module SetM := Make Nat_as_OT.


Definition test := SetM.union (SetM.singleton 42)
                           (SetM.empty).
Compute SetM.mem 0 test.

Fixpoint num_ats (t:Term): nat :=
  match t with
  | asp _ => 0
  | att _ t' => S (num_ats t')
  | lseq t1 t2 => (num_ats t1) + (num_ats t2)
  end.
    
Fixpoint places (t:Term): list Plc :=
  match t with
  | asp _ => []
  | att q t' => q :: (places t')
  | lseq t1 t2 => (places t1) ++ (places t2)
  end.

Fixpoint placesM (t:Term): SetM.t :=
  match t with
  | asp _ => SetM.empty
  | att q t' => SetM.add q (placesM t')
  | lseq t1 t2 => SetM.union (placesM t1) (placesM t2)
  end.

Lemma places_iff_placesM: forall t x,
    In x (places t) <-> SetM.In x (placesM t).
Proof.
  split.
  -
  induction t; intros.
  +
    destruct a;
      df;
      solve_by_inversion.
  +
    df.
    destruct H.
    ++
    subst.
    rewrite SetM.add_spec.
    eauto.
    ++
      rewrite SetM.add_spec.
      right.
      eauto.
  +
    df.
    rewrite SetM.union_spec.
    apply in_app_or in H.
    destruct H; eauto.
  -
    generalizeEverythingElse t.
    induction t; intros.
    +
      destruct a;
        df; try solve_by_inversion.
    +
      df.
      rewrite SetM.add_spec in *.
      destruct H.
      ++
      left.
      lia.
      ++
        right.
        eauto.
    +
      df.
      rewrite SetM.union_spec in *.
      destruct H;
        apply in_or_app;
        eauto.
Defined.





(*
Definition inc_vm_id (m:VMID_Map) (p:Plc) : (VM_ID*VMID_Map) :=
  let val := map_get m p in
  match val with
  | Some v => (v,map_replace m p (v + 1))
  | None => (0,map_set m p 1)
  end.
 *)






(*
Inductive TermN : SetM.t -> Type :=
| aspN: forall s, ASP -> TermN s
| attN: forall s s', {x:Plc | SetM.In x s} -> TermN s' -> SetM.Subset s' s -> TermN s
| lseqN: forall s1 s2, TermN s1 -> TermN s2 -> TermN (SetM.union s1 s2).
*)

Inductive TermN : SetM.t -> Type :=
| aspN: ASP -> TermN SetM.empty
| attN{s:SetM.t} (x:Plc): TermN s -> TermN (SetM.add x s)
| lseqN{s1 s2:SetM.t}: TermN s1 -> TermN s2 -> TermN (SetM.union s1 s2).

Definition mod_In_pfs (x:Plc) (s:SetM.t)
           (pr:{n : nat | SetM.In n s}) :
  {n:nat | SetM.In n (SetM.add x s)}.
Proof.
  invc pr.
  assert (SetM.In x0 (SetM.add x s)).
  {
    rewrite SetM.add_spec.
    right.
    eassumption.
  }
  econstructor.
  eassumption.
Defined.

Definition mod_In_unioin_pfsL (s1 s2:SetM.t)
           (pr:{n:nat | SetM.In n s1}) :
  {n: nat | SetM.In n (SetM.union s1 s2)}.
Proof.
  invc pr.
  econstructor.
  rewrite SetM.union_spec.
  left.
  eassumption.
Defined.

Definition mod_In_unioin_pfsR (s1 s2:SetM.t)
           (pr:{n:nat | SetM.In n s2}) :
  {n: nat | SetM.In n (SetM.union s1 s2)}.
Proof.
  invc pr.
  econstructor.
  rewrite SetM.union_spec.
  right.
  eassumption.
Defined.


Definition getPlaceDeps{s:SetM.t} (t:TermN s) : list {n:Plc | SetM.In n s}.
Proof.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      exact [].
  -
    assert (SetM.In x (SetM.add x s)).
    {
      rewrite SetM.add_spec.
      left.
      tauto.
    }
    exact ((exist _ x H) :: map (mod_In_pfs x s) IHt).
  -
    exact ((map (mod_In_unioin_pfsL s1 s2) IHt1) ++
           (map (mod_In_unioin_pfsR s1 s2) IHt2)).
Defined.



                                                
    
      
    
    
  
    
    
    
  

Lemma hin: SetM.In 2 (SetM.add 2 SetM.empty).
Proof.
  assert (SetM.mem 2 (SetM.add 2 SetM.empty) = true).
  {
    df.
    tauto.
  }
  rewrite <- SetM.mem_spec.
  eassumption.
Defined.

(*
Definition term_hin : (TermN [2;3]) := attN [2;3] (exist _ 2 hin) (aspN [2;3] CPY).
 *)

(*
Definition term_hin : (TermN  (SetM.add 2 SetM.empty)).
  Check attN.
  refine (attN _ SetM.empty (exist _ 2 _) (aspN _ CPY) _).
  apply hin.
  rewrite <- SetM.subset_spec.
  df.
  tauto.
Defined.
 *)

Definition term_hin_empty : (TermN SetM.empty).
Proof.
  refine (aspN _).
  exact SIG.
Defined.


Definition term_hin : (TermN (SetM.add 2 SetM.empty)).
  Check attN.
  Check aspN.
  refine (attN 2 _).
  refine (aspN _).
  exact CPY.
Defined.

(*
Print well_founded.
Print Acc.

Fixpoint tsize (t:Term) :=
  match t with
  | asp _ => 1
  | att _ t => 1 + tsize t
  | lseq t1 t2 => tsize t1 + tsize t2
  end.

Lemma tsize_always_gt_zero : forall t, tsize t > 0.
Proof.
  intros.
  induction t; intros;
    try (df; lia).
Defined.

Definition lengthOrder (t1 t2 : Term) :=
  tsize t1 < tsize t2.
    
    
    


Lemma lengthOrder_wf : well_founded lengthOrder.
Proof.
  unfold well_founded.
  intros.
  unfold lengthOrder.
  econstructor.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    df.
    destruct a;
    assert (tsize y > 0) by eapply tsize_always_gt_zero; eauto;
      lia.
  -
    econstructor.
    intros.
    df.
    pose (IHa y0).
    apply a0.
    lia.
  -
    df.
    econstructor.
    intros.

    econstructor.
    intros.
Admitted.
*)


(*
Check Fix.

Definition flatten_term_fixed (t:Term) : TermN (placesM t) :=
  refine (Fix lengthOrder_wf (fun 
*)

Definition getPlaces{s:SetM.t} (tn:TermN s) : SetM.t.
Proof.
  exact s.
Defined.

(*

Lemma in_get_places: forall x s1 s2 t1 t2,
    In x (getPlaces (@lseqN s1 s2 t1 t2)) ->
    In x (@getPlaces s1 t1) \/ In x (@getPlaces s2 t2).
Proof.
  intros.
  df.
  cbv in H.


  
Admitted.

Lemma get_places_at: forall x0 s t x,
    In x0 (getPlaces t) ->
    In x0 (getPlaces (@attN s x t)).
Proof.
Admitted.

Lemma in_get_lseq_unionL: forall s1 s2 t1 t2 x,
    In x (getPlaces t1) ->
    In x (getPlaces (@lseqN s1 s2 t1 t2)).
Proof.
Admitted.

Lemma in_get_lseq_unionR: forall s1 s2 t1 t2 x,
    In x (getPlaces t2) ->
    In x (getPlaces (@lseqN s1 s2 t1 t2)).
Proof.
Admitted.
*)

Lemma places_same_termN{s:SetM.t} : forall (t:TermN s) x,
    SetM.In x (getPlaces t) <-> SetM.In x s.
Proof.
  intros.
  unfold getPlaces.
  tauto.
Defined.

(*
  intros.
  split.
  -
    generalizeEverythingElse t.
    induction t; intros.
    +
      df.
      solve_by_inversion.
    +
      destruct H.
      ++
        subst.
        rewrite SetM.add_spec.
        eauto.
      ++
        rewrite SetM.add_spec.
        right.
        apply IHt.
        eassumption.
    +
      eapply in_get_places in H.
      destruct H;
      rewrite SetM.union_spec;
      eauto.
  -
    generalizeEverythingElse t.
    induction t; intros.
    +
      df.
      invc H.
    +
      rewrite SetM.add_spec in *.
      destruct H.
      ++
        subst.
        df.
        left.
        eauto.
      ++
        assert (In x0 (getPlaces t)) by eauto.



        eapply get_places_at; eauto.
    +
      rewrite SetM.union_spec in *.
      destruct H.
      ++
        assert (In x (getPlaces t1)) by eauto.


        eapply in_get_lseq_unionL; eauto.

      ++


        
        eapply in_get_lseq_unionR; eauto.
Defined.
*)

      
        
        
      

    
    


Definition flatten_term_fixed (t:Term) : TermN (placesM t).
Proof.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a.
    +
      df.
      exact (aspN SIG).
      (*
      exact (aspN CPY). *)
    +
      df.
      exact (aspN (ASPC n l)).
    +
      df.
      exact (aspN SIG).
    +
      df.
      exact (aspN HSH).
  -
    df.
    Check attN.
    
    (*refine ((attN _ _ _ (flatten_term_fixed t) _)). *)
    refine ((attN n _)).
    eassumption.
    (*
    refine (exist _ n _).
    rewrite SetM.add_spec.
    left.
    tauto.
    apply IHt.
    unfold SetM.Subset.
    intros.
    apply SetM.add_spec.
    right.
    eassumption. *)
  -
    df.
    Check lseqN.

    refine (lseqN _ _);
      eassumption.
Defined.

Check flatten_term_fixed.
Print flatten_term_fixed.

Compute (flatten_term_fixed (att 1 (asp CPY))).

Check Term_rect.
Print Term_rect.

Check (flatten_term_fixed (att 3 ((att 4(asp CPY))))).

Print TermN.



(*
Inductive term_placesN_r{s:SetM.t} : TermN s -> Plc -> Prop :=
| atPlaceN: forall q t', term_placesN_r (attN q t') q.
| atRecPlaceN: forall x q t',
    term_placesN_r t' x ->
    term_placesN_r (att q t') x
| atLseqPlacelN: forall t1 t2 p,
    term_placesN_r t1 p ->
    term_placesN_r (lseq t1 t2) p
| atLseqPlacerN: forall t1 t2 p,
    term_placesN_r t2 p ->
    term_placesN_r (lseq t1 t2) p.
*)


Inductive term_places_r : Term -> Plc -> Prop :=
| atPlace: forall q t', term_places_r (att q t') q
| atRecPlace: forall x q t',
    term_places_r t' x ->
    term_places_r (att q t') x
| atLseqPlacel: forall t1 t2 p,
    term_places_r t1 p ->
    term_places_r (lseq t1 t2) p
| atLseqPlacer: forall t1 t2 p,
    term_places_r t2 p ->
    term_places_r (lseq t1 t2) p.

(*
Lemma places_iff_placesM: forall t x,
    In x (places t) <-> SetM.In x (placesM t).
Proof.
*)
  

Lemma term_places_iff_rel: forall t p,
    term_places_r t p <-> In p (places t).
Proof.
  split.
  -
    generalizeEverythingElse t.
    induction t; intros; df.
    +
      solve_by_inversion.
    +
      
      invc H.
      ++
        left.
        tauto.
      ++
        assert (In p (places t)) by eauto.
        right.
        eauto.
    +
      invc H.
      ++
        assert (In p (places t1)) by eauto.
        eapply in_or_app. eauto.
      ++
        assert (In p (places t2)) by eauto.
        eapply in_or_app. eauto.
  -
    intros.
    generalizeEverythingElse t.
    induction t; intros; df.
    +
      solve_by_inversion.
    +
      destruct H.
      ++
        subst.
        econstructor.
      ++
        assert (term_places_r t p) by eauto.
        econstructor.
        eauto.
    +
      apply in_app_or in H.
      destruct H.
      ++
        assert (term_places_r t1 p) by eauto.
        econstructor; eauto.
      ++
        assert (term_places_r t2 p) by eauto.
        eapply atLseqPlacer; eauto.
Defined.

Lemma term_places_set: forall t p,
    SetM.In p (placesM t) <-> term_places_r t p.
Proof.
  intros.
  rewrite term_places_iff_rel.
  rewrite places_iff_placesM.
  tauto.
Defined.

    

(*
Definition flatten_term_fixed (t:Term) : TermN (placesM t).
 *)

Check getPlaces.

Lemma thisone: forall p t,
    SetM.In p (getPlaces (flatten_term_fixed t)) <-> term_places_r t p.
Proof.
  intros.
  rewrite <- term_places_set.
  unfold getPlaces.
  tauto.
Defined.

  

(*
      
      







Fixpoint flatten_term' (t:Term) (n:nat) (m:MapC VM_ID Plc): (nat * ((MapC VM_ID Plc) * Term)) :=
  match t with
  | asp _ => (n,(m,t))
  | att q t' =>
    let '(n',(m',t'')) := flatten_term' t' (n + 1) (map_set m n q) in
    (n', (m',att n t''))
  | lseq t1 t2 =>
    let '(n',(m',t1')) := flatten_term' t1 n m in
    let '(n'',(m'',t2')) := flatten_term' t2 n' m' in
    (n'', (m'', lseq t1' t2'))
  end.

Definition flatten_term_init (t:Term) : (MapC VM_ID Plc * Term) :=
  let '(n', (m', t')) := flatten_term' t 1 [] in
  (m',t').

Definition flatten_term (t:Term): Term :=
  snd (flatten_term_init t).

Definition flatten_term_map (t:Term): MapC VM_ID Plc :=
  fst (flatten_term_init t).
          
Lemma numats_places: forall t,
    length (places t) = num_ats t.
Proof.
  intros.
  induction t; intros.
  -
    df.
    tauto.
  -
    df.
    eauto.
  -
    df.
    Search (length (_ ++ _)).
    erewrite app_length.
    eauto.
Defined.

Lemma flatten_numats: forall t i i' m m' t',
    flatten_term' t i m = (i', (m',t')) ->
    i' = i + (num_ats t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    df.
    lia.
  -
    df.
    assert (i' = (i + 1) + num_ats t) by eauto.
    subst.
    lia.
  -
    df.
    assert (n = i + num_ats t1) by eauto.
    assert (i' = n + num_ats t2) by eauto.
    lia.
Defined.

Lemma flatten_attnum: forall t n n' m m' t',
    flatten_term' t n m = (n', (m', t')) ->
    places t' = seq n (num_ats t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    df.
    tauto.
  -
    df.
    
    assert (places t0 = seq (n0 + 1) (num_ats t)).
    {
      eapply IHt.
      eauto.
    }
    find_rewrite.

    assert (n0 + 1 = S n0) by lia.
    rewrite H0.
    tauto.
  -
    df.
    assert(places t = seq n (num_ats t1)) by eauto.

    assert (places t0 = seq n0 (num_ats t2)) by eauto.

    repeat find_rewrite.

    repeat erewrite seq_app.

    assert (n0 = n + (num_ats t1)).
    {
      eapply flatten_numats; eauto.
    }

    repeat find_rewrite.
    tauto.
Defined.

(*
Definition map_union{A B:Type} `{H : EqClass A} (m:MapC A B) (n:MapC A B): MapC A B.
Admitted.
*)

Definition dom_union{A: Type} (l:list A) (l':list A): list A.
Admitted.

Axiom dom_union_nil_r: forall A (l:list A), dom_union l [] = l.

Axiom dom_union_nil_l: forall A (l:list A), dom_union [] l = l.

Axiom dom_union_cons: forall A (x:A) l l',
    dom_union (x::l) l' =
    dom_union l (x::l').

Axiom dom_union_app: forall A (l1 l2 l3:list A),
    dom_union l1 (l2 ++ l3) = dom_union (dom_union l1 l2) l3.

Lemma map_dom_places: forall t n m,
    map_dom (fst (snd (flatten_term' t n m))) = dom_union (map_dom m) (seq n (num_ats t)).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    df.
    rewrite dom_union_nil_r.
    tauto.
  -
    df.
    unfold map_set in *.
    df.

    specialize IHt with(n:=n0 + 1) (m:=  ((n0, n) :: m)).
    repeat break_let.
    repeat find_inversion.
    df.
    rewrite IHt.
    simpl.

    assert (S n0 = n0 + 1) by lia.
    rewrite H.

    rewrite dom_union_cons.
    tauto.
  -
    df.
    specialize IHt1 with (n:=n) (m:=m).

    specialize IHt2 with (n:= n0) (m:=m0).
    repeat break_let.
    repeat find_inversion.

    df.
    rewrite IHt2.
    rewrite IHt1.

    rewrite seq_app.

    assert (seq (n + num_ats t1) (num_ats t2) =
            seq n0 (num_ats t2)).
    {
      assert (n0 = n + num_ats t1).
      {
        eapply flatten_numats; eauto.
      }
      congruence.
    }
    rewrite H.

    rewrite dom_union_app.
    tauto.
Defined.

Lemma map_dom_places': forall t n,
    map_dom (fst (snd (flatten_term' t n []))) = (seq n (num_ats t)).
Proof.
  intros.
  assert (seq n (num_ats t) = dom_union [] (seq n (num_ats t))).
  {
    rewrite dom_union_nil_l.
    tauto.
  }
  rewrite H.
  eapply map_dom_places.
Defined.

Lemma map_dom_places_corr: forall t,
    (*map_dom (fst (flatten_term_init t)) = seq 1 (num_ats t). *)
    map_dom (flatten_term_map t) = seq 1 (num_ats t).
Proof.
  intros.
  unfold flatten_term_map.
  unfold flatten_term_init.
  repeat break_let.
  df.
  assert (m = fst (snd (flatten_term' t 1 []))).
  {
    find_rewrite.
    tauto.
  }
  rewrite H.
  eapply map_dom_places'.
Defined.
  
Lemma seq_places: forall t,
    places (flatten_term t) = seq 1 (num_ats t).
Proof.
  intros.
  induction t.
  -
    df.
    tauto.
  -
    df.
    unfold flatten_term in *.
    unfold flatten_term_init in *.
    repeat break_let.
    df.
    unfold map_set in *.

    assert (places t2 = seq 2 (num_ats t)).
    {

      eapply flatten_attnum; eauto.
    }
    congruence.
  -
    df.
    unfold flatten_term in *.
   
    repeat erewrite seq_app.

    rewrite <- IHt1.

    unfold flatten_term_init in *.

    repeat break_let.
    repeat find_inversion.
    df.

    assert (places t0 = seq 1 (num_ats t1)).
    {
      eapply flatten_attnum; eauto.
    }
    find_rewrite.

    (*

    unfold flatten_term_init in Heqp0.
    repeat break_let.

    repeat find_rewrite. *)
    assert (places t5 = seq n0 (num_ats t2)).
    {
      eapply flatten_attnum; eauto.
    }
    repeat find_rewrite.

    repeat find_inversion.

    assert (n0 = 1 + (num_ats t1)).
    {
      eapply flatten_numats; eauto.
    }
    repeat find_rewrite.
    simpl.
    tauto.
Defined.

Lemma map_eq_places: forall t,
    (*map_dom (fst (flatten_term_init t)) = places (snd (flatten_term_init t)). *)
    map_dom (flatten_term_map t) = places (flatten_term t).
Proof.
  intros.
  rewrite seq_places.
  rewrite map_dom_places_corr.
  tauto.
Defined.

Definition VMID_Map := (MapC VM_ID Plc).
    
Inductive term_places_r : Term -> Plc -> Prop :=
| atPlace: forall q t', term_places_r (att q t') q
| atRecPlace: forall x q t',
    term_places_r t' x ->
    term_places_r (att q t') x
| atLseqPlacel: forall t1 t2 p,
    term_places_r t1 p ->
    term_places_r (lseq t1 t2) p
| atLseqPlacer: forall t1 t2 p,
    term_places_r t2 p ->
    term_places_r (lseq t1 t2) p.

Lemma term_places_iff_rel: forall t p,
    term_places_r t p <-> In p (places t).
Proof.
  split.
  -
    generalizeEverythingElse t.
    induction t; intros; df.
    +
      solve_by_inversion.
    +
      
      invc H.
      ++
        left.
        tauto.
      ++
        assert (In p (places t)) by eauto.
        right.
        eauto.
    +
      invc H.
      ++
        assert (In p (places t1)) by eauto.
        eapply in_or_app. eauto.
      ++
        assert (In p (places t2)) by eauto.
        eapply in_or_app. eauto.
  -
    intros.
    generalizeEverythingElse t.
    induction t; intros; df.
    +
      solve_by_inversion.
    +
      destruct H.
      ++
        subst.
        econstructor.
      ++
        assert (term_places_r t p) by eauto.
        econstructor.
        eauto.
    +
      apply in_app_or in H.
      destruct H.
      ++
        assert (term_places_r t1 p) by eauto.
        econstructor; eauto.
      ++
        assert (term_places_r t2 p) by eauto.
        eapply atLseqPlacer; eauto.
Defined.



*)
