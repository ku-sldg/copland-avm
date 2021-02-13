Require Import EqClass Maps Term_Defs Auto.

Require Import List.
Require Import Lists.List.
Import ListNotations.

Require Import Lia Coq.Arith.PeanoNat  Coq.Program.Tactics Coq.Program.Equality.

Require Import StructTact.StructTactics.

Require Import StructTact.Fin.

Set Nested Proofs Allowed.

(*
Require Import MSets.

Module SetM := Make Nat_as_OT.


Definition test := SetM.union (SetM.singleton 42)
                           (SetM.empty).
Compute SetM.mem 0 test.
*)

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

Inductive TermFin (n:nat): Type :=
| aspF: ASP -> TermFin n
| attF: (fin n) -> TermFin n -> TermFin n
| lseqFin: TermFin n -> TermFin n -> TermFin n.

Fixpoint placesF{n:nat} (t:TermFin n): list (fin n) :=
  match t with
  | aspF _ _ => []
  | attF _ q t' => q :: (placesF t')
  | lseqFin _ t1 t2 => (placesF t1) ++ (placesF t2)
  end.

Fixpoint term_to_termFin' {n:nat} (t:Term) (l:list (fin n)) :
  option (list (fin n) * TermFin n) :=
  match t with
  | asp a => Some (l,aspF n a)
                 
  | att p t' =>
    let mh := hd_error l in
    match mh with
    | Some v =>
      let mRec := term_to_termFin' t' (tl l) in
      match mRec with
      | Some (l',t'') => Some (l', attF n v t'')
      | _ => None
      end    
    | _ => None
    end
  | lseq t1 t2 =>
    let m1 := term_to_termFin' t1 l in
    match m1 with
    | Some (l',t1') =>
      let m2 := term_to_termFin' t2 l' in
      match m2 with
      | Some (l'',t2') => Some (l'', lseqFin n t1' t2')
      | _ => None
      end
    | _ => None
    end
  end.

Fixpoint tsize (t:Term) :=
  match t with
  | asp _ => 0
  | att _ t => 1 + tsize t
  | lseq t1 t2 => tsize t1 + tsize t2
  end.

Lemma skipn_assoc{A:Type}: forall (ls:list A) n1 n2,
    skipn n2 (skipn n1 ls) = skipn (n1 + n2) ls.
Proof.
  intros.
  generalizeEverythingElse ls.
  induction ls; intros.
  -
    Search skipn.
    repeat rewrite More_lists.skipn_nil.
    tauto.
  -
    destruct n1.
    +
      df.
      tauto.
    +
      df.
      eauto.
Defined.

Lemma fin_succeeds_resl{n:nat} : forall t t' (ls: list (fin n)) ls',
    term_to_termFin' t ls = Some (ls',t') ->
    ls' = skipn (tsize t) ls.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      df;
      tauto.
  -
    df.
    repeat break_match; try solve_by_inversion.
    df.
    eauto.
  -
    df.
    repeat break_match; try solve_by_inversion.
    df.

    assert (l = skipn (tsize t1) ls) by eauto.
    assert (ls' = skipn (tsize t2) l) by eauto.
    subst.
    eapply skipn_assoc.
Defined.

Lemma fin'_always_some{n:nat} : forall t (ls: list (fin n)),
    length ls >= (tsize t) ->
    exists l' tf,
      term_to_termFin' t ls = Some (l',tf).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    df.
    eauto.
  -
    df.
    assert (exists v, hd_error ls = (Some v)) as HH.
    {
      destruct ls; try solve_by_inversion.
      df.
      eauto.
    }
    destruct_conjs.
    rewrite H0.
    clear H0.
    pose (IHt n0 (tl ls)).
    assert (length (tl ls) >= tsize t).
    {
      destruct ls.
      +
        df.
        lia.
      +
        df.
        lia.
    }
    pose (e H0).
    destruct_conjs.

    rewrite H2.
    eauto.
  -
    df.

    pose (IHt1 n ls).

    Search firstn.

    assert (length ls >= tsize t1).
    {
      lia.
    }

    pose (e H0).
    destruct_conjs.

    assert (e0 = skipn (tsize t1) ls).
    {
      eapply fin_succeeds_resl; eauto.
    }
    

    
    rewrite H2.
    clear H2.
    rewrite H3.
    clear H3.

    pose (IHt2 n (skipn (tsize t1) ls)).

    assert (length (skipn (tsize t1) ls) >= tsize t2).
    {
      Search skipn.

      (* skipn_length :: length (skipn n l) = length l - n *)
      assert (length (skipn (tsize t1) ls) = length ls - (tsize t1)).
      {
        eapply skipn_length.
      }
      rewrite H2.
      lia.
    }

    pose (e1 H2).
    destruct_conjs.
    rewrite H4.
    eauto.
Defined.

Lemma length_allfin: forall n,
    length (all_fin n) = n.
Proof.
  intros.
  induction n; intros.
  -
    df.
    tauto.
  -
    df.
    Search map.
    erewrite map_length.
    eauto.
Defined.

Lemma tail_len{A:Type}: forall (ls: list A) n,
    length ls = S n ->
    length (tl ls) >= n.
Proof.
  intros.
  generalizeEverythingElse ls.
  induction ls; intros.
  -
    df.
    lia.
  -
    df.
    lia.
Defined.

Definition term_to_termFin (t:Term) : option (list (fin (tsize t)) * TermFin (tsize t)) :=
  @term_to_termFin' (tsize t) t (all_fin (tsize t) ).

Lemma term_to_termFin_always_Some : forall t,
    (* exists (l':list (fin (tsize t))) t', *)
    exists l' t',
      term_to_termFin t = Some (l', t').
Proof.
  intros.
  induction t; intros.
  -
    destruct a;
    df;
    eauto.
  -
    df.
    assert ((map (fun x : fin (tsize t) => Some x) (all_fin (tsize t))) =
            tl (all_fin (S (tsize t)))) as HH.
    {
      df.
      tauto.
    }
    rewrite HH.
    clear HH.

    assert (exists l' tf,
               term_to_termFin' t (tl (all_fin (S (tsize t)))) = Some (l',tf)).
    {
      eapply fin'_always_some.
      eapply tail_len.
      eapply length_allfin.
    }
    destruct_conjs.
    rewrite H1.
    eauto.
  -
    destruct_conjs.
    df.
    assert (exists l' tf,
               term_to_termFin' t1  (all_fin (tsize t1 + tsize t2)) = Some (l',tf)).
    {
      eapply fin'_always_some.
      assert (length (all_fin (tsize t1 + tsize t2)) = (tsize t1 + tsize t2)).
      {
        eapply length_allfin.
      }
      lia.
    }
    destruct_conjs.
    rewrite H5.

    assert (H3 = skipn (tsize t1) (all_fin (tsize t1 + tsize t2))).
    {
      eapply  fin_succeeds_resl.
      eassumption.
    }
    rewrite H6.
    
    assert (exists l' tf,
               term_to_termFin' t2 (skipn (tsize t1) (all_fin (tsize t1 + tsize t2))) =
               (Some (l',tf))).
    {
      eapply fin'_always_some.

      assert (length (skipn (tsize t1) (all_fin (tsize t1 + tsize t2))) = tsize t2).
      {
        assert (length (all_fin (tsize t1 + tsize t2)) = (tsize t1 + tsize t2)).
        {
          eapply length_allfin.
        }
        Search skipn.
        erewrite skipn_length.
        rewrite H7.
        lia.
      }
      lia.
    }
    destruct_conjs.
    rewrite H9.
    eauto.
Defined.

Lemma fin'_always_some_eq : forall t (ls: list (fin (tsize t))),
    length ls = (tsize t) ->
    exists l' tf,
      term_to_termFin' t ls = Some (l',tf) /\ (placesF tf = all_fin (tsize t)).
Proof.
  intros.
  assert (exists l' tf,
             term_to_termFin' t ls = Some (l', tf)).
  eapply fin'_always_some.
  lia.
  destruct_conjs.
  exists H0. exists H1.
  split.
  eassumption.

  assert (length (all_fin (tsize t)) = tsize t).
  {
    eapply length_allfin.
  }

  generalizeEverythingElse t.
  dependent induction t; intros.
  -
    df.
    tauto.
  -
    df.
    repeat break_match; try solve_by_inversion.
    inversion H2.
    df.
    unfold hd_error in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    df.
Abort.

Definition fromSome{A:Type} (default:A) (opt:option A): A :=
  match opt with
  | Some x => x
  | _ => default
  end.

Definition do_term_to_termFin (t:Term) : (list (fin (tsize t))*TermFin (tsize t)) :=
  fromSome ([], aspF (tsize t) CPY) (term_to_termFin t).

Definition do_term_to_termFin_term (t:Term) : TermFin (tsize t) :=
  snd (do_term_to_termFin t).

Definition term_1 := att 1 (att 2 (asp CPY)).

Definition term_1_seq := lseq term_1 term_1.

Compute (term_to_termFin term_1_seq).

Definition term_1_seqF := do_term_to_termFin_term term_1_seq.

Compute (term_1_seqF).

Compute (placesF term_1_seqF).
Compute (all_fin (tsize term_1_seq)).

Lemma places_placesF: forall t,
    placesF (do_term_to_termFin_term t) = all_fin (tsize t).
Proof.
  intros.
  unfold do_term_to_termFin_term.
  unfold do_term_to_termFin.
  unfold fromSome.
  assert (exists l' tf, term_to_termFin t = Some (l', tf)).
  {
    eapply term_to_termFin_always_Some.
  }
  destruct_conjs.
  rewrite H1.
  df.

  generalizeEverythingElse t.
  dependent induction t; intros.
  -
    df.
    tauto.
  -
    df.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    df.
    unfold term_to_termFin in IHt.

    assert ((map (fun x : fin (tsize t) => Some x) (all_fin (tsize t))) =
            tl (all_fin (S (tsize t)))) as HH.
    {
      df.
      tauto.
    }
    rewrite HH in *.
    clear HH.
Abort.




HERE



    
    

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
