Require Import EqClass Maps Term_Defs Auto.

Require Import List.
Require Import Lists.List.
Import ListNotations.

Require Import Lia Coq.Arith.PeanoNat.

Require Import StructTact.StructTactics.

Set Nested Proofs Allowed.



(*
Definition inc_vm_id (m:VMID_Map) (p:Plc) : (VM_ID*VMID_Map) :=
  let val := map_get m p in
  match val with
  | Some v => (v,map_replace m p (v + 1))
  | None => (0,map_set m p 1)
  end.
 *)

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
