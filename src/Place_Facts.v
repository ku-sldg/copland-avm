Require Import Maps Term_Defs Auto.

Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.

(*
Definition inc_vm_id (m:VMID_Map) (p:Plc) : (VM_ID*VMID_Map) :=
  let val := map_get m p in
  match val with
  | Some v => (v,map_replace m p (v + 1))
  | None => (0,map_set m p 1)
  end.
 *)

Definition VMID_Map := (MapC VM_ID Plc).

Fixpoint flatten_places' (t:Term) (n:nat) (m:MapC VM_ID Plc): (nat*(MapC VM_ID Plc)) :=
  match t with
  | asp a => (n,m)     
  | att q t' =>
    flatten_places' t' (n+1) (map_set m n q)              
  | lseq t1 t2 =>
    let '(n',m') := flatten_places' t1 n m in
    flatten_places' t2 n' m'
  end.

Definition flatten_places (t:Term) : (MapC Plc VM_ID) :=
  snd (flatten_places' t 1 []).



(* TODO: import and use option monad scope/notation *)
Fixpoint flatten_term (t:Term) (m:MapC Plc VM_ID): option Term :=
  match t with
  | asp a => Some (asp a)
                
  | att q t' =>
    let mp := map_get m q in
    let mt' := flatten_term t' m in
    match (mp, mt') with
    | (Some v, Some newTerm) => Some (att v newTerm)
    | _ => None
    end              
  | lseq t1 t2 =>
    let mt1 := flatten_term t1 m in
    let mt2 := flatten_term t2 m in
    match (mt1,mt2) with
    | (Some new_t1, Some new_t2) => Some (lseq new_t1 new_t2)
    | _ => None
    end
end.

Fixpoint term_places' (t:Term) (ls:list Plc): list Plc :=
  match t with
  | asp _ => ls   
  | att q t' =>
    term_places' t' (q::ls)              
  | lseq t1 t2 =>
    term_places' t2 (term_places' t1 ls)
  end.

Definition term_places (t:Term): list Plc :=
  term_places' t [].

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

Set Nested Proofs Allowed.
Require Import Coq.Arith.PeanoNat.

Lemma term_places'_cumul: forall t p ls,
    In p ls ->
    In p (term_places' t ls).
Proof.
  induction t; intros.
  -
    df.
    eassumption.
  -
    df.
    assert (In p (term_places' t (n::ls))).
    {
    eapply IHt.
    right.
    eassumption.
    }
    eassumption.
  -
    df.
    eauto.
Defined.

Lemma places_input_order: forall t p n n0 ls,
    In p (term_places' t (n :: n0 :: ls)) ->
    In p (term_places' t (n0 :: n:: ls)).
Proof.
  intros.

  assert (In p (n :: n0 :: ls) \/ In p (term_places' t [])).
  {
    admit.
  }
  destruct H0.
  eapply term_places'_cumul.
  admit.
Admitted.

Lemma lseq_places_fact: forall t1 t2 p ls,
    In p (term_places' t2 (term_places' t1 ls)) ->
    In p (term_places' t1 ls) \/ In p (term_places' t2 []).
Proof.
Admitted.

Lemma lseq_places_assoc: forall t1 t2 p n ls,
    In p (term_places' t2 (term_places' t1 (n :: ls))) ->
    In p (term_places' t2 (n :: term_places' t1 ls)).
Proof.
Admitted.


Lemma peel_one: forall t n ls p,
    In p (term_places' t (n :: ls)) ->
    p <> n ->
    In p (term_places' t ls).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    df.
    destruct H; try eauto.
    congruence.
  -
    df.
    eapply IHt.
    Focus 2.
    eassumption.
    eapply places_input_order; eauto.
  -
    df.
    assert (In p (term_places' t1 (n::ls)) \/ In p (term_places' t2 [])).
    {
      eapply lseq_places_fact; eauto.
    }
    destruct H1.
    +
      eapply term_places'_cumul.
      eauto.
    +
      eapply IHt2 with (n:=n).
      eapply lseq_places_assoc; eauto.
      eassumption.
Defined.

(*
Lemma fff: forall p t n,
    In p (term_places' t []) ->
    p <> n ->
    In p (term_places' t [n]).
Proof.
Admitted.
*)

Lemma term_places_weaken: forall t p ls,
    In p (term_places' t []) ->
    In p (term_places' t ls).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    solve_by_inversion.
  -
    cbn in H.
    destruct (Nat.eq_dec p n).
    +
      subst.
      df.
      eapply term_places'_cumul.
      econstructor.
      tauto.
    +
      assert (In p (term_places' t [])).
      {
        eapply peel_one; eauto.
        (*
        
        
        edestruct singleton_places_fact.
        eassumption.
        invc H0.
        congruence.
        invc H1.
        eassumption. *)
      }
      df.
      eauto.
  -
    df.
    edestruct lseq_places_fact.
    eassumption.
    assert (In p (term_places' t1 ls)) by eauto.
    eapply term_places'_cumul.
    eassumption.
    eauto.
Defined.

Lemma term_places_iff_rel: forall t p,
    term_places_r t p <-> In p (term_places t).
Proof.
  split.
  -
    unfold term_places.
    induction t; intros; df.
    +
      solve_by_inversion.
    +
      invc H.
      ++
        eapply term_places'_cumul; eauto.
        econstructor.
        tauto.
      ++
        concludes.

        eapply term_places_weaken; eauto.
    +
      invc H.
      ++
        concludes.
        eapply term_places'_cumul; eauto.
      ++
        concludes.
        eapply term_places_weaken.
        eassumption.
  -
    intros.
    unfold term_places in *.
    generalizeEverythingElse t.
    induction t; intros; df.
    +
      solve_by_inversion.
    +
      destruct (Nat.eq_dec p n).
      ++
        subst.
        econstructor.
      ++
        econstructor.
        eapply IHt.
        eapply peel_one; eauto.

        (*

        edestruct singleton_places_fact.
        eassumption.
        invc H0.
        congruence.
        invc H1.
        eassumption. *)
    +
      assert (In p (term_places' t1 []) \/ In p (term_places' t2 [])).
      {       
        eapply lseq_places_fact; eauto.
      }
      destruct H0.
      ++
        econstructor; eauto.
      ++
        apply atLseqPlacer.
        eauto.
Defined.

(*
Definition flatten_places (t:Term) : (MapC Plc VM_ID) :=
  snd (flatten_places' t 1 []).
 *)

Lemma places_match: forall t,
    map_dom (flatten_places t) = term_places t.
Proof.
Admitted.


Lemma flatten_some: forall t,
  (*term_places_r t p ->
  In p (map_dom m) -> *)
  (*map_dom m = term_places t -> *)
  exists t', flatten_term t (flatten_places t) = Some t'.
Proof.
Admitted.

Definition t1 := att 1 (asp (ASPC 1 [])).
Definition t2 := (asp (ASPC 2 [])).
Definition myterm := att 1 (lseq t1 (att 2 (lseq t2 (att 3 t1)))).

Compute flatten_places myterm.
