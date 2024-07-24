(* Helper functions used by the Manifest Generator implementation. *)

Require Import Term_Defs_Core Params_Admits Manifest Eqb_Evidence.

Require Import EqClass Maps StructTactics Auto.

Require Export EnvironmentM Manifest_Set.

Require Import List.
Import ListNotations.

(* places' t ls -- helper function for places below.  Term (t) is the term 
    being walked, ls is the accumulated list of places. *)
Fixpoint places' (t:Term) (ls:list Plc) : list Plc :=
  match t with
  | asp _ => ls 
  | att q t' => (q :: (places' t' ls))
  | lseq t1 t2 => places' t2 (places' t1 ls)
  | bseq _ t1 t2 => places' t2 (places' t1 ls)
  | bpar _ t1 t2 => places' t2 (places' t1 ls)
  end.
  
(* places p t -- enumerates places (includes duplicates) discovered in a given 
    Term (t) executed at top-level place (p). *)
Definition places (p:Plc) (t:Term): list Plc := 
  p :: (places' t []).



(* places_manset' t ls -- helper function for places below.  Term (t) is the term 
    being walked, ls is the accumulated set of places. *)
Fixpoint places_manset' (t:Term) (ls:manifest_set Plc) : manifest_set Plc :=
  match t with
  | asp _ => ls 
  | att q t' => (manset_add q (places_manset' t' ls))
  | lseq t1 t2 => places_manset' t2 (places_manset' t1 ls)
  | bseq _ t1 t2 => places_manset' t2 (places_manset' t1 ls)
  | bpar _ t1 t2 => places_manset' t2 (places_manset' t1 ls)
  end.
  
(* places_manset p t -- enumerates places (does NOT add duplicates) discovered in a given 
    Term (t) executed at top-level place (p). *)
Definition places_manset (p:Plc) (t:Term): manifest_set Plc := 
  manset_add p (places_manset' t []).

Lemma nodup_places_manset' : forall t s,
  NoDup s -> 
  NoDup (places_manset' t s).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; unfold places_manset; unfold places_manset'; ff; 
    try (econstructor; eauto); econstructor.
  - (* at case *)
    cbn in *.
    specialize (IHt s H).

    eapply nodup_manset_add.
    eassumption.
  -
    cbn.
    eapply IHt2.
    eauto.
  -
    cbn.
    eauto.
  -
    cbn.
    eauto.
Qed.
  

Lemma nodup_places_manset : forall tp t,
  NoDup (places_manset tp t).
Proof.
  intros.
  unfold places_manset.
  eapply nodup_manset_add.
  eapply nodup_places_manset'.
  econstructor.
Qed.

(* place_terms t tp p -- enumerates Terms (includes duplicates) that place p is responsible 
    for executing, assuming top-level execution of term t by place tp. 

   This function is currently only used for verification (not by the manifest generator implemtnation).  
    TODO:  consider moving this definition somewhere more logical.  *)
Fixpoint place_terms (t:Term) (tp:Plc) (p:Plc) : list Term := 
  if(eqb_plc tp p)
  then [t]
  else (
    match t with 
    | asp a => []
    | att q t' => place_terms t' q p (* if (eqb_plc p q) then ([t'] ++ (place_terms t' q p)) else (place_terms t' q p) *)
    | lseq t1 t2 => (place_terms t1 tp p) ++ (place_terms t2 tp p)
    | bseq _ t1 t2 => (place_terms t1 tp p) ++ (place_terms t2 tp p)
    | bpar _ t1 t2 => (place_terms t1 tp p) ++ (place_terms t2 tp p)
    end).