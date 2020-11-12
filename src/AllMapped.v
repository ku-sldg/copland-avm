Require Import Term StAM Maps StructTactics Auto GenStMonad MonadVM.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Inductive evMapped : Evidence -> AM_St -> Prop :=
| evMappedMt : forall m, evMapped mt m
| evMappedU : forall p i args e' m st,
    m = st_aspmap st ->
    evMapped e' st -> 
    (exists j, bound_to m (p,i) j) -> 
    evMapped (uu i args p e') st
| evMappedG : forall e' m p st,
    m = st_sigmap st ->
    evMapped e' st ->
    (exists j, bound_to m p j) ->
    evMapped (gg p e') st
(*| evMappedH : forall e' p st,
    (*m = st_sigmap st -> *)
    evMapped e' st ->
    evMapped (hh p e') st    
| evMappedN : forall e' m nid st,
    m = st_aspmap st ->
    evMapped e' st ->
    evMapped (nn nid e') st 
*)
| evMappedS : forall e1 e2 st,
    evMapped e1 st ->
    evMapped e2 st ->
    evMapped (ss e1 e2) st
             (*
| evMappedP : forall e1 e2 st,
    evMapped e1 st ->
    evMapped e2 st ->
    evMapped (pp e1 e2) st 
 *).


Inductive allMapped : AnnoTerm -> AM_St -> Plc -> Evidence -> Prop :=
| allMapped_cpy : forall r p st e,
    (*m = st_aspmap st -> *)
    (*p = am_pl st -> *)
    evMapped e st ->
    allMapped (aasp r (CPY)) st p e
| allMapped_asp : forall m st p i r args e,
    (*p = am_pl st -> *)
    evMapped e st ->
    m = st_aspmap st ->
    (exists j, bound_to m (p,i) j) ->
    allMapped (aasp r (ASPC i args)) st p e
| allMapped_sig : forall r p st m e,
    evMapped e st ->
    (*p = am_pl st -> *)
    m = st_sigmap st ->
    (exists j, bound_to m p j) ->
    allMapped (aasp r (SIG)) st p e
(*| allMapped_hsh : forall r p st e,
    evMapped e st ->
    (*p = am_pl st -> *)
    allMapped (aasp r (HSH)) st p e *)
| allMapped_at : forall t' p q r st e m x y z z',
    m = st_aspmap st ->
    (*evMapped e m -> *) (* TODO: need this? *)
    st = (mkAM_St x y z z') ->
    allMapped t' (mkAM_St x y z z') q e ->
    allMapped (aatt r q t') st p e
| allMapped_lseq : forall t1 t2 p st r e,
    (* m = st_aspmap st ->
       evMapped e m -> *)  (* TODO: need this? *)
    (*p = am_pl st -> *)
    allMapped t1 st p e ->
    allMapped t2 st p mt (*(eval (unanno t1) p e)*) -> (* TODO: is mt ok here? *)
    allMapped (alseq r t1 t2) st p e
| allMapped_bseq_nn : forall t1 t2 p st e r,
    (*p = am_pl st -> *)
    allMapped t1 st p mt ->
    allMapped t2 st p mt ->
    allMapped (abseq r (NONE,NONE) t1 t2) st p e
| allMapped_bseq_na : forall t1 t2 p st e r,
    (*p = am_pl st -> *)
    allMapped t1 st p mt ->
    allMapped t2 st p e ->
    allMapped (abseq r (NONE,ALL) t1 t2) st p e
| allMapped_bseq_an : forall t1 t2 p st e r,
    (*p = am_pl st -> *)
    allMapped t1 st p e ->
    allMapped t2 st p mt ->
    allMapped (abseq r (ALL,NONE) t1 t2) st p e
| allMapped_bseq_aa : forall t1 t2 p st e r,
    (*p = am_pl st -> *)
    allMapped t1 st p e ->
    allMapped t2 st p e ->
    allMapped (abseq r (ALL,ALL) t1 t2) st p e
              (*
| allMapped_bpar_nn : forall t1 t2 p st e r,
    (*p = am_pl st -> *)
    allMapped t1 st p mt ->
    allMapped t2 st p mt ->
    allMapped (abpar r (NONE,NONE) t1 t2) st p e
| allMapped_bpar_na : forall t1 t2 p st e r,
    (*p = am_pl st -> *)
    allMapped t1 st p mt ->
    allMapped t2 st p e ->
    allMapped (abpar r (NONE,ALL) t1 t2) st p e
| allMapped_bpar_an : forall t1 t2 p st e r,
   (* p = am_pl st -> *)
    allMapped t1 st p e ->
    allMapped t2 st p mt ->
    allMapped (abpar r (ALL,NONE) t1 t2) st p e
| allMapped_bpar_aa : forall t1 t2 p st e r,
    (*p = am_pl st ->*)
    allMapped t1 st p e ->
    allMapped t2 st p e ->
    allMapped (abpar r (ALL,ALL) t1 t2) st p e*).

(*
Definition allMapped (t:AnnoTerm) (a_st:AM_St) (p:Plc) (e:Evidence) : Prop :=
  evMapped (eval (unanno t) p e) a_st.
 *)

Ltac debound :=
  match goal with
  | [H: bound_to _ _ _ |- _] => invc H
  end.

Ltac evMappedFacts :=
  match goal with
  | [H: evMapped (uu _ _ _ _) _ |- _] => invc H
  | [H: evMapped (gg _ _) _ |- _] => invc H
  (* 
  | [H: evMapped (hh _ _) _ |- _] => invc H 
  | [H: evMapped (nn _ _) _ |- _] => invc H *)
  | [H: evMapped (ss _ _) _ |- _] => invc H
(*  | [H: evMapped (pp _ _) _ |- _] => invc H  
   *)
  end;
  destruct_conjs;
  try debound.

Ltac allMappedFacts := 
  match goal with
  | [H: allMapped (aasp _ _) _ _ _ |- _] => invc H
  | [H: allMapped (aatt _ _ _) _ _ _ |- _] => invc H
  | [H: allMapped (alseq _ _ _) _ _ _ |- _] => invc H
  
  | [H: allMapped (abseq _ _ _ _) _ _ _ |- _] => invc H
(*  | [H: allMapped (abpar _ _ _ _) _ _ _ |- _] => invc H 
   *)
  end;
  destruct_conjs.



Lemma allMappedAt : forall r n a p st e,
    allMapped (aatt r n a) st p e ->
    allMapped a st n e.
Proof.
  intros.
  allMappedFacts.
  df.
  eauto.
Defined.

Ltac df :=
  repeat (
      cbn in *;
      unfold runSt in *;
      repeat break_let;
      repeat (monad_unfold; cbn in *; find_inversion);
      monad_unfold;
      repeat dunit;
      unfold snd in * ).

Lemma allMappedSub' : forall a a_st e p,
    allMapped a a_st p e ->
    allMapped a a_st p mt.
Proof.
  induction a; intros.
  -
    destruct a.
    +
      allMappedFacts.
      econstructor.
      econstructor.
    +
      allMappedFacts.
      econstructor.
      econstructor.
      reflexivity.
      eexists.
      eauto.
    +
      allMappedFacts.
      econstructor.
      econstructor.
      reflexivity.
      eexists.
      eauto.
  -
    allMappedFacts.
    df.
    econstructor.
    reflexivity.
    reflexivity.
    eauto.
  -
    allMappedFacts.
    assert (allMapped a1 a_st p mt) by eauto.
    econstructor.
    eassumption.
    eassumption.
  -
    allMappedFacts;
      try (econstructor; eauto).
Defined.

Lemma allMappedSub : forall a a_st t p n,
    allMapped a a_st p (Term.eval t n mt) ->
    allMapped a a_st p mt.
Proof.
  intros.
  eapply allMappedSub'; eauto.
Defined.


