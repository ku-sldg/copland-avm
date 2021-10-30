Require Import ConcreteEvidence AutoApp OptMonad Auto Helpers_VmSemantics Term_Defs StVM Impl_vm.

Require Import List.
Import ListNotations.

Require Import Lia.

Lemma firstn_long: forall (e:list BS) x,
    length e >= x ->
    length (firstn x e) = x.
Proof.
  intros.
  eapply firstn_length_le.
  lia.
Defined.

Lemma skipn_long: forall (e:list BS) x y,
    length e = x + y ->
    length (skipn x e) = y.
Proof.
  intros.
  assert (length (skipn x e) = length e - x).
  { eapply skipn_length. }
  lia.
Defined.

Definition peel_bs (ls:EvBits) : option (BS * EvBits) :=
  match ls with
  | bs :: ls' => Some (bs, ls')
  | _ => None
  end.

Lemma peel_fact': forall e x y H,
    length e = S x ->
    peel_bs e = Some (y, H) ->
    length H = x.
Proof.
  intros.
  destruct e;
    ff; eauto.
Defined.

Lemma peel_fact: forall e x y H et,
    length e = S x ->
    peel_bs e = Some (y, H) ->
    et_size et = x ->
    wf_ec (evc H et).
Proof.
  intros.
  econstructor.
  eapply peel_fact'; eauto.
  lia.
Defined.


Fixpoint encodeEv (e:EvidenceC) : EvBits :=
  match e with
  | mtc => []
  | nnc _ bs => [bs]
  | uuc _ _ _ _ _ bs e' =>
    bs :: (encodeEv e')
  | ggc _ bs e' =>
    bs :: (encodeEv e')
  | hhc _ bs _ =>
    [bs]
  | ssc e1 e2 =>
    (encodeEv e1) ++ (encodeEv e2)
  | ppc e1 e2 =>
    (encodeEv e1) ++ (encodeEv e2)
  end.

Fixpoint reconstruct_ev' (ls:EvBits) (et:Evidence) : option EvidenceC :=
  match et with
  | mt => (* Some mtc *)
    match ls with
    | [] => Some mtc
    | _ => None
    end 
  | uu i args tpl tid p et' =>
    '(bs, ls') <- peel_bs ls ;;
    x <- reconstruct_ev' ls' et' ;;
    Some (uuc i args tpl tid p bs x)
  | gg p et' =>
    '(bs, ls') <- peel_bs ls ;;
    x <- reconstruct_ev' ls' et' ;;
    Some (ggc p bs x)
  | hh p et' =>
    '(bs, ls') <- peel_bs ls ;;
     match ls' with
    | [] => Some (hhc p bs et')
    | _ => None
    end 
   
  | nn i =>
    '(bs, ls') <- peel_bs ls ;;
     match ls' with
    | [] => Some (nnc i bs)
    | _ => None
    end 
    
  | ss et1 et2 =>
    e1 <- reconstruct_ev' (firstn (et_size et1) ls) et1 ;;
    e2 <- reconstruct_ev' (skipn (et_size et1) ls) et2 ;;
    Some (ssc e1 e2)
  | pp et1 et2 =>
    e1 <- reconstruct_ev' (firstn (et_size et1) ls) et1 ;;
    e2 <- reconstruct_ev' (skipn (et_size et1) ls) et2 ;;
    Some (ppc e1 e2)  
  end.

Definition reconstruct_ev (e:EvC) : option EvidenceC :=
  match e with
  | evc ls et => reconstruct_ev' ls et
  end.

Inductive reconstruct_evP: EvC -> EvidenceC -> Prop :=
| reconstruct_evC: forall e ee,
    Some ee = reconstruct_ev e ->
    reconstruct_evP e ee.

Lemma fold_recev: forall e0 e1,
    reconstruct_ev' e0 e1 = reconstruct_ev (evc e0 e1).
Proof.
  ff.
  tauto.
Defined.

Lemma wrap_reconP: forall ec e,
    reconstruct_ev ec = Some e ->
    reconstruct_evP ec e.
Proof.
  intros.
  econstructor.
  congruence.
Defined.

Ltac do_wrap_reconP :=
  repeat
  match goal with
  | [H: reconstruct_ev ?ec = Some ?e
     |- _] =>
    apply wrap_reconP in H
  end.

Ltac do_rewrap_reconP :=
  match goal with
  | [H: reconstruct_evP (evc _ (?cc _)) _
     |- _] =>
    invc H;
    repeat ff;
    try rewrite fold_recev in *;
    do_wrap_reconP
  end.

Lemma reconP_determ: forall ec e e',
    reconstruct_evP ec e ->
    reconstruct_evP ec e' ->
    e = e'.
Proof.
  intros.
  invc H; invc H0.
  repeat jkjke'.
  ff.
Defined.

Ltac do_reconP_determ :=
  repeat 
  match goal with
  | [H: reconstruct_evP ?ec ?e,
        H2: reconstruct_evP ?ec ?e2
     |- _] =>
    assert_new_proof_by (e = e2)
                        ltac:(eapply reconP_determ; [apply H | apply H2]);
    clear H2
  end; subst.

Inductive annoP: AnnoTerm -> Term -> nat -> Prop :=
| annoP_c: forall anno_term t n,
    anno_term = snd (anno t n) ->
    annoP anno_term t n.

Inductive anno_parP: AnnoTermPar -> AnnoTerm -> Loc -> Prop :=
| anno_parP_c: forall par_term t loc,
    par_term = snd (anno_par t loc) ->
    anno_parP par_term t loc.

Lemma anno_parP_redo: forall t pt loc loc',
    anno_par t loc = (loc', pt) ->
    anno_parP pt t loc.
Proof.
  intros.
  econstructor.
  jkjke.
Defined.

Ltac do_annopar_redo :=
  match goal with
  | [H: anno_par ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parP_redo in H
  end.

Ltac inv_annoparP :=
  match goal with
  | [H: anno_parP ?t (?c _) _
     |- _ ] =>
    inversion H
  end.

Inductive copland_compileP : AnnoTermPar -> cvm_st -> (option unit) -> cvm_st ->  Prop :=
| ccp: forall t st st' res,
    copland_compile t st = (res, st') ->
    copland_compileP t st res st'.

Lemma ccp_implies_cc: forall t st st' res,
  copland_compileP t st res st' ->
  copland_compile t st = (res,st').
Proof.
  intros.
  solve_by_inversion.
Defined.

Lemma cc_implies_ccp: forall t st st' res,
  copland_compile t st = (res,st') -> 
  copland_compileP t st res st'.
Proof.
  intros.
  econstructor.
  tauto.
Defined.

Lemma ccp_iff_cc: forall t st st' res,
  copland_compile t st = (res,st') <-> 
  copland_compileP t st res st'.
Proof.
  intros.
  split; intros;
    try (eapply cc_implies_ccp; eauto);
    try (eapply ccp_implies_cc; eauto).
Defined.

Ltac dd :=
  repeat (
      df;
      annogo;
      dosome;
      do_asome;
      subst).

Ltac wrap_ccp :=
  
  try rewrite <- ccp_iff_cc in *;
  try inv_annoparP;
  dd;
  repeat do_annopar_redo;
  do_wf_pieces;
  repeat do_pl_immut;
  dd;
  try rewrite ccp_iff_cc in *.
