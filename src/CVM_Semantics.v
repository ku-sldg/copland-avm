Require Import CVM_Instr LTS Term_Defs Term StructTactics Auto.

Require Import List.
Import ListNotations.

Require Import Coq.Program.Tactics.

Set Nested Proofs Allowed.

Lemma ilseq_decomp: forall r l t1 t2 e e' p tr,
    well_formed (alseq r l t1 t2) ->
    CVM_Instr.lstar
      (iconf (instr_compiler (alseq r l t1 t2)) p e) tr
      (istop p e') ->
    exists e' tr' p',
      CVM_Instr.lstar
        (iconf (instr_compiler t1) p e) tr'
        (istop p' e') /\
      exists tr'',
        CVM_Instr.lstar
          (iconf (instr_compiler t2) p' e') tr''
          (istop p e') /\
        tr = tr' ++ tr''. 

Proof.
Admitted.

Lemma instr_pl_immut: forall t p e tr p' e',
    well_formed t ->
    CVM_Instr.lstar (iconf (instr_compiler t) p e) tr (istop p' e') ->
    p = p'.
Proof.
Admitted.

Ltac clear_trivs :=
  repeat 
  match goal with
  | [H: ?x = ?x |- _] =>
    clear H
  end.

Ltac do_pl_immut :=
  repeat
    match goal with
    | [H: CVM_Instr.lstar (iconf (instr_compiler ?t) ?p _) _ (istop ?p' _),
          H2: well_formed ?t |- _] =>
      assert_new_proof_by (p = p')
                          ltac:(eapply instr_pl_immut; [apply H2 | apply H])  
    end;
  subst; clear_trivs.

Ltac inv_lstar :=
  match goal with
  | [H: CVM_Instr.lstar (?C _) _ _(*(iconf (?C _) _ _) _ _*) |- _] =>
    invc H
  end;
  try solve_by_inversion.

Ltac inv_istep :=
  match goal with
  | [H: Instr_step (iconf (?C _) _ _) _ _ |- _] =>
    invc H
  end;
  try solve_by_inversion.

Lemma cvm_refines_lts_event_ordering_corrolary : forall t ai tr et e e' p (*p' o o'*),
    well_formed t ->
    ai = instr_compiler t ->
    CVM_Instr.lstar (iconf ai p e) tr (istop p e') ->
    (*copland_compile t (mk_st e [] p o) = (Some tt, (mk_st e' tr p' o')) ->
    st_trace (run_cvm t
                     (mk_st e [] p o)) = tr -> *)
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    subst;
    destruct a;
      repeat (df; inv_lstar; inv_istep);
      eapply lstar_tran;
        try apply stasp;
        df; inv_lstar.
  -
    subst.
    do_wf_pieces.
    edestruct ilseq_decomp; eauto.
    destruct_conjs.
    subst.

    do_pl_immut.

    econstructor.
    econstructor.
    eapply lstar_transitive.
    eapply lstar_stls.

    eapply IHt1; eauto.
    
    eapply lstar_silent_tran.
    apply stlseqstop.
    eapply IHt2; eauto.
Defined.

    
      
      
      
      
