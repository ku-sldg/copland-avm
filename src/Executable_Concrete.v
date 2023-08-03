Require Import List Manifest_Generator Term_Defs_Core Executable_Defs_Prop Manifest Manifest_Compiler.
Import ListNotations.

Definition properlyCompiledASPIDs : Prop :=
  True.

Fixpoint concrete_executable (t : Term) (k : Plc) 
    (cm : ConcreteManifest) {struct t} : Prop :=
  match t with
  | asp (ENC p) => (* Do we know p's pub key *)
      Maps.map_get cm.(Concrete_PubKeys) p <> None
  | asp (ASPC _ _ (asp_paramsC aspId _ targP targId)) => 
      In targP cm.(Concrete_Targets) /\
      In aspId cm.(Concrete_ASPs)
  | asp _ => (* NULL, CPY, SIG, HSH *)
      (* Fundamental ASP's management are included at 
      implementation time covered by the CakeML_ASPCallback *)
      properlyCompiledASPIDs
  | att p' t => 
      (* Can we contact the external AM *)
      Maps.map_get cm.(Concrete_Plcs) p' <> None
  | lseq t1 t2 =>
      concrete_executable t1 k cm /\ 
      concrete_executable t2 k cm
  | bseq _ t1 t2 =>
      concrete_executable t1 k cm /\ 
      concrete_executable t2 k cm
  | bpar _ t1 t2 =>
      concrete_executable t1 k cm /\ 
      concrete_executable t2 k cm
  end.

Definition lib_supports_manifest (al : AM_Library) (am : Manifest) : Prop :=
  (forall (a : ASP_ID), In a am.(asps) -> Maps.map_get al.(Local_ASPS) a <> None) /\
  (forall (up : Plc), In up am.(uuidPlcs) -> Maps.map_get al.(Local_Plcs) up <> None) /\
  (forall (pkp : Plc), In pkp am.(pubKeyPlcs) -> Maps.map_get al.(Local_PubKeys) pkp <> None).

Lemma man_comp_target_plcs_preserved : 
  forall am al cm aspCb plcCb pkCb uuidCb,
  manifest_compiler am al = (cm, aspCb, plcCb, pkCb, uuidCb) ->
  (forall tp, In tp am.(targetPlcs) ->
    In tp cm.(Concrete_Targets)).
Proof.
  induction am; destruct al; unfold manifest_compiler; intuition;
  inversion H; simpl in *; intuition; eauto.
Qed.

Lemma man_comp_plcs_preserved : 
  forall am al cm aspCb plcCb pkCb uuidCb,
  manifest_compiler am al = (cm, aspCb, plcCb, pkCb, uuidCb) ->
  (forall p, Maps.map_get (Local_Plcs al) p = Maps.map_get (Concrete_Plcs cm) p).
Proof.
  induction am; destruct al; unfold manifest_compiler; intuition;
  inversion H; simpl in *; intuition; eauto.
Qed.

Lemma man_comp_asps_preserved : 
  forall am al cm aspCb plcCb pkCb uuidCb,
  manifest_compiler am al = (cm, aspCb, plcCb, pkCb, uuidCb) ->
  (forall a, In a am.(asps) ->
    In a (Concrete_ASPs cm)).
Proof.
  induction am; destruct al; unfold manifest_compiler; intuition;
  inversion H; simpl in *; intuition; eauto.
Qed.

Lemma man_comp_pubKeys_preserved :
  forall am al cm aspCb plcCb pkCb uuidCb,
  manifest_compiler am al = (cm, aspCb, plcCb, pkCb, uuidCb) ->
  (forall p, Maps.map_get (Local_PubKeys al) p = Maps.map_get (Concrete_PubKeys cm) p).
Proof.
  induction am; destruct al; unfold manifest_compiler; intuition;
  inversion H; simpl in *; intuition; eauto.
Qed.

Theorem manifest_compiler_soundness : 
  forall (em : EnvironmentM) (t : Term) (p : Plc),
    executable_global t p em ->
    (forall (am : Manifest),
      Maps.map_get em p = Some am ->
      forall (al : AM_Library) cm aspCb plcCb pkCb uuidCb, 
        lib_supports_manifest al am ->
        manifest_compiler am al = (cm, aspCb, plcCb, pkCb, uuidCb) ->
        concrete_executable t p cm
    ).
Proof.
  induction t; intros; simpl in *;
  unfold lib_supports_manifest in *; intuition;
  pose proof (man_comp_target_plcs_preserved _ _ _ _ _ _ _ H2); eauto.
  - destruct a; eauto; try apply I.
    * destruct a; intuition; eauto.
      ** eapply H4; 
          unfold canRunAsp_Env, canRunAsp_Manifest, canRun_aspid in *;
          simpl in *;
          rewrite H0 in H; destruct am; simpl in *; 
          intuition; eauto.
      ** unfold knowsPub_Env, canRunAsp_Env, canRunAsp_Manifest, canRun_aspid in *;
          rewrite H0 in H; destruct am; simpl in *; intuition.
          eapply man_comp_asps_preserved; eauto.
    * unfold knowsPub_Env, canRunAsp_Env, canRunAsp_Manifest, canRun_aspid in *.
      rewrite H0 in H; destruct am; simpl in *; intuition.
      erewrite <- man_comp_pubKeys_preserved in H6; eauto.
  - unfold knowsOf_Env in *; rewrite H0 in *;
    pose proof (H1 _ H4); eauto;
    pose proof (man_comp_plcs_preserved _ _ _ _ _ _ _ H2);
    congruence.
Qed.