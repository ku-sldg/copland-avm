Require Import List Manifest_Generator Term_Defs_Core Executable_Facts Manifest.

Definition properlyCompiledASPIDs : Prop :=
  True.

Fixpoint concrete_executable (t : Term) (k : Plc) 
    (compiler_output : (ConcreteManifest * 
      (ConcreteManifest -> CakeML_ASPCallback) * 
      (ConcreteManifest -> CakeML_PlcCallback) * 
      (ConcreteManifest -> CakeML_PubKeyCallback) * 
      (ConcreteManifest -> CakeML_uuidCallback))) {struct t} : Prop :=
  match compiler_output with
  | (cm, aspCb, plcCb, pubKeyCb, uuidCb) =>
    match t with
    | asp (ENC p) => (* Do we know p's pub key *)
        Maps.map_get cm.(Concrete_PubKeys) p <> None
    | asp _ => (* NULL, CPY, SIG, HSH, (ASPC _ _ params) *)
        (* Fundamental ASP's management are included at 
        implementation time covered by the CakeML_ASPCallback *)
        properlyCompiledASPIDs
    | att p' t => 
        (* Can we contact the external AM *)
        Maps.map_get cm.(Concrete_Plcs) p' <> None
    | lseq t1 t2 =>
        concrete_executable t1 k compiler_output /\ 
        concrete_executable t2 k compiler_output
    | bseq _ t1 t2 =>
        concrete_executable t1 k compiler_output /\ 
        concrete_executable t2 k compiler_output
    | bpar _ t1 t2 =>
        concrete_executable t1 k compiler_output /\ 
        concrete_executable t2 k compiler_output
    end
  end.

Definition lib_supports_manifest (al : AM_Library) (am : Manifest) : Prop :=
  (forall (a : ASP_ID), In a am.(asps) -> Maps.map_get al.(Local_ASPS) a <> None) /\
  (forall (up : Plc), In up am.(uuidPlcs) -> Maps.map_get al.(Local_Plcs) up <> None) /\
  (forall (pkp : Plc), In pkp am.(pubKeyPlcs) -> Maps.map_get al.(Local_PubKeys) pkp <> None).

Theorem manifest_compiler_soundness : 
  forall (em : EnvironmentM) (t : Term) (p : Plc),
    executable_static t p em ->
    (forall (am : Manifest),
      Maps.map_get em p = Some am ->
      forall (al : AM_Library), 
        lib_supports_manifest al am ->
        concrete_executable t p (manifest_compiler am al)
    ).
Proof.
  induction t; simpl; 
  unfold lib_supports_manifest in *; intuition.
  - destruct a; eauto; try apply I;
    eapply H4; unfold knowsPub_Env in H;
    rewrite H0 in H; eauto.
  - unfold knowsOf_Env in H0; rewrite H in H0; eauto.
Qed.

