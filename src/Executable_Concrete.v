Require Import List Manifest_Generator Term_Defs_Core Executable_Facts Manifest.

Fixpoint concrete_executable (t : Term) (k : Plc) 
    (compiler_output : (ConcreteManifest * 
      (ConcreteManifest -> CakeML_ASPCallback) * 
      (ConcreteManifest -> CakeML_PlcCallback) * 
      (ConcreteManifest -> CakeML_PubKeyCallback) * 
      (ConcreteManifest -> CakeML_uuidCallback))) {struct t} : Prop :=
  match compiler_output with
  | (cm, aspCb, plcCb, pubKeyCb, uuidCb) =>
    match t with
    | asp (ASPC _ _ params) =>
        forall plcs bss ev, (aspCb cm params plcs bss ev) = passed_bs
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
  (forall (a : ASP_ID), In a am.(asps) -> 
    (exists cb,
      forall params plcs bss ev, 
      (Maps.map_get al.(Local_ASPS) a = Some cb) /\
      (cb params plcs bss ev) = passed_bs)) /\
  (forall (up : Plc), In up am.(uuidPlcs) -> Maps.map_get al.(Local_Plcs) up <> None) /\
  (forall (pkp : Plc), In pkp am.(pubKeyPlcs) -> Maps.map_get al.(Local_PubKeys) pkp <> None) /\
  (forall addr, forall params plcs bss ev, al.(ASPServer_Cb) addr params plcs bss ev = failed_bs).

Require Import Maps EqClass.

Lemma minifyRetrieval : forall {A B : Type} `{H : EqClass A} (m : MapC A B) asps a,
  In a asps ->
  Maps.map_get
    (minify_mapC m (fun x0 : A => if in_dec (EqClass.EqClass_impl_DecEq A) x0 asps then true else false)) a =
  Maps.map_get m a.
Proof.
  induction m; simpl in *; eauto; intros; intuition.
  pose proof (IHm _ _ H0).
  destruct (in_dec (EqClass_impl_DecEq A) a1 asps) eqn:E1;
  simpl in *; eauto.
  * destruct (eqb a0 a1); eauto.
  * destruct (eqb a0 a1) eqn:E2; eauto.
    rewrite eqb_leibniz in E2. congruence.
Qed.

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
  - destruct a; eauto; try apply I.
    * unfold canRunAsp_Env in H.
      rewrite H0 in H. unfold Executable_Defs_Prop.canRunAsp_Manifest in H.
      destruct a.
      pose proof (H2 a).
      destruct am eqn:E; destruct H.
      pose proof (H4 H). clear H4.
      destruct H7. simpl in *. intros.
      pose proof (H4 (asp_paramsC a l p0 t) plcs bss ev).
      destruct H7; intuition; eauto.
      clear H4 H2.
      pose proof (minifyRetrieval (Local_ASPS al) _ _ H).
      rewrite H7 in *. clear H7.
      destruct (@map_get ASP_ID CakeML_ASPCallback AbstractedTypes.Eq_Class_ID_Type
          (@minify_mapC ASP_ID CakeML_ASPCallback AbstractedTypes.Eq_Class_ID_Type (Local_ASPS al)
             (fun x0 : ASP_ID =>
              match @in_dec ASP_ID (@EqClass_impl_DecEq ASP_ID AbstractedTypes.Eq_Class_ID_Type) x0 asps return bool with
              | left _ => true
              | right _ => false
              end))); simpl in *.
      ** inversion H2; eauto.
      ** inversion H2.
    * eapply H3; unfold knowsPub_Env in H;
      rewrite H0 in H; eauto.
  - unfold knowsOf_Env in H0; rewrite H in H0; eauto.
Qed.

