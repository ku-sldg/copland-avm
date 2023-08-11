Require Import Manifest Manifest_Compiler Manifest_Generator 
  Maps Term_Defs List Cvm_St Cvm_Impl ErrorStMonad_Coq StructTactics Cvm_Monad EqClass Manifest_Admits.

Require Import Auto.

Lemma map_get_minify : forall {A B : Type} `{EqClass A} `{EqClass B} (m : MapC A B) (a : A) b l,
  map_get m a = Some b ->
  (map_get 
    (minify_mapC 
      m 
      (fun x => if (in_dec (EqClass_impl_DecEq _) x (a :: l)) then true else false))
    a) = Some b.
Proof.
  induction m; simpl in *; intuition; eauto;
  repeat (break_match; simpl in *; eauto).
  - destruct o; subst; find_inversion; try congruence.
  - destruct f; left; rewrite eqb_leibniz in Heqb0; eauto.
Qed.



(* map_get (minify_mapD Local_Plcs (fun _ : Plc => false)) p1 *)

Definition lib_supports_manifest (al : AM_Library) (am : Manifest) : Prop :=
  (forall (a : ASP_ID), In a am.(asps) -> exists cb, Maps.map_get al.(Local_ASPS) a = Some cb) /\
  (forall (up : Plc), In up am.(uuidPlcs) -> exists b, Maps.map_get al.(Local_Plcs) up = Some b) /\
  (forall (pkp : Plc), In pkp am.(pubKeyPlcs) -> exists b, Maps.map_get al.(Local_PubKeys) pkp = Some b).

Ltac unfolds :=
  repeat monad_unfold;
  repeat unfold manifest_compiler, generate_ASP_dispatcher, 
    generate_Plc_dispatcher, generate_PubKey_dispatcher,
    generate_UUID_dispatcher, lib_supports_manifest in *;
  simpl in *; 
  repeat (match goal with
      | x : cvm_st |- _ => destruct x
      | x : AM_Config |- _ => destruct x
      | x : AM_Library |- _ => destruct x
      | x : CallBackErrors |- _ => destruct x
  end; simpl in *; eauto);
  intuition.

Theorem manifest_compiler_sound : forall t p envM,
  manifest_generator t p = envM ->
  (forall p' absMan, 
    map_get envM p' = Some absMan ->
    (forall amLib amConf, 
      lib_supports_manifest amLib absMan ->
      manifest_compiler absMan amLib = amConf ->
      (forall st,
        st.(st_AM_config) = amConf ->
        exists st', 
          build_cvm (copland_compile t) st = (resultC tt, st') \/
          build_cvm (copland_compile t) st = (errC (dispatch_error Runtime), st')
      )
    )
  )
  .
Proof.
  induction t; simpl in *; intros.
  - destruct a; simpl in *; repeat (ff; simpl in *; eauto); unfolds;
    invc H3.
    * destruct (H a0); intuition;
      eapply map_get_minify with (l := nil) in H0; simpl in *.
      break_match; setoid_rewrite H0 in Heqo; invc Heqo;
      repeat break_match; intuition; eauto;
      invc Heqr2; eauto.
    * destruct (H a0); intuition;
      eapply map_get_minify with (l := nil) in H0; simpl in *.
      break_match; setoid_rewrite H0 in Heqo; invc Heqo;
      repeat break_match; intuition; eauto;
      invc Heqr2; eauto.
    * destruct (H sig_aspid); intuition;
      eapply map_get_minify with (l := nil) in H0; simpl in *.
      break_match; setoid_rewrite H0 in Heqo; invc Heqo;
      repeat break_match; intuition; eauto;
      invc Heqr2; eauto.
    * destruct (H hsh_aspid); intuition;
      eapply map_get_minify with (l := nil) in H0; simpl in *.
      repeat break_match. setoid_rewrite H0 in Heqr2; invc Heqo;
      repeat break_match; intuition; eauto;
      invc Heqr2; eauto.
      rewrite H0 in Heqo.
    * repeat monad_unfold;
  repeat unfold manifest_compiler, generate_ASP_dispatcher, 
    generate_Plc_dispatcher, generate_PubKey_dispatcher,
    generate_UUID_dispatcher, lib_supports_manifest in *;
  simpl in *; repeat break_match; try solve_by_inversion; 
    cbn in *; unfold runErr in *; simpl in *;
      repeat (monad_unfold; cbn in *; find_inversion);
      monad_unfold;
      repeat dunit;
      unfold snd in *; intuition; eauto.
      
      
       destruct par.
      break_let.
    try (destruct (H a0); intuition; eauto).
    * eapply map_get_minify in H3. 
       
      erewrite H0 in Heqo.
    * unfold manifest_compiler
    * 
      unfold manifest_compiler in H3; simpl in *; ff; simpl in *; eauto. ff.
      | H1 : build_cvm t1 _ = (_, _), H2 : build_cvm t1 _ = (_, _) |- _ =>
        eapply IHt1 in H1; eauto; simpl in *; intuition; subst; try congruence; eauto
      | H1 : build_cvm t2 _ = (_, _), H2 : build_cvm t2 _ = (_, _) |- _ =>
        eapply IHt2 in H1; eauto; simpl in *; intuition; subst; try congruence; eauto
      end.
      destruct st; simpl in *; repeat (ff; simpl in *; eauto).
    * 

  
Qed.
