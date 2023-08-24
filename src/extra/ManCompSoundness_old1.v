Require Import Manifest Manifest_Compiler Manifest_Generator 
  Maps Term_Defs List Cvm_St Cvm_Impl ErrorStMonad_Coq StructTactics Cvm_Monad EqClass Manifest_Admits.
Require Import Manifest_Generator_Facts Executable_Defs_Prop Executable_Facts_Dist.

Require Import Auto.



(* map_get (minify_mapD Local_Plcs (fun _ : Plc => false)) p1 *)

Theorem executable_impl_precond : forall t p envM,
  executable_global t p envM ->
  (forall p' absMan,
    map_get envM p' = Some absMan ->
    ((forall (a : ASP_ID), In a (asps absMan)) /\ 
     (forall (u : Plc), In u (uuidPlcs absMan)) /\
     (forall (p : Plc), In p (pubKeyPlcs absMan)))
  ).
Proof.
  induction t; simpl in *; intuition; eauto.
Admitted.

Definition lib_supports_manifest (al : AM_Library) (am : Manifest) : Prop :=
  (forall (a : ASP_ID), In a am.(asps) -> exists cb, Maps.map_get al.(Local_ASPS) a = Some cb) /\
  (forall (up : Plc), In up am.(uuidPlcs) -> exists b, Maps.map_get al.(Local_Plcs) up = Some b) /\
  (forall (pkp : Plc), In pkp am.(pubKeyPlcs) -> exists b, Maps.map_get al.(Local_PubKeys) pkp = Some b).

Ltac unfolds :=
  repeat monad_unfold;
  repeat unfold manifest_generator, manifest_compiler, generate_ASP_dispatcher, 
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

Theorem man_gen_aspid_in : forall a m,
  In a (asps (aspid_manifest_update a m)).
Proof.
  induction m; simpl in *; eauto.
Qed.



Lemma stupid_map_killer : forall a Local_ASPS st_pl st_ev p t m l d,
  (exists cb : CakeML_ASPCallback CallBackErrors, map_get Local_ASPS a = Some cb) ->
  (match
      map_get
        (minify_mapC Local_ASPS
            (fun x : ASP_ID =>
            if
              in_dec (EqClass_impl_DecEq ASP_ID) x (asps (aspid_manifest_update a (update_manifest_policy_targ p t m)))
            then true
            else false)) a
        with
        | Some cb =>
            match cb (asp_paramsC a l p t) st_pl (encodeEvRaw (get_bits st_ev)) (get_bits st_ev) with
            | errC c => match c with
                        | messageLift _ => errC Runtime
                        end
            | resultC r => resultC r
            end
        | None => errC Unavailable
        end = errC d) ->
  d = Runtime.
Proof.
  destruct d; eauto; intros; repeat break_match; 
  try congruence; clear H0.
  destruct H; pose proof man_gen_aspid_in; eauto.
  pose proof (H0 a). clear H0.
  assert (Some x = None). {
    rewrite <- H, <- Heqo.
    clear Heqo H st_pl st_ev x l.
    induction Local_ASPS; simpl in *; eauto.
    rewrite IHLocal_ASPS. clear IHLocal_ASPS.
    simpl in *.
    destruct a0, (eqb a a0) eqn:E; simpl in *; eauto;
    try (rewrite eqb_leibniz in E; subst; eauto).
    - destruct (in_dec (EqClass_impl_DecEq ASP_ID) a0 (asps (aspid_manifest_update a0 (update_manifest_policy_targ p t m)))); simpl in *; try rewrite eqb_refl in *; eauto; try (pose proof (H1 (update_manifest_policy_targ p t m))); try congruence.
    - destruct (in_dec (EqClass_impl_DecEq ASP_ID) a0 (asps (aspid_manifest_update a (update_manifest_policy_targ p t m)))); simpl in *; eauto; rewrite E; eauto.
  }
  congruence.
Qed.


Global Hint Resolve stupid_map_killer : core.
Global Hint Resolve man_gen_aspid_in : core.

Lemma updated_map_includes_updated_asp : forall (l : MapC ASP_ID (CakeML_ASPCallback CallBackErrors)) a p t m,
  (exists cb : CakeML_ASPCallback CallBackErrors, map_get l a = Some cb) ->
  (map_get (minify_mapC 
    l (fun x : ASP_ID => if in_dec (EqClass_impl_DecEq ASP_ID) x (asps (aspid_manifest_update a (update_manifest_policy_targ p t m))) then true else false)) a = None) -> False.
Proof.
  intros.
  induction l; simpl in *.
  - destruct H; congruence.
  - destruct a0, (eqb a a0) eqn:E, 
    (in_dec (EqClass_impl_DecEq ASP_ID) a0 (asps (aspid_manifest_update a (update_manifest_policy_targ p t m))));
    simpl in *; try (rewrite E in *); try congruence; eauto.
    rewrite eqb_leibniz in *; subst; destruct n; eauto.
Qed.

Global Hint Resolve updated_map_includes_updated_asp : core.
(* 
Lemma generated_uuid_plcs_not_none : forall (l : MapD Plc UUID) (p : Plc) t p0 backEnv p' absMan,
  (map_get (manifest_generator' p t (at_manifest_generator p0 p backEnv)) p' = Some absMan) ->
  (forall up : Plc, In up (uuidPlcs absMan) -> exists b : UUID, map_get l up = Some b) ->
  (map_get (minify_mapD l 
    (fun x : Plc => if in_dec (EqClass_impl_DecEq Plc) x (uuidPlcs absMan) then true else false)) p = None) ->
  False.
Proof.
  induction l; simpl in *; intuition; eauto.
  - admit.
  - repeat (break_if; simpl in *; eauto; try congruence).
    * admit.
    * 
    * pose proof (IHl _ _ _ _ _ _ H).
      eapply IHl; eauto; intros.
      destruct (H0 _ H2); break_if; eauto; invc H3.
      rewrite eqb_leibniz in *; subst. *)

Theorem filter_resolver : forall {A B} `{EqClass A} (m : MapC A B) a (filt : A -> bool),
  (exists x, map_get m a = Some x) ->
  filt a = true ->
  exists x, map_get (minify_mapC m filt) a = Some x.
Proof.
  induction m; intuition; simpl in *;
  destruct (eqb a a0) eqn:E.
  - rewrite eqb_leibniz in E; subst. rewrite H1; simpl in *; rewrite eqb_refl; eauto.
  - destruct (filt a0); simpl in *; eauto; rewrite E; eauto.
Qed.


Theorem filter_resolver_mapd : forall {A B} `{EqClass A, EqClass B} (m : MapC A B) a (filt : A -> bool),
  (exists x, map_get m a = Some x) ->
  filt a = true ->
  exists x, map_get (minify_mapD m filt) a = Some x.
Proof.
  induction m; intuition; simpl in *;
  destruct (eqb a a0) eqn:E.
  - rewrite eqb_leibniz in E; subst; destruct H1; simpl in *; 
    repeat find_injection; rewrite H2; simpl in *; rewrite eqb_refl; eauto.
  - destruct (filt a0); simpl in *; eauto; rewrite E; eauto.
Qed.

Global Hint Resolve filter_resolver : core.
Global Hint Resolve filter_resolver_mapd : core.

Lemma in_dec_helper : forall {A B} `{EqClass A} X l l' a (c : B),
  map_get (minify_mapC l (fun x : A => if in_dec X x l' then true else false)) a = Some c ->
  In a l'.
Proof.
  induction l; simpl in *; intuition; try congruence;
  repeat break_if; eauto; simpl in *; 
  repeat break_if; eauto; try rewrite eqb_leibniz in Heqb1; 
  subst; eauto; congruence.
Qed.

Global Hint Resolve filter_resolver : core.

Require Import Helpers_CvmSemantics.

Theorem manifest_compiler_sound : forall t p backEnv envM,
  manifest_generator' p t backEnv = envM ->
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
  intros.
  pose proof (manifest_generator_executability_static' t p backEnv).
  rewrite <- H in H0.
  pose proof (executable_impl_precond _ _ _ H4 _ _ H0); intuition.
  unfold lib_supports_manifest in *; intuition.
  assert (forall a : ASP_ID, exists cb : CakeML_ASPCallback CallBackErrors, map_get (Local_ASPS amLib) a = Some cb
  ); eauto.
  assert (forall up : Plc, exists b : UUID, map_get (Local_Plcs amLib) up = Some b); eauto.
  assert (forall p : Plc, exists b : PublicKey, map_get (Local_PubKeys amLib) p = Some b); eauto.
  clear H1 H10 H7 H H0 H4 backEnv envM p p'; intuition.
  generalizeEverythingElse t.
  induction t; simpl in *; unfolds; intuition; eauto;
  repeat find_injection; simpl in *; monad_unfold; simpl in *; intuition; eauto;
  repeat monad_unfold; simpl in *; eauto.
  - destruct a; 
    repeat (try break_if; try monad_unfold; try break_match; simpl in *; intuition; 
    repeat find_injection; repeat find_inversion; eauto; try congruence);
    destruct st, st_AM_config; simpl in *; find_injection; eauto;
    repeat break_match;
    simpl in *; repeat find_injection; repeat find_inversion; eauto; try congruence;
    match goal with
      | H:  context[ map_get (minify_mapC ?l ?filt) ?a],
        H1: forall a' : ASP_ID, (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapC l filt) a = Some x)
        (* ;
        [
          eapply filter_resolver; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ] *)
    end.
    * eapply filter_resolver; eauto.
  - edestruct IHt; intuition; eauto;
    repeat break_match; repeat break_if;
    repeat find_injection; repeat find_inversion;
    repeat find_rewrite; simpl in *; eauto; 
    repeat (monad_unfold; unfolds; simpl in *; eauto; try congruence).
    * unfold remote_session in *; simpl in *; monad_unfold;
      repeat break_match; repeat break_if;
      repeat find_injection; repeat find_inversion;
      repeat find_rewrite; simpl in *; eauto;
      try congruence.
      unfold doRemote_session' in *; repeat break_match;
      simpl in *; eauto; repeat monad_unfold;
      repeat break_match; simpl in *; repeat find_injection;
      repeat find_inversion; intuition; eauto; try congruence.
      unfold do_remote in *; simpl in *; repeat break_match;
      repeat find_injection; try congruence;
      try (match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end); eauto.
    * unfold remote_session in *; simpl in *; monad_unfold;
      repeat break_match; repeat break_if;
      repeat find_injection; repeat find_inversion;
      repeat find_rewrite; simpl in *; eauto;
      try congruence.
      unfold doRemote_session' in *; repeat break_match;
      simpl in *; eauto; repeat monad_unfold;
      repeat break_match; simpl in *; repeat find_injection;
      repeat find_inversion; intuition; eauto; try congruence.
      unfold do_remote in *; simpl in *; repeat break_match;
      repeat find_injection; try congruence;
      try (match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end); eauto.
  - pose proof (IHt1 _ _ _ H2 st H3); intuition.
    destruct H; intuition; 
    try (rewrite H0; eauto).
    assert (st_AM_config x = amConf). {
      destruct st; monad_unfold.
      pose proof (ac_immut (copland_compile t1) st_ev st_trace st_pl st_evid st_AM_config).
      monad_unfold.
      rewrite H0 in H.
      simpl in *; subst; eauto.
    }
    pose proof (IHt2 _ _ _ H2 x H); intuition.
    destruct H1; intuition; 
    try (rewrite H4; eauto).
  - destruct s, s, s0; simpl in *; monad_unfold; intuition; eauto.
    * pose proof (IHt1 _ _ _ H2 {|
          st_ev := st_ev st;
          st_trace := st_trace st ++ Term_Defs.split (st_evid st) (st_pl st) :: nil;
          st_pl := st_pl st;
          st_evid := st_evid st + 1;
          st_AM_config := st_AM_config st
        |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
      assert (st_AM_config x = amConf). {
      destruct st; monad_unfold.
      pose proof (ac_immut (copland_compile t1) st_ev (st_trace ++ Term_Defs.split st_evid st_pl :: nil) 
        st_pl (st_evid + 1) st_AM_config).
      monad_unfold.
      rewrite H0 in H.
      simpl in *; subst; eauto.
      }
      pose proof (IHt2 _ _ _ H2 {|
              st_ev := st_ev st; st_trace := st_trace x; st_pl := st_pl x; st_evid := st_evid x; st_AM_config := st_AM_config x
            |} H); intuition.
      destruct H1; intuition; 
      try (rewrite H4; eauto).
    * pose proof (IHt1 _ _ _ H2 {| 
            st_ev := st_ev st;
            st_trace := st_trace st ++ Term_Defs.split (st_evid st) (st_pl st) :: nil;
            st_pl := st_pl st;
            st_evid := st_evid st + 1;
            st_AM_config := st_AM_config st
          |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto);
      assert (st_AM_config x = amConf). {
        destruct st; monad_unfold;
        pose proof (ac_immut (copland_compile t1) st_ev (st_trace ++ Term_Defs.split st_evid st_pl :: nil) 
          st_pl (st_evid + 1) st_AM_config);
        monad_unfold;
        rewrite H0 in H;
        simpl in *; subst; eauto.
      }
      pose proof (IHt2 _ _ _ H2 {|
                st_ev := mt_evc; st_trace := st_trace x; st_pl := st_pl x; st_evid := st_evid x; st_AM_config := st_AM_config x
              |} H); intuition;
      destruct H1; intuition; 
      try (rewrite H4; eauto).
    * pose proof (IHt1 _ _ _ H2 {| 
            st_ev := mt_evc;
            st_trace := st_trace st ++ Term_Defs.split (st_evid st) (st_pl st) :: nil;
            st_pl := st_pl st;
            st_evid := st_evid st + 1;
            st_AM_config := st_AM_config st
          |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto);
      assert (st_AM_config x = amConf). {
        destruct st; monad_unfold;
        pose proof (ac_immut (copland_compile t1) mt_evc (st_trace ++ Term_Defs.split st_evid st_pl :: nil) 
          st_pl (st_evid + 1) st_AM_config);
        monad_unfold;
        rewrite H0 in H;
        simpl in *; subst; eauto.
      }
      pose proof (IHt2 _ _ _ H2 {|
                st_ev := st_ev st; st_trace := st_trace x; st_pl := st_pl x; st_evid := st_evid x; st_AM_config := st_AM_config x
              |} H); intuition;
      destruct H1; intuition; 
      try (rewrite H4; eauto).
    * pose proof (IHt1 _ _ _ H2 {| 
            st_ev := mt_evc ;
            st_trace := st_trace st ++ Term_Defs.split (st_evid st) (st_pl st) :: nil;
            st_pl := st_pl st;
            st_evid := st_evid st + 1;
            st_AM_config := st_AM_config st
          |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto);
      assert (st_AM_config x = amConf). {
        destruct st; monad_unfold;
        pose proof (ac_immut (copland_compile t1) mt_evc (st_trace ++ Term_Defs.split st_evid st_pl :: nil) 
          st_pl (st_evid + 1) st_AM_config);
        monad_unfold;
        rewrite H0 in H;
        simpl in *; subst; eauto.
      }
      pose proof (IHt2 _ _ _ H2 {|
                st_ev := mt_evc; st_trace := st_trace x; st_pl := st_pl x; st_evid := st_evid x; st_AM_config := st_AM_config x
              |} H); intuition;
      destruct H1; intuition; 
      try (rewrite H4; eauto).
  - destruct s, s, s0; simpl in *; monad_unfold; intuition; eauto.
    * pose proof (IHt1 _ _ _ H2 {|
           st_ev := st_ev st;
           st_trace :=
             (st_trace st ++ Term_Defs.split (st_evid st) (st_pl st) :: nil) ++
             cvm_thread_start 0 (st_pl st) (copland_compile t2) (get_et (st_ev st)) :: nil;
           st_pl := st_pl st;
           st_evid := st_evid st + 1;
           st_AM_config := st_AM_config st
         |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
    * pose proof (IHt1 _ _ _ H2 {|
                 st_ev := st_ev st;
                 st_trace :=
                   app (app (st_trace st) (cons (Term_Defs.split (st_evid st) (st_pl st)) nil))
                     (cons (cvm_thread_start 0 (st_pl st) (lseqc (aspc CLEAR) (copland_compile t2)) (get_et (st_ev st))) nil);
                 st_pl := st_pl st;
                 st_evid := Nat.add (st_evid st) 1;
                 st_AM_config := st_AM_config st
               |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
    * pose proof (IHt1 _ _ _ H2 {|
                  st_ev := mt_evc;
                  st_trace :=
                    app (app (st_trace st) (cons (Term_Defs.split (st_evid st) (st_pl st)) nil))
                      (cons (cvm_thread_start 0 (st_pl st) (copland_compile t2) (get_et (st_ev st))) nil);
                  st_pl := st_pl st;
                  st_evid := Nat.add (st_evid st) 1;
                  st_AM_config := st_AM_config st
                |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
    * pose proof (IHt1 _ _ _ H2 {|
                  st_ev := mt_evc;
                  st_trace :=
                    app (app (st_trace st) (cons (Term_Defs.split (st_evid st) (st_pl st)) nil))
                      (cons (cvm_thread_start 0 (st_pl st) (lseqc (aspc CLEAR) (copland_compile t2)) (get_et (st_ev st))) nil);
                  st_pl := st_pl st;
                  st_evid := Nat.add (st_evid st) 1;
                  st_AM_config := st_AM_config st
                |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
Qed.
