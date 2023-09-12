Require Import Manifest Manifest_Compiler Manifest_Generator AbstractedTypes
  Maps Term_Defs List Cvm_St Cvm_Impl ErrorStMonad_Coq StructTactics 
  Cvm_Monad EqClass Manifest_Admits Auto.
Require Import Manifest_Generator_Facts Executable_Defs_Prop 
  Executable_Facts_Dist Eqb_Evidence.

Require Import Coq.Program.Tactics.

Import ListNotations.

(* Set Nested Proofs Allowed. *)

Fixpoint add_to_list {A : Type} `{EqClass A} (l : list A) (v : A) : list A :=
  match l with
  | nil => v :: nil
  | h :: t => if (eqb h v) then (h :: t) else h :: (add_to_list t v)
  end.


Definition lib_supports_manifest (al : AM_Library) (am : Manifest) : Prop :=
  (forall (a : ASP_ID), In a am.(asps) -> exists cb, Maps.map_get al.(Local_ASPS) a = Some cb) /\
  (forall (up : Plc), In up am.(uuidPlcs) -> exists b, Maps.map_get al.(Local_Plcs) up = Some b) /\
  (forall (pkp : Plc), In pkp am.(pubKeyPlcs) -> exists b, Maps.map_get al.(Local_PubKeys) pkp = Some b).

Ltac unfolds :=
  (* repeat monad_unfold; *)
  repeat unfold manifest_generator, manifest_compiler, generate_ASP_dispatcher, 
    generate_Plc_dispatcher, generate_PubKey_dispatcher,
    generate_UUID_dispatcher, lib_supports_manifest, aspid_manifest_update,
    sig_params, hsh_params, enc_params in *;
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

Global Hint Resolve man_gen_aspid_in : core.

Theorem filter_resolver : forall {A B} `{EqClass A} (m : MapC A B) a (filt : A -> bool),
  (exists x, map_get m a = Some x) ->
  filt a = true ->
  exists x, map_get (minify_mapC m filt) a = Some x.
Proof.
  induction m; intuition; simpl in *;
  destruct (eqb a a0) eqn:E.
  - rewrite eqb_leibniz in E; subst. rewrite H1; simpl in *; rewrite eqb_refl; eauto.
  - repeat break_match; simpl in *; 
    try (pose proof eqb_symm; congruence);
    simpl in *; eauto.
    rewrite eqb_symm; rewrite E; eauto.
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
  - repeat break_match; simpl in *; 
    try (pose proof eqb_symm; congruence);
    simpl in *; eauto;
    repeat (find_rewrite; intuition; eauto; try congruence).
    rewrite eqb_symm in E; congruence.
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

Lemma callbacks_work_asps : forall absMan amLib amConf,
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  (forall x, In x absMan.(asps) -> 
    forall l p t p' ev ev' res,
      aspCb amConf (asp_paramsC x l p t) p' ev ev' = res ->
      res = errC Runtime \/ exists r, res = resultC r
  ).
Proof.
  induction absMan; simpl in *; intuition;
  destruct res; eauto; destruct d; eauto.
  destruct amConf; simpl in *;
  destruct amLib; simpl in *.
  unfold manifest_compiler in H0; repeat find_injection;
  simpl in *.
  repeat break_match; try congruence.
  unfold lib_supports_manifest in *; simpl in *;
  intuition.
  pose proof (H0 _ H1).
  assert ((fun x : ASP_ID =>
             if in_dec (EqClass_impl_DecEq ASP_ID) x asps
             then true
             else false) x = true).
  repeat break_match; eauto.
  pose proof (filter_resolver _ _ ((fun x : ASP_ID =>
             if in_dec (EqClass_impl_DecEq ASP_ID) x asps
             then true
             else false)) H3 H5).
  destruct H6. 
  assert (Some x0 = None). 
  rewrite <- H6. rewrite <- Heqo; eauto.
  congruence.
Qed.

Lemma add_to_list_works : forall {A} `{EqClass A} (l : list A) x,
  In x (add_to_list l x).
Proof.
  induction l; simpl in *; intuition; eauto;
  break_match; simpl in *; eauto.
  - rewrite eqb_leibniz in *; subst; eauto.
Qed.

Local Hint Resolve add_to_list_works : core.

(*
Lemma ac_immut : forall t e tr p i ac,
  st_AM_config 
    (execErr 
      (build_cvm t)
      {|
        st_ev := e;
        st_trace := tr;
        st_pl := p;
        st_evid := i;
        st_AM_config := ac
      |}) = ac.
Proof.

*)

Lemma never_change_am_conf : forall t st res st',
  build_cvm (copland_compile t) st = (res, st') ->
  st_AM_config st = st_AM_config st'.
Proof.
  intros.
  destruct st.
  simpl. 
  edestruct ac_immut.
  unfold execErr.
  rewrite H.
  simpl. eauto.
Qed.

Definition supports_am (ac1 ac2 : AM_Config) : Prop :=
  (forall aid l targ targid p' ev ev',
      (forall res, 
      ac1.(aspCb) (asp_paramsC aid l targ targid) p' ev ev' = resultC res ->
      ac2.(aspCb) (asp_paramsC aid l targ targid) p' ev ev' = resultC res)) /\
  (forall p, (forall res, 
      ac1.(pubKeyCb) p = resultC res ->
      ac2.(pubKeyCb) p = resultC res)) /\
  (forall p, (forall res, 
      ac1.(plcCb) p = resultC res ->
      ac2.(plcCb) p = resultC res)) /\
  (forall aid l targ targid p' ev ev',
      ac1.(aspCb) (asp_paramsC aid l targ targid) p' ev ev' = errC Runtime ->
      ac2.(aspCb) (asp_paramsC aid l targ targid) p' ev ev' = errC Runtime) /\
  (forall p, 
      ac1.(pubKeyCb) p = errC Runtime ->
      ac2.(pubKeyCb) p = errC Runtime) /\
  (forall p, 
      ac1.(plcCb) p = errC Runtime ->
      ac2.(plcCb) p = errC Runtime).

Theorem supports_am_refl : forall ac1,
  supports_am ac1 ac1.
Proof.
  unfold supports_am; intuition.
Qed.

Theorem supports_am_trans : forall ac1 ac2 ac3,
  supports_am ac1 ac2 ->
  supports_am ac2 ac3 ->
  supports_am ac1 ac3.
Proof.
  unfold supports_am; intuition.
Qed.

Local Hint Resolve never_change_am_conf : core.
Local Hint Resolve supports_am_refl : core.
Local Hint Resolve supports_am_trans : core.

Fixpoint am_config_support_exec (t : Term) 
    (p : Plc) (ac : AM_Config) : Prop :=
  match t with
  | asp a =>
      match a with
      | NULL => True
      | CPY => True
      | SIG => 
          forall l targ targid p' ev ev',
          ((exists res, 
          ac.(aspCb) (asp_paramsC sig_aspid l targ targid) p' ev ev' = resultC res) \/ 
          ac.(aspCb) (asp_paramsC sig_aspid l targ targid) p' ev ev' = errC Runtime)
      | HSH =>
          forall l targ targid p' ev ev',
          ((exists res, 
          ac.(aspCb) (asp_paramsC hsh_aspid l targ targid) p' ev ev' = resultC res) \/ 
          ac.(aspCb) (asp_paramsC hsh_aspid l targ targid) p' ev ev' = errC Runtime)
      | ENC p =>
          (forall l targ targid p' ev ev',
          ((exists res, 
          ac.(aspCb) (asp_paramsC enc_aspid l targ targid) p' ev ev' = resultC res) \/ 
          ac.(aspCb) (asp_paramsC enc_aspid l targ targid) p' ev ev' = errC Runtime)) /\
          ((exists res, ac.(pubKeyCb) p = resultC res) \/ 
          ac.(pubKeyCb) p = errC Runtime)
      | ASPC _ _ (asp_paramsC aspid _ _ _) =>
          (forall l targ targid p' ev ev',
          ((exists res, 
          ac.(aspCb) (asp_paramsC aspid l targ targid) p' ev ev' = resultC res) \/ 
          ac.(aspCb) (asp_paramsC aspid l targ targid) p' ev ev' = errC Runtime)) 
      end
  | att p' t' =>
      ((exists res, ac.(plcCb) p' = resultC res) \/ 
      ac.(plcCb) p' = errC Runtime)
      (* /\ am_config_support_exec t' p' ac *)
  | lseq t1 t2 =>
      exists ac1 ac2,
      (am_config_support_exec t1 p ac1) /\
      (am_config_support_exec t2 p ac2) /\
      supports_am ac1 ac /\
      supports_am ac2 ac
  | bseq _ t1 t2 =>
      exists ac1 ac2,
      (am_config_support_exec t1 p ac1) /\
      (am_config_support_exec t2 p ac2) /\
      supports_am ac1 ac /\
      supports_am ac2 ac
  | bpar _ t1 t2 =>
      exists ac1 ac2,
      (am_config_support_exec t1 p ac1) /\
      (am_config_support_exec t2 p ac2) /\
      supports_am ac1 ac /\
      supports_am ac2 ac
  end.

Theorem well_formed_am_config_impl_executable : forall t p amConf,
  am_config_support_exec t p amConf ->
  forall st,
  supports_am amConf (st.(st_AM_config)) ->
  exists st', 
    build_cvm (copland_compile t) st = (resultC tt, st') \/
    build_cvm (copland_compile t) st = (errC (dispatch_error Runtime), st').
Proof.
  induction t; simpl in *; intuition; eauto.
  - destruct a;
    try (simpl in *; monad_unfold; eauto; fail); (* NULL, CPY *)
    subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      try break_match;
      try monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
    unfold supports_am, sig_params, enc_params, hsh_params in *; intuition;
    match goal with
    | H1 : forall _, _,
      H2 : aspCb _ (asp_paramsC ?a ?l ?targ ?tid) ?p' ?ev ?ev' = _,
      H3 : context[ aspCb _ _ _ _ _ = errC Runtime -> _],
      H4 : context[ aspCb _ _ _ _ _ = resultC _ -> _]
      |- _ =>
        let H := fresh "H" in
        let H' := fresh "Hx" in
        let H'' := fresh "Hx" in
        let res := fresh "res" in
        destruct (H1 l targ tid p' ev ev') as [H | H]
        ; 
        [
          (* result side *)
          destruct H as [res H''];
          pose proof (H4 a l targ tid p' ev ev') as H';
          erewrite H' in *; eauto; congruence
          |
          (* err side *)
          pose proof (H3 a l targ tid p' ev ev') as H';
          intuition; find_rewrite; find_injection; eauto
        ]
    end.
  - subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      unfold remote_session, doRemote_session', do_remote, check_cvm_policy in *;
      try break_match;
      try monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
    unfold supports_am in *; intuition.
    +
      destruct H0;
      erewrite H2 in *; try congruence; eauto.
  - subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      unfold remote_session, doRemote_session', do_remote, check_cvm_policy in *;
      try break_match;
      try monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
    unfold supports_am in *; intuition;
    erewrite H6 in *; try congruence;
    find_injection; eauto.
  - subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      try break_match;
      try monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
      match goal with
      | H1 : exists _ _ : AM_Config, _
        |- _ =>
          let ac1 := fresh "ac" in
          let ac2 := fresh "ac" in
          let AS1 := fresh "AS" in
          let AS2 := fresh "AS" in
          let S1 := fresh "S" in
          let S2 := fresh "S" in
          destruct H1 as [ac1 [ac2 [AS1 [AS2 [S1 S2]]]]]
          ;
          match goal with
          | H2 : build_cvm (copland_compile t1) ?st = _
            |- _ =>
              let A := fresh "A" in
              assert (A : supports_am ac1 (st_AM_config st)); [ 
                simpl in *; eauto
                |
                destruct (IHt1 p ac1 AS1 st A);
                intuition; repeat find_rewrite;
                repeat find_injection;
                try congruence; eauto
              ]
          end;
          match goal with
          | H3 : build_cvm (copland_compile t2) ?st = _
            |- _ =>
              let A := fresh "A" in
              assert (A : supports_am ac2 (st_AM_config st)); [ 
                repeat find_eapply_lem_hyp never_change_am_conf;
                repeat find_rewrite;
                simpl in *; eauto
                |
                destruct (IHt2 p ac2 AS2 st A);
                intuition; repeat find_rewrite;
                repeat find_injection;
                try congruence; eauto
              ]
          end
      end. 
  - subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      try break_match;
      try monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
    match goal with
    | H1 : exists _ _ : AM_Config, _
      |- _ =>
        let ac1 := fresh "ac" in
        let ac2 := fresh "ac" in
        let AS1 := fresh "AS" in
        let AS2 := fresh "AS" in
        let S1 := fresh "S" in
        let S2 := fresh "S" in
        destruct H1 as [ac1 [ac2 [AS1 [AS2 [S1 S2]]]]]
        ;
        match goal with
        | H2 : build_cvm (copland_compile t1) ?st = _
          |- _ =>
            let A := fresh "A" in
            assert (A : supports_am ac1 (st_AM_config st)); [ 
              simpl in *; eauto
              |
              destruct (IHt1 p ac1 AS1 st A);
              intuition; repeat find_rewrite;
              repeat find_injection;
              try congruence; eauto
            ]
        end;
        match goal with
        | H3 : build_cvm (copland_compile t2) ?st = _
          |- _ =>
            let A := fresh "A" in
            assert (A : supports_am ac2 (st_AM_config st)); [ 
              repeat find_eapply_lem_hyp never_change_am_conf;
              repeat find_rewrite;
              simpl in *; eauto
              |
              destruct (IHt2 p ac2 AS2 st A);
              intuition; repeat find_rewrite;
              repeat find_injection;
              try congruence; eauto
            ]
        end;
        repeat find_rewrite; eauto
    end.
  - subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      try break_match;
      try monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
    match goal with
    | H1 : exists _ _ : AM_Config, _
      |- _ =>
        let ac1 := fresh "ac" in
        let ac2 := fresh "ac" in
        let AS1 := fresh "AS" in
        let AS2 := fresh "AS" in
        let S1 := fresh "S" in
        let S2 := fresh "S" in
        destruct H1 as [ac1 [ac2 [AS1 [AS2 [S1 S2]]]]]
        ;
        match goal with
        | H2 : build_cvm (copland_compile t1) ?st = _
          |- _ =>
            let A := fresh "A" in
            assert (A : supports_am ac1 (st_AM_config st)); [ 
              simpl in *; eauto
              |
              destruct (IHt1 p ac1 AS1 st A);
              intuition; repeat find_rewrite;
              repeat find_injection;
              try congruence; eauto
            ]
        end;
        match goal with
        | H3 : build_cvm (copland_compile t2) ?st = _
          |- _ =>
            let A := fresh "A" in
            assert (A : supports_am ac2 (st_AM_config st)); [ 
              repeat find_eapply_lem_hyp never_change_am_conf;
              repeat find_rewrite;
              simpl in *; eauto
              |
              destruct (IHt2 p ac2 AS2 st A);
              intuition; repeat find_rewrite;
              repeat find_injection;
              try congruence; eauto
            ]
        end;
        repeat find_rewrite; eauto
    end.
  (* Unshelve. (* Weirdly, we have trivial existentials left *)
  all: try (eapply default_bs); try (eapply default_UUID). *)
Qed.

Lemma in_add_to_list : forall {A} `{EqClass A} (l : list A) x x',
  In x l ->
  In x (add_to_list l x').
Proof.
  induction l; simpl in *; intuition; eauto;
  subst; eauto; break_match; simpl in *; eauto.
Qed.

Local Hint Resolve in_add_to_list : core.

Lemma in_add_to_list_rev : forall {A} `{EqClass A} (l : list A) (a a' : A),
  a <> a' ->
  In a (add_to_list l a') ->
  In a l.
Proof.
  induction l; simpl in *; intuition; eauto.
  break_match; simpl in *; intuition; eauto.
Qed.

Lemma in_dec_add_to_list : forall {A} `{EqClass A} l a a',
  a <> a' ->
  (if (in_dec (EqClass_impl_DecEq A) a l) then true else false) =  
  if (in_dec (EqClass_impl_DecEq A) a (add_to_list l a')) then true else false.
Proof.
  intuition; repeat break_match; eauto.
  - destruct n; eapply in_add_to_list; eauto.
  - destruct n; eapply in_add_to_list_rev; eauto.
Qed.

Lemma cannot_be_in_filter_map : forall {A B} `{EqClass A} (l : MapC A B) l' a,
  ~ (In a l') ->
  map_get (minify_mapC l 
    (fun x : A => if in_dec (EqClass_impl_DecEq A) x l' then true else false)) a = None.
Proof.
  induction l; simpl in *; intuition; eauto;
  repeat (break_match; simpl in *; eauto; try congruence);
  rewrite eqb_leibniz in *; congruence.
Qed.

Lemma cannot_be_in_filter_mapd : forall {A B} `{EqClass A, EqClass B} (l : MapD A B) l' a,
  ~ (In a l') ->
  map_get (minify_mapD l 
    (fun x : A => if in_dec (EqClass_impl_DecEq A) x l' then true else false)) a = None.
Proof.
  induction l; simpl in *; intuition; eauto;
  repeat (break_match; simpl in *; eauto; try congruence);
  rewrite eqb_leibniz in *; congruence.
Qed.

Lemma map_get_minify_eq_under_add_to_list : forall {A B} `{EqClass A} (l : MapC A B) l' a a' v,
  map_get (minify_mapC l 
    (fun x : A => if in_dec (EqClass_impl_DecEq A) x l' then true else false)) a = Some v ->
  map_get (minify_mapC l 
    (fun x : A => if in_dec (EqClass_impl_DecEq A) x (add_to_list l' a') then true else false)) a = Some v.
Proof.
  induction l; simpl in *; intuition; eauto;
  repeat (break_match; simpl in *; auto with *; eauto; try congruence);
  rewrite eqb_leibniz in *; subst.
  - assert (Some v = None). {
      rewrite <- H0; eapply cannot_be_in_filter_map; eauto.
    }
    congruence.
Qed.


Lemma mapD_get_minify_eq_under_add_to_list : forall {A B} `{EqClass A, EqClass B} (l : MapD A B) l' a a' v,
  map_get (minify_mapD l 
    (fun x : A => if in_dec (EqClass_impl_DecEq A) x l' then true else false)) a = Some v ->
  map_get (minify_mapD l 
    (fun x : A => if in_dec (EqClass_impl_DecEq A) x (add_to_list l' a') then true else false)) a = Some v.
Proof.
  induction l; simpl in *; intuition; eauto;
  repeat (break_match; simpl in *; auto with *; eauto; try congruence);
  rewrite eqb_leibniz in *; subst.
  - assert (Some v = None). {
      rewrite <- H1; eapply cannot_be_in_filter_mapd; eauto.
    }
    congruence.
Qed.

Definition manifest_support_am_config (m : Manifest) (ac : AM_Config) : Prop :=
  (forall a, In a (m.(asps)) -> 
    forall l targ targid p' ev ev',
    (exists res, ac.(aspCb) (asp_paramsC a l targ targid) p' ev ev' = resultC res) \/
    (ac.(aspCb) (asp_paramsC a l targ targid) p' ev ev' = errC Runtime)) /\
  (forall p, In p (m.(uuidPlcs)) ->
    (exists res, ac.(plcCb) p = resultC res) \/
    (ac.(plcCb) p = errC Runtime)) /\
  (forall p, In p (m.(pubKeyPlcs)) ->
    (exists res, ac.(pubKeyCb) p = resultC res) \/
    (ac.(pubKeyCb) p = errC Runtime)).

Theorem manifest_support_am_config_compiler : forall absMan amLib,
  lib_supports_manifest amLib absMan ->
  manifest_support_am_config absMan (manifest_compiler absMan amLib).
Proof.
  unfold lib_supports_manifest, manifest_support_am_config, 
    manifest_compiler, generate_PubKey_dispatcher, generate_Plc_dispatcher in *;
  simpl in *; intuition;
  repeat break_match; simpl in *; intuition; eauto;
  match goal with
  | H:  context[ map_get (minify_mapC ?l ?filt) ?a],
    H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
    assert (CO : exists x, map_get (minify_mapC l filt) a = Some x)
    ;
      [
      eapply filter_resolver; eauto;
      repeat break_match; intuition; try congruence
      | 
      rewrite H in CO; destruct CO; congruence
    ]
  | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
    H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
    assert (CO : exists x, map_get (minify_mapD l filt) a = Some x)
    ;
      [
      eapply filter_resolver_mapd; eauto;
      repeat break_match; intuition; try congruence
      | 
      rewrite H in CO; destruct CO; congruence
    ]
  end.
Qed.

Fixpoint manifest_support_term (m : Manifest) (t : Term) : Prop :=
  match t with
  | asp a =>
      match a with
      | NULL => True
      | CPY => True
      | SIG => 
          In sig_aspid (m.(asps))
      | HSH =>
          In hsh_aspid (m.(asps))
      | ENC p =>
          In enc_aspid (m.(asps)) /\
          In p (m.(pubKeyPlcs))
      | ASPC _ _ (asp_paramsC aspid _ _ _) =>
          In aspid (m.(asps))
      end
  | att p' t' =>
      In p' (m.(uuidPlcs))
  | lseq t1 t2 =>
      manifest_support_term m t1 /\
      manifest_support_term m t2
  | bseq _ t1 t2 =>
      manifest_support_term m t1 /\
      manifest_support_term m t2
  | bpar _ t1 t2 =>
      manifest_support_term m t1 /\
      manifest_support_term m t2
  end.

Theorem manifest_support_am_config_impl_am_config: forall t p absMan amConf,
  manifest_support_am_config absMan amConf ->
  manifest_support_term absMan t ->
  am_config_support_exec t p amConf.
Proof.
  induction t; simpl in *; intuition; eauto;
  unfold manifest_support_am_config in *; intuition; eauto;
  repeat (try break_match; simpl in *; intuition; eauto).
  - pose proof (IHt1 p absMan amConf); 
    pose proof (IHt2 p absMan amConf); intuition;
    exists amConf, amConf; eauto.
  - pose proof (IHt1 p absMan amConf); 
    pose proof (IHt2 p absMan amConf); intuition;
    exists amConf, amConf; eauto.
  - pose proof (IHt1 p absMan amConf); 
    pose proof (IHt2 p absMan amConf); intuition;
    exists amConf, amConf; eauto.
Qed.

Lemma places_decomp: forall t1 t2 p tp,
In p (places' t2 (places' t1 [])) -> 
(In p (places tp t1) \/ 
      In p (places tp t2)).
Proof.
intros.

assert (In p (places' t2 []) \/ In p (places' t1 [])).
{
  assert (In p (places' t1 []) \/ (~ In p (places' t1 []))).
  { 
      apply In_dec_tplc.
  }
  door.
  +
    eauto.
  +             
    assert (In p (places' t2 [])).
    {
      eapply places_app_cumul.
      apply H.
      eassumption.
    }
    eauto.
}
door.
right.
unfold places.
right.
eauto.

left.
right.
eauto.
Qed.

Lemma has_manifest_env_places_env_has_manifest' : forall t p tp m e,
map_get (manifest_generator' tp t e) p = Some m ->
(exists m', map_get e p = Some m') \/ 
In p (places tp t).
Proof.

intros.
generalizeEverythingElse t.
induction t; intros.
-
  destruct a; ff.
  +
    unfold asp_manifest_generator in *.
    unfold asp_manifest_update in *.
    unfold manifest_update_env in *.
    ff.
    ++

    destruct (eq_plc_dec tp p); try solve_by_inversion.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    eassumption.
    eassumption. 

    ++
    destruct (eq_plc_dec tp p); try solve_by_inversion.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    eassumption.
    eassumption.
    +
    unfold asp_manifest_generator in *.
    unfold asp_manifest_update in *.
    unfold manifest_update_env in *.
    ff.
    ++

    destruct (eq_plc_dec tp p); try solve_by_inversion.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    eassumption.
    eassumption. 

    ++
    destruct (eq_plc_dec tp p); try solve_by_inversion.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    eassumption.
    eassumption.
    +
    unfold asp_manifest_generator in *.
    unfold asp_manifest_update in *.
    unfold manifest_update_env in *.
    ff.
    ++

    destruct (eq_plc_dec tp p); try solve_by_inversion.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    eassumption.
    eassumption. 

    ++
    destruct (eq_plc_dec tp p); try solve_by_inversion.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    eassumption.
    eassumption.
    +
    unfold asp_manifest_generator in *.
    unfold asp_manifest_update in *.
    unfold manifest_update_env in *.
    ff.
    ++

    destruct (eq_plc_dec tp p); try solve_by_inversion.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    eassumption.
    eassumption. 

    ++
    destruct (eq_plc_dec tp p); try solve_by_inversion.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    eassumption.
    eassumption.
    +
    unfold asp_manifest_generator in *.
    unfold asp_manifest_update in *.
    unfold manifest_update_env in *.
    ff.
    ++

    destruct (eq_plc_dec tp p); try solve_by_inversion.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    eassumption.
    eassumption. 

    ++
    destruct (eq_plc_dec tp p); try solve_by_inversion.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    eassumption.
    eassumption.
    +
    unfold asp_manifest_generator in *.
    unfold asp_manifest_update in *.
    unfold manifest_update_env in *.
    ff.
    ++

    destruct (eq_plc_dec tp p); try solve_by_inversion.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    eassumption.
    eassumption. 

    ++
    destruct (eq_plc_dec tp p); try solve_by_inversion.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    eassumption.
    eassumption.
  -
  unfold manifest_generator in H.
  simpl in H.
  unfold at_manifest_generator in *.
  ff.
  unfold manifest_generator in IHt.

  destruct (eq_plc_dec tp p0); try solve_by_inversion.
  destruct (eq_plc_dec p p0); try solve_by_inversion.

  apply IHt in H.
  door.
  +
    unfold manifest_update_env in *.
    ff; try solve_by_inversion.
    ++
    unfold knowsof_manifest_update in *.
    ff.
    subst.
    ff.
    left.
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    apply n. 
    eassumption.
    ++
    left. 
    eexists.
    eapply mapC_get_distinct_keys_from_set.
    apply n. 
    eassumption.
  +
    door; try solve_by_inversion.
  - (* lseq case *)
    ff.

    find_apply_hyp_hyp.

    door.
    +
      find_apply_hyp_hyp.
      door.
      ++
      left.
      eauto.
      ++
      right.
      door; eauto.
      right.

      eapply places'_cumul.
      eassumption.
    +
      door.
      ++
      right.
      eauto.
      ++
      right.
      right.
      eapply places_app_cumul.
      eassumption.
      unfold not in *.
      intros.
      solve_by_inversion.
  -
  ff.

  find_apply_hyp_hyp.

  door.
  +
    find_apply_hyp_hyp.
    door.
    ++
    left.
    eauto.
    ++
    right.
    door; eauto.
    right.

    eapply places'_cumul.
    eassumption.
  +
    door.
    ++
    right.
    eauto.
    ++
    right.
    right.
    eapply places_app_cumul.
    eassumption.
    unfold not in *.
    intros.
    solve_by_inversion.

  -
  ff.

  find_apply_hyp_hyp.

  door.
  +
    find_apply_hyp_hyp.
    door.
    ++
    left.
    eauto.
    ++
    right.
    door; eauto.
    right.

    eapply places'_cumul.
    eassumption.
  +
    door.
    ++
    right.
    eauto.
    ++
    right.
    right.
    eapply places_app_cumul.
    eassumption.
    unfold not in *.
    intros.
    solve_by_inversion.
Qed.

Lemma has_manifest_env_places_env_has_manifest : forall t p tp m,
map_get (manifest_generator t tp) p = Some m ->
In p (places tp t).
Proof.
  intros.
  unfold manifest_generator in *.
  apply has_manifest_env_places_env_has_manifest' in H.
  destruct_conjs.
  door; ff. 
Qed.

Lemma places_env_has_manifest : forall t p tp e,
In p (places tp t) -> 
exists m, 
map_get (manifest_generator' tp t e) p = Some m.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    ff.
    door; try solve_by_inversion.
    subst.
    destruct a; 
    unfold asp_manifest_generator;
    unfold asp_manifest_update;
    unfold manifest_update_env;
    ff;
    eexists;
    eapply mapC_get_works.

  - (* at case *)

    ff.
    door; ff.
    subst.
    unfold at_manifest_generator.
    unfold knowsof_manifest_update.
    ff.
    unfold manifest_update_env.
    ff.
    +
      subst.

      assert (Environment_subset 
      (map_set e p0
          {|
            my_abstract_plc := my_abstract_plc;
            asps := asps;
            appraisal_asps := appraisal_asps;
            uuidPlcs := p :: uuidPlcs;
            pubKeyPlcs := pubKeyPlcs;
            targetPlcs := targetPlcs;
            policy := policy
          |})

          (manifest_generator' p t
       (map_set e p0
          {|
            my_abstract_plc := my_abstract_plc;
            asps := asps;
            appraisal_asps := appraisal_asps;
            uuidPlcs := p :: uuidPlcs;
            pubKeyPlcs := pubKeyPlcs;
            targetPlcs := targetPlcs;
            policy := policy
          |}))
      
      ).
      {
        eapply manifest_generator_cumul'.
      }
      unfold Environment_subset in *.


      assert (
        map_get
      (map_set e p0
         {|
           my_abstract_plc := my_abstract_plc;
           asps := asps;
           appraisal_asps := appraisal_asps;
           uuidPlcs := p :: uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |}) p0 = Some {|
         my_abstract_plc := my_abstract_plc;
         asps := asps;
         appraisal_asps := appraisal_asps;
         uuidPlcs := p :: uuidPlcs;
         pubKeyPlcs := pubKeyPlcs;
         targetPlcs := targetPlcs;
         policy := policy
       |}
      ).
      {
        eapply mapC_get_works.

      }

      specialize H with (m1 := {|
        my_abstract_plc := my_abstract_plc;
        asps := asps;
        appraisal_asps := appraisal_asps;
        uuidPlcs := p :: uuidPlcs;
        pubKeyPlcs := pubKeyPlcs;
        targetPlcs := targetPlcs;
        policy := policy
      |}) (p := p0).
      find_apply_hyp_hyp.
      destruct_conjs.

      exists H0.
      eauto.


      +

      subst.

      assert (Environment_subset 
      (map_set e p0
          {|
            my_abstract_plc := my_abstract_plc;
            asps := asps;
            appraisal_asps := appraisal_asps;
            uuidPlcs := p :: uuidPlcs;
            pubKeyPlcs := pubKeyPlcs;
            targetPlcs := targetPlcs;
            policy := policy
          |})

          (manifest_generator' p t
       (map_set e p0
          {|
            my_abstract_plc := my_abstract_plc;
            asps := asps;
            appraisal_asps := appraisal_asps;
            uuidPlcs := p :: uuidPlcs;
            pubKeyPlcs := pubKeyPlcs;
            targetPlcs := targetPlcs;
            policy := policy
          |}))
      
      ).
      {
        eapply manifest_generator_cumul'.
      }
      unfold Environment_subset in *.


      assert (
        map_get
      (map_set e p0
         {|
           my_abstract_plc := my_abstract_plc;
           asps := asps;
           appraisal_asps := appraisal_asps;
           uuidPlcs := p :: uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |}) p0 = Some {|
         my_abstract_plc := my_abstract_plc;
         asps := asps;
         appraisal_asps := appraisal_asps;
         uuidPlcs := p :: uuidPlcs;
         pubKeyPlcs := pubKeyPlcs;
         targetPlcs := targetPlcs;
         policy := policy
       |}
      ).
      {
        eapply mapC_get_works.

      }

      specialize H with (m1 := {|
        my_abstract_plc := my_abstract_plc;
        asps := asps;
        appraisal_asps := appraisal_asps;
        uuidPlcs := p :: uuidPlcs;
        pubKeyPlcs := pubKeyPlcs;
        targetPlcs := targetPlcs;
        policy := policy
      |}) (p := p0).
      find_apply_hyp_hyp.
      destruct_conjs.

      exists H0.
      eauto.

    - (* lseq case *)
      ff.
      door; ff.




      assert (In p (places tp t1) \/ 
              In p (places tp t2)).
              {
                eapply places_decomp; eauto.
              }
      door.
      +
        assert (exists mm, 
                map_get (manifest_generator' tp t1 e) p = Some mm).
        {
          eauto.
        }
        destruct_conjs.

        assert (Environment_subset 
        (manifest_generator' tp t1 e)
        (manifest_generator' tp t2
         (manifest_generator' tp t1 e))
        ).
        {
          eapply manifest_generator_cumul'.
        }

        unfold Environment_subset in *.
        specialize H3 with (m1:=H1) (p:=p).
        find_apply_hyp_hyp.
        destruct_conjs.
        eexists.
        eassumption.

      +
      eapply IHt2.
      unfold places in H0.
      invc H0.
      eauto.
      eauto.


      - (* lseq case *)
      ff.
      door; ff.




      assert (In p (places tp t1) \/ 
              In p (places tp t2)).
              {
                eapply places_decomp; eauto.
              }
      door.
      +
        assert (exists mm, 
                map_get (manifest_generator' tp t1 e) p = Some mm).
        {
          eauto.
        }
        destruct_conjs.

        assert (Environment_subset 
        (manifest_generator' tp t1 e)
        (manifest_generator' tp t2
         (manifest_generator' tp t1 e))
        ).
        {
          eapply manifest_generator_cumul'.
        }

        unfold Environment_subset in *.
        specialize H3 with (m1:=H1) (p:=p).
        find_apply_hyp_hyp.
        destruct_conjs.
        eexists.
        eassumption.

      +
      eapply IHt2.
      unfold places in H0.
      invc H0.
      eauto.
      eauto.



      - (* lseq case *)
      ff.
      door; ff.




      assert (In p (places tp t1) \/ 
              In p (places tp t2)).
              {
                eapply places_decomp; eauto.
              }
      door.
      +
        assert (exists mm, 
                map_get (manifest_generator' tp t1 e) p = Some mm).
        {
          eauto.
        }
        destruct_conjs.

        assert (Environment_subset 
        (manifest_generator' tp t1 e)
        (manifest_generator' tp t2
         (manifest_generator' tp t1 e))
        ).
        {
          eapply manifest_generator_cumul'.
        }

        unfold Environment_subset in *.
        specialize H3 with (m1:=H1) (p:=p).
        find_apply_hyp_hyp.
        destruct_conjs.
        eexists.
        eassumption.

      +
      eapply IHt2.
      unfold places in H0.
      invc H0.
      eauto.
      eauto.
Qed.



(* TODO:  this is likely not provable forall p ... 
   TODO:  perhaps generalize to something like:  
            forall p, In p ((places t1 tp) ++ places e) ?? *)
Lemma asdf : forall t1 t2 tp p' absMan e,
map_get (manifest_generator' tp t2 
            (manifest_generator' tp t1 e)) p' = Some absMan -> 
In p' (places tp t1) ->
exists m', 
map_get (manifest_generator' tp t1 e) p' = Some m' /\ 
manifest_subset m' absMan.
Proof.
  intros.

  assert (Environment_subset 
          (manifest_generator' tp t1 e)
          (manifest_generator' tp t2
            (manifest_generator' tp t1 e))
          
  ).
  {
    eapply manifest_generator_cumul'.
  }

  eapply places_env_has_manifest in H0.
  destruct_conjs.

  unfold Environment_subset in *.

  specialize H1 with (m1 := H0) (p:=p').

  assert (
    exists m2 : Manifest,
       map_get
         (manifest_generator' tp t2
            (manifest_generator' tp t1 e)) p' =
       Some m2 /\ manifest_subset H0 m2
  ).
  {
    eapply H1.
    eassumption.
  }

  destruct_conjs.
  exists H0.
  split; eauto.
  find_rewrite.
  ff.
Qed.

Lemma asdf_easy : forall t1 t2 tp absMan e,
map_get (manifest_generator' tp t2 
            (manifest_generator' tp t1 e)) tp = Some absMan -> 
            
exists m', (* p', 
In p' (places tp t1) /\
*)
map_get (manifest_generator' tp t1 e) tp = Some m' /\ 
manifest_subset m' absMan.
Proof.
  intros.
  eapply asdf.
  eassumption.
  ff.
  eauto.
Qed.

Lemma manifest_supports_term_sub : forall m1 m2 t,
manifest_subset m1 m2 ->
manifest_support_term m1 t -> 
manifest_support_term m2 t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* asp case *)
    ff.
    ff.
    subst.
    unfold manifest_subset in *.
    destruct_conjs.
    eauto.
  - (* at case *)
    ff.
    unfold manifest_subset in *.
    destruct_conjs.
    eauto.
  - (* lseq case *)
    ff.
    destruct_conjs.
    split; eauto.
  - (* bseq case *)
    ff.
    destruct_conjs.
    split; eauto.
  - (* bpar case *)
    ff.
    destruct_conjs.
    split; eauto.
Qed.

Lemma env_subset_man_subset : forall e1 e2 p m m',
Environment_subset e1 e2 -> 
map_get e1 p = Some m -> 
map_get e2 p = Some m' -> 
manifest_subset m m'.
Proof.
  intros.
  unfold Environment_subset in *.
  specialize H with (m1:= m) (p:=p).
  find_apply_hyp_hyp.
  destruct_conjs.
  find_rewrite.
  ff.
Qed.

Lemma fdsa : forall e e2 p p0 m absMan,
Environment_subset
  (map_set e p0 m) 
  (e2) -> 
map_get e2 p0 = Some absMan -> 
In p (uuidPlcs m) -> 
In p (uuidPlcs absMan).
Proof.
  intros.
  assert (map_get (map_set e p0 m) p0 = Some m).
  {
    eapply mapC_get_works; eauto.
  }
  assert (manifest_subset m absMan).
  {
    eapply env_subset_man_subset; eauto.
  }

  unfold manifest_subset in *.
  destruct_conjs.
  eauto.
Qed.

Theorem man_gen_old_always_supports : forall t t' tp p backMan absMan,
  map_get (manifest_generator' tp t backMan) p = Some absMan ->
  In p (places tp t) ->
  In t' (place_terms t tp p) ->
  manifest_support_term absMan t'.
Proof.

  induction t; intuition.
  - repeat (try break_match; 
      unfold asp_manifest_generator, manifest_update_env, knowsof_manifest_update,
        aspid_manifest_update, update_manifest_policy_targ, pubkey_manifest_update in *;
      subst; simpl in *; intuition; eauto; try congruence;
      repeat find_rewrite;
      repeat find_injection;
      simpl in * );
    try (rewrite mapC_get_works in *; simpl in *; repeat find_injection; simpl in *; intuition; eauto).


  - (* at case *)
  ff.

  ff.
  +
    door; try solve_by_inversion.
    subst.
    ff.
    unfold at_manifest_generator in *.
    ff.
    unfold manifest_update_env in *.
    ff.
    ++
      unfold knowsof_manifest_update in *.
      ff.
      subst.
      assert (tp = p0).
      {
        eapply eqb_eq_plc; eauto.
      }
      subst.

      pose (manifest_generator_cumul' t p 
              (map_set backMan p0
              {|
                my_abstract_plc := my_abstract_plc;
                asps := asps;
                appraisal_asps := appraisal_asps;
                uuidPlcs := p :: uuidPlcs;
                pubKeyPlcs := pubKeyPlcs;
                targetPlcs := targetPlcs;
                policy := policy
              |})).

    eapply fdsa; eauto.
    simpl.
    eauto.

    ++
    assert (tp = p0).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.


    pose (manifest_generator_cumul' t p 
            ((map_set backMan p0
              {|
                my_abstract_plc := empty_Manifest_Plc;
                asps := [];
                appraisal_asps := [];
                uuidPlcs := [p];
                pubKeyPlcs := [];
                targetPlcs := [];
                policy := empty_PolicyT
              |}))).

    eapply fdsa; eauto.
    simpl.
    eauto.
  +
    door; eauto.
    subst.
    rewrite eqb_plc_refl in *.
    solve_by_inversion.

  - (* lseq case *)

  ff.
  ff.
  +
  door; try solve_by_inversion.
  subst.
  ff.
  assert (tp = p).
  {
    eapply eqb_eq_plc; eauto.
  }
  subst.



  split.
    ++

    find_apply_lem_hyp asdf_easy.
    destruct_conjs.

    eapply manifest_supports_term_sub.
    eassumption.


    eapply IHt1.
    eassumption.
    eauto.
    apply top_plc_refl.

  ++
  eapply IHt2.
  eassumption.
  eauto.
  apply top_plc_refl.


  + (* tp <> p *)
    destruct H0.
    ++
      subst.
      rewrite eqb_plc_refl in *.
      solve_by_inversion.
    ++
      assert ((In t' (place_terms t1 tp p)) \/ (In t' (place_terms t2 tp p))).
      {
        eapply in_app_or; eauto.
      }
      clear H1.

      destruct H2.
      +++ (* In t' (place_terms t1 tp p) *)
        assert (In p (places tp t1)).
        {
          apply in_plc_term.
          eapply in_not_nil.
          eassumption.
        }
          find_apply_lem_hyp asdf.
          ++++
            destruct_conjs.
            eapply manifest_supports_term_sub.
            eassumption.
            eapply IHt1.
            eassumption.
            eauto.
            eassumption.

          ++++
            right.
            unfold places in *.
            invc H2.
            +++++
              rewrite eqb_plc_refl in Heqb.
              solve_by_inversion.
            +++++
              eauto.
      +++ (* In t' (place_terms t2 tp p) *)
        simpl.

        assert (In p (places tp t2)).
      {
        apply in_plc_term.
        eapply in_not_nil; eauto.
      }

        eapply IHt2.
        ++++
          eassumption.
        ++++
          right.
          unfold places in H2.
          eauto.
          invc H2.
            +++++
              rewrite eqb_plc_refl in *.
              solve_by_inversion.
            +++++
              eassumption.
          ++++
            eassumption.

  - (* bseq case*) 

  ff.
  ff.
  +
  door; try solve_by_inversion.
  subst.
  ff.
  assert (tp = p).
  {
    eapply eqb_eq_plc; eauto.
  }
  subst.

  split.
    ++
      find_apply_lem_hyp asdf_easy.
      destruct_conjs.
  
      eapply manifest_supports_term_sub.
      eassumption.
  
  
      eapply IHt1.
      eassumption.
      eauto.
      apply top_plc_refl.

    ++
      eapply IHt2.
      eassumption.
      eauto.
      apply top_plc_refl.

  + (* tp <> p *)
    destruct H0.
    ++
      subst.
      rewrite eqb_plc_refl in *.
      solve_by_inversion.
    ++
      assert ((In t' (place_terms t1 tp p)) \/ (In t' (place_terms t2 tp p))).
      {
        eapply in_app_or; eauto.
      }
      clear H1.
    
      destruct H2.
      +++ (* In t' (place_terms t1 tp p) *)
        assert (In p (places tp t1)).
        {
          apply in_plc_term.
          eapply in_not_nil.
          eassumption.
        }
          find_apply_lem_hyp asdf.
          ++++
            destruct_conjs.
        
            eapply manifest_supports_term_sub.
            eassumption.
            eapply IHt1.
            eassumption.
            eauto.
            eassumption.
      
          ++++
            right.
            unfold places in *.
            invc H2.
            +++++
              rewrite eqb_plc_refl in Heqb.
              solve_by_inversion.
            +++++
              eauto.
      +++ (* In t' (place_terms t2 tp p) *)
        simpl.
    
        assert (In p (places tp t2)).
      {
        apply in_plc_term.
        eapply in_not_nil; eauto.
      }
    
        eapply IHt2.
        ++++
          eassumption.
        ++++
          right.
          unfold places in H2.
          eauto.
          invc H2.
          +++++
            rewrite eqb_plc_refl in *.
            solve_by_inversion.
          +++++
            eassumption.
        ++++
          eassumption.


  - (* bpar case*) 

  ff.
  ff.
  +
  door; try solve_by_inversion.
  subst.
  ff.
  assert (tp = p).
  {
    eapply eqb_eq_plc; eauto.
  }
  subst.

  split.
    ++
      find_apply_lem_hyp asdf_easy.
      destruct_conjs.
  
      eapply manifest_supports_term_sub.
      eassumption.
  
  
      eapply IHt1.
      eassumption.
      eauto.
      apply top_plc_refl.

    ++
      eapply IHt2.
      eassumption.
      eauto.
      apply top_plc_refl.

  + (* tp <> p *)
    destruct H0.
    ++
      subst.
      rewrite eqb_plc_refl in *.
      solve_by_inversion.
    ++
      assert ((In t' (place_terms t1 tp p)) \/ (In t' (place_terms t2 tp p))).
      {
        eapply in_app_or; eauto.
      }
      clear H1.
    
      destruct H2.
      +++ (* In t' (place_terms t1 tp p) *)
        assert (In p (places tp t1)).
        {
          apply in_plc_term.
          eapply in_not_nil.
          eassumption.
        }
          find_apply_lem_hyp asdf.
          ++++
            destruct_conjs.
        
            eapply manifest_supports_term_sub.
            eassumption.
            eapply IHt1.
            eassumption.
            eauto.
            eassumption.
      
          ++++
            right.
            unfold places in *.
            invc H2.
            +++++
              rewrite eqb_plc_refl in Heqb.
              solve_by_inversion.
            +++++
              eauto.
      +++ (* In t' (place_terms t2 tp p) *)
        simpl.
    
        assert (In p (places tp t2)).
      {
        apply in_plc_term.
        eapply in_not_nil; eauto.
      }
    
        eapply IHt2.
        ++++
          eassumption.
        ++++
          right.
          unfold places in H2.
          eauto.
          invc H2.
          +++++
            rewrite eqb_plc_refl in *.
            solve_by_inversion.
          +++++
            eassumption.
        ++++
          eassumption.
Qed.

Theorem manifest_generator_compiler_soundness_distributed : forall t tp p absMan amLib amConf,
  map_get (manifest_generator t tp) p = Some absMan ->
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  forall st,

  st.(st_AM_config) = amConf ->

  (*
    (* Note, this should be trivial typically as amConf = st.(st_AM_config) and refl works *)
    supports_am amConf (st.(st_AM_config)) ->  

    *)

    (  forall t', 
         In t' (place_terms t tp p) -> 
         st.(st_pl) = p -> 
        
         exists st', 
        
        build_cvm (copland_compile t') st = (resultC tt, st') \/
        build_cvm (copland_compile t') st = (errC (dispatch_error Runtime), st')
    ).
Proof.
  intros.
  assert (supports_am amConf (st.(st_AM_config))) by ff.
  assert (In p (places tp t)) by 
            (eapply has_manifest_env_places_env_has_manifest; eauto).
  eapply well_formed_am_config_impl_executable.
  - unfold manifest_generator, e_empty in *; simpl in *.
    eapply manifest_support_am_config_impl_am_config.
    * eapply manifest_support_am_config_compiler; eauto.
    * (* NOTE: This is the important one, substitute proof of any manifest here *)
      eapply man_gen_old_always_supports.
      eassumption.
      door.
      +
        subst.
        unfold places.
        left.
        eauto.
      +
        unfold places.
        right.
        eauto.
      +
        subst.
        eassumption.
  -
    rewrite H1; eauto. 
  Unshelve. eapply min_id_type.
Qed.
