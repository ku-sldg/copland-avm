(* Implementation of the Manifest Generator.
    Includes separate (but similar) versions of the generator for both 
    attestation (manifest_generator) and appraisal (manifest_generator_app) scenarios. *)

Require Import Term_Defs_Core Params_Admits Manifest Eqb_Evidence
               Manifest_Generator_Helpers.

Require Import EqClass Maps StructTactics.

Require Import Manifest_Union.

Require Export EnvironmentM Manifest_Set.

Require Import List.
Import ListNotations.

Definition aspid_manifest_update (i:ASP_ID) (m:Manifest) : Manifest := 
  let '{| my_abstract_plc := oldPlc;
          asps := oldasps; 
          appraisal_asps := old_app_asps;
          uuidPlcs := oldKnowsOf; 
          pubKeyPlcs := oldContext; 
          targetPlcs := oldTargets ;
          policy := oldPolicy |} := m in
  (Build_Manifest oldPlc (manset_add i oldasps) old_app_asps oldKnowsOf oldContext oldTargets oldPolicy).

Definition knowsof_manifest_update (toPlc:Plc) (m:Manifest) : Manifest := 
    let '{| my_abstract_plc := oldPlc;
            asps := oldasps; 
            appraisal_asps := old_app_asps;
            uuidPlcs := oldKnowsOf; 
            pubKeyPlcs := oldContext; 
            targetPlcs := oldTargets ;
            policy := oldPolicy |} := m in
    (Build_Manifest oldPlc oldasps old_app_asps (manset_add toPlc oldKnowsOf) oldContext oldTargets oldPolicy).

Definition knowsof_myPlc_manifest_update (m:Manifest) : Manifest :=
  knowsof_manifest_update (my_abstract_plc m) m.

Definition myPlc_manifest_update (p:Plc) (m:Manifest) : Manifest := 
  let '{| my_abstract_plc := _;
          asps := oldasps; 
          appraisal_asps := old_app_asps;
          uuidPlcs := oldKnowsOf; 
          pubKeyPlcs := oldContext; 
          targetPlcs := oldTargets; 
          policy := oldPolicy |} := m in
  (Build_Manifest p oldasps old_app_asps oldKnowsOf oldContext oldTargets oldPolicy).

Definition pubkey_manifest_update (p:Plc) (m:Manifest) : Manifest := 
  let '{| my_abstract_plc := oldPlc;
          asps := oldasps; 
          appraisal_asps := old_app_asps;
          uuidPlcs := oldKnowsOf; 
          pubKeyPlcs := oldContext; 
          targetPlcs := oldTargets ;
          policy := oldPolicy |} := m in
  (Build_Manifest oldPlc oldasps old_app_asps oldKnowsOf (manset_add p oldContext) oldTargets oldPolicy).

Definition pubkeys_manifest_update_replace_all (ps:manifest_set Plc) (m:Manifest) : Manifest := 
        let '{| my_abstract_plc := oldMyPlc;
                asps := oldasps; 
                appraisal_asps := old_app_asps;
                uuidPlcs := oldKnowsOf; 
                pubKeyPlcs := _; 
                targetPlcs := oldTargets ;
                policy := oldPolicy |} := m in
        (Build_Manifest oldMyPlc oldasps old_app_asps oldKnowsOf ps oldTargets oldPolicy).

Definition pubkeys_manifest_update (ps:manifest_set Plc) (m:Manifest) : Manifest := 
  let '{| my_abstract_plc := oldMyPlc;
          asps := oldasps; 
          appraisal_asps := old_app_asps;
          uuidPlcs := oldKnowsOf; 
          pubKeyPlcs := oldPubs; 
          targetPlcs := oldTargets ;
          policy := oldPolicy |} := m in
  (Build_Manifest oldMyPlc oldasps old_app_asps oldKnowsOf (fold_right manset_add oldPubs ps) oldTargets oldPolicy).

Definition update_manifest_policy_targ (targp:Plc) (targid:Plc) (m:Manifest) : Manifest :=
  let '{| my_abstract_plc := oldMyPlc;
          asps := oldasps; 
          appraisal_asps := old_app_asps;
          uuidPlcs := oldKnowsOf; 
          pubKeyPlcs := oldContext ; 
          targetPlcs := oldTargets ;
          policy := oldPolicy |} := m in
  (Build_Manifest oldMyPlc oldasps old_app_asps oldKnowsOf oldContext (manset_add targp oldTargets) oldPolicy).

  
Definition asp_manifest_update (a:ASP) (m:Manifest) : Manifest :=
  match a with 
  | ASPC _ _ params => 
      match params with
      | asp_paramsC i _ targp targid => 
        let m' := update_manifest_policy_targ targp targid m in
          aspid_manifest_update i m'
      end
  | SIG => aspid_manifest_update (sig_aspid) m
  | HSH => aspid_manifest_update (hsh_aspid) m
  | ENC p => 
      let m' := pubkey_manifest_update p m in
        aspid_manifest_update (enc_aspid) m'
  | NULL => m 
  | CPY => m
  end.

  (*
Definition manifest_set_my_plc (p : Plc) (m : Manifest) : Manifest :=
  let '{| my_abstract_plc := _ ;
          asps := oldasps; 
          appraisal_asps := old_app_asps;
          uuidPlcs := oldKnowsOf; 
          pubKeyPlcs := oldContext ; 
          targetPlcs := oldTargets ;
          policy := oldPolicy |} := m in
  (Build_Manifest p oldasps old_app_asps oldKnowsOf oldContext oldTargets oldPolicy).
  *)
  
Definition manifest_update_env (p:Plc) (e:EnvironmentM) 
            (f:Manifest -> Manifest) : EnvironmentM := 
  let m := 
    match (map_get e p) with
    | Some mm => mm
    | None => (myPlc_manifest_update p empty_Manifest)
    end in

    let m' := (f m) in 
      map_set e p m'.

        
Definition asp_manifest_generator (a:ASP) (p:Plc) (e:EnvironmentM) : EnvironmentM :=
  manifest_update_env p e (asp_manifest_update a).

Definition at_manifest_generator (fromPlc:Plc) (toPlc:Plc) 
                                    (e:EnvironmentM) : EnvironmentM :=
  manifest_update_env fromPlc e (knowsof_manifest_update toPlc).


Fixpoint manifest_generator' (p:Plc) (t:Term) (e:EnvironmentM) : EnvironmentM :=
  match t with
  | asp a => asp_manifest_generator a p e
  | att q t' => 
      let e' := at_manifest_generator p q e in 
        manifest_generator' q t' e'
  | lseq t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 e)
  | bseq _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 e)
  | bpar _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 e)
  end.

Fixpoint dedup_list (ps:list Plc) : list Plc := 
  match ps with
  | [] => ps
  | (p::ps') =>
    if (eqb (List.count_occ eq_plc_dec ps' p) O)
    then (p::(dedup_list ps'))
    else dedup_list ps'
  end.

Definition manifest_generator_terms (p:Plc) (ts:list Term) : EnvironmentM :=
  fold_right (manifest_generator' p) e_empty ts.

Definition manifest_generator (t:Term) (p:Plc) : EnvironmentM :=
  manifest_generator' p t e_empty.

Lemma manifest_generator_never_empty : forall t p e,
  manifest_generator' p t e <> nil.
Proof.
  induction t; simpl in *; intuition; eauto.
  - destruct a; unfold asp_manifest_generator, 
      manifest_update_env, asp_manifest_update in *; 
    repeat break_match; destruct e; simpl in *; try congruence;
    try (destruct p0; break_if; congruence);
    try (destruct p1; break_if; congruence).
Qed.

Definition places_terms' (ts: list Term) (p:Plc) : list (list Plc) :=
  List.map (places p) ts.

Definition places_terms (ts:list Term) (p:Plc) : list Plc :=
  dedup_list (List.concat (places_terms' ts p)).

Definition fromSome{A:Type} (v:option A) (a:A) : A :=
  match v with 
  | Some v' => v'
  | _ => a 
  end.

Definition get_manifest_env_default (e:EnvironmentM) (p:Plc) : Manifest :=
  let m' := fromSome (map_get e p) empty_Manifest in
    myPlc_manifest_update p m'.

Definition get_unique_manifests_env' (ps:list Plc) (e:EnvironmentM) : list Manifest :=
  List.map (get_manifest_env_default e) ps.

Definition get_unique_manifests_env (ts: list Term) (p:Plc) (e:EnvironmentM) : list Manifest :=
  let ps := places_terms ts p in
    get_unique_manifests_env' ps e.

Definition get_final_manifests_env (ts:list Term) (p:Plc) (e:EnvironmentM) : list Manifest :=
  let ms := get_unique_manifests_env ts p e in 
  let ms' := List.map (knowsof_myPlc_manifest_update) ms in
  List.map (pubkeys_manifest_update (list_to_manset (places_terms ts p))) ms'.

Definition man_gen_run (ts:list Term) (p:Plc) : EnvironmentM := manifest_generator_terms p ts.

Definition environment_to_manifest_list (e:EnvironmentM) : list Manifest :=
  map_vals e.

Definition demo_man_gen_run (ts:list Term) (p:Plc) : list Manifest := 
  get_final_manifests_env ts p (man_gen_run ts p).

Definition attify (t:Term) (p:Plc) : Term := 
  att p t.

Definition attify_terms' (pr:(Term * Plc)) : Term := 
  match pr with 
  | (t, p) => attify t p
  end.

Definition attify_terms (ls:list (Term * Plc)) : list Term :=
  List.map attify_terms' ls.

Definition app_aspid_manifest_update (i:ASP_ID) (p:Plc) (m:Manifest) : Manifest := 
  let '{| my_abstract_plc := oldPlc;
          asps := oldasps; 
          appraisal_asps := old_app_asps;
          uuidPlcs := oldKnowsOf; 
          pubKeyPlcs := oldContext; 
          targetPlcs := oldTargets ;
          policy := oldPolicy |} := m in
  (Build_Manifest oldPlc oldasps (manset_add (i,p) old_app_asps) oldKnowsOf oldContext oldTargets oldPolicy).

Fixpoint manifest_generator_app'' (et:Evidence) (m:Manifest) : Manifest :=
  match et with 
  | mt => m 
  | nn _ => m (* TODO: account for nonce handling here? *)
  | uu p fwd ps e' => 
    match fwd with 
    | (EXTD n) => 
      match ps with 
      | asp_paramsC a _ targ _ =>
          manifest_generator_app'' e' 
            (app_aspid_manifest_update targ a m)
      end 
    | ENCR => 
      match ps with 
      | asp_paramsC _ _ p' _ =>
          manifest_generator_app'' e' 
            (pubkey_manifest_update p' m)
      end
    | KEEP => manifest_generator_app'' e' m
    | _ => m
    end
  | ss e1 e2 => 
      manifest_generator_app'' e2 (manifest_generator_app'' e1 m)
  end.

Definition manifest_generator_app' (p:Plc) (et:Evidence) (env:EnvironmentM) : EnvironmentM :=
  manifest_update_env p env (manifest_generator_app'' et).


Definition manifest_generator_app (et:Evidence) (p:Plc) : EnvironmentM := 
  manifest_generator_app' p et e_empty.