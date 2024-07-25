(* Implementation of the Manifest Generator.
    Includes separate (but similar) versions of the generator for both 
    attestation (manifest_generator) and appraisal (manifest_generator_app) scenarios. *)

Require Import Term_Defs_Core Params_Admits Manifest Eqb_Evidence
               Manifest_Generator_Helpers.

Require Import ResultT String EqClass Maps StructTactics.

Require Import Manifest_Union.

Require Export EnvironmentM Manifest_Set.

Require Import List.
Import ListNotations.

Definition aspid_manifest_update (i:ASP_ID) (m:Manifest) : Manifest := 
  let '{| asps := oldasps; 
          ASP_Compat_Map := oldCompatMap;
          ASP_Mapping := oldFSMap;
          man_policy := oldPolicy |} := m in
  (Build_Manifest (manset_add i oldasps) oldCompatMap oldFSMap oldPolicy).

Definition add_compat_map_manifest (m : Manifest) (cm : ASP_Compat_MapT) : Manifest :=
  let '{| asps := oldasps; 
          ASP_Compat_Map := oldCompatMap;
          ASP_Mapping := oldFSMap;
          man_policy := oldPolicy |} := m in
  (Build_Manifest oldasps cm oldFSMap oldPolicy).
  
Definition asp_manifest_update (a:ASP) (m:Manifest) : Manifest :=
  match a with 
  | ASPC _ _ params => 
      match params with
      | asp_paramsC i _ _ _ => aspid_manifest_update i m
      end
  | SIG => aspid_manifest_update (sig_aspid) m
  | HSH => aspid_manifest_update (hsh_aspid) m
  | ENC p => aspid_manifest_update (enc_aspid) m
  | NULL => m 
  | CPY => m
  end.

Definition manifest_update_env_res (p:Plc) (e:EnvironmentM) 
            (f:Manifest -> ResultT Manifest string) 
            : ResultT EnvironmentM string := 
  let m := 
    match (map_get e p) with
    | Some mm => mm
    | None => empty_Manifest
    end 
  in
  match (f m) with
  | resultC m' => resultC (map_set e p m')
  | errC e => errC e
  end.
  
Definition manifest_update_env (p:Plc) (e:EnvironmentM) 
            (f:Manifest -> Manifest) : EnvironmentM := 
  let m := 
    match (map_get e p) with
    | Some mm => mm
    | None => empty_Manifest
    end in
  let m' := (f m) in 
    map_set e p m'.

Fixpoint manifest_generator' (p:Plc) (t:Term) (e:EnvironmentM) : EnvironmentM :=
  match t with
  | asp a => manifest_update_env p e (asp_manifest_update a)
  | att q t' => 
    manifest_generator' q t' 
      (* Have to add an empty for self just to be safe *)
      (manifest_update_env p e (fun m => manifest_union_asps m empty_Manifest))
  | lseq t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 e)
  | bseq _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 e)
  | bpar _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 e)
  end.

Definition manifest_generator_terms (p:Plc) (ts:list Term) : EnvironmentM :=
  fold_right (manifest_generator' p) e_empty ts.

Definition manifest_generator (t:Term) (p:Plc) : EnvironmentM :=
  manifest_generator' p t e_empty.

Lemma manifest_generator_never_empty : forall t p e,
  manifest_generator' p t e <> nil.
Proof.
  induction t; simpl in *; intuition; eauto.
  - destruct a; unfold manifest_update_env, asp_manifest_update in *; 
    repeat break_match; destruct e; simpl in *; try congruence;
    try (destruct p0; break_if; congruence);
    try (destruct p1; break_if; congruence).
Qed.

Definition environment_to_manifest_list (e:EnvironmentM) : list Manifest :=
  map_vals e.

Fixpoint manifest_generator_app' (comp_map : ASP_Compat_MapT) 
    (et:Evidence) (m:Manifest) : ResultT Manifest string :=
  match et with 
  | mt => resultC m 
  | nn _ => resultC m (* TODO: account for nonce handling here? *)
  | uu p fwd ps e' => 
    match fwd with 
    | (EXTD n) => 
      match ps with 
      | asp_paramsC a _ targ _ =>
        match (map_get comp_map a) with
        | Some a' => 
            manifest_generator_app' comp_map e' (aspid_manifest_update a' m)
        | None => errC "Compatible Appraisal ASP not found in AM Library"%string
        end
      end 
    | ENCR => 
      match ps with 
      | asp_paramsC a _ p' _ =>
        match (map_get comp_map a) with
        | Some a' => 
            manifest_generator_app' comp_map e' (aspid_manifest_update a' m)
        | None => errC "Compatible Appraisal ASP not found in AM Library"%string
        end
      end
    | KEEP => 
      let '(asp_paramsC a _ _ _) := ps in
      match (map_get comp_map a) with
      | Some a' => 
          manifest_generator_app' comp_map e' (aspid_manifest_update a' m)
      | None => errC "Compatible Appraisal ASP not found in AM Library"%string
      end
    | _ => resultC m
    end
  | ss e1 e2 => 
    match (manifest_generator_app' comp_map e1 m) with
    | resultC m' => manifest_generator_app' comp_map e2 m'
    | errC e => errC e
    end
  end.

Import ResultNotation.
Definition manifest_generator_app (comp_map : ASP_Compat_MapT) 
    (et:Evidence) (p:Plc) : ResultT EnvironmentM string := 
  env <- manifest_update_env_res p e_empty (manifest_generator_app' comp_map et) ;;
  result_map 
    (fun '(p,m) => resultC (p, add_compat_map_manifest m comp_map)) 
    env.
