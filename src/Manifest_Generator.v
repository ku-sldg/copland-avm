Require Import Term_Defs_Core Params_Admits Manifest Executable_Dec
               Example_Phrases_Admits Example_Phrases Eqb_Evidence.

Require Import EqClass Maps.

Require Import List.
Import ListNotations.

Definition EnvironmentM : Type := MapC Plc Manifest.

Definition e_empty : EnvironmentM := [].

Definition aspid_manifest_update (i:ASP_ID) (m:Manifest) : Manifest := 
  let '{| my_abstract_plc := oldPlc;
          asps := oldasps; 
          uuidPlcs := oldKnowsOf; 
          pubKeyPlcs := oldContext; 
          policy := oldPolicy (*; 
          ac_policy := oldAcPol*) |} := m in
  (Build_Manifest oldPlc (i::oldasps) oldKnowsOf oldContext oldPolicy (*oldAcPol*)).

Definition knowsof_manifest_update (toPlc:Plc) (m:Manifest) : Manifest := 
    let '{| my_abstract_plc := oldPlc;
            asps := oldasps; 
            uuidPlcs := oldKnowsOf; 
            pubKeyPlcs := oldContext; 
            policy := oldPolicy (*; 
            ac_policy := oldAcPol*) |} := m in
    (Build_Manifest oldPlc oldasps (toPlc::oldKnowsOf) oldContext oldPolicy (*oldAcPol*)).

Definition knowsof_myPlc_manifest_update (m:Manifest) : Manifest :=
  let '{| my_abstract_plc := oldPlc;
          asps := oldasps; 
          uuidPlcs := oldKnowsOf; 
          pubKeyPlcs := oldContext; 
          policy := oldPolicy (*; 
          ac_policy := oldAcPol*) |} := m in
    (Build_Manifest oldPlc oldasps (oldPlc::oldKnowsOf) oldContext oldPolicy (*oldAcPol*)).

Definition myPlc_manifest_update (p:Plc) (m:Manifest) : Manifest := 
      let '{| my_abstract_plc := _;
              asps := oldasps; 
              uuidPlcs := oldKnowsOf; 
              pubKeyPlcs := oldContext; 
              policy := oldPolicy (*; 
              ac_policy := oldAcPol*) |} := m in
      (Build_Manifest p oldasps oldKnowsOf oldContext oldPolicy (*oldAcPol*)).

Definition pubkeys_manifest_update (ps:list Plc) (m:Manifest) : Manifest := 
        let '{| my_abstract_plc := oldMyPlc;
                asps := oldasps; 
                uuidPlcs := oldKnowsOf; 
                pubKeyPlcs := _; 
                policy := oldPolicy (*; 
                ac_policy := oldAcPol*) |} := m in
        (Build_Manifest oldMyPlc oldasps oldKnowsOf ps oldPolicy (*oldAcPol*)).

Definition asp_manifest_update (a:ASP) (m:Manifest) : Manifest :=
  match a with 
  | ASPC _ _ params => 
      match params with
      | asp_paramsC i _ targp targid => 
          aspid_manifest_update i m
      end
  | SIG => aspid_manifest_update (sig_aspid) m
  | _ => m 
  end.
        
Definition asp_manifest_generator (a:ASP) (p:Plc) (e:EnvironmentM) : EnvironmentM :=
  match (map_get e p) with
  | Some m => 
    let m' := asp_manifest_update a m in 
      map_set e p m'
  | _ => 
    let m' := asp_manifest_update a empty_Manifest in 
      map_set e p m'
  end.

  Definition plc_manifest_generator (fromPlc:Plc) (toPlc:Plc) (e:EnvironmentM) : EnvironmentM :=
    match (map_get e fromPlc) with
    | Some m => 
      let m' := knowsof_manifest_update toPlc m in 
        map_set e fromPlc m'
    | _ => 
      let m' := knowsof_manifest_update toPlc empty_Manifest in 
        map_set e fromPlc m'
    end.


Fixpoint manifest_generator' (p:Plc) (t:Term) (e:EnvironmentM) : EnvironmentM :=
  match t with
  | asp a => asp_manifest_generator a p e
  | att q t' => 
      let e' := plc_manifest_generator p q e in 
        manifest_generator' q t' e'
  | lseq t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 e)
  | bseq _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 e)
  | bpar _ t1 t2 => manifest_generator' p t2 (manifest_generator' p t1 e)
  end.


(*
Check List.fold_left.
  (*
  fold_left
	 : forall A B : Type, (A -> B -> A) -> list B -> A -> A
  *)
Check List.fold_right.
  (*
    fold_right
	 : forall A B : Type, (B -> A -> A) -> A -> list B -> A
   *)

Check List.map.
   (* map
    : forall A B : Type, (A -> B) -> list A -> list B
    *)

Check List.remove.
Check List.count_occ.


Definition plc_list : list Plc := [P0; P1; P2].

Compute (List.count_occ eq_plc_dec plc_list P1 ).
Check Nat.leb.
Check negb.
*)

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


Fixpoint places' (t:Term) (ls:list Plc) : list Plc :=
  match t with
  | asp _ => ls 
  | att q t' => (q :: (places' t' ls))
  | lseq t1 t2 => places' t2 (places' t1 ls)
  | bseq _ t1 t2 => places' t2 (places' t1 ls)
  | bpar _ t1 t2 => places' t2 (places' t1 ls)
  end.

Definition places (p:Plc) (t:Term): list Plc := 
  p :: (places' t []).

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
  List.map (pubkeys_manifest_update (places_terms ts p)) ms'.

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

Definition man_gen_run_attify (ls:list (Term*Plc)) : list Manifest := 
  let plc_default := default_place in 
  let ts := attify_terms ls in 
    demo_man_gen_run ts plc_default.



(*

Definition man_gen_res : Manifest := (fromSome (map_get (man_gen_run [cert_style] P0) P1) empty_Manifest).
Compute man_gen_res.

Compute man_gen_run.

Example mytest : (man_gen_run [cert_style] P0 = map_empty).
Proof.
  cbv.
  break_let.
  assert (eqb P2 P1 = false).
  admit.
  find_rewrite.
  simpl.
  pose proof (eqb_leibniz P2 P2). intuition.
  find_rewrite.
  Abort.

Eval cbv iota in (fromSome (map_get (man_gen_run [cert_style] P0) P1) empty_Manifest).

*)
