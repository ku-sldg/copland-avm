Require Import Term_Defs_Core Manifest_Admits Manifest Params_Admits EnvironmentM.

Require Import Eqb_Evidence.
Require Import List.
Import ListNotations.

Definition can_measure_target_prop (m : Manifest) (pol:PolicyT) (tplc:Plc) (targid:TARG_ID) : Prop
  := In_set tplc m.(targetPlcs).

Definition canRunAsp_Manifest (m:Manifest)(params:ASP_PARAMS) : Prop :=
  match params with
  | asp_paramsC aspid aspargs targplc targid =>
    let '{| asps := aspsM; uuidPlcs := knowsOfM; pubKeyPlcs := _;
            policy := policyM |} := m in
    In_set aspid aspsM /\
    can_measure_target_prop m policyM targplc targid 
  end.

Definition canRun_aspid (m:Manifest) (i:ASP_ID):Prop :=
  In_set i m.(asps).

Definition knowsOf_Manifest (e:Manifest)(p:Plc) : Prop :=
  In_set p e.(uuidPlcs).

Definition knowsPub_Manifest (e:Manifest)(p:Plc): Prop :=
  In_set p e.(pubKeyPlcs).

Fixpoint executable_local (t:Term) (e:Manifest) : Prop :=
  match t with
  | asp (ASPC _ _ params)  => canRunAsp_Manifest e params
  | asp (ENC p) => knowsPub_Manifest e p
  | asp SIG => canRun_aspid e (sig_aspid)
  | asp HSH => canRun_aspid e (hsh_aspid)
  | asp _ => True
  | att p t => knowsOf_Manifest e p (* -> executable t k e *)
  | lseq t1 t2 => executable_local t1 e /\ executable_local t2 e
  | bseq _ t1 t2 => executable_local t1 e /\ executable_local t2 e
  | bpar _ t1 t2 => executable_local t1 e /\ executable_local t2 e
  end.

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

  Fixpoint place_terms (t:Term) (tp:Plc) (p:Plc) : list Term := 
    if(eqb_plc tp p)
    then [t]
    else (
      match t with 
      | asp a => []
      | att q t' => place_terms t' q p (* if (eqb_plc p q) then ([t'] ++ (place_terms t' q p)) else (place_terms t' q p) *)
      | lseq t1 t2 => (place_terms t1 tp p) ++ (place_terms t2 tp p)
      | bseq _ t1 t2 => (place_terms t1 tp p) ++ (place_terms t2 tp p)
      | bpar _ t1 t2 => (place_terms t1 tp p) ++ (place_terms t2 tp p)
      end).



  Definition distributed_executability 
  (t:Term) (tp:Plc) (env_map:EnvironmentM) : Prop := 
  forall p t', 
    In p (places tp t) /\ 
    In t' (place_terms t tp p) ->
    (exists (m:Manifest),
      Maps.map_get env_map p = Some m /\
      executable_local t' m).

Definition canRunAsp_Env (k:Plc) (em:EnvironmentM) (ps: ASP_PARAMS) : Prop := 
match (Maps.map_get em k) with 
| None => False 
| Some m => canRunAsp_Manifest m ps
end. 
  
Definition canRun_aspid_Env (k:Plc) (em:EnvironmentM) (i:ASP_ID) : Prop :=
  match (Maps.map_get em k) with 
  | None => False 
  | Some m => canRun_aspid m i
  end. 

Definition knowsOf_Env (k:Plc)(em:EnvironmentM)(p:Plc):Prop :=
  match (Maps.map_get em k) with 
  | None => False
  | Some m => In_set p m.(uuidPlcs)
  end.

Definition knowsPub_Env (k:Plc)(em:EnvironmentM)(p:Plc):Prop :=
    match (Maps.map_get em k) with 
    | None => False
    | Some m => In_set p m.(pubKeyPlcs)
    end.


(**************************
  *   GLOBAL EXECUTABILITY 
  *************************)

(** Static guarentee that states: 
  * Is term [t] exectuable on the    
  * attestation manager named [k] in
  * environment [e]?  
  * Are ASP resources available at the right attesation managers
  * and are necessary communications allowed?
  *)
Fixpoint executable_global (t:Term) (k:Plc) (em:EnvironmentM) : Prop := 
  match t with
    | asp (ASPC _ _ ps)  => canRunAsp_Env k em ps
    | asp SIG => canRun_aspid_Env k em (sig_aspid)
    | asp HSH => canRun_aspid_Env k em (hsh_aspid)
    | asp (ENC p) => knowsPub_Env k em p
    | asp _ => exists m, Maps.map_get em k = Some m(* asp _ => True *)
    | att p t1 => knowsOf_Env k em p /\ executable_global t1 p em
    | lseq t1 t2 => executable_global t1 k em /\ executable_global t2 k em
    | bseq _ t1 t2 => executable_global t1 k em /\ executable_global t2 k em
    | bpar _ t1 t2 => executable_global t1 k em /\ executable_global t2 k em
  end.

(* A dynamic version of executabiilty. 
   At runtime, we cannot know if an att term can be executed on a remote place. *)
Fixpoint executable_dynamic (t:Term) (k:Plc) (em:EnvironmentM) : Prop := 
  match t with
    | asp (ASPC _ _ ps)  => canRunAsp_Env k em ps
    | asp SIG => canRun_aspid_Env k em (sig_aspid)
    | asp HSH => canRun_aspid_Env k em (hsh_aspid)
    | asp (ENC p) => knowsPub_Env k em p
    | asp _ =>  exists m, Maps.map_get em k = Some m (* True *)
    | att p t => knowsOf_Env k em p
    | lseq t1 t2 => executable_dynamic t1 k em /\ executable_dynamic t2 k em
    | bseq _ t1 t2 => executable_dynamic t1 k em /\ executable_dynamic t2 k em
    | bpar _ t1 t2 => executable_dynamic t1 k em /\ executable_dynamic t2 k em
  end.
