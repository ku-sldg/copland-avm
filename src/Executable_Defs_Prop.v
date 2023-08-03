Require Import Term_Defs_Core Manifest_Admits Manifest Params_Admits EnvironmentM.

Require Import List.
Import ListNotations.

Definition can_measure_target_prop (m : Manifest) (pol:PolicyT) (tplc:Plc) (targid:TARG_ID) : Prop
  := In tplc m.(targetPlcs).

Definition canRunAsp_Manifest (m:Manifest)(params:ASP_PARAMS) : Prop :=
  match params with
  | asp_paramsC aspid aspargs targplc targid =>
    let '{| asps := aspsM; uuidPlcs := knowsOfM; pubKeyPlcs := _;
            policy := policyM |} := m in
    In aspid aspsM /\
    can_measure_target_prop m policyM targplc targid 
  end.

Definition canRun_aspid (m:Manifest) (i:ASP_ID):Prop :=
  In i m.(asps).

Definition knowsOf_Manifest (e:Manifest)(p:Plc) : Prop :=
  In p e.(uuidPlcs).

Definition knowsPub_Manifest (e:Manifest)(p:Plc): Prop :=
  In p e.(pubKeyPlcs).

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
  | Some m => In p m.(uuidPlcs)
  end.

Definition knowsPub_Env (k:Plc)(em:EnvironmentM)(p:Plc):Prop :=
    match (Maps.map_get em k) with 
    | None => False
    | Some m => In p m.(pubKeyPlcs)
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
