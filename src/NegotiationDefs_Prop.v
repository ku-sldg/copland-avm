Require Import Term_Defs_Core NegotiationDefs Manifest.

Require Import List.
Import ListNotations.


(* Within the enviornment e, does the AM at place k have ASP a? *)
Definition hasASPe(k:Plc)(e:Environment)(a:ASP_ID):Prop :=
  match (e k) with
  | None => False
  | Some m => In a m.(asps)
  end.

Definition canRunAsp_Manifest(* (k:Plc) *) (m:Manifest)(params:ASP_PARAMS):Prop :=
  match params with
  | asp_paramsC aspid aspargs targplc targid =>
    let '{| asps := aspsM; uuidPlcs := knowsOfM; pubKeyPlcs := _;
            policy := policyM (*; ac_policy := ac_policyM *) |} := m in
    In aspid aspsM /\
    can_measure_target policyM(*ac_policyM*) targplc targid = true 
  end.
  
(* Within the system s, does the AM located at place k have ASP a? *)
Fixpoint hasASPs(k:Plc)(s:System)(a:ASP_ID):Prop :=
  match s with
  | [] => False
  | s1 :: s2 => (hasASPe k s1 a) \/ (hasASPs k s2 a)
  end.

(** Determine if manifest [k] from [e] knows how to communicate from [k]
  * to [p]
  *)
Definition knowsOfe(k:Plc)(e:Environment)(p:Plc):Prop :=
  match (e k) with
  | None => False
  | Some m => In p m.(uuidPlcs)
  end.

Definition knowsOf_Manifest(*(k:Plc)*)(e:Manifest)(p:Plc):Prop :=
  In p e.(uuidPlcs).
  (*
  match (e k) with
  | None => False
  | Some m => In p m.(knowsOf)
  end.
   *)

(** Determine if place [k] within the system [s] knows 
  * how to communicate with [p]
  *)
Fixpoint knowsOfs(k:Plc)(s:System)(p:Plc):Prop :=
  match s with
  | [] => False
  | s1 :: s2 => (knowsOfe k s1 p) \/ (knowsOfs k s2 p)
  end.

(** Determine if place [k] within the environment [e]  
  * depends on place [p] (the context relation)
  *)
Definition dependsOne (k:Plc)(e:Environment)(p:Plc):Prop :=
  match (e k) with
  | None => False
  | Some m => In p m.(pubKeyPlcs)
  end.

(** Determine if place [k] within the system [s]  
  * depends on place [p] (the context relation)
  *)
Fixpoint dependsOns (k:Plc)(s:System)(p:Plc):Prop :=
  match s with
  | [] => False
  | s1 :: s2 => (dependsOne k s1 p) \/ (dependsOns k s2 p)
  end.

Fixpoint executable(t:Term)(*(k:Plc)*)(e:Manifest):Prop :=
  match t with
  | asp (ASPC _ _ params)  => canRunAsp_Manifest e params
  | asp _ => True
  | att p t => knowsOf_Manifest e p (* -> executable t k e *)
  | lseq t1 t2 => executable t1 e /\ executable t2 e
  | bseq _ t1 t2 => executable t1 e /\ executable t2 e
  | bpar _ t1 t2 => executable t1 e /\ executable t2 e
  end.
