Require Import Term_Defs_Core Manifest_Admits Manifest Params_Admits.

Require Import List.
Import ListNotations.

Definition can_measure_target_prop (pol:PolicyT) (tplc:Plc) (targid:TARG_ID) : Prop
  := True.

Definition canRunAsp_Manifest(* (k:Plc) *) (m:Manifest)(params:ASP_PARAMS):Prop :=
  match params with
  | asp_paramsC aspid aspargs targplc targid =>
    let '{| asps := aspsM; uuidPlcs := knowsOfM; pubKeyPlcs := _;
            policy := policyM (*; ac_policy := ac_policyM *) |} := m in
    In aspid aspsM /\
    can_measure_target_prop policyM(*ac_policyM*) targplc targid 
  end.

Definition canRun_aspid (m:Manifest) (i:ASP_ID):Prop :=
  In i m.(asps).

Definition knowsOf_Manifest(*(k:Plc)*)(e:Manifest)(p:Plc):Prop :=
  In p e.(uuidPlcs).

Definition knowsPub_Manifest (e:Manifest)(p:Plc): Prop :=
  In p e.(pubKeyPlcs).

Fixpoint executable(t:Term)(*(k:Plc)*)(e:Manifest):Prop :=
  match t with
  | asp (ASPC _ _ params)  => canRunAsp_Manifest e params
  | asp (ENC p) => knowsPub_Manifest e p
  | asp SIG => canRun_aspid e (sig_aspid)
  | asp HSH => canRun_aspid e (hsh_aspid)
  | asp _ => True
  | att p t => knowsOf_Manifest e p (* -> executable t k e *)
  | lseq t1 t2 => executable t1 e /\ executable t2 e
  | bseq _ t1 t2 => executable t1 e /\ executable t2 e
  | bpar _ t1 t2 => executable t1 e /\ executable t2 e
  end.
