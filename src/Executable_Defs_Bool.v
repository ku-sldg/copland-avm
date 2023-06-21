Require Import Term_Defs_Core Manifest_Admits Manifest EqClass Eqb_Evidence (*NegotiationDefs*).

Require Import Lists.List.
Import ListNotations.


Definition can_measure_target (pol:PolicyT) (tplc:Plc) (targid:TARG_ID) : bool 
  := true.

Definition canRunAsp_ManifestB(* (k:Plc) *) (m:Manifest)(params:ASP_PARAMS):bool :=
  match params with
  | asp_paramsC aspid aspargs targplc targid =>
        let '{| asps := aspsM; uuidPlcs := knowsOfM; pubKeyPlcs := _;
                policy := policyM (* ; ac_policy := ac_policyM*) |} := m in
        (existsb (eqb aspid) aspsM) &&
        (can_measure_target policyM(*ac_policyM*) targplc targid)
        
  end.

Definition knowsOf_ManifestB(*(k:Plc)*)(e:Manifest)(p:Plc):bool :=
  existsb (eqb_plc p) e.(uuidPlcs).


Fixpoint executableB(t:Term)(*(k:Plc)*)(e:Manifest):bool :=
  match t with
  | asp (ASPC _ _ params)  => canRunAsp_ManifestB e params
  | asp _ => true
  | att p t => knowsOf_ManifestB e p (* -> executableB t k e *)
  | lseq t1 t2 => executableB t1 e && executableB t2 e
  | bseq _ t1 t2 => executableB t1 e && executableB t2 e
  | bpar _ t1 t2 => executableB t1 e && executableB t2 e
  end.
