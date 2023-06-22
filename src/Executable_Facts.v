Require Import Term_Defs_Core Manifest Manifest_Generator Manifest_Generator_Facts Executable_Defs_Prop.

Require Import List.
Import ListNotations.


Definition Environment := Plc -> option Manifest.


(********************
  *   EXECUTABLE 
  ********************)

(** Static guarentee that states: 
  * Is term [t] exectuable on the    
  * attestation manager named [k] in
  * environment [e]?  
  * Are ASPs available at the right attesation managers
  * and are necessary communications allowed?
  *)

Print Manifest. 
Print Environment.

Definition canRunAsp_Env (k:Plc) (e:Environment) (a: ASP_ID) : Prop := 
  match (e k) with 
  | None => False
  | Some m => In a m.(asps)
  end.
  
Print EnvironmentM.
(*  Maps.MapC Plc Manifest *)
Print knowsOf_Manifest.

Definition knowsOf_Env (k:Plc)(e:Environment)(p:Plc):Prop :=
  match (e k) with
  | None => False
  | Some m => In p m.(uuidPlcs)
  end.

Fixpoint executable_static (t:Term) (k:Plc) (e:Environment) : Prop := 
  match t with
    | asp (ASPC _ _ (asp_paramsC asp_id _ _ _))  => canRunAsp_Env k e asp_id
    | asp _ => True
    | att p t => knowsOf_Env k e p -> executable_static t k e
    | lseq t1 t2 => executable_static t1 k e /\ executable_static t2 k e
    | bseq _ t1 t2 => executable_static t1 k e /\ executable_static t2 k e
    | bpar _ t1 t2 => executable_static t1 k e /\ executable_static t2 k e
  end.

Definition envs_eq_at (e:Environment) (em:EnvironmentM) (ps:list Plc) : Prop := 
    forall p, 
        In p ps ->
        e p = Maps.map_get em p.


(* Proof that the dynamic notion of executability respects the static notion of executability. *)
Theorem static_executability_implies_distributed : 
    forall t p e em,
      envs_eq_at e em (places p t) ->
      executable_static t p e -> 
      distributed_executability t p em.
Proof.
Abort.