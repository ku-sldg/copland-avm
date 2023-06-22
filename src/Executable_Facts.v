Require Import Term_Defs_Core Manifest Manifest_Generator Manifest_Generator_Facts.

Require Import List.
Import ListNotations.


Definition Environment := Plc -> option Manifest.

Definition executable_static (t:Term) (p:Plc) (e:Environment) : Prop.
Admitted.

Definition envs_eq_at (e:Environment) (em:EnvironmentM) (ps:list Plc) : Prop := 
    forall p, 
        In p ps ->
        e p = Maps.map_get em p.


Theorem static_executability_implies_distributed : 
    forall t p e em,
      envs_eq_at e em (places p t) ->
      executable_static t p e -> 
      distributed_executability t p em.
Proof.
Abort.