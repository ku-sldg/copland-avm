Require Import Term_Defs_Core Manifest Manifest_Generator Manifest_Generator_Facts Executable_Defs_Prop Manifest_Admits.

Require Import List.
Import ListNotations.

(*
Definition Environment := Plc -> option Manifest.
*)


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

  (*
Print Manifest. 
Print Environment.
*)

Definition canRunAsp_Env (k:Plc) (em:EnvironmentM) (a: ASP_ID) : Prop := 
  match (Maps.map_get em k) with 
  | None => False 
  | Some m => In a m.(asps)
  end. 
  
  
Print EnvironmentM.
(*  Maps.MapC Plc Manifest *)

Print knowsOf_Manifest.

Definition knowsOf_Env (k:Plc)(em:EnvironmentM)(p:Plc):Prop :=
  match (Maps.map_get em k) with 
  | None => False
  | Some m => In p m.(uuidPlcs)
  end.

(* Statically, we have a global view so we can use the environement to reason about the system *)
Fixpoint executable_static (t:Term) (k:Plc) (em:EnvironmentM) : Prop := 
  match t with
    | asp (ASPC _ _ (asp_paramsC asp_id _ _ _))  => canRunAsp_Env k em asp_id
    | asp _ => True
    | att p t' => knowsOf_Env k em p /\ executable_static t' p em
    | lseq t1 t2 => executable_static t1 k em /\ executable_static t2 k em
    | bseq _ t1 t2 => executable_static t1 k em /\ executable_static t2 k em
    | bpar _ t1 t2 => executable_static t1 k em /\ executable_static t2 k em
  end.


(*

(* A dynamic version of executabiilty. 
   At runtime, we cannot know if an att term can be executed on a remote place. *)
Fixpoint executable_dynamic (t:Term) (k:Plc) (em:EnvironmentM) : Prop := 
  match t with
    | asp (ASPC _ _ (asp_paramsC asp_id _ _ _))  => canRunAsp_Env k em asp_id
    | asp _ => True
    | att p t => knowsOf_Env k em p
    | lseq t1 t2 => executable_dynamic t1 k em /\ executable_dynamic t2 k em
    | bseq _ t1 t2 => executable_dynamic t1 k em /\ executable_dynamic t2 k em
    | bpar _ t1 t2 => executable_dynamic t1 k em /\ executable_dynamic t2 k em
  end.



Definition envs_eq_at (e:Environment) (em:EnvironmentM) (ps:list Plc) : Prop := 
    forall p, 
        In p ps ->
        e p = Maps.map_get em p.

(* Record Manifest : Set := Build_Manifest
                            { my_abstract_plc : Plc;
                              asps : list ASP_ID;
                              uuidPlcs : list Plc;
                              pubKeyPlcs : list Plc;
                              policy : Manifest_Admits.PolicyT }.*)

(* Try to build a manifest. *)

Definition build_manifest_helper p a p1 p2 pol : Manifest := 
{|  my_abstract_plc := p ; 
    asps :=  a ;
    uuidPlcs := p1 ; 
    pubKeyPlcs := p2 ; 
    policy := pol |}. 

(* Proof that the dynamic notion of executability respects the static notion of executability. *)
Theorem static_executability_implies_distributed : 
    forall t p em,
      executable_static t p em -> 
      distributed_executability t p em.
Proof.
  intros. unfold distributed_executability. intros; subst.
  induction t.  
  + destruct a eqn:H'.
  ++ induction em.
  +++ simpl in *; auto. split with (x := (build_manifest_helper p0 [] [] [] empty_PolicyT) ).
  +++ left.    
  remember (build_manifest_helper p0 [] [] [] empty_PolicyT) as m.

  
  
  inversion H1; simpl in *. 
  
  
  
  
  
  
  inversion H.   remember (build_manifest_helper p0 [] [] [] empty_PolicyT) as m.
     exists m. split.
  +++ simpl in *.      
  
  destruct em eqn:H'.
  ++ split with (x := []).  split with (x := a).
Abort.


*)