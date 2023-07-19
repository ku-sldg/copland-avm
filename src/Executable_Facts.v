Require Import Term_Defs_Core Manifest Manifest_Generator Executable_Defs_Prop Manifest_Admits Eqb_Evidence.

Require Import Params_Admits.
Require Import List.
Import ListNotations.

(*
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

Definition build_manifest_helper p a p1 p2 pol : Manifest := 
{|  my_abstract_plc := p ; 
    asps :=  a ;
    uuidPlcs := p1 ; 
    pubKeyPlcs := p2 ; 
    policy := pol |}. 

*)

(*
Lemma eqb_plc_refl : forall p0, Eqb_Evidence.eqb_plc p0 p0 = true.
Proof.
  intros. apply eqb_eq_plc. auto.
Qed.  
*)