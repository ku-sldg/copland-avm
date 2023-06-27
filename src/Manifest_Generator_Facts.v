Require Import Maps Term_Defs_Core Manifest Eqb_Evidence
  Manifest_Generator Executable_Defs_Prop.


Require Import List.
Import ListNotations.


(* place_terms -- 
    Given:  
      Term t
      Top-level place top_plc
      Specific place p
    Return:
      All subterms place p is responsible for executing, assuming top_plc 
        is the initial requester/client.

*)
Fixpoint place_terms (t:Term) (top_plc:Plc) (p:Plc) : list Term := 
  match t with
  | asp a  => if (eqb_plc top_plc p) then [asp a] else []
  | att q t' => if (eqb_plc p q) then [t'] ++ place_terms t' q p else place_terms t' q p  
  | lseq t1 t2 => (place_terms t1 top_plc p) ++ (place_terms t2 top_plc p)
  | bseq _ t1 t2 => (place_terms t1 top_plc p) ++ (place_terms t2 top_plc p)
  | bpar _ t1 t2 => (place_terms t1 top_plc p) ++ (place_terms t2 top_plc p)
  end.

Definition distributed_executability (t:Term) (tp:Plc) (env_map:EnvironmentM) : Prop := 
    forall (* (t_places:list Plc) *) (p:Plc) (t':Term), 
(*         t_places = (places tp t) ->*)
        In p (places tp t) -> 
        In t' (place_terms t tp p) ->
        (exists (m:Manifest),
            Maps.map_get env_map p = Some m /\
            executable t' m
        ).

Theorem manifest_generator_executability :
    forall (t:Term) (p:Plc), 
        distributed_executability t p (manifest_generator t p).
Proof.
Abort.



(*
Theorem manifest_generator_executability :
    forall (t t':Term) (top_plc p:Plc) (t_places : list Plc) 
           (env_map : EnvironmentM) (m:Manifest), 
    env_map = (manifest_generator t top_plc) ->
    t_places = (places top_plc t) ->
    In p t_places -> 
    In t' (place_terms t top_plc p) ->
    Maps.map_get env_map p = Some m ->
    executable t' m.
*)