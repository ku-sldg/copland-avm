Require Import Maps Term_Defs_Core Manifest Eqb_Evidence
  Manifest_Generator Executable_Defs_Prop.


Require Import List.
Import ListNotations.

Locate executable.

Locate places.

(* place_terms -- 
    Given:  
      Term t
      Top-level place top_plc
      Specific place p
    Return:
      All subterms place p is responsible for executing, assuming top_plc 
        is the initial requester/client.

*)

(*
Fixpoint place_terms' (t:Term) (top_plc:Plc) (p:Plc) (ls:list Term) : list Term := 
  (* if (eqb_plc top_plc p)
  then [t] ++ ls (* ++ (place_terms' t top_plc p [])  *)
  else ( *)
    match t with 
    | asp a => if (eqb_plc top_plc p) then [asp a] ++ ls else ls
    | att q t' => if (eqb_plc p q) then ([t'] ++ ls) (* place_terms t' q p *) else (place_terms' t' q p ls)
    | lseq t1 t2 => (place_terms' t1 top_plc p []) ++ (place_terms' t2 top_plc p []) ++ ls
    | bseq _ t1 t2 => (place_terms' t1 top_plc p []) ++ (place_terms' t2 top_plc p []) ++ ls
    | bpar _ t1 t2 => (place_terms' t1 top_plc p []) ++ (place_terms' t2 top_plc p []) ++ ls
    end.

Definition place_terms (t:Term) (top_plc:Plc) (p:Plc) : list Term :=
  place_terms' t top_plc p [].
*)



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


    Locate executable.



















(*
Fixpoint place_terms (t:Term) (top_plc:Plc) (p:Plc) : list Term := 
  if (eqb_plc top_plc p) 
  then [t]
  else (
  match t with
  | asp a  => []
  | att q t' => if (eqb_plc p q) then [t'] ++ place_terms t' q p else place_terms t' q p  
  | lseq t1 t2 => (place_terms t1 top_plc p) ++ (place_terms t2 top_plc p)
  | bseq _ t1 t2 => (place_terms t1 top_plc p) ++ (place_terms t2 top_plc p)
  | bpar _ t1 t2 => (place_terms t1 top_plc p) ++ (place_terms t2 top_plc p)
  end).
  *)

Definition distributed_executability 
  (t:Term) (tp:Plc) (env_map:EnvironmentM) : Prop := 
  forall p t', 
    In p (places tp t) /\ 
    In t' (place_terms t tp p) ->

    (exists (m:Manifest),
      Maps.map_get env_map p = Some m /\
      executable t' m).





(* 
Definition distributed_executability 
  (t:Term) (tp:Plc) (env_map:EnvironmentM) : Prop := 
forall (p:Plc),
(In p (places tp t)) ->
(
  forall t' (_:(In t' (place_terms t tp p))),
    (exists (m:Manifest),
      Maps.map_get env_map p = Some m /\
      executable t' m)).
  *)


(*
Definition distributed_executability 
          (t:Term) (tp:Plc) (env_map:EnvironmentM) : Prop := 
    forall (p:Plc),
      In p (places tp t) -> 
    (
      forall t', 
      (
        In t' (place_terms t tp p) ->
        (exists (m:Manifest),
            Maps.map_get env_map p = Some m /\
            executable t' m
        ))).
        *)

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