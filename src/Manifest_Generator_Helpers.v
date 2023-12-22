Require Import Term_Defs_Core (* Params_Admits *) Manifest
               (* Example_Phrases_Admits Example_Phrases *) Eqb_Evidence.

Require Import (* EqClass *) Maps StructTactics.

Require Export EnvironmentM.

Require Import List.
Import ListNotations.



Fixpoint places' (t:Term) (ls:list Plc) : list Plc :=
    match t with
    | asp _ => ls 
    | att q t' => (q :: (places' t' ls))
    | lseq t1 t2 => places' t2 (places' t1 ls)
    | bseq _ t1 t2 => places' t2 (places' t1 ls)
    | bpar _ t1 t2 => places' t2 (places' t1 ls)
    end.
  
  Definition places (p:Plc) (t:Term): list Plc := 
    p :: (places' t []).
  
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