Require Import List.
Import List.ListNotations.

Require Export Params_Admits.
Require Import Term_Defs.

Require Import Example_Phrases_Demo Example_Phrases_Demo_Admits.  

Require Import String.
(* notation scope so that strings are interpreted correctly. *)
Open Scope string_scope.

Definition get_data' : Term :=
  asp (
  ASPC ALL EXTD (asp_paramsC get_data_aspid get_data_args source_plc get_data_targid)).

Check get_data_aspid.

(* ASPIDs are defined by Definition... not an inductive structure. *)

(* everything is just strings... check this file to ensure strings match 
https://github.com/ku-sldg/am-cakeml/blob/tpm-dev/stubs/Example_Phrases_Demo_Admits.sml*)
Fixpoint privPolicy (sendPlc:Plc) (t:Term) : bool := 
    match t with 
    | asp (ASPC _ _ (asp_paramsC "get_data" args rp tid)) => match sendPlc, rp with 
                                                            | 0, 1 => true 
                                                            | _ , _ => false
                                                            end
    | asp _ => true
    | att p t => privPolicy sendPlc t
    | lseq t1 t2 => andb (privPolicy sendPlc t1) (privPolicy sendPlc t2)
    | bseq _ t1 t2 => andb (privPolicy sendPlc t1) (privPolicy sendPlc t2) 
    | bpar _ t1 t2 => andb (privPolicy sendPlc t1) (privPolicy sendPlc t2)
    end. 