Require Import List.
Import List.ListNotations.

Require Export Params_Admits.
Require Import Term_Defs.

Require Import Example_Phrases_Demo Example_Phrases_Demo_Admits.  

Require Import String.
(* notation scope so that strings are interpreted correctly. *)
Open Scope string_scope.

Require Import Eqb_Evidence. 

(* here is the get_data term copied. We want to make sure that the get_data_aspid is only called when the target (0) requests from the source (1)*)
Definition get_data' : Term :=
  asp (
  ASPC ALL EXTD (asp_paramsC get_data_aspid get_data_args source_plc get_data_targid)).

Check get_data_aspid.
Check eqb_aspid. 

(* ASPIDs are defined by Definition. use eqb_aspid for string comparison *)

(* privacy policy ensures that the sending place (place that sends the request aka the target) can recieve the requested data. In this case, the data should only be shared between source (O) and target (S O) . *)
Fixpoint privPolicy (sendPlc:Plc) (t:Term) : bool := 
    match t with 
    | asp (ASPC _ _ (asp_paramsC aspid args rp tid)) => match eqb_aspid aspid get_data_aspid with 
                                                        | true => if andb (Nat.eqb sendPlc 1) (Nat.eqb rp 0) then true else false  
                                                        | false => true 
                                                        end
    | asp _ => true
    | att p t => privPolicy sendPlc t
    | lseq t1 t2 => andb (privPolicy sendPlc t1) (privPolicy sendPlc t2)
    | bseq _ t1 t2 => andb (privPolicy sendPlc t1) (privPolicy sendPlc t2) 
    | bpar _ t1 t2 => andb (privPolicy sendPlc t1) (privPolicy sendPlc t2)
    end.

Global Hint Resolve privPolicy : core. 

Example privCheck1 : privPolicy 1 get_data' = true.
Proof. 
  unfold privPolicy. simpl. rewrite eqb_refl. 
  (* can't finish this proof since the term has source_plc as an admitted value *)
Abort. 

Example privCheck2 : privPolicy 2 get_data' = false.
Proof. 
  unfold privPolicy. simpl. rewrite eqb_refl. auto.
Qed. 

