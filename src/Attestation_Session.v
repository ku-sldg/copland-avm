Require Import Maps Term_Defs_Core Manifest.
Require Import String List.
Require Import JSON Stringifiable.
Import ListNotations.

Record Attestation_Session := 
  mkAtt_Sesplit_evt {
  Session_Plc     : Plc ;
  Plc_Mapping     : MapC Plc UUID;
  PubKey_Mapping  : MapC Plc PublicKey;
}.

Inductive DispatcherErrors : Type :=
| Unavailable   : DispatcherErrors
| Runtime       : string -> DispatcherErrors.

Inductive CallBackErrors : Type := 
| messageLift   : string -> CallBackErrors.

Definition ASPCallback (ErrType : Type) : Type := 
  ASP_PARAMS -> RawEv -> ResultT RawEv ErrType.

Definition PolicyT := list (Plc * ASP_ID).

Record Session_Config := {
  session_plc         : Plc ;
  session_context     : GlobalContext ;
  aspCb               : (ASPCallback DispatcherErrors) ;
  plc_map             : MapC Plc UUID ;
  pubkey_map          : MapC Plc PublicKey ;
  policy              : PolicyT ;
}.

Open Scope string_scope.
Global Instance Jsonifiable_Attestation_Session `{Jsonifiable (MapC Plc UUID), Jsonifiable (MapC Plc PublicKey)}: Jsonifiable Attestation_Session.
eapply Build_Jsonifiable with 
  (to_JSON := (fun v => 
                JSON_Object [
                  ("Session_Plc", JSON_String (to_string (Session_Plc v)));
                  ("Plc_Mapping", to_JSON (Plc_Mapping v));
                  ("PubKey_Mapping", to_JSON (PubKey_Mapping v))])) 
  (from_JSON := (fun j =>
    match (JSON_get_string "Session_Plc" j), (JSON_get_Object "Plc_Mapping" j), (JSON_get_Object "PubKey_Mapping" j) with
    | resultC plc, resultC plc_map, resultC pub_map =>
        match (from_string plc), (from_JSON plc_map), (from_JSON pub_map) with
        | resultC plc', resultC plc_map', resultC pub_map' =>
            resultC {| Session_Plc := plc'; Plc_Mapping := plc_map'; PubKey_Mapping := pub_map' |}
        | _, _, _ => errC "Error in parsing Attestation_Session"
        end
    | _, _, _ => errC "Error in parsing Attestation_Session"
    end)).
simpl in *; intuition.
repeat rewrite canonical_jsonification; destruct a; eauto.
Defined.