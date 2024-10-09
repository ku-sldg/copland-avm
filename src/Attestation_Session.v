Require Import Maps Term_Defs_Core Manifest.
Require Import String List.
Require Import JSON Stringifiable ResultT Interface_Strings_Vars.
Import ListNotations.
Import ResultNotation.

Record Attestation_Session := 
  mkAtt_Sess {
  Session_Plc     : Plc ;
  Plc_Mapping     : Map Plc UUID;
  PubKey_Mapping  : Map Plc PublicKey;
  ats_context     : GlobalContext
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
  plc_map             : Map Plc UUID ;
  pubkey_map          : Map Plc PublicKey ;
  policy              : PolicyT ;
}.

Open Scope string_scope.
Global Instance Jsonifiable_Attestation_Session `{Jsonifiable (Map Plc UUID), Jsonifiable (Map Plc PublicKey), Jsonifiable GlobalContext}: Jsonifiable Attestation_Session.
eapply Build_Jsonifiable with 
  (to_JSON := (fun v => 
                JSON_Object [
                  (STR_Session_Plc, JSON_String (to_string (Session_Plc v)));
                  (STR_Plc_Mapping, to_JSON (Plc_Mapping v));
                  (STR_PubKey_Mapping, to_JSON (PubKey_Mapping v));
                  (STR_Session_Context, to_JSON (ats_context v))])) 
  (from_JSON := (fun j =>
    plc <- JSON_get_string STR_Session_Plc j ;;
    plc_map <- JSON_get_Object STR_Plc_Mapping j ;;
    pub_map <- JSON_get_Object STR_PubKey_Mapping j ;;
    sc <- JSON_get_Object STR_Session_Context j ;;
    plc' <- from_string plc ;;
    plc_map' <- from_JSON plc_map ;;
    pub_map' <- from_JSON pub_map ;;
    sc <- from_JSON sc ;;
    resultC {| Session_Plc := plc'; Plc_Mapping := plc_map'; PubKey_Mapping := pub_map'; ats_context := sc |})); solve_json.
Defined.