Require Import JSON Manifest Term_Defs_Core Manifest_JSON_Admits List ErrorStringConstants.
Import ListNotations ResultNotation.

Definition Manifest_to_JSON (m : Manifest) : JSON :=
  let '(Build_Manifest my_abstract_plc asps appraisal_asps uuidPlcs pubKeyPlcs targetPlcs policy) := m 
  in
    JSON_Object [
      (MAN_ABS_PLC, to_JSON my_abstract_plc);
      (MAN_ASPS, to_JSON asps);
      (MAN_APPR_ASPS, to_JSON appraisal_asps);
      (MAN_UUID_PLCS, to_JSON uuidPlcs);
      (MAN_PUBKEY_PLCS, to_JSON pubKeyPlcs);
      (MAN_TARGET_PLCS, to_JSON targetPlcs);
      (MAN_POLICY, to_JSON policy)
    ].

Definition JSON_to_Manifest (js : JSON) : ResultT Manifest StringT :=
  temp_ABS_PLC <- JSON_get_stringT MAN_ABS_PLC js;;
  temp_ASPS <- JSON_get_JSON MAN_ASPS js;;
  temp_APPR_ASPS <- JSON_get_JSON MAN_APPR_ASPS js;;
  temp_UUID_PLCS <- JSON_get_JSON MAN_UUID_PLCS js;;
  temp_PUBKEY_PLCS <- JSON_get_JSON MAN_PUBKEY_PLCS js;;
  temp_TARGET_PLCS <- JSON_get_JSON MAN_TARGET_PLCS js;;
  temp_POLICY <- JSON_get_JSON MAN_POLICY js;;
  ABS_PLC <- stringT_to_Plc temp_ABS_PLC;;
  ASPS <- from_JSON temp_ASPS;;
  APPR_ASPS <- from_JSON temp_APPR_ASPS;;
  UUID_PLCS <- from_JSON temp_UUID_PLCS;;
  PUBKEY_PLCS <- from_JSON temp_PUBKEY_PLCS;;
  TARGET_PLCS <- from_JSON temp_TARGET_PLCS;;
  POLICY <- from_JSON temp_POLICY;;
  resultC (Build_Manifest ABS_PLC ASPS APPR_ASPS UUID_PLCS PUBKEY_PLCS TARGET_PLCS POLICY).

Global Instance Jsonifiable_Manifest : Jsonifiable Manifest :=
  { to_JSON := Manifest_to_JSON;
    from_JSON := JSON_to_Manifest
  }.

Definition AM_Lib_to_JSON (am : AM_Library) : JSON :=
  let '(Build_AM_Library clone_uuid lib_asps lib_appr_asps lib_plcs lib_pubkeys) := am
  in
    JSON_Object [
      (AM_CLONE_UUID, to_JSON clone_uuid);
      (AM_LIB_ASPS, to_JSON lib_asps);
      (AM_LIB_APPR_ASPS, to_JSON lib_appr_asps);
      (AM_LIB_PLCS, to_JSON lib_plcs);
      (AM_LIB_PUBKEYS, to_JSON lib_pubkeys)
    ].

Definition JSON_to_AM_Lib (js : JSON) : ResultT AM_Library StringT :=
  temp_CLONE_UUID <- JSON_get_stringT AM_CLONE_UUID js;;
  temp_LIB_ASPS <- JSON_get_JSON AM_LIB_ASPS js;;
  temp_LIB_APPR_ASPS <- JSON_get_JSON AM_LIB_APPR_ASPS js;;
  temp_LIB_PLCS <- JSON_get_JSON AM_LIB_PLCS js;;
  temp_LIB_PUBKEYS <- JSON_get_JSON AM_LIB_PUBKEYS js;;
  CLONE_UUID <- stringT_to_UUID temp_CLONE_UUID;;
  LIB_ASPS <- from_JSON temp_LIB_ASPS;;
  LIB_APPR_ASPS <- from_JSON temp_LIB_APPR_ASPS;;
  LIB_PLCS <- from_JSON temp_LIB_PLCS;;
  LIB_PUBKEYS <- from_JSON temp_LIB_PUBKEYS;;
  resultC (Build_AM_Library CLONE_UUID LIB_ASPS LIB_APPR_ASPS LIB_PLCS LIB_PUBKEYS).

Global Instance Jsonifiable_AM_Library : Jsonifiable AM_Library :=
  { to_JSON := AM_Lib_to_JSON;
    from_JSON := JSON_to_AM_Lib
  }.