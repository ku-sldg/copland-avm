Require Import Serializable.
Require Import JSON Manifest Manifest_Set Term_Defs_Core Manifest_JSON_Vars List ErrorStringConstants.
Import ListNotations ResultNotation.


Definition Manifest_to_JSON (m : Manifest) : JSON :=
  let '(Build_Manifest my_abstract_plc asps appraisal_asps uuidPlcs pubKeyPlcs targetPlcs policy) := m 
  in
    JSON_Object [
      (MAN_ABS_PLC, 
        (InJSON_String (to_string my_abstract_plc)));
      (MAN_ASPS, 
        (InJSON_Array (manifest_set_to_list_InJson asps)));
      (MAN_APPR_ASPS, 
        (InJSON_Array (manifest_set_pairs_to_list_InJson appraisal_asps)));
      (MAN_UUID_PLCS, 
        (InJSON_Array (manifest_set_to_list_InJson uuidPlcs)));
      (MAN_PUBKEY_PLCS, 
        (InJSON_Array (manifest_set_to_list_InJson pubKeyPlcs)));
      (MAN_TARGET_PLCS, 
        (InJSON_Array (manifest_set_to_list_InJson targetPlcs)));
      (MAN_POLICY, 
        (InJSON_Array (manifest_set_pairs_to_list_InJson policy)))
    ].

Definition JSON_to_Manifest (js : JSON) : ResultT Manifest string :=
  temp_ABS_PLC <- JSON_get_string MAN_ABS_PLC js;;
  temp_ASPS <- JSON_get_Array MAN_ASPS js;;
  temp_APPR_ASPS <- JSON_get_Array MAN_APPR_ASPS js;;
  temp_UUID_PLCS <- JSON_get_Array MAN_UUID_PLCS js;;
  temp_PUBKEY_PLCS <- JSON_get_Array MAN_PUBKEY_PLCS js;;
  temp_TARGET_PLCS <- JSON_get_Array MAN_TARGET_PLCS js;;
  temp_POLICY <- JSON_get_Array MAN_POLICY js;;

  ABS_PLC <- from_string temp_ABS_PLC;;
  ASPS <- list_InJson_to_manifest_set temp_ASPS;;
  APPR_ASPS <- list_InJson_to_manifest_set_pairs temp_APPR_ASPS;;
  UUID_PLCS <- list_InJson_to_manifest_set temp_UUID_PLCS;;
  PUBKEY_PLCS <- list_InJson_to_manifest_set temp_PUBKEY_PLCS;;
  TARGET_PLCS <- list_InJson_to_manifest_set temp_TARGET_PLCS;;
  POLICY <- list_InJson_to_manifest_set_pairs temp_POLICY;;
  resultC (Build_Manifest ABS_PLC ASPS APPR_ASPS UUID_PLCS PUBKEY_PLCS TARGET_PLCS POLICY).

Global Instance Jsonifiable_Manifest : Jsonifiable Manifest :=
  { to_JSON := Manifest_to_JSON;
    from_JSON := JSON_to_Manifest
  }.

Definition AM_Lib_to_JSON (am : AM_Library) : JSON :=
  let '(Build_AM_Library clone_uuid lib_asps lib_appr_asps lib_plcs lib_pubkeys) := am
  in
    JSON_Object [
      (AM_CLONE_UUID, (InJSON_String (to_string clone_uuid)));
      (AM_LIB_ASPS, (InJSON_Object (to_JSON lib_asps)));
      (AM_LIB_APPR_ASPS, (InJSON_Array (map_pair_to_InnerJSON lib_appr_asps)));
      (AM_LIB_PLCS, (InJSON_Object (to_JSON lib_plcs)));
      (AM_LIB_PUBKEYS, (InJSON_Object (to_JSON lib_pubkeys)))
    ].

Definition JSON_to_AM_Lib (js : JSON) : ResultT AM_Library string :=
  temp_CLONE_UUID <- JSON_get_string AM_CLONE_UUID js;;
  temp_LIB_ASPS <- JSON_get_JSON AM_LIB_ASPS js;;
  temp_LIB_APPR_ASPS <- JSON_get_Array AM_LIB_APPR_ASPS js;;
  temp_LIB_PLCS <- JSON_get_JSON AM_LIB_PLCS js;;
  temp_LIB_PUBKEYS <- JSON_get_JSON AM_LIB_PUBKEYS js;;

  CLONE_UUID <- from_string temp_CLONE_UUID;;
  LIB_ASPS <- from_JSON temp_LIB_ASPS;;
  LIB_APPR_ASPS <- InnerJson_to_map_pair temp_LIB_APPR_ASPS;;
  LIB_PLCS <- from_JSON temp_LIB_PLCS;;
  LIB_PUBKEYS <- from_JSON temp_LIB_PUBKEYS;;
  resultC (Build_AM_Library CLONE_UUID LIB_ASPS LIB_APPR_ASPS LIB_PLCS LIB_PUBKEYS).

Global Instance Jsonifiable_AM_Library : Jsonifiable AM_Library :=
  { to_JSON := AM_Lib_to_JSON;
    from_JSON := JSON_to_AM_Lib
  }.