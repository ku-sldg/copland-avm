Require Import Stringifiable.
Require Import JSON Manifest Manifest_Set Term_Defs_Core Manifest_JSON_Vars List ErrorStringConstants EqClass.
Import ListNotations ResultNotation.


Definition Manifest_to_JSON (m : Manifest) : JSON :=
  let '(Build_Manifest my_abstract_plc asps uuidPlcs pubKeyPlcs targetPlcs policy) := m 
  in
    JSON_Object [
      (MAN_ABS_PLC, 
        (InJSON_String (to_string my_abstract_plc)));
      (MAN_ASPS, 
        (InJSON_Array (manifest_set_to_list_InJson asps)));
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
  temp_UUID_PLCS <- JSON_get_Array MAN_UUID_PLCS js;;
  temp_PUBKEY_PLCS <- JSON_get_Array MAN_PUBKEY_PLCS js;;
  temp_TARGET_PLCS <- JSON_get_Array MAN_TARGET_PLCS js;;
  temp_POLICY <- JSON_get_Array MAN_POLICY js;;

  ABS_PLC <- from_string temp_ABS_PLC;;
  ASPS <- list_InJson_to_manifest_set temp_ASPS;;
  UUID_PLCS <- list_InJson_to_manifest_set temp_UUID_PLCS;;
  PUBKEY_PLCS <- list_InJson_to_manifest_set temp_PUBKEY_PLCS;;
  TARGET_PLCS <- list_InJson_to_manifest_set temp_TARGET_PLCS;;
  POLICY <- list_InJson_to_manifest_set_pairs temp_POLICY;;
  resultC (Build_Manifest ABS_PLC ASPS UUID_PLCS PUBKEY_PLCS TARGET_PLCS POLICY).

Global Instance Jsonifiable_Manifest : Jsonifiable Manifest. 
eapply Build_Jsonifiable with 
  (to_JSON := Manifest_to_JSON)
  (from_JSON := JSON_to_Manifest).
intuition; destruct a; simpl in *.
unfold JSON_to_Manifest, res_bind; simpl in *;
repeat (try break_match; simpl in *; subst; try find_injection; try find_rewrite; eauto; try congruence);
repeat rewrite canonical_list_injson_to_manset in *;
repeat rewrite canonical_list_injson_to_manset_pairs in *;
try congruence; repeat find_injection; eauto.
Defined.

Definition AM_Lib_to_JSON (am : AM_Library) : JSON :=
  let '(Build_AM_Library clone_uuid lib_asps lib_plcs lib_pubkeys compat_asps_map) := am
  in
    JSON_Object [
      (AM_CLONE_UUID, (InJSON_String (to_string clone_uuid)));
      (AM_LIB_ASPS, (InJSON_Object (to_JSON lib_asps)));
      (AM_LIB_PLCS, (InJSON_Object (to_JSON lib_plcs)));
      (AM_LIB_PUBKEYS, (InJSON_Object (to_JSON lib_pubkeys)));
      (AM_LIB_COMPAT_ASPS, (InJSON_Object (to_JSON compat_asps_map)))
    ].

Definition JSON_to_AM_Lib (js : JSON) : ResultT AM_Library string :=
  temp_CLONE_UUID <- JSON_get_string AM_CLONE_UUID js;;
  temp_LIB_ASPS <- JSON_get_Object AM_LIB_ASPS js;;
  temp_LIB_PLCS <- JSON_get_Object AM_LIB_PLCS js;;
  temp_LIB_PUBKEYS <- JSON_get_Object AM_LIB_PUBKEYS js;;
  temp_COMPAT_ASPS <- JSON_get_Object AM_LIB_COMPAT_ASPS js;;

  CLONE_UUID <- from_string temp_CLONE_UUID;;
  LIB_ASPS <- from_JSON temp_LIB_ASPS;;
  LIB_PLCS <- from_JSON temp_LIB_PLCS;;
  LIB_PUBKEYS <- from_JSON temp_LIB_PUBKEYS;;
  COMPAT_ASPS <- from_JSON temp_COMPAT_ASPS;;
  resultC (Build_AM_Library CLONE_UUID LIB_ASPS LIB_PLCS LIB_PUBKEYS COMPAT_ASPS).

Global Instance Jsonifiable_AM_Library : Jsonifiable AM_Library.
eapply Build_Jsonifiable with
  (to_JSON := AM_Lib_to_JSON)
  (from_JSON := JSON_to_AM_Lib).
intuition; destruct a; simpl in *.
unfold JSON_to_AM_Lib, res_bind; simpl in *;
repeat rewrite canonical_stringification in *;
repeat (try break_match; simpl in *; subst; try find_injection; try find_rewrite; eauto; try congruence);
try (repeat match goal with
| H : result_map _ (map _ ?l) = errC _ |- _ => 
    induction l; simpl in *; intuition; try congruence;
    unfold res_bind in *; repeat (try break_match; simpl in *; subst; intuition; eauto; try find_injection; try find_rewrite; try congruence);
    repeat rewrite canonical_stringification in *; congruence
| H : result_map _ (map _ ?l) = resultC ?l' |- _ => 
    let IH' := fresh "IH'" in
    assert (l = l') by (
      generalize dependent l';
      induction l as [| ? l IH']; simpl in *; intuition; try congruence;
      unfold res_bind in *; repeat (try break_match; simpl in *; subst; intuition; eauto; try find_injection; try find_rewrite; try congruence);
      repeat rewrite canonical_stringification in *; try congruence;
      repeat find_injection; eauto;
      erewrite IH'; eauto); subst; clear H; eauto
end; fail).
Defined.