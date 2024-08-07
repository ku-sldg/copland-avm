Require Import Stringifiable.
Require Import JSON Manifest Manifest_Set Term_Defs_Core Manifest_JSON_Vars List Maps.
Import ListNotations ResultNotation.


Definition Manifest_to_JSON (m : Manifest) : JSON :=
  let '(Build_Manifest asps asp_compat_map asp_fs_map policy) := m 
  in
    JSON_Object [
      (MAN_ASPS, 
        (JSON_Array (manifest_set_to_list_JSON asps)));
      (MAN_ASP_COMPAT_MAP, 
        (to_JSON asp_compat_map));
      (MAN_ASP_FS_MAP, 
        (to_JSON asp_fs_map));
      (MAN_POLICY, 
        (JSON_Array (manifest_set_pairs_to_list_JSON policy)))
    ].

Definition JSON_to_Manifest (js : JSON) : ResultT Manifest string :=
  temp_ASPS <- JSON_get_Array MAN_ASPS js;;
  temp_ASP_COMPAT_MAP <- JSON_get_Object MAN_ASP_COMPAT_MAP js;;
  temp_ASP_FS_MAP <- JSON_get_Object MAN_ASP_FS_MAP js;;
  temp_POLICY <- JSON_get_Array MAN_POLICY js;;

  ASPS <- list_JSON_to_manifest_set temp_ASPS;;
  ASP_COMPAT_MAP <- from_JSON temp_ASP_COMPAT_MAP;;
  ASP_FS_MAP <- from_JSON temp_ASP_FS_MAP;;
  POLICY <- list_JSON_to_manifest_set_pairs temp_POLICY;;
  resultC (Build_Manifest ASPS ASP_COMPAT_MAP ASP_FS_MAP POLICY).

Global Instance Jsonifiable_Manifest `{Jsonifiable (MapC ASP_ID FS_Location), Jsonifiable (ASP_Compat_MapT)}: Jsonifiable Manifest. 
eapply Build_Jsonifiable with 
(to_JSON := (fun m =>
  JSON_Object [
    (MAN_ASPS, 
      (JSON_Array (manifest_set_to_list_JSON (asps m))));
    (MAN_ASP_COMPAT_MAP, 
      (to_JSON (ASP_Compat_Map m)));
    (MAN_ASP_FS_MAP, 
      (to_JSON (ASP_Mapping m)));
    (MAN_POLICY, 
      (JSON_Array (manifest_set_pairs_to_list_JSON (man_policy m))))
  ]))
(from_JSON := (fun js =>
    temp_ASPS <- JSON_get_Array MAN_ASPS js;;
  temp_ASP_COMPAT_MAP <- JSON_get_Object MAN_ASP_COMPAT_MAP js;;
  temp_ASP_FS_MAP <- JSON_get_Object MAN_ASP_FS_MAP js;;
  temp_POLICY <- JSON_get_Array MAN_POLICY js;;

  ASPS <- list_JSON_to_manifest_set temp_ASPS;;
  ASP_COMPAT_MAP <- from_JSON temp_ASP_COMPAT_MAP;;
  ASP_FS_MAP <- from_JSON temp_ASP_FS_MAP;;
  POLICY <- list_JSON_to_manifest_set_pairs temp_POLICY;;
  resultC (Build_Manifest ASPS ASP_COMPAT_MAP ASP_FS_MAP POLICY))).
simpl_json; rewrite canonical_list_injson_to_manset;
rewrite canonical_list_injson_to_manset_pairs; solve_json.
Defined.
