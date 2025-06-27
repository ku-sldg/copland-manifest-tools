From RocqCandy Require Import All.
From RocqJSON Require Import JSON.
From CoplandManifestTools Require Import Manifest_Type Manifest_Set.
From CoplandSpec Require Import Term_Defs System_Types.

(* Manifest Admits *)
Definition MAN_ABS_PLC : string := "ABS_PLC".

Definition MAN_ASPS : string := "ASPS".

Definition MAN_ASP_COMPAT_MAP : string := "ASP_COMPAT_MAP".

Definition MAN_ASP_FS_MAP : string := "ASP_FS_MAP".

Definition MAN_POLICY : string := "POLICY". 

(* Manifest Jsonifiables *)
Definition Manifest_to_JSON (m : Manifest) : JSON :=
  let '(Build_Manifest asps asp_fs_map policy) := m 
  in
    JSON_Object [
      (MAN_ASPS, 
        (JSON_Array (manifest_set_to_list_JSON asps)));
      (MAN_ASP_FS_MAP, 
        (to_JSON asp_fs_map));
      (MAN_POLICY, 
        (JSON_Array (manifest_set_pairs_to_list_JSON policy)))
    ].

Definition JSON_to_Manifest (js : JSON) : Result Manifest string :=
  temp_ASPS <- JSON_get_Array MAN_ASPS js;;
  temp_ASP_FS_MAP <- JSON_get_Object MAN_ASP_FS_MAP js;;
  temp_POLICY <- JSON_get_Array MAN_POLICY js;;

  ASPS <- list_JSON_to_manifest_set temp_ASPS;;
  ASP_FS_MAP <- from_JSON temp_ASP_FS_MAP;;
  POLICY <- list_JSON_to_manifest_set_pairs temp_POLICY;;
  res (Build_Manifest ASPS ASP_FS_MAP POLICY).

Global Instance Jsonifiable_Manifest `{Jsonifiable (Map ASP_ID FS_Location), Jsonifiable (ASP_Compat_MapT)}: Jsonifiable Manifest. 
eapply Build_Jsonifiable with 
(to_JSON := (fun m =>
  JSON_Object [
    (MAN_ASPS, 
      (JSON_Array (manifest_set_to_list_JSON (asps m))));
    (MAN_ASP_FS_MAP, 
      (to_JSON (ASP_Mapping m)));
    (MAN_POLICY, 
      (JSON_Array (manifest_set_pairs_to_list_JSON (man_policy m))))
  ]))
(from_JSON := (fun js =>
    temp_ASPS <- JSON_get_Array MAN_ASPS js;;
  temp_ASP_FS_MAP <- JSON_get_Object MAN_ASP_FS_MAP js;;
  temp_POLICY <- JSON_get_Array MAN_POLICY js;;

  ASPS <- list_JSON_to_manifest_set temp_ASPS;;
  ASP_FS_MAP <- from_JSON temp_ASP_FS_MAP;;
  POLICY <- list_JSON_to_manifest_set_pairs temp_POLICY;;
  res (Build_Manifest ASPS ASP_FS_MAP POLICY))).
simpl_json; rewrite canonical_list_injson_to_manset;
rewrite canonical_list_injson_to_manset_pairs; solve_json.
Qed.