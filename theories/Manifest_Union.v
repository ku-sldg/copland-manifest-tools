(* Defining union operations for Manifests and Manifest Environments. *)

From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs System_Types.
From CoplandManifestTools Require Import Manifest_Type Manifest_Set Manifest_Environment.

Definition manifest_union_asps (m1:Manifest) (m2:Manifest) : Manifest := 
    match (m1, m2) with 
    | ((Build_Manifest asps1 asp_fs_map1 myPol1),
       (Build_Manifest asps2 _ _)) =>

       Build_Manifest
        (manset_union asps1 asps2)
        asp_fs_map1
        myPol1
    end.

Definition environment_union'' (p:Plc) (m1:Manifest) (e2:EnvironmentM) : EnvironmentM := 
  match (e2 ![ p ]) with 
  | Some m2 => e2 ![ p := manifest_union_asps m2 m1 ]
  | None => e2 ![ p := m1 ]
  end.

Definition env_union_helper (e1_pr:(Plc*Manifest)) (e2:EnvironmentM) : EnvironmentM := 
  environment_union'' (fst e1_pr) (snd e1_pr) e2.

Definition environment_union (e1:EnvironmentM) (e2:EnvironmentM) : EnvironmentM :=
  fold_right env_union_helper e2 e1.