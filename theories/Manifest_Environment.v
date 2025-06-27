(* Definition of a Manifest Environment mapping (EnvironmentM).  *)
From RocqCandy Require Import All.
From CoplandManifestTools Require Import Manifest_Type.
From CoplandSpec Require Import Term_Defs.

Definition EnvironmentM : Type := Map Plc Manifest.

Definition e_empty : EnvironmentM := [].