(* 
   Core definitions of the Manifest, AM_Library, and AM_Config datatypes.

   Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs System_Types.
From CoplandManifestTools Require Import Manifest_Set.

Definition PolicyT := list (Plc * ASP_ID).

(** [Manifest] defines an attestation manger, a list of ASPs, and other
   * managers it is aware of (a single AM and its interconnections).
   *)
Record Manifest := {
  asps              : manifest_set ASP_ID; 
  ASP_Mapping       : Map ASP_ID FS_Location;
  man_policy        : PolicyT  ;
  (* TO DO: Add privacy and selection policies to manifest? *)
}.

Definition empty_Manifest : Manifest :=
  Build_Manifest nil nil nil.
