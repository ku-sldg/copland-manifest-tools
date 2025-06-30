From CoplandManifestTools Require Import Manifest Manifest_Generator Manifest_Generator_Union.
From CLITools Require Import CLI_Tools.
From EasyBakeCakeML Require Import
  EasyBakeCakeML
  ExtrCakeMLNativeString
  ExtrCakeMLNat
  CakeML_Stdlib.All.
From RocqCandy Require Import All.

(*
Inductive cli_arg_kind :=
  | ArgPositional
  | ArgOption
  | ArgFlag.

Record arg_spec := {
  arg_name : string;
  arg_kind : cli_arg_kind;
  arg_required : bool;
  arg_help : string;
  arg_default : option string
}.
*)

Local Open Scope string_scope.

Definition term_arg_spec : arg_spec := {|
  arg_name := "term";
  arg_kind := ArgOption;
  arg_required := true;
  arg_help := "The term to generate a manifest for.";
  arg_default := None
|}.

Definition global_context_arg_spec : arg_spec := {|
  arg_name := "global_context";
  arg_kind := ArgOption;
  arg_required := false;
  arg_help := "The global context to use for the manifest generation.";
  arg_default := None
|}.

Definition output_dir_arg_spec : arg_spec := {|
  arg_name := "output_dir";
  arg_kind := ArgOption;
  arg_required := true;
  arg_help := "The directory to output the generated manifest.";
  arg_default := None
|}.

Definition unwrap_opt {A B} (opt: option A) (alt : B) : Result A B :=
  match opt with
  | Some v => res v
  | None => err alt
  end.

Local Open Scope map_scope.

Definition write_manifest_to_file (man : Manifest) (filename : string) :=
  let content := to_string man in
  TextIO.writeFile filename content.

Definition write_out_manifests (out_dir : string) (env : EnvironmentM) :=
  let _ := List.map 
    (fun '(p, m) =>
      let filename := String.append out_dir (String.append "/" (to_string p)) in
      write_manifest_to_file m filename)
    env 
  in tt.

Definition man_gen_front_end : unit := 
  let comname := CommandLine.name tt in
  let comargs := CommandLine.arguments tt in
  let args_spec := [term_arg_spec; global_context_arg_spec; output_dir_arg_spec] in
  let runtime := (
    args_res <- gather_args_stub comname comargs args_spec ;;
    (* Parse the args into the values *)
    term_arg <- unwrap_opt (args_res ![ "term" ]) "Term argument is required." ;;
    term_arg <- unwrap_opt (arg_value term_arg) "Term argument value was not found." ;;
    term_val <- from_string term_arg ;;
    (* Getting global context argument *)
    global_context_arg <- unwrap_opt (args_res ![ "global_context" ]) "Global context argument is required." ;;
    global_context_arg <- unwrap_opt (arg_value global_context_arg) "Global context argument value was not found." ;;
    global_context_val <- from_string global_context_arg ;;
    (* Getting output directory argument *)
    output_dir_arg <- unwrap_opt (args_res ![ "output_dir" ]) "Output directory argument is required." ;;
    output_dir_arg <- unwrap_opt (arg_value output_dir_arg) "Output directory argument value was not found." ;;
    output_dir_val <- from_string output_dir_arg ;;
    (* Generate the manifests *)
    man_env <- end_to_end_mangen global_context_val term_val ;;
    (* Now, for each of the manifests, write them out *)
    res (write_out_manifests output_dir_val man_env)) in
  match runtime with
  | res _ => tt
  | err e => TextIO.printLn_err ("Error in Manifest Generation: " ++ e)
  end.

Local Close Scope map_scope.
Local Close Scope string_scope.

Separate CakeML_Extraction man_gen_front_end.