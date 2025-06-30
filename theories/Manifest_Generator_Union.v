(*  (Mostly experimental) combination of Manifest Generation for both Attestation and Appraisal.
      Uses the (as-yet-unverified) manifest environment union operation to merge manifests 
      generated for combined Attestation and Appraisal scenarios.        *)

From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs_Core.
From CoplandManifestTools Require Export Manifest Manifest_Generator.

Local Open Scope string_scope.

Definition Term_Plc_list := list (Term*Plc).

Definition term_plc_list_name_constant : string := "Term_Plc_List".

Definition Term_Plc_list_to_JSON `{Jsonifiable Term} (ls: Term_Plc_list) : JSON :=
  JSON_Object [
    (term_plc_list_name_constant,
      (JSON_Array 
        (List.map 
          (fun '(et,p) => 
            JSON_Array [ to_JSON et; JSON_String (to_string p) ]
          ) ls)
      )
    )].

Definition Term_Plc_list_from_JSON `{Jsonifiable Term} (js : JSON) 
    : Result Term_Plc_list string :=
  match (JSON_get_Array term_plc_list_name_constant js) with
  | res jsArr =>
    let resv := result_map (fun js => 
      match js with
      | JSON_Array [jsTerm; JSON_String jsP] =>
        et <- from_JSON jsTerm ;;
        p <- from_string jsP ;;
        res (et, p)
      | _ => err err_str_json_parsing_failure_wrong_number_args
      end
    ) jsArr in
    match resv with
    | res resv => res resv
    | err e => err e
    end
  | err e => err e
  end.
Close Scope string_scope.

Global Instance Jsonifiable_Term_Plc_list `{Jsonifiable Term} : Jsonifiable Term_Plc_list.
eapply Build_Jsonifiable with 
  (to_JSON := Term_Plc_list_to_JSON)
  (from_JSON := Term_Plc_list_from_JSON).
unfold Term_Plc_list_from_JSON, Term_Plc_list_to_JSON.
simpl in *.
induction a; ff u;
repeat (rewrite canonical_jsonification in *); 
repeat (rewrite canonical_stringification in *); ff.
Defined.

Definition end_to_end_mangen (G : GlobalContext) (ts: Term_Plc_list) 
    : Result EnvironmentM string := 
  result_fold (fun '(t,p) => fun env =>
    manifest_generator G p t) e_empty ts.

