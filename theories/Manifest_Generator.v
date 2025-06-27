(* Implementation of the Manifest Generator.
    Includes separate (but similar) versions of the generator for both 
    attestation (manifest_generator) and appraisal (manifest_generator_app) scenarios. *)

From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs.
From CoplandManifestTools Require Import Manifest.

Definition aspid_manifest_update (i:ASP_ID) (m:Manifest) : Manifest := 
  let '{| asps := oldasps; 
          ASP_Mapping := oldFSMap;
          man_policy := oldPolicy |} := m in
  (Build_Manifest (manset_add i oldasps) oldFSMap oldPolicy).

Fixpoint appr_manifest_update (G : GlobalContext) (e : EvidenceT) 
    (m : Manifest) : Result Manifest string :=
  match e with
  | mt_evt => res m
  | nonce_evt _ => res (aspid_manifest_update (check_nonce_aspid) m)
  | asp_evt p par e' => 
    let '(asp_paramsC asp_id args targ_plc targ) := par in
    match (asp_comps G) ![ asp_id ] with
    | None => err err_str_asp_no_compat_appr_asp
    | Some appr_asp_id =>
      (* let dual_par := asp_paramsC appr_asp_id args targ_plc targ in *)
      match (asp_types G) ![ asp_id ] with
      | None => err err_str_asp_no_type_sig
      | Some (ev_arrow fwd in_sig out_sig) =>
        match fwd with
        | REPLACE => (* Only need to do the dual ASP *)
          res (aspid_manifest_update appr_asp_id m)
        | WRAP =>
          (* first do the dual ASP to unwrap *)
          (* NOTE: Do we need to be checking that appr_asp_id is an UNWRAP here? *)
          let m' := aspid_manifest_update appr_asp_id m in
          appr_manifest_update G e' m'
        | UNWRAP =>
          (* to appraise an UNWRAP is to appraise whatever is below 
          the UNWRAP and WRAP *)
          match out_sig with
          | OutN _ => err err_str_unwrap_must_have_outwrap
          | OutUnwrap =>
            m' <- (apply_to_evidence_below G (fun e => appr_manifest_update G e m) [Trail_UNWRAP asp_id] e') ;;
            m'
          end

        | EXTEND =>
          match out_sig with
          | OutUnwrap => err err_str_extend_must_have_outn
          | (OutN n) =>
            (* first we split, left for the appr of extended part, right for rest *)
            let m' := aspid_manifest_update appr_asp_id m in
            appr_manifest_update G e' m'
          end
        end
      end
    end
  | left_evt e' => 
    res <- apply_to_evidence_below G (fun e => appr_manifest_update G e m) [Trail_LEFT] e' ;;
    res
  | right_evt e' => 
    res <- apply_to_evidence_below G (fun e => appr_manifest_update G e m) [Trail_RIGHT] e' ;;
    res
  | split_evt e1 e2 => 
    m1 <- appr_manifest_update G e1 m ;;
    appr_manifest_update G e2 m1
  end.

Definition asp_manifest_update (G : GlobalContext) (e : EvidenceT) 
    (a:ASP) (m:Manifest) : Result Manifest string :=
  match a with 
  | ASPC (asp_paramsC i _ _ _) => res (aspid_manifest_update i m)
  | APPR => appr_manifest_update G e m
  | SIG => res (aspid_manifest_update (sig_aspid) m)
  | HSH => res (aspid_manifest_update (hsh_aspid) m)
  | ENC p => res (aspid_manifest_update (enc_aspid) m)
  | NULL => res m 
  end.

Definition manifest_update_env_res (p:Plc) (e:EnvironmentM) 
            (f:Manifest -> Result Manifest string) 
            : Result EnvironmentM string := 
  let m := 
    match e ![ p ] with
    | Some mm => mm
    | None => empty_Manifest
    end 
  in
  match (f m) with
  | res m' => res (e ![ p := m' ])
  | err e => err e
  end.
  
Fixpoint manifest_generator' (G : GlobalContext) (p:Plc) (et : EvidenceT) 
    (t:Term) (e :EnvironmentM) : Result EnvironmentM string :=
  match t with
  | asp a => manifest_update_env_res p e (asp_manifest_update G et a)

  | att q t' => 
      match (e ![ p ]) with
      | Some m => manifest_generator' G q et t' e
      | None => manifest_generator' G q et t' ((p, empty_Manifest) :: e)
      end

  | lseq t1 t2 => 
    e' <- manifest_generator' G p et t1 e ;; 
    et' <- eval G p et t1 ;;
    manifest_generator' G p et' t2 e'

  | bseq _ t1 t2 => 
    e' <- manifest_generator' G p et t1 e ;;
    manifest_generator' G p et t2 e'

  | bpar _ t1 t2 => 
    e' <- manifest_generator' G p et t1 e ;;
    manifest_generator' G p et t2 e'
  end.

Definition manifest_generator_terms (G : GlobalContext) (p:Plc) (ts:list Term) 
    : Result EnvironmentM string :=
  result_fold (fun t => fun env =>
      et <- eval G p mt_evt t ;;
      manifest_generator' G p et t env) e_empty ts.

Definition manifest_generator (G : GlobalContext) (p : Plc) (t:Term) 
    : Result EnvironmentM string :=
  manifest_generator' G p mt_evt t e_empty.

Lemma manifest_generator_never_empty : forall G t p e et,
  manifest_generator' G p et t e <> res nil.
Proof.
  induction t; simpl in *; intuition; eauto; 
  ff a, u.
  - destruct a; ff;
    unfold manifest_update_env_res, asp_manifest_update in *;
    ff u;
    find_eapply_lem_hyp @insert_not_empty; ff.
Qed.

Definition environment_to_manifest_list (e:EnvironmentM) : list Manifest :=
  map snd e.
