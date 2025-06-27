(* Core properties about the Manifest Generator output.
    Also included:  manifest and environment subset definitions and associated properties. *)
From CoplandManifestTools Require Import Manifest Manifest_Generator.
From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs.
Import MapNotations.

Local Open Scope map_scope.

Definition manifest_subset (m1:Manifest) (m2:Manifest) : Prop :=
  (forall i, In_set i (asps m1) -> In_set i (asps m2)).

Definition Environment_subset (e1:EnvironmentM) (e2:EnvironmentM) : Prop := 
  forall m1 p, 
  e1 ![ p ] = Some m1 ->
  (exists m2, 
    e2 ![ p ] = Some m2 /\
    manifest_subset m1 m2
  ).

Lemma manifest_subset_refl : forall m,
  manifest_subset m m.
Proof.
  intros; 
  unfold manifest_subset; eauto.
Qed.
Global Hint Resolve manifest_subset_refl : manifest.

Lemma manifest_subset_trans : forall m1 m2 m3,
  manifest_subset m1 m2 ->
  manifest_subset m2 m3 ->
  manifest_subset m1 m3.
Proof.
  intros; unfold manifest_subset in *; intuition.
Qed.
Global Hint Resolve manifest_subset_trans : manifest.

Lemma manifest_subset_union_l : forall m1 m2,
  manifest_subset m1 (manifest_union_asps m1 m2).
Proof.
  induction m1; ff;
  unfold manifest_subset; 
  unfold manifest_union_asps; ff;
  eapply union_inclusion_l; ff.
Qed.
Global Hint Resolve manifest_subset_union_l : manifest.

Lemma manifest_subset_union_r : forall m1 m2,
  manifest_subset m2 (manifest_union_asps m1 m2).
Proof.
  induction m1; ff;
  unfold manifest_subset; 
  unfold manifest_union_asps; ff;
  eapply union_inclusion_r; ff.
Qed.
Global Hint Resolve manifest_subset_union_r : manifest.


Lemma env_subset_refl : forall e, 
  Environment_subset e e.
Proof.
  intros.
  unfold Environment_subset; ff;
  exists m1; split; ff.
Qed.

Lemma env_subset_trans : forall e1 e2 e3,
  Environment_subset e1 e2 ->
  Environment_subset e2 e3 -> 
  Environment_subset e1 e3.
Proof.
  intros.
  unfold Environment_subset in *; intros.
  specialize H with (m1:= m1) (p:=p); ff a.
  eexists; split; ff.
  eapply manifest_subset_trans; ff.
Qed.

Lemma env_subset_set_man : forall e p m1 m2,
  e ![ p ] = Some m1 ->
  manifest_subset m1 m2 ->
  Environment_subset e (e ![ p := m2 ]).
Proof.
  induction e; ff u, a.
  - unfold Environment_subset; intuition; simpl in *;
    ff; eauto.
    exists m0; split; ff.
  - unfold Environment_subset; intuition; simpl in *;
    ff; eauto; ff a.
    * exists m0; split; ff.
    * destruct (dec_eq p p1); ff a.
      ** erewrite lookup_insert_eq; eexists; split; ff.
      ** erewrite lookup_insert_neq; ff l; eexists; split; ff.
Qed.

Lemma env_subset_set : forall e p m,
  e ![ p ] = Some m ->
  Environment_subset e (e ![ p := m ]).
Proof.
  intros.
  apply env_subset_set_man with (m1:=m); eauto;
  apply manifest_subset_refl.
Qed. 

Lemma env_subset_set_none : forall e p m,
  e ![ p ] = None ->
  Environment_subset e (e ![ p := m ]).
Proof.
  intros.
  unfold Environment_subset; intros.
  assert (p <> p0) by ff.
  exists m1; split; ff; eauto with maps.
  erewrite lookup_insert_neq; ff l.
Qed.

Lemma manifest_union_asps_empty_r : forall m,
  manifest_union_asps m empty_Manifest = m.
Proof.
  destruct m; reflexivity.
Qed.

Lemma env_subset_cons_none : forall e2 e1 p m,
  e2 ![ p ] = None ->
  Environment_subset e1 e2 ->
  Environment_subset e1 ((p, m) :: e2).
Proof.
  intros.
  unfold Environment_subset in *.
  intuition.
  eapply H0 in H1; ff.
Qed.

Lemma appr_manifest_update_cumul : forall G et m m',
  appr_manifest_update G et m = res m' ->
  manifest_subset m m'.
Proof.
  intros G.
  induction et using (Evidence_subterm_path_Ind_special G);
  intros; simpl in *; intuition; ff;
  unfold aspid_manifest_update, manifest_subset in *;
  intuition; simpl in *; ff; try (erewrite manadd_In_set; ff a, u; fail); eauto;
  ff a, u;
  try (eapply IHet in H1; eauto; simpl in *;
  try (erewrite manadd_In_set; ff a, u); eauto);
  try (ateb_unpack Heqr; ff a, u).
Qed.

Lemma manifest_generator_cumul : forall G t et p e1 e2 e',
  Environment_subset e1 e2 ->
  manifest_generator' G p et t e2 = res e' ->
  Environment_subset e1 e'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; try (ff a, u; eauto; fail).
  - (* asp case *)
    ff; eauto; unfold Environment_subset in *; intuition.
    unfold manifest_update_env_res, asp_manifest_update, 
      aspid_manifest_update in *; ff a, u;
    try (destruct (dec_eq p p0) > [
        ff; erewrite lookup_insert_eq; eexists; split; ff
        | 
        ff; erewrite lookup_insert_neq; ff l; eexists; split; ff
    ]);
    try (unfold manifest_subset in *; ff; erewrite manadd_In_set; ff a, u).
    pp (appr_manifest_update_cumul _ _ _ _ Heqr);
    eapply manifest_subset_trans; ff.
  - simpl in *; ff a.
    eapply IHt >
    [ eapply env_subset_cons_none; eauto | eauto ].
Qed.

Lemma manifest_generator_cumul' : forall G t et p e e',
  manifest_generator' G p et t e = res e' ->
  Environment_subset e e'.
Proof.
  intros.
  eapply manifest_generator_cumul; eauto;
  apply env_subset_refl.
Qed.

Lemma empty_manifest_always_sub: forall m,
  manifest_subset empty_Manifest m.
Proof.
  intros;
  unfold empty_Manifest; unfold manifest_subset; intros; ff.
Qed.

Global Hint Resolve empty_manifest_always_sub : manifest.

Lemma env_subset_l_cons : forall e1 e2 p m m',
  e2 ![ p ] = Some m ->
  Environment_subset e1 e2 ->
  manifest_subset m' m ->
  Environment_subset ((p, m') :: e1) e2.
Proof.
  intuition;
  unfold Environment_subset, manifest_subset in *;
  simpl in *; intuition; ff; eauto;
  rewrite String.eqb_eq in *; subst; eauto.
Qed.

Lemma env_subset_both_cons : forall e1 e2 p m,
  Environment_subset e1 e2 ->
  Environment_subset ((p, m) :: e1) ((p, m) :: e2).
Proof.
  intuition;
  unfold Environment_subset, manifest_subset in *;
  simpl in *; intuition; ff; eauto;
  rewrite String.eqb_eq in *; subst; eauto.
Qed.

Lemma lookup_mangen : forall G t et e e' p p' v,
  e ![ p ] = Some v ->
  manifest_generator' G p' et t e = res e' ->
  exists v', e' ![ p ] = Some v'.
Proof.
  intros;
  find_eapply_lem_hyp manifest_generator_cumul'; 
  unfold Environment_subset in *; ff a.
Qed.
