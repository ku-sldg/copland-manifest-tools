(*  Helper Lemmas in support of Manifest Compiler Soundness proofs.  *)

From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs_Core.
From CoplandManifestTools Require Export Manifest Manifest_Generator Proofs.Manifest_Generator_Helpers.

Global Create HintDb mancomp.

Lemma places'_cumul : forall t p ls,
    In p ls ->
    In p (places' t ls).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; ff.
Qed.

Lemma app_neq_nil : forall A (ls1 ls2 : list A),
  ls1 ++ ls2 <> [] ->
  (ls1 <> [] \/ ls2 <> []).
Proof.
  induction ls2; ff u.
  - rewrite app_nil_r in *; ff.
  - right; ff.
Qed.

Lemma places_app_cumul : forall p t ls ls',
  In p (places' t ls) -> 
  ~ In p ls ->
  In p (places' t ls').
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; ff u, a; intuition; ff;
  destruct (In_dec dec_eq p (places' t1 ls)); ff a;
  eapply places'_cumul; eauto.
Qed.

Lemma top_plc_refl: forall t' p1,  In t' (place_terms t' p1 p1).
Proof.
  intros.
  unfold place_terms.
  destruct t'; ff.
Qed.

Lemma places'_cumul' : forall t p ls,
    In p (places' t []) ->
    In p (places' t ls).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; ff a, u;
  destruct (In_dec dec_eq p (places' t1 [])) > [
    eapply places'_cumul; ff
    |
    eapply places_app_cumul; ff
  ].
Qed.

Lemma in_plc_term : forall p p0 t,
  place_terms t p p0 <> [] ->
  In p0 (places p t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; ff u, a;
  Control.enter (fun () =>
  find_eapply_lem_hyp app_neq_nil;
  break_or_hyp; ff a; right;
  try (eapply places'_cumul; ff; fail);
  try (eapply places'_cumul'; ff; fail)).
Qed.


Lemma in_not_nil : forall A x (ls:list A),
  In x ls -> 
  ls <> [].
Proof.
  intros; destruct ls; ff.
Qed.