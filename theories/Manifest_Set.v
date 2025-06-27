(* Definition of the manifest_set datatype, its operations, and related properties.  
    This datatype is used for "collection" manifest fields, and should act like a 
    traditional mathematical set (e.g. cumulative, non-duplicating, ...) *)
From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs.

Definition manifest_set (A : Type) := list A.

Definition manifest_set_empty {A : Type} : manifest_set A := nil.

Fixpoint manset_add {A : Type} `{HA : DecEq A} (a : A) (s : manifest_set A) : manifest_set A :=
  match s with
  | nil => a :: nil
  | h :: t =>
    if dec_eq a h
    then s
    else h :: manset_add a t
  end.

Lemma manset_add_not_nil {A : Type} `{HA : DecEq A} (a : A) (s : manifest_set A) :
  manset_add a s <> nil.
Proof.
  induction s; ff.
Qed.

Fixpoint list_to_manset' {A : Type} `{HA : DecEq A} (l : list A) : manifest_set A :=
  match l with
  | nil => nil
  | h :: t => manset_add h (list_to_manset' t)
  end.

Definition list_to_manset {A : Type} `{HA : DecEq A} (l : list A) : manifest_set A :=
  rev (list_to_manset' l).

Definition filter_manset {A : Type} (f : A -> bool) (s : manifest_set A) : manifest_set A :=
  filter f s.

Definition is_empty_manset {A : Type} (s:manifest_set A) : bool :=
  match s with
  | nil => true
  | _ => false
  end.

Lemma manempty_is_empty {A : Type} : is_empty_manset (@manifest_set_empty A) = true.
Proof. auto. Qed.

Definition In_set {A : Type} (a : A) (s : manifest_set A) : Prop :=
  In a s.

Definition in_dec_set {A : Type} `{HA : DecEq A} (a : A) (s : manifest_set A) : {In_set a s} + {~ In_set a s} :=
  in_dec dec_eq a s.

Lemma In_set_empty_contra {A : Type} : forall (a : A) (P : Prop),
  In_set a manifest_set_empty -> P.
Proof.
  ff.
Qed.

Lemma manadd_In_set {A : Type} `{HA : DecEq A}: forall (s : manifest_set A) i j,
  In_set i (manset_add j s) <->
  i = j \/ In_set i s.
Proof.
  split; induction s; ff a.
Qed.

Lemma in_list_to_set {A : Type} `{HA : DecEq A} : forall (l : list A) a,
  In a l <-> In_set a (list_to_manset l).
Proof.
  unfold In_set;
  split; 
  induction l; ff; unfold list_to_manset in *; ff;
  erewrite <- in_rev in *; ff;
  erewrite manadd_In_set in *; 
  unfold In_set in *; ff.
Qed.

Lemma nodup_manset_add {A : Type} `{HA : DecEq A} (a : A) (s : manifest_set A) :
  NoDup s ->
  NoDup (manset_add a s).
Proof.
  induction s; ff.
  - constructor; ff.
  - constructor; ff; invc H; ff;
    erewrite manadd_In_set in *; ff.
Qed.

Lemma nodup_list_to_manset {A : Type} `{HA : DecEq A} (l : list A) :
  NoDup (list_to_manset l).
Proof.
  induction l; ff.
  - constructor.
  - apply NoDup_rev. simpl. apply nodup_manset_add.
    apply NoDup_rev in IHl. unfold list_to_manset in IHl. rewrite rev_involutive in IHl.
    auto.
Qed.

Lemma manset_add_result {A : Type} `{HA : DecEq A} (s : manifest_set A) a :
  manset_add a s = s \/ manset_add a s = app s (a :: nil).
Proof.
  induction s; ff.
Qed. 

Lemma manset_add_same_dup {A : Type} `{HA : DecEq A} (s : manifest_set A) a :
  manset_add a s = s -> In_set a s /\ ~NoDup (a::s).
Proof.
  split; induction s; ff.
  - invc H0; ff.
  - eapply IHs; ff.
    pp (NoDup_remove_1 [a] s a0); ff.
Qed.

Lemma nodup_preserves_manset {A : Type} `{HA : DecEq A} (l : list A) :
  NoDup l -> list_to_manset l = l.
Proof.
  intros. induction l; auto.
  - inversion H; subst; intuition.
    unfold list_to_manset.
    assert (list_to_manset' l = rev l).
    {
       unfold list_to_manset in H0. rewrite <- H0. rewrite rev_involutive. rewrite H0. auto.
    }
    simpl. rewrite H1.
    destruct (manset_add_result (rev l) a).
    + apply manset_add_same_dup in H4. intuition. apply in_rev in H5. congruence.
    + ff. 
      erewrite rev_unit; erewrite rev_involutive; eauto.
Qed.

Fixpoint manset_union {A : Type} `{HA : DecEq A} (a b : manifest_set A) : manifest_set A :=
  match b with
  | nil => a
  | h :: t => (*manset_union t (manset_add h b)*)
              manset_union (manset_add h a) t
  end.

Lemma manset_add_not_in {A : Type} `{HA : DecEq A} (a : A) (s : manifest_set A) :
  ~In_set a s -> manset_add a s = s ++ [a].
Proof.
  intros. induction s; ff r;
  destruct H; ff.
Qed.

Lemma NoDup_app_single {A : Type} (a : A) (a0 : list A) :
  NoDup (a0 ++ [a]) <-> NoDup (a :: a0).
Proof.
  split.
  - induction a0; auto.
    intros. rewrite <- app_comm_cons in H.
    inversion H; subst; intuition.
    constructor.
    + intro. simpl in H1. destruct H1.
      * subst. auto with *.
      * inversion H0; subst; intuition.  
    + constructor.
      * intro. auto with *.
      * inversion H0; auto.
  - induction a0; auto.
    intros. simpl. constructor.
    + intro. inversion H; subst; auto.
      apply in_app_or in H0; destruct H0.
      * inversion H4; subst; auto.
      * simpl in H0. destruct H0; auto. subst. simpl in H3. intuition.
    + apply IHa0. apply NoDup_cons_iff. inversion H; subst; auto.
      inversion H3; subst; auto. simpl in H2; subst; auto.
Qed.


Theorem exclusive_set_unification {A : Type} `{HA : DecEq A} (b a : manifest_set A) :
  NoDup a -> NoDup b ->
  (forall x, In_set x a -> ~In_set x b) -> (forall y, In_set y b -> ~In_set y a) ->
  manset_union a b = a ++ b.
Proof.
  intros. ltac1:(generalize dependent a). induction b; intros.
  - induction a; auto. simpl. rewrite app_nil_r. auto.
  - simpl. pose proof (H2 a). rewrite manset_add_not_in by (apply H3; simpl; auto).
    assert (a :: b = [a] ++ b) by auto.
    rewrite H4. rewrite app_assoc.
    apply IHb.
    + inversion H0; auto.
    + simpl in H3; intuition. apply NoDup_app_single. constructor; auto.
    + intuition. apply in_app_or in H5; intuition.
      * unfold In_set in *. pose proof (H2 x); auto with *.
      * simpl in H7. destruct H7; subst; auto. inversion H0; subst; auto.
    + intuition. apply in_app_or in H6; intuition.
      * unfold In_set in *. pose proof (H1 y); auto with *.
      * simpl in H7. destruct H7; subst; auto; inversion H0; subst; auto.
Qed.

Lemma manset_union_nil_r {A : Type} `{HA : DecEq A} (s : manifest_set A) :
  NoDup s ->
  manset_union [] s = s.
Proof.
  intros. apply exclusive_set_unification; auto. constructor.
Qed.

Lemma manset_union_nil_l {A : Type} `{HA : DecEq A} (s : manifest_set A) :
  manset_union s [] = s.
Proof.
  auto.
Qed.

Theorem nodup_manset_union {A : Type} `{HA : DecEq A} (a b : manifest_set A) :
  NoDup a ->
  NoDup (manset_union a b).
Proof.
  ltac1:(generalize dependent a). induction b; intros; auto.
  - simpl. auto using nodup_manset_add.
Qed.

Theorem union_inclusion_l {A : Type} `{HA : DecEq A} (a b : manifest_set A) :
  forall x, In_set x a -> In_set x (manset_union a b).
Proof.
  ltac1:(generalize dependent a). induction b; intros; auto.
  - simpl. eapply IHb. erewrite manadd_In_set; ff.
Qed.

Theorem union_inclusion_r {A : Type} `{HA : DecEq A} (a b : manifest_set A) :
  forall y, In_set y b -> In_set y (manset_union a b).
Proof.
  ltac1:(generalize dependent a). induction b; intros; auto.
  - inversion H.
  - simpl. apply in_inv in H. destruct H; subst; auto.
    + apply union_inclusion_l. erewrite manadd_In_set; ff.
Qed.

Lemma union_inclusion {A : Type} `{HA : DecEq A} (a b : manifest_set A) :
  forall z, In_set z a \/ In_set z b <-> In_set z (manset_union a b).
Proof.
  split; intros.
  - intuition; auto using union_inclusion_l, union_inclusion_r.
  - ltac1:(generalize dependent a). induction b; intros; auto.
    simpl in H; apply IHb in H; destruct H; auto with *.
    + apply manadd_In_set in H; destruct H; subst; auto with *.       
Qed.

Fixpoint manifest_set_to_list_JSON {A :Type} `{Stringifiable A} 
    `{DecEq A} (m : manifest_set A) : list JSON :=
  match m with
  | nil => []
  | h :: t => 
    (JSON_String (to_string h)) :: (manifest_set_to_list_JSON t)
  end.

Fixpoint list_JSON_to_manifest_set {A :Type} `{Stringifiable A} `{DecEq A}
    (l : list JSON) : Result (manifest_set A) string :=
  match l with
  | nil => res []
  | h :: t => 
    match h with
    | JSON_String s =>
      match (list_JSON_to_manifest_set t) with
      | res t' => 
          match (from_string s) with
          (* TODO: This should really use a safer add, but man sets arent guarded inductively so in proofs the fact is lost for resolution *)
          | res h' => res (h' :: t')
          | err e => err e
          end
      | err e => err e
      end
    | _ => err err_str_list_json_to_manifest_set
    end
  end.

Lemma canonical_list_injson_to_manset {A : Type} `{Stringifiable A} `{DecEq A} (m : manifest_set A) :
  list_JSON_to_manifest_set (manifest_set_to_list_JSON m) = res m.
Proof.
  induction m; simpl in *; intuition; eauto;
  find_rewrite; rewrite canonical_stringification in *; simpl in *; eauto.
Qed.

Fixpoint manifest_set_pairs_to_list_JSON {A B : Type} `{Stringifiable A} 
    `{Stringifiable B} (m : manifest_set (A * B)) : list JSON :=
  match m with
  | [] => []
  | h :: t => (to_JSON h) :: (manifest_set_pairs_to_list_JSON t)
  end.

Fixpoint list_JSON_to_manifest_set_pairs {A B :Type} `{Stringifiable A} 
    `{Stringifiable B} `{DecEq A} `{DecEq B}
    (l : list JSON) : Result (manifest_set (A * B)) string :=
  match l with
  | nil => res []
  | h :: t => 
    match (from_JSON h) with
    | res h' =>
      match (list_JSON_to_manifest_set_pairs t) with
      (* TODO: Same here as above, we would like to use add but it doesnt have all we need *)
      | res t' => res (h' :: t')
      | err e => err e
      end
    | err e => err e
    end
  end.

Lemma canonical_list_injson_to_manset_pairs {A B : Type} `{Stringifiable A, Stringifiable B} `{DecEq A, DecEq B} (m : manifest_set (A * B)) :
  list_JSON_to_manifest_set_pairs (manifest_set_pairs_to_list_JSON m) = res m.
Proof.
  induction m; simpl in *; intuition; eauto;
  find_rewrite; repeat (rewrite canonical_stringification in *); simpl in *; eauto.
Qed.