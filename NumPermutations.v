Require Import Omega.
Require Import List.
Require Import Permutation.
Require Import ListTheorems.
Import ListNotations.

Definition rotate1 {A : Type} (L : list A) : list A :=
  match L with
  | [] => []
  | x :: M => M ++ [x]
  end.

Fixpoint rotate {A : Type} (k : nat) (L : list A) : list A :=
  match k with
  | 0 => L
  | S k' => rotate k' (rotate1 L)
  end.

Definition rotations {A : Type} (L : list A) : list (list A) :=
  map (fun k => rotate k L) (seq 1 (length L)).

Fixpoint permutations {A : Type} (L : list A) : list (list A) :=
  match L with
  | [] => [[]]
  | x :: M => flat_map rotations (map (cons x) (permutations M))
  end.

Lemma rotate_length :
  forall (A : Type) (k : nat) (L : list A), length (rotate k L) = length L.
Proof.
  intros A k.
  induction k as [|k IH]; trivial.
  intro L.
  simpl.
  rewrite (IH (rotate1 L)).
  induction L as [|x L IHL]; trivial.
  simpl.
  rewrite app_length.
  simpl.
  omega.
Qed.

Lemma rotate_full :
  forall (A : Type) (L : list A), rotate (length L) L = L.
Proof.
  intros A L.
  set (M := @nil A).
  change (rotate (length L) L = M ++ L).
  assert (rotate (length L) L = rotate (length L) (L ++ M)) as RW.
    rewrite app_nil_r.
    trivial.
  rewrite RW.
  generalize M.
  clear M RW.
  induction L as [|x L IH]; intro M; simpl.
  - auto with *.
  - specialize (IH (M ++ [x])).
    rewrite <- app_assoc in *.
    trivial.
Qed.

Lemma rotate_plus :
  forall (A : Type) (m n : nat) (L : list A),
    rotate n (rotate m L) = rotate (m + n) L.
Proof.
  intros A m.
  induction m as [|m IH]; trivial.
  intros n L.
  exact (IH n (rotate1 L)).
Qed.

Lemma Permutation_rotate :
  forall (A : Type) (k : nat) (L : list A), Permutation (rotate k L) L.
Proof.
  intros A k.
  induction k as [|k IH]; trivial.
  intro L.
  simpl.
  specialize (IH (rotate1 L)).
  rewrite IH.
  destruct L; trivial.
  symmetry.
  apply Permutation_cons_append.
Qed.

Lemma rotate_head :
  forall (A : Type) (L : list A) (x : A),
    In x L -> exists k, k < length L /\ head (rotate k L) = Some x.
Proof.
  intros A L x H.
  set (M := @nil A).
  assert (L = L ++ M) as RW by (rewrite app_nil_r; trivial).
  replace L with (L ++ M) by (rewrite app_nil_r; trivial).
  replace (length (L ++ M)) with (length L) by (rewrite app_nil_r; trivial).
  generalize M.
  clear M RW.
  induction L as [|y L IH]; [simpl in H; tauto|]; intro M.
  destruct H as [H|H].
  - subst.
    exists 0.
    simpl.
    auto with *.
  - specialize (IH H (M ++ [y])).
    destruct IH as [n [H1 H2]].
    exists (S n).
    simpl.
    split; [omega|].
    rewrite <- app_assoc.
    trivial.
Qed.

Theorem permutations_correct :
  forall (A : Type) (L M : list A), In M (permutations L) <-> Permutation L M.
Proof.
  intros A L.
  induction L as [|x L IH]; intro M; simpl.
  - split.
    + intuition; subst; trivial.
    + intro H.
      rewrite (Permutation_nil H).
      tauto.
  - rewrite in_flat_map.
    unfold rotations.
    split.
    + intros [N [H1 H2]].
      rewrite in_map_iff in *.
      destruct H1 as [P [E1 H1]].
      destruct H2 as [k [E2 H2]].
      subst N M.
      rewrite IH in H1.
      rewrite Permutation_rotate.
      auto.
    + intro H.
      assert (In x M) as HxM.
        apply (Permutation_in _ H).
        auto with *.
      apply rotate_head in HxM.
      destruct HxM as [k [Hk HM]].
      exists (rotate k M).
      repeat rewrite in_map_iff.
      split.
      * exists (tail (rotate k M)).
        rewrite IH.
        rewrite <- (Permutation_rotate A k M) in H.
        destruct (rotate k M) as [|y Q]; [discriminate|].
        injection HM as E.
        subst y.
        split; trivial.
        revert H.
        apply Permutation_cons_inv.
      * exists (length M - k).
        rewrite rotate_plus, in_seq, rotate_length.
        replace (k + (length M - k)) with (length M) by omega.
        rewrite rotate_full.
        auto with *.
Qed.

Lemma rotate_injective1 :
  forall (A : Type) (k : nat) (L : list A),
    NoDup L -> k < length L -> head (rotate k L) = head L -> k = 0.
Proof.
  intros A k L HL Hk ER.
  destruct HL as [|x L Hx HL]; [simpl in Hk; omega|].
  destruct (zerop k) as [Hk2|Hk2]; trivial.
  contradict Hx.
  destruct k as [|k]; [omega|].
  simpl in *.
  apply lt_S_n in Hk.
  set (M := @nil A).
  replace (L ++ [x]) with (L ++ [x] ++ M) in ER by (rewrite app_nil_r; trivial).
  revert Hk ER.
  generalize M.
  clear HL M Hk2.
  revert L.
  induction k as [|k IH]; intros [|y L] M Hk ER; simpl in Hk; try omega.
  - injection ER as E.
    subst y.
    auto with *.
  - apply lt_S_n in Hk.
    specialize (IH L (M ++ [y])).
    simpl in *.
    rewrite <- app_assoc in ER.
    tauto.
Qed.

Lemma rotate_injective2 :
  forall (A : Type) (k1 k2 : nat)(L M : list A),
    NoDup L ->
    NoDup M ->
    head L = head M ->
    1 <= k1 < 1 + length L ->
    1 <= k2 < 1 + length M ->
    rotate k1 L = rotate k2 M ->
      k1 <= k2.
Proof.
  intros A k1 k2 L M HL HM EH Hk1 Hk2 ER.
  pose (f_equal (@length A) ER) as EL.
  repeat rewrite rotate_length in EL.
  apply not_gt.
  intro G.
  apply (f_equal (rotate (length L - k2))) in ER.
  repeat rewrite rotate_plus in ER.
  replace (k1 + (length L - k2)) with (length L + (k1 - k2)) in ER by omega.
  replace (k2 + (length L - k2)) with (length L) in ER by omega.
  rewrite <- rotate_plus, rotate_full, EL, rotate_full in ER.
  apply (f_equal (@head A)) in ER.
  rewrite <- EH in ER.
  apply rotate_injective1 in ER; trivial; omega.
Qed.

Lemma rotate_injective3 :
  forall (A : Type) (k1 k2 : nat) (L M : list A),
    NoDup L ->
    NoDup M ->
    head L = head M ->
    1 <= k1 < 1 + length L ->
    1 <= k2 < 1 + length M ->
    rotate k1 L = rotate k2 M ->
      k1 = k2.
Proof.
  intros.
  assert (k1 <= k2 /\ k1 >= k2).
  - split.
    + apply (rotate_injective2 A _ _ L M); trivial.
    + apply (rotate_injective2 A _ _ M L); auto.
  - omega.
Qed.

Lemma NoDup_rotations :
  forall (A : Type) (L : list A), NoDup L -> NoDup (rotations L).
Proof.
  intros A L HL.
  apply NoDup_map, NoDup_seq.
  intros k1 k2.
  repeat rewrite in_seq.
  apply rotate_injective3; trivial.
Qed.

Theorem NoDup_permutations :
  forall (A : Type) (L : list A), NoDup L -> NoDup (permutations L).
Proof.
  intros A L.
  induction L as [|x L IH]; intro ND; [apply NoDup_cons, NoDup_nil; tauto|].
  simpl.
  apply NoDup_flat_map.
  - intros M HM.
    rewrite in_map_iff in HM.
    destruct HM as [P [E HP]].
    subst M.
    apply permutations_correct, (perm_skip x) in HP.
    apply NoDup_rotations.
    revert HP ND.
    apply Permutation_NoDup.
  - intros L1' L2' M.
    unfold rotations.
    repeat rewrite in_map_iff.
    intros [L1 [E1 H1]] [L2 [E2 H2]] [k1 [E3 H3]] [k2 [ER H4]].
    subst L1' L2' M.
    symmetry in ER.
    rewrite permutations_correct, in_seq in *.
    assert (k1 = k2) as Ek.
      revert H3 H4 ER.
      apply rotate_injective3; trivial; revert ND; apply Permutation_NoDup; auto.
    subst k2.
    assert (length (x :: L1) = length (x :: L2)) as EL.
      apply (f_equal (@length A)) in ER.
      repeat rewrite rotate_length in ER.
      trivial.
    apply (f_equal (rotate (length (x :: L1) - k1))) in ER.
    repeat rewrite rotate_plus in ER.
    replace (k1 + (length (x :: L1) - k1))
      with (length (x :: L1)) in ER by omega.
    rewrite rotate_full, EL, rotate_full in ER.
    trivial.
  - apply NoDup_map.
    + intros L1 L2 H1 H2 E.
      injection E.
      trivial.
    + apply IH.
      revert ND.
      apply (NoDup_remove_1 nil).
Qed.

Theorem permutations_length :
  forall (A : Type) (L : list A), length (permutations L) = fact (length L).
Proof.
  intros A L.
  induction L as [|x L IH]; trivial.
  simpl.
  rewrite (flat_map_length _ _ _ _ (S (length L))).
  - rewrite map_length, IH.
    trivial.
  - intros M H.
    unfold rotations.
    rewrite map_length, seq_length.
    rewrite in_map_iff in H.
    destruct H as [P [E HP]].
    subst M.
    apply permutations_correct, Permutation_length in HP.
    rewrite HP.
    trivial.
Qed.
