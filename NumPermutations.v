Require Import Omega.
Require Import List.
Require Import Permutation.
Require Import ListTheorems.
Require Import NPeano.
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

Definition rotate_neg (k n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => m - (k + m) mod n
  end.

Definition rotations' {A : Type} (L : list A) : list (list A) :=
  map (fun k => rotate k L) (seq 0 (length L)).

Definition rotations {A : Type} (L : list A) : list (list A) :=
  if empty_dec L then [[]] else rotations' L.

Fixpoint permutations {A : Type} (L : list A) : list (list A) :=
  match L with
  | [] => [[]]
  | x :: M => flat_map rotations' (map (cons x) (permutations M))
  end.

Lemma rotate1_length :
  forall (A : Type) (L : list A), length (rotate1 L) = length L.
Proof.
  intros A L.
  induction L as [|x L IHL]; trivial.
  simpl.
  rewrite app_length.
  simpl.
  omega.
Qed.

Lemma rotate_length :
  forall (A : Type) (k : nat) (L : list A), length (rotate k L) = length L.
Proof.
  intros A k.
  induction k as [|k IH]; trivial.
  intro L.
  simpl.
  rewrite (IH (rotate1 L)).
  apply rotate1_length.
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

Lemma rotate_mult :
  forall (A : Type) (k : nat) (L : list A), rotate (k * length L) L = L.
Proof.
  intros A k L.
  induction k as [|k IH]; trivial.
  simpl.
  rewrite <- rotate_plus, rotate_full.
  trivial.
Qed.

Lemma rotate_nil :
  forall (A : Type) (k : nat), rotate k [] = @nil A.
Proof.
  intros A k.
  induction k as [|k IH]; trivial.
Qed.

Lemma rotate_mod :
  forall (A : Type) (k : nat) (L : list A),
    rotate (k mod (length L)) L = rotate k L.
Proof.
  intros A k L.
  destruct L as [|x M]; [symmetry; apply rotate_nil|].
  set (r := k mod (length (x :: M))).
  rewrite (div_mod k (length (x :: M))) by (simpl; auto).
  rewrite <- rotate_plus, mult_comm, rotate_mult.
  trivial.
Qed.

Lemma rotate_neg_bound :
  forall k n : nat, rotate_neg k n < max 1 n.
Proof.
  intros k n.
  destruct n as [|m]; [auto|].
  simpl.
  omega.
Qed.

Lemma rotate_inv :
  forall (A : Type) (k : nat) (L : list A),
    rotate (rotate_neg k (length L)) (rotate k L) = L.
Proof.
  intros A k L.
  destruct L as [|x M].
  - repeat rewrite rotate_nil.
    trivial.
  - set (m := length M).
    set (r := (k + m) mod (S m)).
    set (q := (k + m) / (S m)).
    change (rotate (m - r) (rotate k (x :: M)) = x :: M).
    rewrite rotate_plus.
    assert (r < S m) as B by (apply mod_bound_pos; omega).
    replace (k + (m - r)) with ((k + m) - r) by omega.
    rewrite (div_mod (k + m) (S m)) by auto.
    rewrite Nat.add_sub, mult_comm.
    change (rotate (q * length (x :: M)) (x :: M) = x :: M).
    apply rotate_mult.
Qed.

Lemma rotate1_map :
  forall (A B : Type) (f : A -> B) (L : list A),
    rotate1 (map f L) = map f (rotate1 L).
Proof.
  intros A B f L.
  induction L as [|x L IH]; trivial.
  simpl.
  rewrite map_app.
  trivial.
Qed.

Lemma rotate_map :
  forall (A B : Type) (k : nat) (f : A -> B) (L : list A),
    rotate k (map f L) = map f (rotate k L).
Proof.
  intros A B k f L.
  induction k as [|k IH]; trivial.
  replace (S k) with (k + 1) by omega.
  repeat rewrite <- rotate_plus.
  rewrite IH.
  apply rotate1_map.
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

Lemma rotations_rotations' :
  forall (A : Type) (L : list A), L <> [] -> rotations L = rotations' L.
Proof.
  intros A L H.
  unfold rotations.
  destruct (empty_dec L) as [E|E]; tauto.
Qed.

Lemma in_rotations :
  forall (A : Type) (L M : list A),
    In L (rotations M) <-> exists k, L = rotate k M.
Proof.
  intros A L M.
  unfold rotations, rotations'.
  destruct (empty_dec M) as [E|N].
  - simpl.
    split.
    + intros [H|H]; [|tauto].
      exists 0.
      subst.
      trivial.
    + intros [k H].
      subst.
      rewrite rotate_nil.
      tauto.
  - split.
    + rewrite in_map_iff.
      intros [x [H1 H2]].
      exists x.
      auto.
    + intros [x E].
      subst L.
      apply in_map_iff.
      exists (x mod (length M)).
      split.
      * apply rotate_mod.
      * apply nonempty_length in N.
        apply in_seq, mod_bound_pos; omega.
Qed.

Lemma rotate1_empty :
  forall (A : Type) (L : list A), L = [] <-> rotate1 L = [].
Proof.
  intros A L.
  repeat rewrite empty_length.
  rewrite rotate1_length.
  tauto.
Qed.

Lemma rotations_rotate1 :
  forall (A : Type) (L : list A),
    rotations (rotate1 L) = rotate1 (rotations L).
Proof.
  intros A L.
  unfold rotations, rotations'.
  pose (rotate1_empty _ L) as HE3.
  destruct (empty_dec L) as [HE|HE]; destruct (empty_dec (rotate1 L)) as [HE2|HE2]; try tauto.
  rewrite rotate1_length.
  set (n := length L).
  assert (n = length L) as E by trivial.
  rewrite <- (map_map S (fun k => rotate k L)).
  rewrite seq_shift.
  destruct n as [|n]; trivial.
  replace (seq 1 (S n)) with (seq 1 n ++ [S n]) by (
    change (seq 1 n ++ seq (S n) 1 = seq 1 (S n));
    rewrite seq_app;
    auto with *
  ).
  rewrite map_app.
  simpl.
  apply (f_equal (fun x => map _ _ ++ [x])).
  change (rotate (S n) L = L).
  rewrite E.
  apply rotate_full.
Qed.

Lemma rotations_rotate :
  forall (A : Type) (k : nat) (L : list A),
    rotations (rotate k L) = rotate k (rotations L).
Proof.
  intros A k.
  induction k as [|k IH]; trivial.
  intro L.
  simpl.
  rewrite <- rotations_rotate1, IH.
  trivial.
Qed.

Lemma rotations_self :
  forall (A : Type) (L : list A), In L (rotations L).
Proof.
  intros A L.
  apply in_rotations.
  exists 0.
  trivial.
Qed.

Lemma rotations_length :
  forall (A : Type) (L : list A), length (rotations L) = max 1 (length L).
Proof.
  intros A L.
  unfold rotations, rotations'.
  destruct (empty_dec L) as [H|H].
  - subst.
    trivial.
  - rewrite map_length, seq_length.
    apply nonempty_length in H.
    rewrite max_r; trivial.
Qed.

Lemma in_rotations_rotate :
  forall (A : Type) (k : nat) (L : list A), In L (rotations (rotate k L)).
Proof.
  intros A k L.
  rewrite rotations_rotate.
  apply (Permutation_in (l := rotations L)).
  + symmetry.
    apply Permutation_rotate.
  + apply rotations_self.
Qed.

Lemma Permutation_rotations :
  forall (A : Type) (L M : list A), In L (rotations M) -> Permutation L M.
Proof.
  intros A L M H.
  rewrite in_rotations in H.
  destruct H as [x H].
  subst L.
  apply Permutation_rotate.
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
    split.
    + intros [N [H1 H2]].
      rewrite in_map_iff in H1.
      destruct H1 as [P [E1 H1]].
      rewrite <- rotations_rotations' in H2 by (subst; auto with *).
      rewrite in_rotations in H2.
      destruct H2 as [k E2].
      subst N M.
      rewrite IH in H1.
      rewrite Permutation_rotate.
      auto.
    + intro H.
      assert (In x M) as HxM by (apply (Permutation_in _ H); auto with *).
      apply rotate_head in HxM.
      destruct HxM as [k [Hk HM]].
      exists (rotate k M).
      split.
      * rewrite in_map_iff.
        exists (tail (rotate k M)).
        rewrite IH.
        rewrite <- (Permutation_rotate A k M) in H.
        destruct (rotate k M) as [|y Q]; [discriminate|].
        injection HM as E.
        subst y.
        split; trivial.
        revert H.
        apply Permutation_cons_inv.
      * rewrite <- rotations_rotations'; [apply in_rotations_rotate|].
        rewrite nonempty_length, rotate_length.
        omega.
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
    0 <= k1 < length L ->
    0 <= k2 < length M ->
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
    0 <= k1 < length L ->
    0 <= k2 < length M ->
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
  unfold rotations.
  destruct (empty_dec L) as [E|E]; [apply NoDup_singleton|].
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
    rewrite <- rotations_rotations' by auto with *.
    apply permutations_correct, (perm_skip x) in HP.
    apply NoDup_rotations.
    revert HP ND.
    apply Permutation_NoDup.
  - intros L1' L2' M.
    unfold rotations'.
    repeat rewrite in_map_iff.
    intros [L1 [E1 H1]] [L2 [E2 H2]] [k1 [E3 H3]] [k2 [ER H4]].
    subst L1' L2' M.
    symmetry in ER.
    rewrite permutations_correct, in_seq in *.
    assert (k1 = k2) as Ek by (
      revert H3 H4 ER;
      apply rotate_injective3; trivial; revert ND; apply Permutation_NoDup; auto
    ).
    subst k2.
    assert (length (x :: L1) = length (x :: L2)) as EL by (
      apply (f_equal (@length A)) in ER;
      repeat rewrite rotate_length in ER;
      trivial
    ).
    apply (f_equal (rotate (length (x :: L1) - k1))) in ER.
    repeat rewrite rotate_plus in ER.
    replace (k1 + (length (x :: L1) - k1)) with (length (x :: L1)) in ER by omega.
    rewrite rotate_full, EL, rotate_full in ER.
    trivial.
  - apply NoDup_map.
    + intros L1 L2 H1 H2 E.
      injection E.
      trivial.
    + apply IH.
      inversion ND.
      trivial.
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
    unfold rotations'.
    rewrite map_length, seq_length.
    rewrite in_map_iff in H.
    destruct H as [P [E HP]].
    subst M.
    apply permutations_correct, Permutation_length in HP.
    rewrite HP.
    trivial.
Qed.
