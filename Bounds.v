Require Import Omega.
Require Import List.
Require Import Permutation.
Require Import ListTheorems.
Require Import NumPermutations.
Import ListNotations.

Definition substring {A : Type} (L M : list A) : Prop :=
  exists LH LT, LH ++ L ++ LT = M.

Definition all_perms (n : nat) (L : list nat) : Prop :=
  forall P, Permutation (seq 0 n) P -> substring P L.

Fixpoint n_strings (n : nat) (L : list nat) : list (list nat) :=
  if le_dec n (length L) then
    match L with
    | [] => [[]]
    | x :: M => firstn n L :: n_strings n M
    end
  else [].

Definition to_bool {P Q : Prop} (x : {P} + {Q}) : bool :=
  if x then true else false.

Definition is_perm (P : list nat) : bool :=
  to_bool (Permutation_dec eq_nat_dec (seq 0 (length P)) P).

Definition is_visited (P : list nat) (Ps : list (list nat)) : bool :=
  to_bool (in_dec (list_eq_dec eq_nat_dec) P Ps).

Definition cycle_complete (P : list nat) (Ps : list (list nat)) : bool :=
  to_bool (incl_dec (list_eq_dec eq_nat_dec) (rotations P) Ps).

Definition genFun (A B : Type) : Type :=
  A -> list A -> B.

Definition testFun (A : Type) : Type :=
  A -> list A -> bool.

Fixpoint assemble {A B : Type} (f : genFun A B) (L : list A) : list B :=
  match L with
  | [] => []
  | x :: M => f x M :: assemble f M
  end.

Definition chosen {A : Type} (f : testFun A) (L : list A) : list A :=
  select (assemble f L) L.

Definition score {A : Type} (f : testFun A) (L : list A) : nat :=
  length (chosen f L).

Definition shift {A B : Type} (f : genFun A B) (x : B) : genFun A B :=
  fun y L =>
    match L with
    | [] => x
    | z :: M => f z M
    end.

Definition test0 (P : list nat) (Ps : list (list nat)) : bool :=
  (is_perm P && negb (is_visited P Ps))%bool.

Definition test1' (P : list nat) (Ps : list (list nat)) : bool :=
  (test0 P Ps && cycle_complete P (P :: Ps))%bool.

Definition test1 : list nat -> list (list nat) -> bool :=
  shift test1' false.

Lemma to_bool_iff :
  forall (P : Prop) (x : {P} + {~ P}), to_bool x = true <-> P.
Proof.
  intuition.
  discriminate.
Qed.

Lemma Permutation_seq_length :
  forall (n : nat) (P : list nat), Permutation (seq 0 n) P -> n = length P.
Proof.
  intros n P H.
  rewrite <- (seq_length n 0).
  apply Permutation_length, H.
Qed.

Lemma Permutation_is_perm :
  forall (n : nat) (P : list nat), Permutation (seq 0 n) P <-> length P = n /\ is_perm P = true.
Proof.
  intros n P.
  unfold is_perm.
  rewrite to_bool_iff.
  split.
  - intro H.
    replace (length P) with n by apply Permutation_seq_length, H.
    tauto.
  - intros [E H].
    subst n.
    trivial.
Qed.

Lemma n_strings_correct :
  forall (n : nat) (L P : list nat),
    In P (n_strings n L) <-> substring P L /\ length P = n.
Proof.
  intros n L P.
  assert (
    forall L', ~ n <= length L' -> (False <-> substring P L' /\ length P = n)
  ) as B.
    intros L' Len.
    split; [tauto|].
    intros [[LH [LT H1]] E].
    apply (f_equal (@length nat)) in H1.
    repeat rewrite app_length in H1.
    omega.
  induction L as [|x L IH]; simpl.
  - destruct (le_dec n 0) as [Len|Len]; [|apply (B []); trivial].
    simpl.
    split.
    + intros [E|F]; [|tauto].
      subst P.
      simpl.
      split; [|omega].
      exists [], [].
      trivial.
    + destruct P; auto with *.
      simpl in *.
      omega.
  - destruct (le_dec n (S (length L))) as [Len|Len]; [|apply B; trivial].
    simpl.
    rewrite IH.
    split.
    + intros [E|[[LH [LT H1]] H2]].
      * subst P.
        rewrite firstn_length.
        rewrite min_l by trivial.
        split; trivial.
        exists [], (skipn n (x :: L)).
        apply firstn_skipn.
      * split; trivial.
        subst L.
        exists (x :: LH), LT.
        trivial.
    + intros [[LH [LT H1]] E].
      subst n.
      destruct LH as [|y LH].
      * left.
        rewrite <- H1.
        simpl.
        apply firstn_correct.
      * right.
        split; trivial.
        exists LH, LT.
        injection H1.
        trivial.
Qed.

Lemma n_strings_length :
  forall (n : nat) (L : list nat), length (n_strings n L) = length L + 1 - n.
Proof.
  intros n L.
  induction L as [|x L IH]; simpl.
  - destruct (le_dec n 0); destruct n; trivial; omega.
  - destruct (le_dec n (S (length L))) as [Len|Len]; destruct n; simpl; omega.
Qed.

Lemma chosen0_correct :
  forall Ps : list (list nat),
    chosen test0 Ps = nub' (list_eq_dec eq_nat_dec) (filter is_perm Ps).
Proof.
  intro Ps.
  rewrite nub'_filter.
  induction Ps as [|P Ps IH]; trivial.
  unfold chosen, test0, is_visited.
  simpl.
  destruct (in_dec (list_eq_dec eq_nat_dec) P Ps);
    simpl;
    rewrite <- IH;
    destruct (is_perm P);
    trivial.
Qed.

Lemma score0_bound :
  forall (n : nat) (L : list nat),
    score test0 (n_strings n L) <= length L + 1 - n.
Proof.
  intros n L.
  unfold score, chosen, test0.
  rewrite select_length, n_strings_length.
  trivial.
Qed.

Lemma score0_final :
  forall (n : nat) (L : list nat),
    all_perms n L -> score test0 (n_strings n L) = fact n.
Proof.
  intros n L H.
  assert (length (permutations (seq 0 n)) = fact n) as F.
    rewrite permutations_length.
    apply f_equal, seq_length.
  rewrite <- F.
  unfold score.
  rewrite chosen0_correct.
  apply Permutation_length, NoDup_Permutation.
  - apply NoDup_nub'.
  - apply NoDup_permutations, NoDup_seq.
  - intro P.
    rewrite in_nub', filter_In, n_strings_correct.
    rewrite permutations_correct, Permutation_is_perm.
    specialize (H P).
    rewrite Permutation_is_perm in H.
    tauto.
Qed.

Lemma chosen1'_complete :
  forall (n : nat) (Ps : list (list nat)) (Q : list nat),
    n >= 1 ->
    Permutation (seq 0 n) Q ->
    incl (rotations Q) Ps ->
      exists k : nat, In (rotate k Q) (chosen test1' Ps).
Proof.
  intros n Ps Q Hn H1 H2.
  assert (length Q > 0) as NZ by (apply Permutation_length in H1; rewrite seq_length in H1; omega).
  induction Ps as [|P Ps IH].
  - assert (In Q []) as H.
    + apply H2, in_rotations; trivial.
      exists 0.
      trivial.
    + apply in_nil in H.
      tauto.
  - unfold chosen.
    simpl.
    destruct (test1' P Ps) eqn:E.
    + destruct (in_dec (list_eq_dec eq_nat_dec) P (rotations Q)) as [I|NI].
      * unfold rotations in I.
        rewrite in_map_iff in I.
        destruct I as [k [I _]].
        exists k.
        simpl.
        auto.
      * apply incl_drop in H2; trivial.
        specialize (IH H2).
        destruct IH as [k IH].
        exists k.
        simpl.
        tauto.
    + apply IH.
      intros R HR.
      pose (H2 R HR) as I.
      destruct I as [E2|I]; trivial.
      subst R.
      unfold rotations in HR.
      rewrite in_map_iff in HR.
      destruct HR as [k [HR _]].
      subst P.
      unfold test1', test0, is_perm, is_visited, cycle_complete in E.
      repeat rewrite Bool.andb_false_iff in E.
      rewrite Bool.negb_false_iff in E.
      repeat rewrite <- Bool.not_true_iff_false in E.
      repeat rewrite to_bool_iff in E.
      repeat rewrite rotate_length in E.
      replace (length Q) with n in E by apply Permutation_seq_length, H1.
      destruct E as [[E|E]|E].
      * contradict E.
        rewrite H1, Permutation_rotate.
        trivial.
      * trivial.
      * contradict E.
        intros R HR.
        apply H2.
        revert HR.
        repeat rewrite in_rotations by (try rewrite rotate_length; trivial).
        intros [m H].
        rewrite rotate_plus in H.
        exists (k + m).
        trivial.
Qed.

Theorem bound0 :
  forall (n : nat) (L : list nat),
    all_perms n L -> length L >= n.
Proof.
  intros n L H.
  assert (substring (seq 0 n) L) as Sub by auto.
  destruct Sub as [LH [LT Sub]].
  apply (f_equal (@length nat)) in Sub.
  repeat rewrite app_length in Sub.
  rewrite seq_length in Sub.
  omega.
Qed.

Theorem bound1 :
  forall (n : nat) (L : list nat),
    all_perms n L -> length L >= fact n + n - 1.
Proof.
  intros n L H.
  rewrite <- (score0_final n L) by trivial.
  pose (score0_bound n L) as IE.
  pose (bound0 n L H) as B0.
  omega.
Qed.
