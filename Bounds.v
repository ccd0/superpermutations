Require Import Omega.
Require Import List.
Require Import Permutation.
Require Import ListTheorems.
Require Import NumPermutations.
Import ListNotations.

Definition substring {A : Type} (L M : list A) :=
  exists LH LT, LH ++ L ++ LT = M.

Definition all_perms (n : nat) (L : list nat) :=
  forall P, Permutation (seq 0 n) P -> substring P L.

Fixpoint n_strings (n : nat) (L : list nat) :=
  if le_dec n (length L) then
    match L with
    | [] => [[]]
    | x :: M => firstn n L :: n_strings n M
    end
  else [].

Definition to_bool {P Q : Prop} (x : {P} + {Q}) :=
  if x then true else false.

Definition is_perm (n : nat) (P : list nat) :=
  to_bool (Permutation_dec eq_nat_dec (seq 0 n) P).

Definition visited (n : nat) (L : list nat) :=
  filter (is_perm n) (n_strings n L).

Definition score0 (n : nat) (Ps : list (list nat)) :=
  length (nub (list_eq_dec eq_nat_dec) Ps).

Lemma to_bool_iff :
  forall (P : Prop) (x : {P} + {~ P}), to_bool x = true <-> P.
Proof.
  intuition.
  discriminate.
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
  + destruct (le_dec n 0) as [Len|Len]; [|apply (B []); trivial].
    simpl.
    split.
    - intros [E|F]; [|tauto].
      subst P.
      simpl.
      split; [|omega].
      exists [], [].
      trivial.
    - destruct P; auto with *.
      simpl in *.
      omega.
  + destruct (le_dec n (S (length L))) as [Len|Len]; [|apply B; trivial].
    simpl.
    rewrite IH.
    split.
    - intros [E|[[LH [LT H1]] H2]].
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
    - intros [[LH [LT H1]] E].
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
  + destruct (le_dec n 0); destruct n; trivial; omega.
  + destruct (le_dec n (S (length L))) as [Len|Len]; destruct n; simpl; omega.
Qed.

Lemma score0_bound :
  forall (n : nat) (L : list nat), score0 n (visited n L) <= length L + 1 - n.
Proof.
  intros n L.
  unfold score0, visited.
  rewrite nub_length, filter_length, n_strings_length.
  trivial.
Qed.

Lemma score0_final :
  forall (n : nat) (L : list nat),
    all_perms n L -> score0 n (visited n L) = fact n.
Proof.
  intros n L H.
  assert (length (permutations (seq 0 n)) = fact n) as F.
    rewrite permutations_length.
    apply f_equal, seq_length.
  rewrite <- F.
  apply Permutation_length, NoDup_Permutation.
  + apply NoDup_nub.
  + apply NoDup_permutations, NoDup_seq.
  + intro P.
    unfold visited, is_perm.
    rewrite permutations_correct, in_nub, filter_In, to_bool_iff, n_strings_correct.
    intuition.
    rewrite <- (seq_length n 0).
    apply Permutation_length.
    auto with *.
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
