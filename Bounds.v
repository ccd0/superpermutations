Require Import Bool.
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

Definition all_perms' (n : nat) (Ps : list (list nat)) : Prop :=
  forall P, Permutation (seq 0 n) P -> In P Ps.

Fixpoint n_strings {A : Type} (n : nat) (L : list A) : list (list A) :=
  if le_dec n (length L) then
    match L with
    | [] => [[]]
    | x :: M => firstn n L :: n_strings n M
    end
  else [].

Definition legal_step {A : Type} (P Q : list A) : Prop :=
  exists (x y : A) (L : list A), P = x :: L /\ Q = L ++ [y].

Fixpoint legal {A : Type} (Ps : list (list A)) : Prop :=
  match Ps with
  | [] => True
  | P :: Qs => match Qs with
    | [] => True
    | Q :: Rs => legal_step P Q /\ legal Qs
    end
  end.

Definition to_bool {P Q : Prop} (x : {P} + {Q}) : bool :=
  if x then true else false.

Definition is_perm (P : list nat) : bool :=
  to_bool (Permutation_dec eq_nat_dec (seq 0 (length P)) P).

Definition is_visited (P : list nat) (Ps : list (list nat)) : bool :=
  to_bool (in_dec (list_eq_dec eq_nat_dec) P Ps).

Definition cycle_complete (P : list nat) (Ps : list (list nat)) : bool :=
  to_bool (incl_dec (list_eq_dec eq_nat_dec) (rotations P) Ps).

Definition cycle2_member (P Q : list nat) : Prop :=
  exists x j k : nat, P = rotate j (x :: rotate k Q).

Definition fill_missing (L : list nat) : list nat :=
  list_diff eq_nat_dec (seq 0 (S (length L))) L ++ L.

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

Definition ort {A : Type} (f g : testFun A) : testFun A :=
  fun x L => f x L || g x L.

Definition andt {A : Type} (f g : testFun A) : testFun A :=
  fun x L => f x L && g x L.

Definition test0 (P : list nat) (Ps : list (list nat)) : bool :=
  is_perm P && negb (is_visited P Ps).

Definition test1' (P : list nat) (Ps : list (list nat)) : bool :=
  test0 P Ps && cycle_complete P (P :: Ps).

Definition test1 : list nat -> list (list nat) -> bool :=
  shift test1' false.

Fixpoint cycle2 (P : list nat) (Ps : list (list nat)) : list nat :=
  if is_perm P then
    match Ps with
    | [] => tail P
    | Q :: Qs => cycle2 Q Qs
    end
  else
    removelast P.

Definition valid_cycle2 (n : nat) (C : list nat) :=
  to_bool (NoDup_dec eq_nat_dec C)
    && to_bool (incl_dec eq_nat_dec C (seq 0 n)).

Definition test2' (P : list nat) (Ps : list (list nat)) : bool :=
  let C := cycle2 P Ps in
    valid_cycle2 (length P) C
      && negb (is_visited C (flat_map rotations (assemble cycle2 Ps))).

Definition test2 (P : list nat) (Ps : list (list nat)) : bool :=
  test2' P Ps && negb (to_bool (empty_dec Ps)).

Definition chosen_cycles2 (Ps : list (list nat)) : list (list nat) :=
  select (assemble test2' Ps) (assemble cycle2 Ps).

Lemma to_bool_iff :
  forall (P : Prop) (x : {P} + {~ P}), to_bool x = true <-> P.
Proof.
  intuition.
  discriminate.
Qed.

Lemma to_bool_false_iff :
  forall (P : Prop) (x : {P} + {~ P}), to_bool x = false <-> ~ P.
Proof.
  intuition.
Qed.

Hint Rewrite
  andb_true_iff andb_false_iff
  orb_true_iff  orb_false_iff
  negb_true_iff negb_false_iff
  to_bool_iff   to_bool_false_iff
  : bool_to_Prop.

Lemma permutations_seq_length :
  forall n : nat, length (permutations (seq 0 n)) = fact n.
Proof.
  intro n.
  rewrite permutations_length, seq_length.
  trivial.
Qed.

Lemma Permutation_seq_length :
  forall (n : nat) (P : list nat), Permutation (seq 0 n) P -> n = length P.
Proof.
  intros n P H.
  rewrite <- (seq_length n 0).
  apply Permutation_length, H.
Qed.

Lemma Permutation_seq_NoDup :
  forall (n : nat) (P : list nat), Permutation (seq 0 n) P -> NoDup P.
Proof.
  intros n P H.
  apply (Permutation_NoDup _ (seq 0 n)); trivial.
  apply NoDup_seq.
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

Lemma in_n_strings1 :
  forall (A : Type) (n : nat) (L P : list A),
    ~ n <= length L -> (False <-> substring P L /\ length P = n).
Proof.
  intros A n L P H.
  split; [tauto|].
  intros [[LH [LT H1]] E].
  apply (f_equal (@length A)) in H1.
  repeat rewrite app_length in H1.
  omega.
Qed.

Lemma in_n_strings :
  forall (A : Type) (n : nat) (L P : list A),
    In P (n_strings n L) <-> substring P L /\ length P = n.
Proof.
  intros A n L P.
  induction L as [|x L IH]; simpl.
  - destruct (le_dec n 0) as [Len|Len]; [|apply in_n_strings1; trivial].
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
  - destruct (le_dec n (S (length L))) as [Len|Len]; [|apply in_n_strings1; trivial].
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
  forall (A : Type) (n : nat) (L : list A), length (n_strings n L) = length L + 1 - n.
Proof.
  intros A n L.
  induction L as [|x L IH]; simpl.
  - destruct (le_dec n 0); destruct n; trivial; omega.
  - destruct (le_dec n (S (length L))) as [Len|Len]; destruct n; simpl; omega.
Qed.

Lemma n_strings_all_perms :
  forall (n : nat) (L : list nat), all_perms n L -> all_perms' n (n_strings n L).
Proof.
  intros n L HL P HP.
  apply in_n_strings.
  split; [auto|].
  apply Permutation_length in HP.
  rewrite seq_length in HP.
  auto.
Qed.

Lemma n_strings_legal :
  forall (A : Type) (n : nat) (L : list A), n >= 1 -> legal (n_strings n L).
Proof.
  intros A n L H.
  induction L as [|x L IH]; simpl.
  - destruct (le_dec n 0) as [K|K]; [omega|apply I].
  - destruct (le_dec n (S (length L))) as [K|K]; [|apply I].
    destruct L as [|y L]; simpl.
    + destruct (le_dec n 0) as [K2|K2]; [omega|trivial].
    + simpl in IH.
      destruct (le_dec n (S (length L))) as [K2|K2]; [|trivial].
      split; [|trivial].
      exists x, (last (firstn n (y :: L)) y), (removelast (firstn n (y :: L))).
      destruct n as [|n]; [omega|].
      split.
      * rewrite removelast_firstn; trivial.
      * apply app_removelast_last.
        discriminate.
Qed.

Lemma legal_app :
  forall (A : Type) (L M : list (list A)), legal (L ++ M) -> legal M.
Proof.
  intros A L M H.
  induction L; trivial.
  simpl in H.
  destruct (L ++ M); tauto.
Qed.

Lemma assemble_app :
  forall (A B : Type) (f : genFun A B) (L M : list A),
    exists N : list B, assemble f (L ++ M) = N ++ assemble f M.
Proof.
  intros A B f L M.
  induction L as [|x L [N IH]]; [exists []; trivial|].
  exists (f x (L ++ M) :: N).
  simpl.
  rewrite IH.
  trivial.
Qed.

Lemma skipn_assemble :
  forall (A B : Type) (f : genFun A B) (k : nat) (L : list A),
    skipn k (assemble f L) = assemble f (skipn k L).
Proof.
  intros A B f k.
  induction k as [|k IH]; intros [|x L]; simpl; trivial.
Qed.

Lemma assemble_length :
  forall (A B : Type) (f : genFun A B) (L : list A),
    length (assemble f L) = length L.
Proof.
  intros A B f L.
  induction L; simpl; auto.
Qed.

Lemma chosen_incl :
  forall (A : Type) (f : testFun A) (Ps : list A),
    incl (chosen f Ps) Ps.
Proof.
  intros.
  apply select_incl.
Qed.

Lemma chosen_imp_incl :
  forall (A : Type) (f g : testFun A) (Ps : list A),
    (forall Q Qs, f Q Qs = true -> g Q Qs = true) ->
      incl (chosen f Ps) (chosen g Ps).
Proof.
  intros A f g Ps H Q.
  induction Ps as [|P Ps IH]; trivial.
  unfold chosen.
  simpl.
  repeat rewrite select_cons, in_app_iff.
  intros [H2|H2]; [|tauto].
  destruct (f P Ps) eqn:E; [|contradict H2].
  apply H in E.
  destruct (g P Ps); [tauto|discriminate].
Qed.

Lemma score_cons :
  forall (A : Type) (f : testFun A) (P : A) (Ps : list A),
    score f (P :: Ps) = (if f P Ps then 1 else 0) + score f Ps.
Proof.
  intros A f P Ps.
  unfold score, chosen, assemble.
  destruct (f P Ps); trivial.
Qed.

Lemma score_plus :
  forall (A : Type) (f g : testFun A) (Ps : list A),
    score (ort f g) Ps + score (andt f g) Ps = score f Ps + score g Ps.
Proof.
  intros A f g Ps.
  induction Ps as [|P Ps IH]; trivial.
  repeat rewrite score_cons.
  rewrite plus_permute_2_in_4, IH.
  unfold ort, andt.
  destruct (f P Ps), (g P Ps); simpl; auto.
Qed.

Lemma score_shift :
  forall (A : Type) (f : testFun A) (P : A) (Ps : list A),
    score (shift f false) (P :: Ps) = score f Ps.
Proof.
  intros A f P Ps.
  revert P.
  induction Ps as [|Q Qs IH]; trivial.
  intro P.
  rewrite score_cons, (score_cons _ f).
  simpl.
  f_equal.
  trivial.
Qed.

Lemma score_bound :
  forall (A : Type) (n : nat) (f : testFun (list A)) (L : list A),
    score f (n_strings n L) <= length L + 1 - n.
Proof.
  intros A n f L.
  unfold score, chosen.
  rewrite select_length, n_strings_length.
  trivial.
Qed.

Lemma legal_step_length :
  forall (A : Type) (P Q : list A), legal_step P Q -> length P = length Q.
Proof.
  intros A P Q [x [y [L [HP HQ]]]].
  subst P Q.
  rewrite app_length.
  simpl.
  omega.
Qed.

Lemma legal_length :
  forall (A : Type) (n : nat) (P : list A) (Ps : (list (list A))),
    legal (P :: Ps) -> length P = n ->
      forall Q : list A, In Q Ps -> length Q = n.
Proof.
  intros A n P Ps.
  revert P.
  induction Ps as [|R Rs IH]; intros P H1 H2 Q H3.
  - simpl in H3.
    tauto.
  - destruct H3 as [H3|H3].
    + subst R.
      simpl in H1.
      rewrite <- (legal_step_length _ P); tauto.
    + apply (IH R).
      * apply (legal_app _ [P]), H1.
      * simpl in H1.
        rewrite <- (legal_step_length _ P); tauto.
      * trivial.
Qed.

Lemma legal_nonempty :
  forall (A : Type) (P : list A) (Ps : (list (list A))),
    P <> [] -> legal (P :: Ps) -> Forall (fun Q => Q <> []) Ps.
Proof.
  intros A P Ps.
  revert P.
  induction Ps as [|Q Qs IH]; trivial.
  intros P HP [H1 H2].
  assert (Q <> []) as N.
  - rewrite nonempty_length in *.
    rewrite <- (legal_step_length _ P Q); trivial.
  - constructor 2; trivial.
    apply (IH Q); trivial.
Qed.

Lemma forced_rotate :
  forall (A : Type) (x y : A) (L : list A),
    Permutation (x :: L) (L ++ [y]) -> x = y.
Proof.
  intros A x y L H.
  rewrite <- Permutation_cons_append in H.
  change (Permutation ([x] ++ L) ([y] ++ L)) in H.
  apply Permutation_app_inv_r, Permutation_length_1 in H.
  trivial.
Qed.

Lemma legal_step_rotate1 :
  forall (A : Type) (P Q : list A), legal_step P Q -> Permutation P Q -> Q = rotate1 P.
Proof.
  intros A P Q [x [y [L [HP HQ]]]] HPQ.
  subst P Q.
  apply forced_rotate in HPQ.
  subst y.
  trivial.
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

Lemma score0_final :
  forall (n : nat) (L : list nat),
    all_perms n L -> score test0 (n_strings n L) = fact n.
Proof.
  intros n L H.
  unfold score.
  rewrite <- permutations_seq_length, chosen0_correct.
  apply Permutation_length, NoDup_Permutation.
  - apply NoDup_nub'.
  - apply NoDup_permutations, NoDup_seq.
  - intro P.
    rewrite in_nub', filter_In, in_n_strings.
    rewrite in_permutations, Permutation_is_perm.
    specialize (H P).
    rewrite Permutation_is_perm in H.
    tauto.
Qed.

Lemma chosen0_chosen1' :
  forall Ps : list (list nat), incl (chosen test1' Ps) (chosen test0 Ps).
Proof.
  intro Ps.
  apply chosen_imp_incl.
  unfold test1'.
  intros Q Qs.
  rewrite andb_true_iff.
  tauto.
Qed.

Lemma chosen1'_complete1 :
  forall (n : nat) (Ps : list (list nat)) (Q : list nat),
    Permutation (seq 0 n) Q ->
    incl (rotations Q) Ps ->
      exists k : nat, In (rotate k Q) (chosen test1' Ps).
Proof.
  intros n Ps Q H1 H2.
  induction Ps as [|P Ps IH].
  - assert (~ In Q []) as H by apply in_nil.
    contradict H.
    apply H2, rotations_self.
  - unfold chosen.
    simpl.
    destruct (test1' P Ps) eqn:E.
    + destruct (in_dec (list_eq_dec eq_nat_dec) P (rotations Q)) as [I|NI].
      * rewrite in_rotations in I.
        destruct I as [k I].
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
      rewrite in_rotations in HR.
      destruct HR as [k HR].
      subst P.
      unfold test1', test0, is_perm, is_visited, cycle_complete in E.
      autorewrite with bool_to_Prop in E.
      repeat rewrite rotate_length in E.
      replace (length Q) with n in E by apply Permutation_seq_length, H1.
      destruct E as [[E|E]|E].
      * contradict E.
        rewrite H1, Permutation_rotate.
        trivial.
      * trivial.
      * contradict E.
        revert H2.
        apply incl_tran.
        rewrite rotations_rotate.
        intro R.
        apply Permutation_in, Permutation_rotate.
Qed.

Lemma chosen1'_complete2 :
  forall (n : nat) (Ps : list (list nat)),
    all_perms' n Ps -> all_perms' n (flat_map rotations (chosen test1' Ps)).
Proof.
  intros n Ps HPs Q HQ.
  apply in_flat_map.
  assert (exists k : nat, In (rotate k Q) (chosen test1' Ps)) as [k I].
  - apply (chosen1'_complete1 n); trivial.
    intros R HR.
    apply HPs.
    apply Permutation_rotations in HR.
    rewrite HR.
    trivial.
  - exists (rotate k Q).
    split; trivial.
    apply in_rotations_rotate.
Qed.

Lemma score1'_final :
  forall (n : nat) (L : list nat),
    n >= 1 -> all_perms n L -> score test1' (n_strings n L) >= fact (n - 1).
Proof.
  intros n L Hn HL.
  set (Ps := n_strings n L).
  apply (mult_S_le_reg_l (n - 1)).
  change (fact (S (n - 1)) <= S (n - 1) * score test1' Ps).
  replace (S (n - 1)) with n by omega.
  rewrite <- permutations_seq_length.
  unfold score.
  rewrite <- (flat_map_length _ _ rotations).
  - apply NoDup_incl_lel.
    + apply NoDup_permutations, NoDup_seq.
    + intro Q.
      rewrite in_permutations.
      apply chosen1'_complete2; trivial.
      apply n_strings_all_perms.
      trivial.
  - intros Q HQ.
    rewrite rotations_length.
    replace (length Q) with n.
    + apply max_r.
      trivial.
    + apply chosen_incl, in_n_strings in HQ.
      omega.
Qed.

Lemma score1_final :
  forall (n : nat) (L : list nat),
    n >= 1 -> all_perms n L -> score test1 (n_strings n L) >= fact (n - 1) - 1.
Proof.
  intros n L Hn HL.
  apply (plus_le_reg_l _ _ 1).
  rewrite <- le_plus_minus by apply lt_O_fact.
  apply (le_trans _ (score test1' (n_strings n L))); [apply score1'_final; trivial|].
  set (Ps := n_strings n L).
  destruct Ps as [|P Ps]; auto.
  unfold test1.
  rewrite score_shift, score_cons.
  destruct (test1' P Ps); auto.
Qed.

Lemma andt_tests01 :
  forall (P Q : list nat) (Rs : list (list nat)),
    legal_step P Q -> andt test0 test1 P (Q :: Rs) = false.
Proof.
  intros P Q Rs HL.
  unfold andt.
  destruct (test0 P (Q :: Rs)) eqn:H; [|tauto].
  destruct (test1 P (Q :: Rs)) eqn:K; [|tauto].
  unfold test1, shift, test1', test0, is_perm, is_visited, cycle_complete in H, K.
  autorewrite with bool_to_Prop in H, K.
  destruct H as [H1 H2].
  destruct K as [[K1 _] K2].
  rewrite <- (legal_step_length _ P Q HL) in K1.
  rewrite H1 in K1.
  apply legal_step_rotate1 in K1; [|trivial].
  contradict H2.
  apply K2.
  subst Q.
  change (In P (rotations (rotate 1 P))).
  apply in_rotations_rotate.
Qed.

Lemma score_andt_tests01 :
  forall (n : nat) (L : list nat), n >= 1 -> score (andt test0 test1) (n_strings n L) = 0.
Proof.
  intros n L Hn.
  set (Ps := n_strings n L).
  assert (legal Ps) as HL by apply n_strings_legal, Hn.
  induction Ps as [|P Qs IH]; trivial.
  destruct Qs as [|Q Rs].
  - rewrite score_cons.
    unfold andt, test1, shift.
    destruct (test0 P []); trivial.
  - rewrite score_cons.
    destruct HL as [HS HL].
    rewrite andt_tests01 by trivial.
    tauto.
Qed.

Lemma score01_final :
  forall (n : nat) (L : list nat),
    n >= 1 ->
    all_perms n L ->
      score (ort test0 test1) (n_strings n L) >= fact n + (fact (n - 1) - 1).
Proof.
  intros n L H Hn.
  rewrite (plus_n_O (score _ _)).
  rewrite <- (score_andt_tests01 n L) by trivial.
  rewrite score_plus.
  rewrite (score_andt_tests01 n L) by trivial.
  apply plus_le_compat.
  - rewrite score0_final; trivial.
  - apply score1_final; trivial.
Qed.

Lemma cycle2_is_perm_false :
  forall (P : list nat) (Ps : list (list nat)), is_perm P = false -> cycle2 P Ps = removelast P.
Proof.
  intros P Ps H.
  destruct Ps; simpl; rewrite H; trivial.
Qed.

Lemma cycle2_member_tail :
  forall P : list nat, P <> [] -> cycle2_member P (tail P).
Proof.
  intros P H.
  destruct P as [|x P]; [tauto|].
  exists x, 0, 0.
  trivial.
Qed.

Lemma cycle2_member_removelast :
  forall P : list nat, P <> [] -> cycle2_member P (removelast P).
Proof.
  intros P H.
  set (Q := removelast P).
  rewrite (@app_removelast_last _ P 0) by trivial.
  exists (last P 0), 1, 0.
  trivial.
Qed.

Lemma cycle2_member_rotate1 :
  forall P Q : list nat, cycle2_member (rotate1 P) Q -> cycle2_member P Q.
Proof.
  intros P Q [x [j [k H]]].
  exists x, (j + rotate_neg 1 (length P)), k.
  rewrite rotate_plus, <- H.
  symmetry.
  apply rotate_inv.
Qed.

Lemma cycle2_correct :
  forall (P : list nat) (Ps : list (list nat)),
    P <> [] -> legal (P :: Ps) -> cycle2_member P (cycle2 P Ps).
Proof.
  intros P Ps HP HL.
  assert (Forall (fun Q => Q <> []) Ps) as HPs by (revert HP HL; apply legal_nonempty).
  revert P HP HL.
  induction Ps as [|Q Qs IH]; intros P HP HL; simpl.
  - destruct (is_perm P).
    + apply cycle2_member_tail, HP.
    + apply cycle2_member_removelast, HP.
  - destruct (is_perm P) eqn:HTP.
    + inversion HPs as [|Q' Qs' HQ HQs [E1 E2]].
      subst Q' Qs'.
      destruct HL as [HS HL].
      specialize (IH HQs Q HQ HL).
      destruct (is_perm Q) eqn:HTQ.
      * apply cycle2_member_rotate1.
        rewrite <- (legal_step_rotate1 _ _ Q); trivial.
        unfold is_perm in HTP, HTQ.
        autorewrite with bool_to_Prop in HTP, HTQ.
        pose (legal_step_length _ P Q HS) as EL.
        rewrite <- EL in HTQ.
        apply (perm_trans (l' := (seq 0 (length P)))); auto with *.
      * rewrite cycle2_is_perm_false by trivial.
        destruct HS as [x [y [L [EP EQ]]]].
        subst P Q.
        exists x, 0, 0.
        rewrite removelast_correct.
        trivial.
    + apply cycle2_member_removelast, HP.
Qed.

Lemma fill_missing_correct :
  forall (n x : nat) (L : list nat),
    Permutation (seq 0 n) (x :: L) -> x :: L = fill_missing L.
Proof.
  intros n x L H.
  unfold fill_missing.
  fold ([x] ++ L).
  apply (f_equal (fun M => M ++ L)).
  symmetry.
  apply Permutation_length_1_inv, Permutation_list_diff.
  rewrite <- Permutation_cons_append, <- H.
  apply Permutation_length in H.
  simpl in H.
  rewrite <- H, seq_length.
  trivial.
Qed.

Lemma valid_cycle2_Permutation :
  forall (n j k x : nat) (P C : list nat),
    Permutation (seq 0 n) P ->
    P = rotate j (x :: rotate k C) ->
      valid_cycle2 n C = true.
Proof.
  intros n j k x P Q H E.
  unfold valid_cycle2.
  autorewrite with bool_to_Prop.
  split.
  - apply (NoDup_rotate _ k).
    assert (NoDup P) as ND by apply (Permutation_seq_NoDup n), H.
    rewrite E in ND.
    apply NoDup_rotate in ND.
    inversion ND.
    trivial.
  - intros y Hy.
    apply (@Permutation_in _ P); [auto with *|].
    rewrite E.
    apply in_rotate.
    right.
    apply in_rotate.
    trivial.
Qed.

Lemma valid_cycle2_rotate :
  forall (n k : nat) (C : list nat),
    valid_cycle2 n (rotate k C) = true <-> valid_cycle2 n C = true.
Proof.
  intros n k C.
  unfold valid_cycle2.
  autorewrite with bool_to_Prop.
  rewrite <- NoDup_rotate.
  rewrite (Permutation_incl_left _ _ C) by apply Permutation_rotate.
  tauto.
Qed.

Lemma chosen_cycles2_complete1 :
  forall (n : nat) (P : list nat) (Qs : list (list nat)),
    Permutation (seq 0 n) P ->
    P <> [] ->
    legal (P :: Qs) -> 
    In (cycle2 P Qs) (flat_map rotations (assemble cycle2 Qs)) ->
    In P (flat_map rotations (map fill_missing (flat_map rotations (chosen_cycles2 Qs)))).
Proof.
  intros n P Qs H1 H2 H3 H4.
  destruct (cycle2_correct _ _ H2 H3) as [x [j [k E]]].
  assert (length P = n) as HL by (symmetry; apply Permutation_seq_length, H1).
  apply in_flat_map.
  exists (x :: rotate k (cycle2 P Qs)).
  split; [|apply in_rotations; exists j; trivial].
  apply in_map_iff.
  exists (rotate k (cycle2 P Qs)).
  rewrite (fill_missing_correct n) by (
    rewrite <- (Permutation_rotate _ j (x :: rotate k (cycle2 P Qs))), <- E; trivial
  ).
  split; trivial.
  apply in_flat_map in H4.
  destruct H4 as [C [H5 H6]].
  apply in_flat_map.
  apply in_rotations in H6.
  destruct H6 as [m H6].
  set (Bs :=
    map
      (fun C' => to_bool (in_dec (list_eq_dec eq_nat_dec) C' (rotations C)))
      (assemble cycle2 Qs)
  ).
  assert (In true Bs) as HB by (
    apply in_map_iff;
    exists C;
    rewrite to_bool_iff;
    split; [apply rotations_self|trivial]
  ).
  destruct (search_last bool_dec true Bs) as [[Bs1 [Bs2 [H7 H8]]]|HN]; [|tauto].
  apply (f_equal (skipn (length Bs1))) in H7.
  unfold Bs in H7.
  rewrite skipn_map, skipn_assemble, skipn_correct in H7.
  set (Rs := skipn (length Bs1) Qs) in *.
  destruct Rs as [|R Ss] eqn:ER; simpl in H7; [discriminate|].
  exists (cycle2 R Ss).
  injection H7 as H10 H9.
  rewrite <- H9, in_map_iff in H8.
  rewrite to_bool_iff, in_rotations in H10.
  destruct H10 as [i H10].
  split.
  - unfold chosen_cycles2.
    rewrite (in_select _ _ []).
    exists (length Bs1).
    repeat rewrite nth_skipn, skipn_assemble.
    fold Rs.
    rewrite ER.
    simpl.
    unfold test2', is_visited.
    autorewrite with bool_to_Prop.
    repeat split.
    + rewrite (legal_length _ n P Qs); trivial.
      * rewrite H10, valid_cycle2_rotate, <- (valid_cycle2_rotate _ m), <- H6.
        apply (valid_cycle2_Permutation n j k x P); trivial.
      * rewrite <- (firstn_skipn (length Bs1)).
        fold Rs.
        rewrite ER.
        auto with *.
    + contradict H8.
      apply in_flat_map in H8.
      destruct H8 as [C' [H11 H12]].
      exists C'.
      rewrite to_bool_iff.
      split; trivial.
      apply in_rotations in H12.
      destruct H12 as [h H12].
      apply rotate_move in H12.
      rewrite H12, H10, <- rotate_plus.
      apply in_rotations.
      exists (i + rotate_neg h (length C')).
      auto.
    + assert (length Rs = length Qs - length Bs1) as H13 by apply skipn_length.
      rewrite ER in H13.
      simpl in H13.
      rewrite assemble_length.
      omega.
  - apply in_rotations.
    apply rotate_move in H10.
    rewrite H6, H10.
    repeat rewrite <- rotate_plus.
    exists (rotate_neg i (length C) + (m + k)).
    trivial.
Qed.

Lemma chosen_cycles2_complete :
  forall (n : nat) (Ps : list (list nat)),
    n >= 1 ->
    legal Ps ->
    all_perms' n Ps ->
    all_perms' n (
      flat_map rotations (map fill_missing (flat_map rotations (chosen_cycles2 Ps)))
    ).
Proof.
  intros n Ps Hn HL HA P HP.
  specialize (HA P HP).
  unfold chosen_cycles2.
  induction Ps as [|Q Qs IH]; trivial.
  destruct HA as [HA|HA].
  - subst Q.
    simpl.
    assert (P <> []) as N by (apply nonempty_length; apply Permutation_seq_length in HP; omega).
    destruct (cycle2_correct _ _ N HL) as [x [j [k E]]].
    destruct (test2' P Qs) eqn:HT.
    + apply in_flat_map.
      exists (x :: rotate k (cycle2 P Qs)).
      split.
      * apply in_map_iff.
        exists (rotate k (cycle2 P Qs)).
        rewrite (fill_missing_correct n) by (
          rewrite <- (Permutation_rotate _ j (x :: rotate k (cycle2 P Qs))), <- E; trivial
        ).
        split; trivial.
        unfold chosen_cycles2.
        simpl.
        rewrite in_app_iff, in_rotations.
        left.
        exists k.
        trivial.
      * apply in_rotations.
        exists j.
        trivial.
    + unfold test2', is_visited in HT.
      autorewrite with bool_to_Prop in HT.
      destruct HT as [HT|HT].
      * contradict HT.
        apply not_false_iff_true.
        rewrite <- (Permutation_seq_length n P) by trivial.
        apply (valid_cycle2_Permutation n j k x P); trivial.
      * rewrite select_cons.
        apply (chosen_cycles2_complete1 n); trivial.
  - simpl.
    rewrite select_cons, flat_map_app, map_app, flat_map_app, in_app_iff.
    right.
    apply IH; trivial.
    apply (legal_app _ [Q]), HL.
Qed.

Lemma cycle2_length :
  forall (n : nat) (P : list nat) (Ps : list (list nat)),
    (forall Q : list nat, In Q (P :: Ps) -> length Q = n) -> length (cycle2 P Ps) = n - 1.
Proof.
  intros n P Ps.
  revert P.
  induction Ps as [|Q Qs IH]; simpl; intros R H; destruct (is_perm R).
  - rewrite tail_length, H; tauto.
  - rewrite removelast_length, H; tauto.
  - rewrite IH; auto.
  - rewrite removelast_length, H; tauto.
Qed.

Lemma chosen_cycles2_length :
  forall (n : nat) (C : list nat) (Ps : list (list nat)),
    (forall P, In P Ps -> length P = n) ->
    In C (chosen_cycles2 Ps) ->
      length C = n - 1.
Proof.
  intros n C Ps HPs.
  unfold chosen_cycles2.
  rewrite (in_select _ _ []).
  intros [k [H2 [H _]]].
  rewrite nth_skipn, skipn_assemble in H, H2.
  destruct (skipn k Ps) as [|Q Qs] eqn:E; [discriminate|].
  simpl in H.
  subst C.
  rewrite (cycle2_length n); trivial.
  rewrite <- E.
  intros R HR.
  apply skipn_incl in HR.
  auto.
Qed.

Lemma valid_cycle2_fill_missing_length :
  forall (n : nat) (C : list nat),
    n >= 1 ->
    valid_cycle2 n C = true ->
    length C = n - 1 ->
      length (fill_missing C) = n.
Proof.
  intros n C Hn HV HL.
  unfold valid_cycle2 in HV.
  autorewrite with bool_to_Prop in HV.
  unfold fill_missing.
  rewrite app_length.
  rewrite HL.
  replace (S (n - 1)) with n by omega.
  rewrite list_diff_NoDup_length by tauto.
  rewrite HL, seq_length.
  omega.
Qed.

Lemma mapped_cycles2_length :
  forall (n : nat) (Q : list nat) (Ps : list (list nat)),
    n >= 1 ->
    (forall P, In P Ps -> length P = n) ->
    In Q (map fill_missing (flat_map rotations (chosen_cycles2 Ps))) ->
      length Q = n.
Proof.
  intros n Q Ps Hn HPs.
  rewrite in_map_iff.
  intros [C [E H]].
  subst Q.
  rewrite in_flat_map in H.
  destruct H as [C' [H H2]].
  apply in_rotations in H2.
  destruct H2 as [m HR].
  apply valid_cycle2_fill_missing_length; trivial.
  - unfold chosen_cycles2, test2' in H.
    rewrite (in_select _ _ []) in H.
    destruct H as [k [H [E _]]].
    rewrite nth_skipn, skipn_assemble in H, E.
    destruct (skipn k Ps) as [|Q Qs] eqn:E2; auto with *.
    simpl in H, E.
    autorewrite with bool_to_Prop in H.
    rewrite HPs in H by (apply (skipn_incl _ k); rewrite E2; auto with *).
    rewrite HR, valid_cycle2_rotate, <- E.
    tauto.
  - rewrite HR, rotate_length.
    apply (chosen_cycles2_length n C' Ps); trivial.
Qed.

Lemma score2'_final :
  forall (n : nat) (L : list nat),
    n >= 2 -> all_perms n L -> score test2' (n_strings n L) >= fact (n - 2).
Proof.
  intros n L Hn HL.
  set (Ps := n_strings n L).
  assert (forall P, In P Ps -> length P = n) as HPs by apply in_n_strings.
  apply (mult_S_le_reg_l (n - 2)), (mult_S_le_reg_l (S (n - 2))).
  change (fact (S (S (n - 2))) <= S (S (n - 2)) * (S (n - 2) * score test2' Ps)).
  replace (S (n - 2)) with (n - 1) by omega.
  replace (S (n - 1)) with n by omega.
  rewrite <- permutations_seq_length.
  unfold score, chosen.
  rewrite (select_length_equal _ _ _ (assemble cycle2 Ps)) by (symmetry; apply assemble_length).
  fold (chosen_cycles2 Ps).
  rewrite <- (flat_map_length _ _ rotations) by (
    intros C H; rewrite rotations_length, (chosen_cycles2_length n C Ps); auto with *
  ).
  rewrite <- (map_length fill_missing (flat_map rotations (chosen_cycles2 Ps))).
  rewrite <- (flat_map_length _ _ rotations) by (
    intros C H; rewrite rotations_length, (mapped_cycles2_length n C Ps); auto with *
  ).
  apply NoDup_incl_lel; [apply NoDup_permutations, NoDup_seq|].
  unfold incl.
  intro P.
  rewrite in_permutations.
  apply chosen_cycles2_complete.
  - omega.
  - apply n_strings_legal.
    omega.
  - apply n_strings_all_perms, HL.
Qed.

Lemma score2_score2' :
  forall (Ps : list (list nat)),
    score test2 Ps >= score test2' Ps - 1.
Proof.
  intro Ps.
  unfold test2.
  induction Ps as [|P Ps IH]; auto.
  repeat rewrite score_cons.
  destruct (test2' P Ps); trivial.
  destruct (empty_dec Ps) as [H|H]; simpl.
  - subst Ps.
    trivial.
  - omega.
Qed.

Lemma score2_final :
  forall (n : nat) (L : list nat),
    n >= 2 -> all_perms n L -> score test2 (n_strings n L) >= fact (n - 2) - 1.
Proof.
  intros n L Hn HL.
  apply (le_trans _ (score test2' (n_strings n L) - 1)).
  - apply minus_le_compat_r, score2'_final; trivial.
  - apply score2_score2'.
Qed.

Lemma test2_is_perm_false :
  forall (P : list nat) (Qs : list (list nat)),
    test2 P Qs = true -> is_perm P = false.
Proof.
  intros P Qs H.
  unfold test2, test2' in H.
  destruct Qs as [|Q Rs]; simpl in H.
  - rewrite andb_false_r in H.
    discriminate.
  - destruct (is_perm P); trivial.
    unfold is_visited in H.
    autorewrite with bool_to_Prop in H.
    destruct H as [[_ H] _].
    contradict H.
    apply in_or_app.
    left.
    apply rotations_self.
Qed.

Lemma andt_tests02 :
  forall (P : list nat) (Qs : list (list nat)),
    andt test0 test2 P Qs = false.
Proof.
  intros P [|Q Rs].
  - unfold andt, test2.
    repeat rewrite andb_false_r.
    trivial.
  - unfold andt, test0.
    destruct (test2 P (Q :: Rs)) eqn:E; autorewrite with bool_to_Prop; [|tauto].
    apply test2_is_perm_false in E.
    tauto.
Qed.

Lemma cycle1_entry :
  forall (x : nat) (L : list nat) (Ps Qs : list (list nat)),
    test1' (L ++ [x]) (Ps ++ (x :: L) :: Qs) = true ->
    is_perm (x :: L) = true ->
    legal ((x :: L) :: Qs) ->
      cycle2 (x :: L) Qs = L.
Proof.
  intros x L Ps Qs H1 H2 H3.
  destruct Qs as [|Q Qs]; simpl; rewrite H2; [trivial|].
  rewrite cycle2_is_perm_false.
  - destruct H3 as [[y [z [M [E1 E2]]]] _].
    injection E1 as E3 E4.
    subst M y Q.
    apply removelast_correct.
  - destruct (is_perm Q) eqn:H4; trivial.
    replace Q with (L ++ [x]) in H1.
    + unfold test1', test0, is_visited in H1.
      autorewrite with bool_to_Prop in H1.
      destruct H1 as [[_ H1] _].
      contradict H1.
      auto with *.
    + symmetry.
      change (Q = rotate1 (x :: L)).
      destruct H3 as [H3 _].
      apply legal_step_rotate1; trivial.
      unfold is_perm in H2, H4.
      autorewrite with bool_to_Prop in H2, H4.
      apply legal_step_length in H3.
      rewrite <- H3, H2 in H4.
      trivial.
Qed.

Lemma old_cycle2 :
  forall (x : nat) (L : list nat) (Ps : list (list nat)),
    test1' (L ++ [x]) Ps = true -> legal Ps -> L <> [] -> In L (assemble cycle2 Ps).
Proof.
  intros x L Ps H1 H2 HN.
  assert (H1a := H1).
  unfold test1', test0, is_perm, is_visited, cycle_complete in H1a.
  autorewrite with bool_to_Prop in H1a.
  destruct H1a as [[H1a H1b] H1c].
  destruct (search_last (list_eq_dec eq_nat_dec) (x :: L) Ps) as [[Qs [Rs [H3 H4]]]|H3].
  - subst Ps.
    destruct (assemble_app _ _ cycle2 Qs ((x :: L) :: Rs)) as [N E].
    rewrite E.
    apply in_or_app.
    right.
    left.
    apply (cycle1_entry _ _ Qs).
    + trivial.
    + unfold is_perm, is_visited.
      autorewrite with bool_to_Prop.
      rewrite <- rotate1_length, H1a.
      symmetry.
      apply Permutation_cons_append.
    + revert H2.
      apply legal_app.
  - contradict H3.
    assert (In (x :: L) (rotations (rotate 1 (x :: L)))) as H4 by apply in_rotations_rotate.
    specialize (H1c (x :: L) H4).
    destruct H1c as [H1c|H1c]; trivial.
    apply Permutation_seq_NoDup in H1a.
    rewrite H1c in H1a.
    destruct L as [|y L].
    * tauto.
    * injection H1c as E1 E2.
      subst y.
      inversion H1a.
      simpl in *.
      tauto.
Qed.

Lemma andt_tests12 :
  forall (P : list nat) (Qs : list (list nat)),
    legal (P :: Qs) -> length P >= 2 -> andt test1 test2 P Qs = false.
Proof.
  intros P [|Q Rs] HL Hn; trivial.
  unfold andt.
  destruct (test2 P (Q :: Rs)) eqn:H2; [|apply andb_false_r].
  assert (is_perm P = false) as H0' by (revert H2; apply test2_is_perm_false).
  unfold test2, test2', valid_cycle2, is_visited in H2.
  autorewrite with bool_to_Prop in H2.
  destruct H2 as [[[H21 H22] H23] _].
  simpl in H21, H22, H23.
  destruct (is_perm P) eqn:H0; [discriminate|].
  rewrite andb_true_r.
  apply not_true_is_false.
  unfold test1.
  simpl.
  contradict H23.
  destruct HL as [[x [y [L [E1 E2]]]] HL].
  subst P Q.
  assert (L <> []) as HN by (apply nonempty_length; auto with *).
  apply in_or_app.
  right.
  apply in_flat_map.
  exists L.
  split.
  - apply (old_cycle2 y); trivial.
    apply (legal_app _ [L ++ [y]]), HL.
  - assert (L = removelast L ++ [last L 0]) as E by apply app_removelast_last, HN.
    set (M := removelast L) in E.
    set (z := last L 0) in E.
    rewrite E in *.
    replace (removelast (x :: M ++ [z])) with (x :: M) in * by (
      symmetry; apply (removelast_correct _ z (x :: M))
    ).
    destruct (eq_nat_dec x z) as [Hxz|Hxz].
    + rewrite <- Hxz.
      change (In (x :: M) (rotations (rotate 1 (x :: M)))).
      apply in_rotations_rotate.
    + apply not_true_iff_false in H0.
      contradict H0.
      unfold is_perm.
      rewrite to_bool_iff.
      unfold test1', test0, is_perm in H23.
      autorewrite with bool_to_Prop in H23.
      destruct H23 as [[H23 _] _].
      symmetry.
      apply NoDup_incl_Permutation.
      * change (NoDup ((x :: M) ++ [z])).
        apply NoDup_app; [trivial|apply NoDup_singleton|].
        intros w [K1 [K2|]]; trivial.
        destruct K1 as [K1|K1]; [omega|].
        subst w.
        apply Permutation_seq_NoDup in H23.
        apply NoDup_remove_1 in H23.
        rewrite app_nil_r in H23.
        assert (Permutation (z :: M) (M ++ [z])) as HP by apply Permutation_cons_append.
        symmetry in HP.
        apply (Permutation_NoDup _ _ (z :: M)) in H23; [|trivial].
        inversion H23.
        tauto.
      * intros w K.
        change (In w ((x :: M) ++ [z])) in K.
        rewrite in_app_iff in K.
        destruct K as [K|K]; [apply H22, K|].
        simpl in K.
        destruct K as [K|K]; [|tauto].
        subst w.
        symmetry in H23.
        rewrite app_length, plus_comm in H23.
        change (Permutation ((M ++ [z]) ++ [y]) (seq 0 (length (x :: M ++ [z])))) in H23.
        apply (Permutation_in _ H23).
        auto with *.
      * rewrite seq_length.
        trivial.
Qed.

Lemma andt_tests012 :
  forall (P : list nat) (Qs : list (list nat)),
    legal (P :: Qs) -> length P >= 2 -> andt (ort test0 test1) test2 P Qs = false.
Proof.
  intros P Qs HL Hn.
  unfold andt, ort.
  rewrite andb_orb_distrib_l.
  fold (andt test0 test2 P Qs).
  fold (andt test1 test2 P Qs).
  rewrite andt_tests02, andt_tests12; trivial.
Qed.

Lemma score_andt_tests012 :
  forall (n : nat) (L : list nat),
    n >= 2 -> score (andt (ort test0 test1) test2) (n_strings n L) = 0.
Proof.
  intros n L Hn.
  set (Ps := n_strings n L).
  assert (legal Ps) as HL by (apply n_strings_legal; omega).
  assert (Forall (fun P => length P = n) Ps) as Hn' by (
    apply Forall_forall; intros P H; apply in_n_strings in H; tauto
  ).
  induction Ps as [|P Qs IH]; trivial.
  rewrite score_cons.
  rewrite andt_tests012.
  - apply IH.
    + apply (legal_app _ [P]), HL.
    + inversion Hn'.
      trivial.
  - apply HL.
  - rewrite Forall_forall in Hn'.
    rewrite Hn'; auto with *.
Qed.

Lemma score012_final :
  forall (n : nat) (L : list nat),
    n >= 2 ->
    all_perms n L ->
      score (ort (ort test0 test1) test2) (n_strings n L)
        >= fact n + (fact (n - 1) - 1) + (fact (n - 2) - 1).
Proof.
  intros n L H Hn.
  rewrite (plus_n_O (score _ _)).
  rewrite <- (score_andt_tests012 n L) by trivial.
  rewrite score_plus.
  rewrite (score_andt_tests012 n L) by trivial.
  apply plus_le_compat; [|apply score2_final; trivial].
  apply score01_final; trivial.
  omega.
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
  pose (score_bound _ n test0 L) as IE.
  pose (bound0 n L H) as B0.
  omega.
Qed.

Theorem bound2 :
  forall (n : nat) (L : list nat),
    all_perms n L -> n >= 1 -> length L >= fact n + fact (n - 1) + n - 2.
Proof.
  intros n L H Hn.
  assert (fact n + (fact (n - 1) - 1) <= length L + 1 - n); [|pose (bound0 n L H); omega].
  apply (le_trans _ (score (ort test0 test1) (n_strings n L))); [|apply score_bound].
  apply score01_final; trivial.
Qed.

Theorem bound3 :
  forall (n : nat) (L : list nat),
    all_perms n L -> n >= 2 -> length L >= fact n + fact (n - 1) + fact (n - 2) + n - 3.
Proof.
  intros n L H Hn.
  assert (fact n + (fact (n - 1) - 1) + (fact (n - 2) - 1) <= length L + 1 - n);
    [|pose (bound0 n L H); omega].
  apply (le_trans _ (score (ort (ort test0 test1) test2) (n_strings n L))); [|apply score_bound].
  apply score012_final; trivial.
Qed.
