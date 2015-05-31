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

Fixpoint n_strings (n : nat) (L : list nat) : list (list nat) :=
  if le_dec n (length L) then
    match L with
    | [] => [[]]
    | x :: M => firstn n L :: n_strings n M
    end
  else [].

Definition legal_step (P Q : list nat) : Prop :=
  exists (x y : nat) (L : list nat), P = x :: L /\ Q = L ++ [y].

Fixpoint legal (Ps : list (list nat)) : Prop :=
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
  if (test0 P Ps) then
    match Ps with
    | [] => tail P
    | Q :: Qs => cycle2 Q Qs
    end
  else
    removelast P.

Definition test2 (P : list nat) (Ps : list (list nat)) : bool :=
  let C := cycle2 P Ps in
    to_bool (NoDup_dec eq_nat_dec C)
      && to_bool (incl_dec eq_nat_dec C (seq 0 (length P)))
      && negb (is_visited C (flat_map rotations (assemble cycle2 Ps)))
      && negb (to_bool (empty_dec Ps)).

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
  forall (n : nat) (L P : list nat),
    ~ n <= length L -> (False <-> substring P L /\ length P = n).
Proof.
  intros n L P H.
  split; [tauto|].
  intros [[LH [LT H1]] E].
  apply (f_equal (@length nat)) in H1.
  repeat rewrite app_length in H1.
  omega.
Qed.

Lemma in_n_strings :
  forall (n : nat) (L P : list nat),
    In P (n_strings n L) <-> substring P L /\ length P = n.
Proof.
  intros n L P.
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
  forall (n : nat) (L : list nat), length (n_strings n L) = length L + 1 - n.
Proof.
  intros n L.
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
  forall (n : nat) (L : list nat), n >= 1 -> legal (n_strings n L).
Proof.
  intros n L H.
  induction L as [|x L IH]; simpl.
  - destruct (le_dec n 0) as [K|K]; [omega|apply I].
  - destruct (le_dec n (S (length L))) as [K|K]; [|apply I].
    destruct L as [|y L]; simpl.
    + destruct (le_dec n 0) as [K2|K2]; [omega|trivial].
    + simpl in IH.
      destruct (le_dec n (S (length L))) as [K2|K2]; [|trivial].
      split; [|trivial].
      exists x, (last (firstn n (y :: L)) 0), (removelast (firstn n (y :: L))).
      destruct n as [|n]; [omega|].
      split.
      * rewrite removelast_firstn; trivial.
      * apply app_removelast_last.
        discriminate.
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
  forall (n : nat) (f : testFun (list nat)) (L : list nat),
    score f (n_strings n L) <= length L + 1 - n.
Proof.
  intros n f L.
  unfold score, chosen.
  rewrite select_length, n_strings_length.
  trivial.
Qed.

Lemma legal_step_length :
  forall P Q : list nat, legal_step P Q -> length P = length Q.
Proof.
  intros P Q [x [y [L [HP HQ]]]].
  subst P Q.
  rewrite app_length.
  simpl.
  omega.
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
  forall P Q : list nat, legal_step P Q -> Permutation P Q -> Q = rotate1 P.
Proof.
  intros P Q [x [y [L [HP HQ]]]] HPQ.
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
  rewrite <- (legal_step_length P Q HL) in K1.
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

Lemma cycle2_test0_false :
  forall (P : list nat) (Ps : list (list nat)), test0 P Ps = false -> cycle2 P Ps = removelast P.
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
  rewrite <- rotate_plus, <- H.
  symmetry.
  apply rotate_inv.
Qed.

Lemma cycle2_correct :
  forall (P : list nat) (Ps : list (list nat)),
    P <> [] -> Forall (fun Q => Q <> []) Ps -> legal (P :: Ps) -> cycle2_member P (cycle2 P Ps).
Proof.
  intros P Ps HP HPs HL.
  revert P HP HL.
  induction Ps as [|Q Qs IH]; intros P HP HL; simpl.
  - destruct (test0 P []).
    + apply cycle2_member_tail, HP.
    + apply cycle2_member_removelast, HP.
  - destruct (test0 P (Q :: Qs)) eqn:HTP.
    + inversion HPs as [|Q' Qs' HQ HQs [E1 E2]].
      subst Q' Qs'.
      destruct HL as [HS HL].
      specialize (IH HQs Q HQ HL).
      destruct (test0 Q Qs) eqn:HTQ.
      * apply cycle2_member_rotate1.
        rewrite <- (legal_step_rotate1 _ Q); trivial.
        unfold test0, is_perm in HTP, HTQ.
        autorewrite with bool_to_Prop in HTP, HTQ.
        pose (legal_step_length P Q HS) as EL.
        rewrite <- EL in HTQ.
        apply (perm_trans (l' := (seq 0 (length P)))); intuition.
      * rewrite cycle2_test0_false by trivial.
        destruct HS as [x [y [L [EP EQ]]]].
        subst P Q.
        exists x, 0, 0.
        rewrite removelast_correct.
        trivial.
    + apply cycle2_member_removelast, HP.
Qed.

Lemma andt_tests02 :
  forall (P Q : list nat) (Rs : list (list nat)),
    andt test0 test2 P (Q :: Rs) = false.
Proof.
  intros P Q Rs.
  unfold andt, test2.
  simpl.
  unfold is_visited.
  destruct (test0 P (Q :: Rs)); autorewrite with bool_to_Prop; [|tauto].
  right.
  left.
  right.
  rewrite in_app_iff.
  left.
  apply rotations_self.
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
  pose (score_bound n test0 L) as IE.
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
  rewrite (plus_n_O (score _ _)).
  rewrite <- (score_andt_tests01 n L) by trivial.
  rewrite score_plus.
  rewrite (score_andt_tests01 n L) by trivial.
  apply plus_le_compat.
  - rewrite score0_final; trivial.
  - apply score1_final; trivial.
Qed.
