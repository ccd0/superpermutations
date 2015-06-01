Require Import Omega.
Require Import List.
Require Import Permutation.
Import ListNotations.

Definition injective {A B : Type} (L : list A) (f : A -> B) : Prop :=
  forall x1 x2, In x1 L -> In x2 L -> f x1 = f x2 -> x1 = x2.

Definition pairwise_disjoint {A B : Type} (L : list A) (f : A -> list B) : Prop :=
  forall x1 x2 y, In x1 L -> In x2 L -> In y (f x1) -> In y (f x2) -> x1 = x2.

Fixpoint nub'
  {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (L : list A) : list A :=
    match L with
    | [] => []
    | x :: M => (if in_dec eq_dec x M then [] else [x]) ++ nub' eq_dec M
    end.

Definition select {A : Type} (L : list bool) (M : list A) : list A :=
  map (@snd bool A) (filter (@fst bool A) (combine L M)).

Lemma empty_length :
  forall (A : Type) (L : list A), L = [] <-> length L = 0.
Proof.
  intros A [|x L].
  - tauto.
  - simpl.
    split; intro H; contradict H; auto with *.
Qed.

Lemma nonempty_length :
  forall (A : Type) (L : list A), L <> [] <-> length L > 0.
Proof.
  intros A [|x L].
  - simpl.
    intuition.
  - simpl.
    auto with *.
Qed.

Lemma removelast_correct :
  forall (A : Type) (x : A) (L : list A), removelast (L ++ [x]) = L.
Proof.
  intros A x L.
  rewrite removelast_app; simpl; auto with *.
Qed.

Lemma firstn_correct :
  forall (A : Type) (L M : list A), firstn (length L) (L ++ M) = L.
Proof.
  intros A L M.
  induction L as [|x L IH]; trivial.
  simpl.
  rewrite IH.
  trivial.
Qed.

Lemma skipn_length :
  forall (A : Type) (k : nat) (L : list A), length (skipn k L) = length L - k.
Proof.
  intros A k L.
  apply (plus_reg_l _ _ (min k (length L))).
  rewrite <- firstn_length at 1.
  rewrite <- app_length, firstn_skipn.
  destruct (le_dec k (length L)) as [H|H]; [rewrite min_l|rewrite min_r]; omega.
Qed.

Lemma in_seq :
  forall m n x, In x (seq m n) <-> m <= x < m + n.
Proof.
  intros m n x.
  revert m.
  induction n as [|n IH]; intro m.
  - simpl in *.
    omega.
  - simpl.
    specialize (IH (S m)).
    assert (m = x \/ m <> x) by omega.
    intuition.
Qed.

Lemma flat_map_length :
  forall (A B : Type) (f : A -> list B) (L : list A) (n : nat),
    (forall x, In x L -> length (f x) = n) ->
      length (flat_map f L) = n * length L.
Proof.
  intros A B f L n.
  rewrite mult_comm.
  induction L as [|x L IH]; trivial.
  intro Hf.
  simpl.
  rewrite app_length.
  rewrite Hf by auto with *.
  rewrite IH by auto with *.
  trivial.
Qed.

Lemma filter_length :
  forall (A : Type) (f : A -> bool) (L : list A),
    length (filter f L) <= length L.
Proof.
  intros A f L.
  induction L as [|x L IH]; trivial.
  simpl.
  destruct (f x); simpl.
  - omega.
  - auto.
Qed.

Lemma NoDup_singleton :
  forall (A : Type) (x : A), NoDup [x].
Proof.
  intros A x.
  apply NoDup_cons; [tauto|].
  apply NoDup_nil.
Qed.

Lemma NoDup_app :
  forall (A : Type) (L M : list A),
    NoDup L -> NoDup M -> (forall x, ~ (In x L /\ In x M)) -> NoDup (L ++ M).
Proof.
  intros A L M HL HM.
  induction HL as [|x L Hx HL IH]; trivial.
  intro HD.
  simpl.
  apply NoDup_cons.
  - rewrite in_app_iff.
    specialize (HD x).
    intuition.
  - apply IH.
    intro y.
    specialize (HD y).
    intuition.
Qed.

Lemma NoDup_map :
  forall (A B : Type) (f : A -> B) (L : list A),
    injective L f -> NoDup L -> NoDup (map f L).
Proof.
  intros A B f L Hf HL.
  induction HL as [|x L Hx HL IH]; [apply NoDup_nil|].
  simpl.
  apply NoDup_cons.
  - rewrite in_map_iff.
    intros [x2 [Ef Hx2]].
    specialize (Hf x2 x).
    rewrite <- Hf in Hx; auto with *.
  - compute in *.
    auto.
Qed.

Lemma NoDup_flat_map :
  forall (A B : Type) (f : A -> list B) (L : list A),
    (forall x, In x L -> NoDup (f x)) ->
    pairwise_disjoint L f ->
    NoDup L ->
      NoDup (flat_map f L).
Proof.
  intros A B f L Hf1 Hf2 HL.
  induction HL as [|x L Hx HL IH]; [apply NoDup_nil|].
  simpl.
  apply NoDup_app.
  - apply Hf1.
    auto with *.
  - apply IH.
    + auto with *.
    + intros x1 x2 y.
      specialize (Hf2 x1 x2 y).
      auto with *.
  - intros y [H1 H2].
    rewrite in_flat_map in H2.
    destruct H2 as [x2 [H2 H3]].
    specialize (Hf2 x x2 y).
    rewrite Hf2 in Hx; auto with *.
Qed.

Lemma NoDup_seq :
  forall m n, NoDup (seq m n).
Proof.
  intros m n.
  revert m.
  induction n as [|n IH]; intro m.
  - apply NoDup_nil.
  - specialize (IH (S m)).
    simpl.
    apply NoDup_cons.
    + rewrite in_seq.
      omega.
    + trivial.
Qed.

Lemma Permutation_NoDup :
  forall (A : Type) (L M : list A), Permutation L M -> NoDup L -> NoDup M.
Proof.
  intros A L M HP.
  induction HP as [ |x L M HP IH| | ].
  - trivial.
  - intro H.
    apply NoDup_cons.
    + intro H2.
      symmetry in HP.
      apply (Permutation_in x) in HP; trivial.
      contradict HP.
      revert H.
      apply (NoDup_remove_2 nil).
    + apply IH.
      revert H.
      apply (NoDup_remove_1 nil).
  - intro H.
    pose (NoDup_remove_1 nil _ _ H) as H2.
    pose (NoDup_remove_2 nil _ _ H) as H3.
    pose (NoDup_remove_1 nil _ _ H2) as H4.
    pose (NoDup_remove_2 nil _ _ H2) as H5.
    repeat apply NoDup_cons; firstorder.
  - tauto.
Qed.

Lemma NoDup_incl_Permutation :
  forall (A : Type) (L M : list A),
    NoDup L -> incl L M -> length L = length M -> Permutation L M.
Proof.
  intros A L M HN.
  revert M.
  induction L as [|x L IH]; intros M HI HL.
  - symmetry in HL.
    apply empty_length in HL.
    subst M.
    trivial.
  - assert (In x M) as H by auto with *.
    destruct (in_split x M H) as [M1 [M2 E]].
    subst M.
    rewrite <- Permutation_middle.
    apply perm_skip.
    apply IH.
    + inversion HN.
      trivial.
    + intros y K.
      assert (In y (x :: L)) as K2 by auto with *.
      specialize (HI y K2).
      rewrite in_app_iff in *.
      simpl in HI.
      destruct HI as [H1|[H2|H3]]; try tauto.
      subst y.
      inversion HN.
      tauto.
    + revert HL.
      repeat rewrite app_length.
      simpl.
      auto with *.
Qed.

Lemma incl_drop :
  forall (A : Type) (L M : list A) (x : A), incl L (x :: M) -> ~ In x L -> incl L M.
Proof.
  intros A L M x H1 H2 y Hy.
  specialize (H1 y Hy).
  destruct H1 as [H1|H1].
  - subst y.
    tauto.
  - trivial.
Qed.

Lemma incl_cons_iff :
  forall (A : Type) (x : A) (L M : list A),
    incl (x :: L) M <-> In x M /\ incl L M.
Proof.
  unfold incl.
  simpl.
  intuition.
  subst.
  trivial.
Qed.

Lemma NoDup_incl_lel :
  forall (A : Type) (L M : list A), NoDup L -> incl L M -> length L <= length M.
Proof.
  intros A L M HI.
  revert M.
  induction L as [|x L IH]; [auto with *|].
  intros M HM.
  rewrite incl_cons_iff in HM.
  destruct HM as [Hx HL].
  apply in_split in Hx.
  destruct Hx as [P [Q HM]].
  subst M.
  rewrite app_length.
  simpl.
  rewrite <- plus_n_Sm, <- app_length.
  apply le_n_S.
  apply IH.
  - inversion HI.
    trivial.
  - intros y Hy.
    specialize (HL y Hy).
    revert HL.
    repeat rewrite in_app_iff.
    intros [H|[H|H]]; try tauto.
    subst y.
    inversion HI.
    tauto.
Qed.

Lemma seq_app :
  forall k m n : nat, seq k m ++ seq (k + m) n = seq k (m + n).
Proof.
  intros k m n.
  revert k.
  induction m as [|m IH]; intro k.
  - replace (k + 0) with k; trivial.
  - simpl.
    replace (k + S m) with (S k + m) by omega.
    rewrite IH.
    trivial.
Qed.

Lemma in_nub' :
  forall (A : Type) eq_dec (L : list A) (x : A), In x (nub' eq_dec L) <-> In x L.
Proof.
  intros A eq_dec L x.
  induction L as [|y L IH]; [tauto|].
  simpl.
  rewrite <- IH.
  destruct (in_dec eq_dec y L) as [H|H].
  - intuition.
    subst.
    tauto.
  - auto with *.
Qed.

Lemma NoDup_nub' :
  forall (A : Type) eq_dec (L : list A), NoDup (nub' eq_dec L).
Proof.
  intros A eq_dec L.
  induction L as [|x L IH]; [apply NoDup_nil|].
  unfold nub'.
  destruct (in_dec eq_dec x L) as [H|H]; fold (@nub' A).
  - trivial.
  - apply NoDup_cons; trivial.
    rewrite in_nub'.
    trivial.
Qed.

Lemma NoDup_nub'_eq :
  forall (A : Type) eq_dec (L : list A), NoDup L -> L = nub' eq_dec L.
Proof.
  intros A eq_dec L H.
  induction L as [|x L IH]; trivial.
  simpl.
  inversion H as [|y M H1 H2 [E1 E2]].
  subst y M.
  destruct (in_dec eq_dec x L) as [N|]; [tauto|].
  rewrite <- IH; trivial.
Qed.

Lemma nub'_length :
  forall (A : Type) eq_dec (L : list A), length (nub' eq_dec L) <= length L.
Proof.
  intros A eq_dec L.
  induction L as [|x L IH]; trivial.
  simpl.
  destruct (in_dec eq_dec x L) as [H|H].
  - auto.
  - simpl.
    omega.
Qed.

Lemma nub'_filter :
  forall (A : Type) eq_dec (f : A -> bool) (L : list A),
    nub' eq_dec (filter f L) = filter f (nub' eq_dec L).
Proof.
  intros A eq_dec f L.
  induction L as [|x L IH]; trivial.
  simpl.
  destruct (f x) eqn:E;
    simpl;
    rewrite IH;
    destruct (in_dec eq_dec x L) as [H1|H1];
    destruct (in_dec eq_dec x (filter f L)) as [H2|H2];
    rewrite filter_In in H2;
    try tauto;
    simpl;
    destruct (f x);
    trivial;
    discriminate.
Qed.

Lemma select_length :
  forall (A : Type) (L : list bool) (M : list A),
    length (select L M) <= length M.
Proof.
  intros A L M.
  unfold select.
  rewrite map_length, filter_length, combine_length.
  auto with *.
Qed.

Lemma select_cons :
  forall (A : Type) (x : bool) (L : list bool) (y : A) (M : list A),
    select (x :: L) (y :: M) = (if x then [y] else []) ++ select L M.
Proof.
  intros A x L y M.
  destruct x; trivial.
Qed.

Lemma select_incl :
  forall (A : Type) (L : list bool) (M : list A),
    incl (select L M) M.
Proof.
  intros A L M x.
  unfold select.
  rewrite in_map_iff.
  intros [[y z] [E H]].
  rewrite filter_In in H.
  simpl in E.
  subst z.
  destruct H as [H _].
  revert H.
  apply in_combine_r.
Qed.

Definition search_first
  {A : Type}
  (eq_dec : forall x y : A, {x = y} + {x <> y})
  (x : A) (L : list A) :
    {M : list A & {N | L = M ++ x :: N /\ ~ In x M}} + {~ In x L}.
Proof.
  induction L as [|y L IH].
  - right.
    tauto.
  - destruct (eq_dec x y) as [E|NE].
    + left.
      exists nil, L.
      subst y.
      tauto.
    + destruct IH as [[M [N [H1 H2]]]|NI].
      * left.
        exists (y :: M), N.
        subst L.
        simpl.
        intuition.
      * right.
        firstorder.
Defined.

Definition search_last
  {A : Type}
  (eq_dec : forall x y : A, {x = y} + {x <> y})
  (x : A) (L : list A) :
    {M : list A & {N | L = M ++ x :: N /\ ~ In x N}} + {~ In x L}.
Proof.
  destruct (search_first eq_dec x (rev L)) as [[M [N [H1 H2]]]|H].
  - left.
    exists (rev N), (rev M).
    rewrite <- (rev_involutive L), <- rev_unit, <- rev_app_distr, <- app_assoc, H1, <- in_rev.
    tauto.
  - right.
    rewrite <- in_rev in H.
    trivial.
Defined.

Definition remove1 {A : Type} eq_dec (x : A) (L : list A) : list A :=
  match search_first eq_dec x L with
  | inleft (existT M (exist N _)) => M ++ N
  | inright _ => L
  end.

Fixpoint list_diff {A : Type} eq_dec (L M : list A) : list A :=
  match M with
  | [] => L
  | x :: N => remove1 eq_dec x (list_diff eq_dec L N)
  end.

Lemma Permutation_remove1 :
  forall (A : Type) eq_dec (x : A) (L M : list A),
    Permutation (x :: L) M -> Permutation L (remove1 eq_dec x M).
Proof.
  intros A eq_dec x L M H.
  unfold remove1.
  destruct (search_first eq_dec x M) as [[M1 [M2 [HM _]]]|NI].
  - subst M.
    apply Permutation_cons_app_inv in H.
    trivial.
  - apply (Permutation_in x) in H.
    + tauto.
    + auto with *.
Qed.

Lemma Permutation_list_diff :
  forall (A : Type) eq_dec (L M N : list A),
    Permutation (L ++ M) N -> Permutation M (list_diff eq_dec N L).
Proof.
  intros A eq_dec L M N.
  revert M.
  induction L as [|x L IH]; trivial.
  intros M H.
  simpl.
  apply Permutation_remove1, IH.
  rewrite <- Permutation_middle.
  trivial.
Qed.

Definition empty_dec {A : Type} (L : list A) :
  {L = []} + {L <> []}.
Proof.
  destruct L.
  - tauto.
  - auto with *.
Defined.

Definition NoDup_dec
  {A : Type}
  (eq_dec : forall x y : A, {x = y} + {x <> y})
  (L : list A) :
    {NoDup L} + {~ NoDup L}.
Proof.
  destruct (list_eq_dec eq_dec L (nub' eq_dec L)) as [Y|N].
  - left.
    rewrite Y.
    apply NoDup_nub'.
  - right.
    contradict N.
    apply NoDup_nub'_eq, N.
Defined.

Definition Permutation_dec
  {A : Type}
  (eq_dec : forall x y : A, {x = y} + {x <> y})
  (L M : list A) :
    {Permutation L M} + {~ Permutation L M}.
Proof.
  revert M.
  induction L as [|x L IH]; intro M.
  - destruct M as [|x M].
    + left.
      apply perm_nil.
    + right.
      intro H.
      apply Permutation_nil in H.
      discriminate.
  - destruct (search_first eq_dec x M) as [[M1 [M2 [HM _]]]|NI].
    subst M.
    + specialize (IH (M1 ++ M2)).
      destruct IH as [YP|NP].
      * left.
        apply Permutation_cons_app.
        trivial.
      * right.
        contradict NP.
        exact (Permutation_cons_app_inv M1 M2 NP).
    + right.
      contradict NI.
      apply (Permutation_in x NI).
      auto with *.
Defined.

Definition incl_dec
  {A : Type}
  (eq_dec : forall x y : A, {x = y} + {x <> y})
  (L M : list A) :
    {incl L M} + {~ incl L M}.
Proof.
  induction L as [|x L IH].
  - left.
    intros x H.
    contradict H.
  - destruct (in_dec eq_dec x M) as [Y|N].
    + destruct IH as [Y2|N2].
      * left.
        auto with *.
      * right.
        contradict N2.
        intro y.
        auto with *.
    + right.
      auto with *.
Defined.
