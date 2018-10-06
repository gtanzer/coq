Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.
Require Import Program.Equality.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

(* ------------------------ PREP DEFINITIONS ------------------------ *)

Section PrepDefs.

  Definition absdiff (n m : nat) : nat :=
    match (n ?= m) with
    | Lt => m - n
    | Eq => 0
    | Gt => n - m
    end.

  Inductive Adjacent : list nat -> list nat -> Prop :=
    | adjacent n x y z : Adjacent (x ++ n :: y ++ (S n) :: z) (x ++ (S n) :: y ++ n :: z).

  Inductive Transposable : list nat -> list nat -> Prop :=
    | transp_refl x : Transposable x x
    | transp_trans x y z : Transposable x y -> Adjacent y z -> Transposable x z.

End PrepDefs.

(* ------------------------ RANKED LIST DISTANCE METRIC DEFINITIONS ------------------------ *)

Section RankedListDefs.

  Function spearman (x y : list nat) : nat :=
    match x, y with
    | a :: x', b :: y' => (absdiff a b) + (spearman x' y')
    | _, _ => 0
    end.

  Function kendall_pred (a b c d : nat) : nat :=
    if (orb (andb (a <? c) (d <? b)) (andb (c <? a) (b <? d))) then 1 else 0.

  Function kendall2 (a b : nat) (x y : list nat) : nat :=
    match x, y with
    | c :: x', d :: y' => (kendall_pred a b c d) + (kendall2 a b x' y')
    | _, _ => 0
    end.

  Function kendall (x y : list nat) : nat :=
    match x, y with
    | a :: x', b :: y' => (kendall2 a b x' y') + (kendall x' y')
    | _, _ => 0
    end.

  Example problem5_spearman :
    spearman
      [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25]
      [22;13;0;8;1;17;11;5;3;18;2;7;9;15;16;6;24;21;10;25;23;14;20;19;4;12]
    = 180.
  Proof. now cbn. Qed.

  Example problem5_kendall :
    kendall
      [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25]
      [22;13;0;8;1;17;11;5;3;18;2;7;9;15;16;6;24;21;10;25;23;14;20;19;4;12]
    = 125.
  Proof. now cbn. Qed.

End RankedListDefs.

(* ------------------------ HELPER LEMMAS ------------------------ *)

Section HelperLemmas.

  Lemma absdiff_eq (n : nat) :
    absdiff n n = 0.
  Proof. now induction n. Qed.

  Lemma absdiff_succ_l (n : nat) :
    absdiff (S n) n = 1.
  Proof. now induction n. Qed.

  Lemma absdiff_succ_r (n : nat) :
    absdiff n (S n) = 1.
  Proof. now induction n. Qed.

  Lemma absdiff_zero_l (n : nat) :
    absdiff 0 n = n.
  Proof. now induction n. Qed.

  Lemma absdiff_zero_r (n : nat) :
    absdiff n 0 = n.
  Proof. now induction n. Qed.

  Lemma absdiff_sym (a b : nat) :
    absdiff a b = absdiff b a.
  Proof.
    induction a, b; auto. remember (S a ?= S b) as cmp1; remember (S b ?= S a) as cmp2.
    unfold absdiff. rewrite <- Heqcmp1. rewrite <- Heqcmp2. destruct cmp1, cmp2; auto.
    1-2: specialize (Nat.compare_eq a b); intros; cbn in Heqcmp1; symmetry in Heqcmp1; specialize (H Heqcmp1); omega.
    1,3:specialize (Nat.compare_eq b a); intros; cbn in Heqcmp2; symmetry in Heqcmp2; specialize (H Heqcmp2); omega.
    specialize (nat_compare_Lt_lt a b);specialize (nat_compare_Lt_lt b a); intros; cbn in *.
    symmetry in Heqcmp1; symmetry in Heqcmp2. apply H0 in Heqcmp1. apply H in Heqcmp2; omega.
    specialize (nat_compare_Gt_gt a b);specialize (nat_compare_Gt_gt b a); intros; cbn in *.
    symmetry in Heqcmp1; symmetry in Heqcmp2. apply H0 in Heqcmp1. apply H in Heqcmp2; omega.
  Qed.

  Ltac exhaust Heqcmp1 Heqcmp2 Heqcmp3 Heqcmp4 :=
    symmetry in Heqcmp1; symmetry in Heqcmp2; symmetry in Heqcmp3; symmetry in Heqcmp4;
    try apply Nat.compare_eq in Heqcmp1; try apply Nat.compare_eq in Heqcmp2; try apply Nat.compare_eq in Heqcmp3; try apply Nat.compare_eq in Heqcmp4;
    try apply nat_compare_Gt_gt in Heqcmp1; try apply nat_compare_Gt_gt in Heqcmp2; try apply nat_compare_Gt_gt in Heqcmp3; try apply nat_compare_Gt_gt in Heqcmp4;
    try apply nat_compare_Lt_lt in Heqcmp1; try apply nat_compare_Lt_lt in Heqcmp2; try apply nat_compare_Lt_lt in Heqcmp3; try apply nat_compare_Lt_lt in Heqcmp4;
    omega.

  Lemma absdiff_cmp_succ_l (a b : nat) :
    absdiff a (S b) + 1 >= absdiff a b.
  Proof.
    induction a; cbn. rewrite absdiff_zero_l; omega. unfold absdiff in *.
    remember (a ?= S b) as cmp1; remember (a ?= b) as cmp2; remember (S a ?= S b) as cmp3; remember (S a ?= b) as cmp4.
    destruct cmp1, cmp2, cmp3, cmp4; exhaust Heqcmp1 Heqcmp2 Heqcmp3 Heqcmp4.
  Qed.

  Lemma absdiff_cmp_succ_r (a b : nat) :
    absdiff a b + 1 >= absdiff a (S b).
  Proof.
    induction a; cbn. rewrite absdiff_zero_l; omega. unfold absdiff in *.
    remember (a ?= S b) as cmp1; remember (a ?= b) as cmp2; remember (S a ?= S b) as cmp3; remember (S a ?= b) as cmp4.
    destruct cmp1, cmp2, cmp3, cmp4; exhaust Heqcmp1 Heqcmp2 Heqcmp3 Heqcmp4.
  Qed.

  Lemma Transposable_length (x y : list nat) :
    Transposable x y -> length x = length y.
  Proof.
    intros. induction H; auto. induction H0. rewrite IHTransposable.
    repeat rewrite app_comm_cons. repeat rewrite app_length. cbn; auto.
  Qed.

  Lemma list_app_decomposition (l x y z : list nat) :
    Transposable l (x ++ y ++ z) -> exists (i j k : list nat),
      l = i ++ j ++ k /\ length i = length x /\ length j = length y /\ length k = length z.
  Proof.
    intros. apply Transposable_length in H. revert H. revert x y z. induction l; intros.
    - cbn in H. symmetry in H. exists [], [], []. repeat rewrite app_length in H.
      assert (length x = 0) by omega; assert (length y = 0) by omega; now assert (length z = 0) by omega.
    - destruct x; cbn in *.
      + destruct y; cbn in *.
        * destruct z; cbn in *.
          -- discriminate.
          -- apply Nat.succ_inj in H. specialize (IHl [] [] z H). destruct IHl as [i [j [k [total [len1 [len2 len3]]]]]].
              apply length_zero_iff_nil in len1; apply length_zero_iff_nil in len2. exists [], [], (a :: k); cbn; subst; auto.
        * apply Nat.succ_inj in H. specialize (IHl [] y z H). destruct IHl as [i [j [k [total [len1 [len2 len3]]]]]].
          apply length_zero_iff_nil in len1. exists [], (a :: j), k; cbn; subst; auto.
      + apply Nat.succ_inj in H. specialize (IHl x y z H). destruct IHl as [i [j [k [total [len1 [len2 len3]]]]]].
        exists (a :: i), j, k; cbn; subst; auto.
  Qed.

  Lemma list_cons_decomposition (a b : nat) (l x y z : list nat) :
    Transposable l (x ++ a :: y ++ b :: z) -> exists (c d : nat) (i j k : list nat),
      l = i ++ c :: j ++ d :: k /\ length i = length x /\ length (c :: j) = length (a :: y) /\ length (d :: k) = length (b :: z).
  Proof.
    intros. apply (list_app_decomposition l x (a :: y) (b :: z)) in H. destruct H as [i [j [k [decomp [len1 [len2 len3]]]]]].
    destruct j; try discriminate; destruct k; try discriminate.
    now exists n, n0, i, j, k.
  Qed.

End HelperLemmas.

(* ------------------------ RANKED LIST HELPER LEMMAS ------------------------ *)

Section RankedListLemmas.

  (* ------------------------ REFLEXIVITY ------------------------ *)

  Lemma spearman_refl (x : list nat) :
    spearman x x = 0.
  Proof.
    induction x; auto. cbn. now rewrite absdiff_eq.
  Qed.

  Lemma kendall_pred_refl (a b : nat) :
    kendall_pred a a b b = 0.
  Proof.
    unfold kendall_pred. remember (a <? b) as cmp1; remember (b <? a) as cmp2.
    destruct cmp1, cmp2; auto. symmetry in Heqcmp1, Heqcmp2.
    apply Nat.ltb_lt in Heqcmp1. apply Nat.ltb_lt in Heqcmp2. omega.
  Qed.

  Lemma kendall2_refl (a : nat) (x : list nat) :
    kendall2 a a x x = 0.
  Proof.
    induction x; auto. cbn. now rewrite kendall_pred_refl.
  Qed.

  Lemma kendall_refl (x : list nat) :
    kendall x x = 0.
  Proof.
    induction x; auto. cbn. now rewrite kendall2_refl.
  Qed.

  (* ------------------------ SYMMETRY ------------------------ *)

  Lemma spearman_sym (x y : list nat) :
    spearman x y = spearman y x.
  Proof.
    functional induction (spearman x y).
    - cbn. rewrite IHn. rewrite absdiff_sym. auto.
    - destruct x, y; auto; contradiction.
  Qed.

  Lemma kendall_pred_sym (a b c d : nat) :
    kendall_pred a b c d = kendall_pred b a d c.
  Proof.
    unfold kendall_pred. destruct (a <? c), (d <? b), (c <? a), (b <? d); cbn; omega.
  Qed.

  Lemma kendall2_sym (a b : nat) (x y : list nat) :
    kendall2 a b x y = kendall2 b a y x.
  Proof.
    functional induction (kendall2 a b x y).
    - cbn. rewrite IHn. now rewrite kendall_pred_sym.
    - destruct x, y; auto; contradiction.
  Qed.

  Lemma kendall_sym (x y : list nat) :
    kendall x y = kendall y x.
  Proof.
    functional induction (kendall x y).
    - cbn. rewrite IHn. now rewrite kendall2_sym.
    - destruct x, y; auto; contradiction.
  Qed.

  (* ------------------------ APPEND BEHAVIOR ------------------------ *)

  Lemma spearman_app (x y z w : list nat) :
    length x = length z -> length y = length w -> spearman (x ++ y) (z ++ w) = spearman x z + spearman y w.
  Proof.
    intros. functional induction (spearman x z).
    - cbn in *. apply Nat.succ_inj in H. specialize (IHn H). omega.
    - destruct _x, _x0; cbn; auto.
      + symmetry in H. apply length_zero_iff_nil in H. now subst.
      + apply length_zero_iff_nil in H. now subst.
      + contradiction.
  Qed.

  Lemma spearman_app_head (x y z : list nat) :
    spearman (x ++ y) (x ++ z) = spearman y z.
  Proof.
    induction x; auto.
    cbn. now rewrite absdiff_eq.
  Qed.

  Lemma kendall2_app_head (a : nat) (x y z : list nat) :
    kendall2 a a (x ++ y) (x ++ z) = kendall2 a a y z.
  Proof.
    induction x; cbn; auto.
    now rewrite kendall_pred_refl.
  Qed.

  Lemma kendall2_app_tail (a : nat) (x y z : list nat) :
    kendall2 a a (x ++ y) (x ++ z) = kendall2 a a y z.
  Proof.
    induction x; cbn; auto.
    now rewrite kendall_pred_refl.
  Qed.

  Lemma kendall2_app (a b : nat) (x y z w : list nat) :
    length x = length y -> kendall2 a b (x ++ z) (y ++ w) = kendall2 a b x y + kendall2 a b z w.
  Proof.
    intros. functional induction (kendall2 a b x y).
    - cbn in *; apply Nat.succ_inj in H; specialize (IHn H); omega.
    - destruct _x.
      + symmetry in H; apply length_zero_iff_nil in H; subst; now cbn.
      + destruct _x0; try contradiction. apply length_zero_iff_nil in H; subst; now cbn.
  Qed.

  Lemma kendall_app_head (x y z : list nat) :
    kendall y z <= kendall (x ++ y) (x ++ z).
  Proof.
    induction x; auto.
    cbn. omega.
  Qed.

  (* ------------------------ KENDALL PREDICATE SUCC BEHAVIOR ------------------------ *)

  Lemma kendall_pred_one (n : nat) :
    kendall_pred n (S n) (S n) n = 1.
  Proof.
    now induction n.
  Qed.

  Ltac kendall_pred_destruct n a := 
    unfold kendall_pred;
    remember (S n <? a) as cmp1; remember (a <? n) as cmp2; remember (a <? S n) as cmp3; remember (n <? a) as cmp4;
    destruct cmp1, cmp2, cmp3, cmp4; cbn; auto.

  Ltac kendall_pred_Lt_contradict Heqcmp1 Heqcmp2 :=
    symmetry in Heqcmp1; apply Nat.ltb_lt in Heqcmp1; symmetry in Heqcmp2; apply Nat.ltb_lt in Heqcmp2; omega.

  Lemma kendall_pred_Sn_n_a_a (n a : nat) :
    kendall_pred (S n) n a a = 0.
  Proof.
    kendall_pred_destruct n a.
    1-4: kendall_pred_Lt_contradict Heqcmp1 Heqcmp2. all: kendall_pred_Lt_contradict Heqcmp3 Heqcmp4.
  Qed.

  Lemma kendall_pred_n_Sn_a_a (n a : nat) :
    kendall_pred n (S n) a a = 0.
  Proof.
    kendall_pred_destruct n a.
    1-4: kendall_pred_Lt_contradict Heqcmp1 Heqcmp2. all: kendall_pred_Lt_contradict Heqcmp3 Heqcmp4.
  Qed.

  Lemma kendall_pred_a_a_Sn_n (n a : nat) :
    kendall_pred a a (S n) n = 0.
  Proof.
    kendall_pred_destruct n a.
    1-4: kendall_pred_Lt_contradict Heqcmp1 Heqcmp2. all: kendall_pred_Lt_contradict Heqcmp3 Heqcmp4.
  Qed.

  Lemma kendall_pred_a_a_n_Sn (n a : nat) :
    kendall_pred a a n (S n) = 0.
  Proof.
    kendall_pred_destruct n a.
    1-4: kendall_pred_Lt_contradict Heqcmp1 Heqcmp2. all: kendall_pred_Lt_contradict Heqcmp3 Heqcmp4.
  Qed.

  Lemma ltb_lt_uni (x y : nat) :
    (x <? y) = true -> x < y.
  Proof. apply Nat.ltb_lt. Qed.

  Lemma ltb_ge_uni (x y : nat) :
    (x <? y) = false -> x >= y.
  Proof. apply Nat.ltb_ge. Qed.

  Ltac comparify Heq :=
    try apply ltb_lt_uni in Heq; try apply ltb_ge_uni in Heq; try symmetry in Heq;
    try apply ltb_lt_uni in Heq; try apply ltb_ge_uni in Heq.

  Lemma kendall_pred_swap (a b c d n : nat) :
    kendall_pred a n c d + kendall_pred b (S n) c d = kendall_pred a (S n) c d + kendall_pred b n c d.
  Proof.
    unfold kendall_pred.
    remember (a <? c) as cmp1; remember (d <? n) as cmp2; remember (c <? a) as cmp3; remember (n <?d) as cmp4;
    remember (b <? c) as cmp5; remember (d <? S n) as cmp6; remember (c <? b) as cmp7; remember (S n <? d) as cmp8.
    destruct cmp1, cmp2, cmp3, cmp4, cmp5, cmp6, cmp7, cmp8; cbn; auto.
    all: comparify Heqcmp1; comparify Heqcmp2; comparify Heqcmp3; comparify Heqcmp4;
         comparify Heqcmp5; comparify Heqcmp6; comparify Heqcmp7; comparify Heqcmp8; try omega.
  Admitted.

  Lemma kendall_perm_swap2 (a b c d n : nat) :
    kendall_pred a b c n + kendall_pred a b d (S n) = kendall_pred a b c (S n) + kendall_pred a b d n.
  Proof.
    unfold kendall_pred.
    remember (a <? c) as cmp1; remember (n <? b) as cmp2; remember (c <? a) as cmp3; remember (b <? n) as cmp4;
    remember (a <? d) as cmp5; remember (S n <? b) as cmp6; remember (d <? a) as cmp7; remember (b <? S n) as cmp8.
    destruct cmp1, cmp2, cmp3, cmp4, cmp5, cmp6, cmp7, cmp8; cbn; auto.
    all: comparify Heqcmp1; comparify Heqcmp2; comparify Heqcmp3; comparify Heqcmp4;
         comparify Heqcmp5; comparify Heqcmp6; comparify Heqcmp7; comparify Heqcmp8; try omega.
  Admitted.

  (* ------------------------ KENDALL2 SUCC BEHAVIOR ------------------------ *)

  Lemma kendall2_zero (n : nat) (x : list nat) :
    kendall2 (S n) n x x = 0.
  Proof.
    induction x; auto. cbn. now rewrite kendall_pred_Sn_n_a_a.
  Qed.

  Lemma kendall2_succ_refl (a : nat) (x : list nat) :
    kendall2 a (S a) x x = 0.
  Proof.
    induction x; auto.
    cbn. now rewrite kendall_pred_n_Sn_a_a.
  Qed.

  Lemma kendall2_one (n : nat) (x y : list nat) :
    kendall2 n (S n) (x ++ S n :: y) (x ++ n :: y) = 1.
  Proof.
    induction x.
    - cbn. rewrite kendall_pred_one. now rewrite kendall2_succ_refl.
    - cbn. now rewrite kendall_pred_n_Sn_a_a.
  Qed.

  (* ------------------------ KENDALL SUCC BEHAVIOR ------------------------ *)

  Lemma kendall_middle (n : nat) (x y : list nat) :
    kendall (x ++ S n :: y) (x ++ n :: y) = 0.
  Proof.
    induction x; cbn.
    - rewrite kendall_refl. now rewrite kendall2_zero.
    - rewrite IHx. rewrite kendall2_app_head. cbn. rewrite kendall2_refl. now rewrite kendall_pred_a_a_Sn_n.
  Qed.

  (* ------------------------ KENDALL CROSS TERMS ------------------------ *)

  Function kendallx (x y z w : list nat) : nat :=
    match x, y with
    | a :: x', b :: y' => (kendall2 a b z w) + kendallx x' y' z w
    | _, _ => 0
    end.

  Lemma kendall_expand (x y z w : list nat) :
    length x = length y -> kendall (x ++ z) (y ++ w) = kendallx x y z w + kendall x y + kendall z w.
  Proof.
    intros; functional induction (kendallx x y z w).
    - cbn in *. apply Nat.succ_inj in H. specialize (IHn H). rewrite kendall2_app by auto. omega.
    - destruct _x. symmetry in H; apply length_zero_iff_nil in H; rewrite H; auto.
      destruct _x0; try contradiction. apply length_zero_iff_nil in H; rewrite H; auto.
  Qed.

  Lemma kendallx_app (x y z w u v : list nat) :
    length x = length y -> length z = length w -> kendallx x y (z ++ u) (w ++ v) = kendallx x y z w + kendallx x y u v.
  Proof.
    intros. functional induction (kendallx x y z w).
    - cbn in *; apply Nat.succ_inj in H. specialize (IHn H H0). rewrite kendall2_app; omega.
    - destruct _x. symmetry in H; apply length_zero_iff_nil in H; rewrite H; auto.
      destruct _x0; try contradiction. apply length_zero_iff_nil in H; rewrite H; auto.
  Qed.

  Lemma kendallx_cons (a b : nat) (x y z w : list nat) :
    length x = length y -> length z = length w -> kendallx x y (a :: z) (b :: w) = kendallx x y [a] [b] + kendallx x y z w.
  Proof.
    intros. assert (a :: z = [a] ++ z) by auto. assert (b :: w = [b] ++ w) by auto. rewrite H1, H2.
    now apply kendallx_app.
  Qed.

  Lemma kendall_pred_destruct (a b c d : nat) :
    kendall_pred a b c d = 0 \/ kendall_pred a b c d = 1.
  Proof. unfold kendall_pred. destruct (((a <? c) && (d <? b) || (c <? a) && (b <? d))%bool); auto. Qed.

  Lemma kendall_cancel (c d n : nat) (i j k x y z : list nat) :
    length i = length x
    -> length j = length y
    -> length k = length z
    -> kendallx i x [c] [n] + kendallx i x [d] [S n] + kendall_pred c n d (S n) + kendall2 c n k z
        + kendallx j y [d] [S n] + kendall2 c n j y + kendall2 d (S n) k z + 1 =
        kendallx i x [c] [S n] + kendallx i x [d] [n] + kendall_pred c (S n) d n + kendall2 c (S n) k z 
        + kendallx j y [d] [n] + kendall2 c (S n) j y + kendall2 d n k z.
  Proof.
    intros. functional induction (kendall2 c n k z).
    - cbn in *. apply Nat.succ_inj in H1. specialize (IHn0 H1).
      assert (kendall_pred c n c0 d0 + kendall_pred d (S n) c0 d0 = kendall_pred c (S n) c0 d0 + kendall_pred d n c0 d0).
      apply kendall_pred_swap. omega.
    - destruct _x.
      + symmetry in H1. apply length_zero_iff_nil in H1; subst; cbn. admit.
      + destruct _x0; try contradiction. apply length_zero_iff_nil in H1; rewrite H1; cbn.
  Restart.
    intros. specialize (kendall_pred_destruct c n d (S n)); intros. specialize (kendall_pred_destruct c n d (S n)); intros.
  Admitted.

End RankedListLemmas.

(* ------------------------ MAIN BOUND ------------------------ *)

Lemma spearman_adj (x y : list nat) :
  Adjacent x y -> spearman x y = 2.
Proof.
  intros. induction H. rewrite spearman_app_head. repeat rewrite app_comm_cons.
  rewrite (spearman_app (n :: y) (S n :: z) (S n :: y) (n :: z)); cbn; auto.
  rewrite absdiff_succ_l; rewrite absdiff_succ_r. now repeat rewrite spearman_refl.
Qed.

Ltac prove_length :=
  repeat rewrite app_comm_cons; repeat rewrite app_length; cbn; auto.

Lemma spearman_step (x y z : list nat) :
  Transposable x y -> Adjacent y z -> spearman x y + spearman y z >= spearman x z.
Proof.
  intros. inversion H0; subst. apply list_cons_decomposition in H. destruct H as [c [d [i [j [k]]]]].
  destruct H as [decomp [len1 [len2 len3]]]; subst.
  assert (length (c :: j ++ d :: k) = length (n :: y0 ++ S n :: z0)) as len4 by prove_length.
  specialize (spearman_app i (c :: j ++ d :: k) x0 (n :: y0 ++ S n :: z0) len1 len4); intros; rewrite H; clear H.
  assert (length (c :: j) = length (n :: y0)) as len5 by prove_length.
  assert (length (d :: k) = length (S n :: z0)) as len6 by prove_length.
  specialize (spearman_app (c :: j) (d :: k) (n :: y0) (S n :: z0) len5 len6); intros.
  repeat rewrite <- app_comm_cons in H; rewrite H; clear H; cbn.
  specialize (spearman_adj (x0 ++ n :: y0 ++ S n :: z0) ((x0 ++ S n :: y0 ++ n :: z0)) H0); intros; rewrite H; clear H.
  assert (length (c :: j ++ d :: k) = length (S n :: y0 ++ n :: z0)) as len7 by prove_length.
  specialize (spearman_app i (c :: j ++ d :: k) x0 (S n :: y0 ++ n :: z0) len1 len7); intros; rewrite H; clear H.
  assert (length (c :: j) = length (S n :: y0)) as len8 by prove_length.
  assert (length (d :: k) = length (n :: z0)) as len9 by prove_length.
  specialize (spearman_app (c :: j) (d :: k) (S n :: y0) (n :: z0) len8 len9); intros.
  repeat rewrite <- app_comm_cons in H; rewrite H; clear H; cbn.
  assert (absdiff c n + absdiff d (S n) + 2 >= absdiff c (S n) + absdiff d n);
  specialize (absdiff_cmp_succ_r c n); specialize (absdiff_cmp_succ_l d n); omega.
Qed.

Lemma kendall_adj (x y : list nat) :
  Adjacent x y -> kendall x y = 1.
Proof.
  intros. induction H. induction x.
  - cbn. rewrite kendall_middle. now rewrite kendall2_one.
  - cbn. rewrite kendall2_app_head. rewrite IHx. cbn.
    rewrite kendall_pred_a_a_n_Sn. rewrite kendall2_app_head.
    cbn. rewrite kendall_pred_a_a_Sn_n. now rewrite kendall2_refl.
Qed.

Lemma kendall_step (x y z : list nat) :
  Transposable x y -> Adjacent y z -> kendall x y + kendall y z = kendall x z.
Proof.
  intros. inversion H0; subst. apply list_cons_decomposition in H. destruct H as [c [d [i [j [k]]]]].
  destruct H as [decomp [len1 [len2 len3]]]; subst.
  rewrite kendall_adj with (x := (x0 ++ n :: y0 ++ S n :: z0)) (y := (x0 ++ S n :: y0 ++ n :: z0)); auto.
  repeat rewrite app_comm_cons; repeat rewrite kendall_expand; auto; cbn in *.
  apply Nat.succ_inj in len2; apply Nat.succ_inj in len3. repeat rewrite kendall2_app; auto; cbn.
  rewrite kendallx_app with (z := c :: j) (u := d :: k) (w := n :: y0) (v := S n :: z0) by (cbn; omega).
  rewrite kendallx_app with (z := c :: j) (u := d :: k) (w := S n :: y0) (v := n :: z0) by (cbn; omega).
  repeat rewrite Nat.add_assoc. rewrite kendallx_cons by auto. rewrite kendallx_cons with (z := j) (w := y0) by auto.
  do 4 rewrite kendallx_cons with (z := k) (w := z0) by auto.
  specialize (kendall_cancel c d n i j k x0 y0 z0 len1 len2 len3); omega.
Qed.

Theorem upper_bound (x y : list nat) :
  Transposable x y -> spearman x y <= 2 * kendall x y.
Proof.
  intros. induction H.
  - rewrite spearman_refl. now rewrite kendall_refl.
  - specialize (spearman_step x y z H H0); intros. rewrite (spearman_adj y z H0) in H1.
    specialize (kendall_step x y z H H0); intros. rewrite (kendall_adj y z H0) in H2; omega.
Qed.