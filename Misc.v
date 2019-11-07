(* Theorems of general usage, which could be (or not) in Coq library *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz Sorted.
Import List List.ListNotations.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat (at level 70, y at next level).

Definition List_combine_all {A} (l1 l2 : list A) (d : A) :=
  let '(l'1, l'2) :=
    match List.length l1 ?= List.length l2 with
    | Eq => (l1, l2)
    | Lt => (l1 ++ List.repeat d (List.length l2 - List.length l1), l2)
    | Gt => (l1, l2 ++ List.repeat d (List.length l1 - List.length l2))
    end
  in
  List.combine l'1 l'2.

Theorem Nat_sub_succ_1 : ∀ n, S n - 1 = n.
Proof. now intros; rewrite Nat.sub_succ, Nat.sub_0_r. Qed.

Theorem Nat_mod_0_mod_div : ∀ a b,
  0 < b ≤ a → a mod b = 0 → a mod (a / b) = 0.
Proof.
intros * Hba Ha.
assert (Hbz : b ≠ 0) by flia Hba.
assert (Habz : a / b ≠ 0). {
  intros H.
  apply Nat.div_small_iff in H; [ | flia Hba ].
  now apply Nat.nle_gt in H.
}
specialize (Nat.div_mod a (a / b) Habz) as H1.
specialize (Nat.div_mod a b Hbz) as H2.
rewrite Ha, Nat.add_0_r in H2.
rewrite H2 in H1 at 3.
rewrite Nat.div_mul in H1; [ | easy ].
rewrite Nat.mul_comm in H1.
flia H1 H2.
Qed.

Theorem Nat_mod_0_div_div : ∀ a b,
  0 < b ≤ a → a mod b = 0 → a / (a / b) = b.
Proof.
intros * Hba Ha.
assert (Hbz : b ≠ 0) by flia Hba.
assert (Habz : a / b ≠ 0). {
  intros H.
  apply Nat.div_small_iff in H; [ | easy ].
  now apply Nat.nle_gt in H.
}
specialize (Nat.div_mod a (a / b) Habz) as H1.
rewrite Nat_mod_0_mod_div in H1; [ | easy | easy ].
rewrite Nat.add_0_r in H1.
apply (Nat.mul_cancel_l _ _ (a / b)); [ easy | ].
rewrite <- H1; symmetry.
rewrite Nat.mul_comm.
apply Nat.mod_divide in Ha; [ | easy ].
rewrite <- Nat.divide_div_mul_exact; [ | easy | easy ].
now rewrite Nat.mul_comm, Nat.div_mul.
Qed.

Theorem Nat_fact_succ : ∀ n, fact (S n) = S n * fact n.
Proof. easy. Qed.

Theorem Nat_divide_fact_fact : ∀ n d, Nat.divide (fact (n - d)) (fact n).
Proof.
intros *.
revert n.
induction d; intros; [ rewrite Nat.sub_0_r; apply Nat.divide_refl | ].
destruct n; [ apply Nat.divide_refl | ].
rewrite Nat.sub_succ.
apply (Nat.divide_trans _ (fact n)); [ apply IHd | ].
rewrite Nat_fact_succ.
now exists (S n).
Qed.

Theorem Nat_divide_mul_fact : ∀ n a b,
  0 < a ≤ n
  → 0 < b ≤ n
  → a < b
  → Nat.divide (a * b) (fact n).
Proof.
intros * Han Hbn Hab.
exists (fact (a - 1) * (fact (b - 1) / fact a) * (fact n / fact b)).
rewrite Nat.mul_comm.
rewrite (Nat.mul_shuffle0 _ b).
do 2 rewrite Nat.mul_assoc.
replace (a * fact (a - 1)) with (fact a). 2: {
  destruct a; [ flia Han | ].
  rewrite Nat_fact_succ.
  now rewrite Nat.sub_succ, Nat.sub_0_r.
}
replace (fact a * (fact (b - 1) / fact a)) with (fact (b - 1)). 2: {
  specialize (Nat_divide_fact_fact (b - 1) (b - 1 - a)) as H1.
  replace (b - 1 - (b - 1 - a)) with a in H1 by flia Hab.
  destruct H1 as (c, Hc).
  rewrite Hc, Nat.div_mul; [ | apply fact_neq_0 ].
  apply Nat.mul_comm.
}
rewrite Nat.mul_comm, Nat.mul_assoc.
replace (b * fact (b - 1)) with (fact b). 2: {
  destruct b; [ flia Hbn | ].
  rewrite Nat_fact_succ.
  now rewrite Nat.sub_succ, Nat.sub_0_r.
}
replace (fact b * (fact n / fact b)) with (fact n). 2: {
  specialize (Nat_divide_fact_fact n (n - b)) as H1.
  replace (n - (n - b)) with b in H1 by flia Hbn.
  destruct H1 as (c, Hc).
  rewrite Hc, Nat.div_mul; [ | apply fact_neq_0 ].
  apply Nat.mul_comm.
}
easy.
Qed.

Theorem List_hd_nth_0 {A} : ∀ l (d : A), hd d l = nth 0 l d.
Proof. intros; now destruct l. Qed.

Theorem List_map_map_map {A B C D} : ∀ (f : A → B → C) (g : A → D → B) h l,
  map (λ d, map (f d) (map (g d) (h d))) l =
  map (λ d, map (λ x, (f d (g d x))) (h d)) l.
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
now rewrite List.map_map, IHl.
Qed.

Theorem List_flat_map_length {A B} : ∀ (l : list A) (f : _ → list B),
  length (flat_map f l) =
    List.fold_right Nat.add 0 (map (@length B) (map f l)).
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
now rewrite app_length, IHl.
Qed.

Theorem List_last_seq : ∀ i n, n ≠ 0 → last (seq i n) 0 = i + n - 1.
Proof.
intros * Hn.
destruct n; [ easy | clear Hn ].
revert i; induction n; intros. {
  cbn; symmetry.
  apply Nat.add_sub.
}
remember (S n) as sn; cbn; subst sn.
remember (seq (S i) (S n)) as l eqn:Hl.
destruct l; [ easy | ].
rewrite Hl.
replace (i + S (S n)) with (S i + S n) by flia.
apply IHn.
Qed.

Theorem List_last_In {A} : ∀ (d : A) l, l ≠ [] → In (last l d) l.
Proof.
intros * Hl.
destruct l as [| a l]; [ easy | clear Hl ].
revert a.
induction l as [| b l]; intros; [ now left | ].
remember (b :: l) as l'; cbn; subst l'.
right; apply IHl.
Qed.

Theorem List_last_app {A} : ∀ l (d a : A), List.last (l ++ [a]) d = a.
Proof.
intros.
induction l; [ easy | ].
cbn.
remember (l ++ [a]) as l' eqn:Hl'.
destruct l'; [ now destruct l | apply IHl ].
Qed.

Theorem not_equiv_imp_False : ∀ P : Prop, (P → False) ↔ ¬ P.
Proof. easy. Qed.

Theorem Sorted_Sorted_seq : ∀ start len, Sorted.Sorted lt (seq start len).
Proof.
intros.
revert start.
induction len; intros; [ apply Sorted.Sorted_nil | ].
cbn; apply Sorted.Sorted_cons; [ apply IHlen | ].
clear IHlen.
induction len; [ apply Sorted.HdRel_nil | ].
cbn. apply Sorted.HdRel_cons.
apply Nat.lt_succ_diag_r.
Qed.

Theorem Forall_inv_tail {A} : ∀ P (a : A) l, Forall P (a :: l) → Forall P l.
Proof.
intros * HF.
now inversion HF.
Qed.

Theorem Sorted_Sorted_lt_app_not_in_l : ∀ a l1 l2,
  Sorted.Sorted lt (l1 ++ a :: l2)
  → not (List.In a l1).
Proof.
intros * Hs Ha.
apply Sorted.Sorted_StronglySorted in Hs; [ | apply Nat.lt_strorder ].
induction l1 as [| b l]; [ easy | cbn ].
destruct Ha as [Ha| Ha]. {
  subst b.
  clear IHl.
  cbn in Hs.
  induction l as [| b l]; intros. {
    cbn in Hs.
    apply Sorted.StronglySorted_inv in Hs.
    destruct Hs as (_, Hr).
    apply Forall_inv in Hr; flia Hr.
  }
  apply IHl.
  apply Sorted.StronglySorted_inv in Hs.
  destruct Hs as (Hs, Hr).
  cbn in Hs, Hr.
  constructor. {
    now apply Sorted.StronglySorted_inv in Hs.
  }
  now apply Forall_inv_tail in Hr.
}
apply IHl; [ | easy ].
cbn in Hs.
now apply Sorted.StronglySorted_inv in Hs.
Qed.

Theorem Sorted_Sorted_lt_app_not_in_r : ∀ a l1 l2,
  Sorted.Sorted lt (l1 ++ a :: l2)
  → not (List.In a l2).
Proof.
intros * Hs Ha.
apply Sorted.Sorted_StronglySorted in Hs; [ | apply Nat.lt_strorder ].
induction l1 as [| b l]. {
  cbn in Hs.
  apply Sorted.StronglySorted_inv in Hs.
  destruct Hs as (Hs, Hr).
  specialize (proj1 (Forall_forall _ _) Hr) as H1.
  specialize (H1 _ Ha); flia H1.
}
cbn in Hs.
apply Sorted.StronglySorted_inv in Hs.
now apply IHl.
Qed.

Theorem NoDup_app_comm {A} : ∀ l l' : list A,
  NoDup (l ++ l') → NoDup (l' ++ l).
Proof.
intros * Hll.
revert l Hll.
induction l' as [| a l']; intros; [ now rewrite app_nil_r in Hll | ].
cbn; constructor. {
  intros Ha.
  apply NoDup_remove_2 in Hll; apply Hll.
  apply in_app_or in Ha.
  apply in_or_app.
  now destruct Ha; [ right | left ].
}
apply IHl'.
now apply NoDup_remove_1 in Hll.
Qed.

Theorem List_in_app_app_swap {A} : ∀ (a : A) l1 l2 l3,
  In a (l1 ++ l3 ++ l2)
  → In a (l1 ++ l2 ++ l3).
Proof.
intros * Hin.
revert l2 l3 Hin.
induction l1 as [| a2 l1]; intros. {
  cbn in Hin; cbn.
  apply in_app_or in Hin.
  apply in_or_app.
  now destruct Hin; [ right | left ].
}
cbn in Hin; cbn.
destruct Hin as [Hin| Hin]; [ now left | right ].
now apply IHl1.
Qed.

Theorem List_fold_left_mul_assoc : ∀ a b l,
  fold_left Nat.mul l a * b = fold_left Nat.mul l (a * b).
Proof.
intros.
revert a b.
induction l as [| c l]; intros; [ easy | ].
cbn; rewrite IHl.
now rewrite Nat.mul_shuffle0.
Qed.

Theorem NoDup_app_app_swap {A} : ∀ l1 l2 l3 : list A,
  NoDup (l1 ++ l2 ++ l3) → NoDup (l1 ++ l3 ++ l2).
Proof.
intros * Hlll.
revert l2 l3 Hlll.
induction l1 as [| a1 l1]; intros; [ now cbn; apply NoDup_app_comm | ].
cbn; constructor. {
  intros Hin.
  cbn in Hlll.
  apply NoDup_cons_iff in Hlll.
  destruct Hlll as (Hin2, Hlll).
  apply Hin2; clear Hin2.
  now apply List_in_app_app_swap.
}
apply IHl1.
cbn in Hlll.
now apply NoDup_cons_iff in Hlll.
Qed.

Theorem NoDup_concat_rev {A} : ∀ (ll : list (list A)),
  NoDup (concat (rev ll)) → NoDup (concat ll).
Proof.
intros * Hll.
destruct ll as [| l ll]; [ easy | ].
cbn; cbn in Hll.
rewrite concat_app in Hll; cbn in Hll.
rewrite app_nil_r in Hll.
apply NoDup_app_comm.
revert l Hll.
induction ll as [| l' ll]; intros; [ easy | ].
cbn in Hll; cbn.
rewrite concat_app in Hll; cbn in Hll.
rewrite app_nil_r, <- app_assoc in Hll.
rewrite <- app_assoc.
apply NoDup_app_app_swap.
rewrite app_assoc.
apply NoDup_app_comm.
now apply IHll.
Qed.

Theorem NoDup_filter {A} : ∀ (f : A → _) l, NoDup l → NoDup (filter f l).
Proof.
intros * Hnd.
induction l as [| a l]; [ easy | cbn ].
remember (f a) as b eqn:Hb; symmetry in Hb.
apply NoDup_cons_iff in Hnd.
destruct Hnd as (Hal, Hl).
destruct b. {
  constructor; [ | now apply IHl ].
  intros H; apply Hal.
  now apply filter_In in H.
}
now apply IHl.
Qed.
