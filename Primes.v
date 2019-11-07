(* Prime numbers *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith SetoidList.
Require Import Misc.
Import List ListNotations.

Notation "x '∈' l" := (List.In x l) (at level 70).
Notation "x '∉' l" := (¬ List.In x l) (at level 70).

Fixpoint prime_test cnt n d :=
  match cnt with
  | 0 => true
  | S c =>
      match n mod d with
      | 0 => n <=? d
      | S _ => prime_test c n (d + 1)
      end
  end.

Definition is_prime n :=
  match n with
  | 0 | 1 => false
  | S (S c) => prime_test c n 2
  end.

Theorem prime_test_false_exists_div_iff : ∀ n k,
  2 ≤ k
  → (∀ d, 2 ≤ d < k → n mod d ≠ 0)
  → prime_test (n - k) n k = false
  ↔ ∃ a b : nat, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b.
Proof.
intros * Hk Hd.
split.
-intros Hp.
 remember (n - k) as cnt eqn:Hcnt; symmetry in Hcnt.
 revert n k Hk Hd Hcnt Hp.
 induction cnt; intros; [ easy | ].
 cbn in Hp.
 remember (n mod k) as m eqn:Hm; symmetry in Hm.
 destruct m. {
   destruct k; [ easy | ].
   apply Nat.mod_divides in Hm; [ | easy ].
   destruct Hm as (m, Hm).
   destruct m; [ now rewrite Hm, Nat.mul_0_r in Hcnt | ].
   destruct k; [ flia Hk | ].
   destruct m. {
     now rewrite Hm, Nat.mul_1_r, Nat.sub_diag in Hcnt.
   }
   exists (S (S k)), (S (S m)).
   rewrite Hm.
   replace (S (S k) * S (S m)) with (S (S k) + k * m + k + 2 * m + 2) by flia.
   split; [ flia | ].
   split; [ flia | easy ].
 }
 destruct n; [ flia Hcnt | ].
 apply (IHcnt (S n) (k + 1)); [ flia Hk | | flia Hcnt | easy ].
 intros d Hdk.
 destruct (Nat.eq_dec d k) as [Hdk1| Hdk1]. {
   now intros H; rewrite <- Hdk1, H in Hm.
 }
 apply Hd; flia Hdk Hdk1.
-intros (a & b & Han & Hbn & Hnab).
 remember (n - k) as cnt eqn:Hcnt; symmetry in Hcnt.
 revert n a b k Hk Hd Hcnt Han Hbn Hnab.
 induction cnt; intros. {
   specialize (Hd a) as H1.
   assert (H : 2 ≤ a < k). {
     split. {
       destruct a; [ flia Hnab Han | ].
       destruct a; [ flia Hnab Han Hbn | flia ].
     }
     rewrite Hnab in Hcnt.
     apply Nat.sub_0_le in Hcnt.
     apply (Nat.lt_le_trans _ (a * b)); [ | easy ].
     destruct a; [ flia Han | ].
     destruct b; [ flia Hbn | ].
     destruct b; [ flia Hbn | ].
     rewrite Nat.mul_comm; cbn.
     remember (b * S a); flia.
   }
   specialize (H1 H).
   exfalso; apply H1; rewrite Hnab, Nat.mul_comm.
   apply Nat.mod_mul; flia H.
 }
 cbn.
 remember (n mod k) as m eqn:Hm; symmetry in Hm.
 destruct m; [ apply Nat.leb_gt; flia Hcnt | ].
 apply (IHcnt _ a b); [ flia Hk | | flia Hcnt | easy | easy | easy ].
 intros d (H2d, Hdk).
 destruct (Nat.eq_dec d k) as [Hdk1| Hdk1]. {
   now intros H; rewrite <- Hdk1, H in Hm.
 }
 apply Hd.
 flia H2d Hdk Hdk1.
Qed.

Theorem not_prime_decomp : ∀ n, 2 ≤ n →
  is_prime n = false
  → ∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b.
Proof.
intros n Hn Hp.
unfold is_prime in Hp.
destruct n; [ flia Hn | ].
destruct n; [ flia Hn | ].
replace n with (S (S n) - 2) in Hp at 1 by flia.
apply (prime_test_false_exists_div_iff _ 2); [ easy | | easy ].
intros * H; flia H.
Qed.

Theorem not_prime_exists_div : ∀ n, 2 ≤ n →
  is_prime n = false
  → ∃ a, 2 ≤ a < n ∧ Nat.divide a n.
Proof.
intros n Hn Hp.
specialize (not_prime_decomp n Hn Hp) as (a & b & Ha & Hb & Hab).
exists a.
split; [ | now rewrite Hab; apply Nat.divide_mul_l ].
split; [ easy | ].
rewrite Hab, Nat.mul_comm.
destruct a; [ flia Ha | ].
destruct b; [ flia Hb | ].
destruct b; [ flia Hb | ].
cbn; remember (b * S a); flia.
Qed.

Theorem prime_divisor : ∀ n, 2 ≤ n →
  ∃ d, is_prime d = true ∧ Nat.divide d n.
Proof.
intros * Hn.
induction n as (n, IHn) using (well_founded_ind lt_wf).
remember (is_prime n) as b eqn:Hb; symmetry in Hb.
destruct b; [ now exists n | ].
specialize (not_prime_exists_div n Hn Hb) as (a & Han & Hd).
specialize (IHn a (proj2 Han) (proj1 Han)) as H1.
destruct H1 as (d & Hpd & Hda).
exists d.
split; [ easy | ].
now transitivity a.
Qed.

Theorem Nat_le_divides_fact : ∀ n d, d ≤ n → Nat.divide (fact d) (fact n).
Proof.
intros * Hdn.
replace d with (n - (n - d)) by flia Hdn.
apply Nat_divide_fact_fact.
Qed.

Theorem Nat_fact_divides_small : ∀ n d,
  1 ≤ d ≤ n
  → fact n = fact n / d * d.
Proof.
intros * (Hd, Hdn).
specialize (Nat_le_divides_fact n d Hdn) as H1.
destruct H1 as (c, Hc).
rewrite Hc at 2.
destruct d; [ easy | ].
rewrite Nat_fact_succ.
rewrite (Nat.mul_comm (S d)).
rewrite Nat.mul_assoc.
rewrite Nat.div_mul; [ | easy ].
rewrite Hc, Nat_fact_succ.
now rewrite Nat.mul_assoc, Nat.mul_shuffle0.
Qed.

Theorem infinitely_many_primes : ∀ n, ∃ m, m > n ∧ is_prime m = true.
Proof.
intros.
specialize (prime_divisor (fact n + 1)) as H1.
assert (H : 2 ≤ fact n + 1). {
  clear.
  induction n; [ easy | ].
  rewrite Nat_fact_succ.
  apply (Nat.le_trans _ (fact n + 1)); [ easy | ].
  apply Nat.add_le_mono_r.
  cbn; flia.
}
specialize (H1 H); clear H.
destruct H1 as (d & Hd & Hdn).
exists d.
split; [ | easy ].
destruct (lt_dec n d) as [Hnd| Hnd]; [ easy | ].
apply Nat.nlt_ge in Hnd; exfalso.
assert (Ht : Nat.divide d (fact n)). {
  exists (fact n / d).
  apply Nat_fact_divides_small.
  split; [ | easy ].
  destruct d; [ easy | flia ].
}
destruct Hdn as (z, Hz).
destruct Ht as (t, Ht).
rewrite Ht in Hz.
apply Nat.add_sub_eq_l in Hz.
rewrite <- Nat.mul_sub_distr_r in Hz.
apply Nat.eq_mul_1 in Hz.
now destruct Hz as (Hz, H); subst d.
Qed.

Lemma prime_test_mod_ne_0 : ∀ n k,
  2 ≤ n
  → prime_test (n - k) n k = true
  → ∀ d, k ≤ d < n → n mod d ≠ 0.
Proof.
intros * Hn Hp d Hd.
remember (n - k) as cnt eqn:Hcnt; symmetry in Hcnt.
revert n k d Hn Hcnt Hp Hd.
induction cnt; intros; [ flia Hcnt Hd | ].
cbn in Hp.
remember (n mod k) as m eqn:Hm; symmetry in Hm.
destruct m; [ apply Nat.leb_le in Hp; flia Hp Hd | ].
destruct n; [ flia Hcnt | ].
destruct (Nat.eq_dec k d) as [Hkd| Hkd]. {
  now intros H; rewrite Hkd, H in Hm.
}
apply (IHcnt (S n) (k + 1)); [ easy | flia Hcnt | easy | flia Hd Hkd ].
Qed.

Theorem prime_divisors : ∀ p,
  is_prime p = true → ∀ a, Nat.divide a p → a = 1 ∨ a = p.
Proof.
intros * Hp a * Hap.
unfold is_prime in Hp.
destruct (lt_dec p 2) as [Hp2| Hp2]. {
  destruct p; [ easy | ].
  destruct p; [ easy | flia Hp2 ].
}
apply Nat.nlt_ge in Hp2.
destruct (zerop a) as [Ha| Ha]. {
  subst a.
  apply Nat.divide_0_l in Hap; flia Hap Hp2.
}
apply Nat.neq_0_lt_0 in Ha.
apply Nat.mod_divide in Hap; [ | easy ].
apply Nat.mod_divides in Hap; [ | easy ].
destruct Hap as (k, Hk).
symmetry in Hk.
destruct p; [ easy | ].
destruct p; [ easy | ].
specialize (prime_test_mod_ne_0 (S (S p)) 2 Hp2) as H1.
replace (S (S p) - 2) with p in H1 by flia.
specialize (H1 Hp).
destruct k; [ now rewrite Nat.mul_0_r in Hk | ].
destruct k; [ now rewrite Nat.mul_1_r in Hk; right | left ].
destruct a; [ easy | ].
destruct a; [ easy | exfalso ].
specialize (H1 (S (S k))) as H2.
assert (H : 2 ≤ S (S k) < S (S p)). {
  split; [ flia Hp2 | ].
  rewrite <- Hk; cbn.
  remember (a * _); flia.
}
specialize (H2 H); clear H.
apply H2; rewrite <- Hk.
now rewrite Nat.mod_mul.
Qed.

Theorem eq_primes_gcd_1 : ∀ a b,
  is_prime a = true → is_prime b = true → a ≠ b
  → Nat.gcd a b = 1.
Proof.
intros p q Hp Hq Hpq.
specialize (prime_divisors _ Hp) as Hpp.
specialize (prime_divisors _ Hq) as Hqp.
specialize (Hpp (Nat.gcd p q) (Nat.gcd_divide_l _ _)) as H1.
specialize (Hqp (Nat.gcd p q) (Nat.gcd_divide_r _ _)) as H2.
destruct H1 as [H1| H1]; [ easy | ].
destruct H2 as [H2| H2]; [ easy | ].
now rewrite H1 in H2.
Qed.

Fixpoint prime_decomp_aux cnt n d :=
  match cnt with
  | 0 => []
  | S c =>
      match n mod d with
      | 0 => d :: prime_decomp_aux c (n / d) d
      | _ => prime_decomp_aux c n (S d)
      end
  end.

Definition prime_decomp n :=
  match n with
  | 0 | 1 => []
  | _ => prime_decomp_aux n n 2
  end.

Lemma prime_decomp_aux_of_prime_test : ∀ n k,
  2 ≤ n
  → prime_test (n - 2) (k + n) (k + 2) = true
  → prime_decomp_aux n (k + n) (k + 2) = [k + n].
Proof.
intros * Hn Hpn.
destruct n; [ easy | ].
destruct n; [ flia Hn | clear Hn ].
replace (S (S n) - 2) with n in Hpn by flia.
revert k Hpn.
induction n; intros. {
  cbn - [ "/" "mod" ].
  rewrite Nat.mod_same; [ | flia ].
  rewrite Nat.div_same; [ | flia ].
  rewrite Nat.mod_1_l; [ easy | flia ].
}
remember (S (S n)) as sn.
cbn - [ "/" "mod" ].
cbn - [ "/" "mod" ] in Hpn.
remember ((k + S sn) mod (k + 2)) as b eqn:Hb; symmetry in Hb.
destruct b; [ apply Nat.leb_le in Hpn; flia Heqsn Hpn | ].
replace (k + S sn) with (S k + sn) in Hpn |-* by flia.
replace (S (k + 2)) with (S k + 2) by flia.
replace (k + 2 + 1) with (S k + 2) in Hpn by flia.
now apply IHn.
Qed.

Theorem prime_ge_2 : ∀ n, is_prime n = true → 2 ≤ n.
Proof.
intros * Hp.
destruct n; [ easy | ].
destruct n; [ easy | flia ].
Qed.

Theorem prime_decomp_of_prime : ∀ n,
  is_prime n = true
  → prime_decomp n = [n].
Proof.
intros * Hpn.
specialize (prime_ge_2 _ Hpn) as Hn.
unfold is_prime in Hpn.
unfold prime_decomp.
replace n with (S (S (n - 2))) in Hpn at 1 by flia Hn.
replace n with (S (S (n - 2))) at 1 by flia Hn.
replace n with (0 + n) in Hpn at 2 by flia.
replace 2 with (0 + 2) in Hpn at 2 by flia.
now apply prime_decomp_aux_of_prime_test in Hpn; [ | easy ].
Qed.

Lemma prime_decomp_aux_le : ∀ cnt n d d',
  d ≤ d' → HdRel le d (prime_decomp_aux cnt n d').
Proof.
intros * Hdd.
revert n d d' Hdd.
induction cnt; intros; [ constructor | cbn ].
destruct (n mod d') as [| Hnd]; [ now constructor | ].
apply IHcnt, (le_trans _ d'); [ easy | ].
apply Nat.le_succ_diag_r.
Qed.

Lemma Sorted_prime_decomp_aux : ∀ cnt n d,
  Sorted le (prime_decomp_aux cnt n d).
Proof.
intros.
revert n d.
induction cnt; intros; [ constructor | cbn ].
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b. {
  constructor; [ apply IHcnt | ].
  now apply prime_decomp_aux_le.
}
apply IHcnt.
Qed.

Theorem Sorted_prime_decomp : ∀ n, Sorted le (prime_decomp n).
Proof.
intros.
destruct n; [ constructor | ].
cbn - [ "/" "mod" ].
destruct n; [ constructor | ].
destruct (S (S n) mod 2) as [| b]. {
  constructor; [ apply Sorted_prime_decomp_aux | ].
  now apply prime_decomp_aux_le.
}
apply Sorted_prime_decomp_aux.
Qed.

Lemma in_prime_decomp_aux_le : ∀ cnt n d d',
  d' ∈ prime_decomp_aux cnt n d
  → d ≤ d'.
Proof.
intros * Hd'.
revert n d d' Hd'.
induction cnt; intros; [ easy | ].
cbn in Hd'.
destruct (n mod d) as [| b]. {
  destruct Hd' as [Hd'| Hd']; [ now subst d' | ].
  now apply (IHcnt (n / d)).
}
transitivity (S d); [ apply Nat.le_succ_diag_r | now apply (IHcnt n) ].
Qed.

Theorem in_prime_decomp_ge_2 : ∀ n d,
  d ∈ prime_decomp n
  → 2 ≤ d.
Proof.
intros * Hd.
destruct n; [ easy | ].
destruct n; [ easy | ].
unfold prime_decomp in Hd.
eapply in_prime_decomp_aux_le.
apply Hd.
Qed.

Theorem prime_decomp_param_ge_2 : ∀ n d,
  d ∈ prime_decomp n
  → 2 ≤ n.
Proof.
intros * Hd.
destruct n; [ easy | ].
destruct n; [ easy | flia ].
Qed.

Lemma in_prime_decomp_aux_divide : ∀ cnt n d p,
  d ≠ 0
  → p ∈ prime_decomp_aux cnt n d
  → Nat.divide p n.
Proof.
intros * Hdz Hp.
specialize (in_prime_decomp_aux_le cnt n d _ Hp) as Hdp.
assert (Hpz : p ≠ 0) by flia Hdz Hdp.
move Hpz before Hdz.
revert n d p Hdz Hp Hpz Hdp.
induction cnt; intros; [ easy | ].
cbn in Hp.
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b. {
  destruct Hp as [Hp| Hp]; [ now subst d; apply Nat.mod_divide | ].
  apply (Nat.divide_trans _ (n / d)). 2: {
    apply Nat.mod_divides in Hb; [ | easy ].
    destruct Hb as (c, Hc).
    rewrite Hc, Nat.mul_comm, Nat.div_mul; [ | easy ].
    apply Nat.divide_factor_l.
  }
  now apply (IHcnt _ d).
}
specialize (in_prime_decomp_aux_le _ _ _ _ Hp) as H1.
now apply (IHcnt _ (S d)).
Qed.

Theorem in_prime_decomp_divide : ∀ n d,
  d ∈ prime_decomp n → Nat.divide d n.
Proof.
intros * Hd.
assert (H2n : 2 ≤ n). {
  destruct n; [ easy | ].
  destruct n; [ easy | flia ].
}
specialize (in_prime_decomp_ge_2 n d Hd) as H2d.
move Hd at bottom.
unfold prime_decomp in Hd.
replace n with (S (S (n - 2))) in Hd by flia H2n.
replace (S (S (n - 2))) with n in Hd by flia H2n.
now apply in_prime_decomp_aux_divide in Hd.
Qed.

Theorem in_prime_decomp_le : ∀ n d : nat, d ∈ prime_decomp n → d ≤ n.
Proof.
intros * Hd.
apply Nat.divide_pos_le; [ | now apply in_prime_decomp_divide ].
destruct n; [ easy | flia ].
Qed.

Lemma prime_decomp_aux_at_1 : ∀ cnt d, 2 ≤ d → prime_decomp_aux cnt 1 d = [].
Proof.
intros * H2d.
destruct d; [ flia H2d | ].
destruct d; [ flia H2d | clear H2d ].
revert d.
induction cnt; intros; [ easy | cbn ].
destruct d; [ apply IHcnt | ].
replace (S d - d) with 1 by flia.
apply IHcnt.
Qed.

Lemma prime_decomp_aux_more_iter : ∀ k cnt n d,
  2 ≤ n
  → 2 ≤ d
  → n + 2 ≤ cnt + d
  → prime_decomp_aux cnt n d = prime_decomp_aux (cnt + k) n d.
Proof.
intros * H2n H2d Hnc.
revert n k d H2n H2d Hnc.
induction cnt; intros. {
  cbn in Hnc; cbn.
  revert d H2d Hnc.
  induction k; intros; [ easy | cbn ].
  rewrite Nat.mod_small; [ | flia Hnc ].
  destruct n; [ flia H2n | ].
  apply IHk; flia Hnc.
}
cbn - [ "/" "mod" ].
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b. {
  f_equal.
  apply Nat.mod_divides in Hb; [ | flia H2d ].
  destruct Hb as (b, Hb); rewrite Nat.mul_comm in Hb.
  rewrite Hb, Nat.div_mul; [ | flia H2d ].
  destruct (le_dec 2 b) as [H2b| H2b]. {
    apply IHcnt; [ easy | easy | ].
    transitivity (n + 1); [ | flia H2n Hnc ].
    rewrite Hb.
    destruct b; [ flia H2n Hb | ].
    destruct d; [ easy | ].
    destruct d; [ flia H2d | ].
    cbn; rewrite Nat.mul_comm; cbn.
    flia.
  }
  apply Nat.nle_gt in H2b.
  destruct b; [ cbn in Hb; subst n; flia H2n | ].
  destruct b; [ | flia H2b ].
  rewrite prime_decomp_aux_at_1; [ | easy ].
  now rewrite prime_decomp_aux_at_1.
}
apply IHcnt; [ easy | | flia Hnc ].
flia H2d Hnc.
Qed.

Lemma prime_test_more_iter : ∀ k cnt n d,
  2 ≤ n
  → n ≤ cnt + d
  → prime_test cnt n d = prime_test (cnt + k) n d.
Proof.
intros * H2n Hnc.
revert n k d H2n Hnc.
induction cnt; intros. {
  cbn in Hnc; cbn.
  revert d Hnc.
  induction k; intros; [ easy | cbn ].
  remember (n mod d) as b eqn:Hb; symmetry in Hb.
  destruct b; [ now symmetry; apply Nat.leb_le | ].
  destruct n; [ flia H2n | ].
  apply IHk; flia Hnc.
}
cbn - [ "/" "mod" ].
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
apply IHcnt; [ easy | flia Hnc ].
Qed.

Lemma hd_prime_decomp_aux_ge : ∀ cnt n d,
  2 ≤ d
  → 2 ≤ hd 2 (prime_decomp_aux cnt n d).
Proof.
intros * H2d.
revert d H2d.
induction cnt; intros; [ easy | cbn ].
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
apply IHcnt; flia H2d.
Qed.

Lemma prev_not_div_prime_test_true : ∀ cnt n d,
  2 ≤ n
  → 2 ≤ d
  → n ≤ cnt + d
  → (∀ e, 2 ≤ e < n → n mod e ≠ 0)
  → prime_test cnt n d = true.
Proof.
intros * H2n H2d Hcnt Hn.
revert n d H2n H2d Hcnt Hn.
induction cnt; intros; [ easy | cbn ].
remember (n mod d) as b1 eqn:Hb1; symmetry in Hb1.
destruct b1. {
  apply Nat.leb_le.
  apply Nat.mod_divides in Hb1; [ | flia H2d ].
  destruct Hb1 as (b1, Hb1).
  destruct b1; [ flia H2d Hb1 | ].
  destruct b1; [ flia Hb1 | ].
  specialize (Hn (S (S b1))) as H1.
  assert (H : 2 ≤ S (S b1) < n). {
    split; [ flia | ].
    rewrite Hb1; remember (S (S b1)) as b.
    destruct d; [ flia H2d | cbn ].
    destruct d; [ flia H2d | cbn ].
    remember (d * b); flia Heqb.
  }
  specialize (H1 H).
  exfalso; apply H1; clear H1.
  rewrite Hb1.
  now apply Nat.mod_mul.
}
apply IHcnt; [ easy | flia H2d | flia Hcnt | easy ].
Qed.

Lemma hd_prime_decomp_aux_prime_test_true : ∀ cnt n b d,
  2 ≤ n
  → 2 ≤ d
  → n + 2 ≤ cnt + d
  → (∀ e : nat, 2 ≤ e < d → n mod e ≠ 0)
  → b = hd 2 (prime_decomp_aux cnt n d)
  → prime_test (b - 2) b 2 = true.
Proof.
intros * H2n H2d Hcnt Hnd Hb.
revert d H2d Hcnt Hnd Hb.
induction cnt; intros; [ now subst b | ].
cbn - [ "/" "mod" ] in Hb.
remember (n mod d) as b1 eqn:Hb1; symmetry in Hb1.
destruct b1. {
  cbn in Hb; subst b.
  apply Nat.mod_divides in Hb1; [ | flia H2d ].
  destruct Hb1 as (b1, Hb1).
  destruct b1; [ flia H2n Hb1 | ].
  destruct b1. {
    rewrite Nat.mul_1_r in Hb1; subst n.
    apply prev_not_div_prime_test_true; [ easy | easy | flia H2d | easy ].
  }
  apply prev_not_div_prime_test_true; [ easy | easy | flia H2n | ].
  intros e He.
  specialize (Hnd e He) as H1.
  intros H2; apply H1; clear H1.
  apply Nat.mod_divides in H2; [ | flia He ].
  destruct H2 as (b2, Hb2); rewrite Nat.mul_comm in Hb2.
  rewrite Hb1, Hb2, Nat.mul_shuffle0.
  apply Nat.mod_mul; flia He.
}
assert (H : ∀ e, 2 ≤ e < 1 + d → n mod e ≠ 0). {
  intros e He.
  destruct (Nat.eq_dec e d) as [Hed| Hed]. {
    now subst e; intros H; rewrite H in Hb1.
  }
  apply Hnd; flia He Hed.
}
move H before Hnd; clear Hnd; rename H into Hnd.
clear b1 Hb1.
replace (S cnt + d) with (cnt + S d) in Hcnt by flia.
apply (IHcnt (S d)); [ flia H2d | easy | easy | easy ].
Qed.

Theorem first_in_decomp_is_prime : ∀ n,
  is_prime (List.hd 2 (prime_decomp n)) = true.
Proof.
intros.
unfold is_prime, prime_decomp.
destruct n; [ easy | ].
destruct n; [ easy | ].
assert (H2n : 2 ≤ S (S n)) by flia.
remember (S (S n)) as n'.
clear n Heqn'; rename n' into n.
specialize (hd_prime_decomp_aux_ge n n 2 (le_refl _)) as H2b.
remember (hd 2 (prime_decomp_aux n n 2)) as b eqn:Hb.
move b before n; move H2b before H2n.
replace b with (S (S (b - 2))) by flia H2b.
replace (S (S (b - 2))) with b by flia H2b.
apply (hd_prime_decomp_aux_prime_test_true n n b 2);
  [ easy | easy | easy | | easy ].
intros e He; flia He.
Qed.

Lemma prime_decomp_aux_not_nil : ∀ cnt n d,
  2 ≤ n
  → 2 ≤ d
  → n + 2 ≤ cnt + d
  → (∀ e : nat, 2 ≤ e < d → n mod e ≠ 0)
  → prime_decomp_aux cnt n d ≠ [].
Proof.
intros * H2n H2d Hcnt Hnd.
revert d H2d Hcnt Hnd.
induction cnt; intros. {
  assert (H : 2 ≤ n < d) by flia H2n Hcnt.
  specialize (Hnd n H); clear H.
  rewrite Nat.mod_same in Hnd; [ easy | flia H2n ].
}
cbn - [ "/" "mod" ].
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
rewrite Nat.add_succ_comm in Hcnt.
apply IHcnt; [ flia H2d | easy | ].
intros e He.
destruct (Nat.eq_dec e d) as [Hed| Hed]. {
  now subst e; intros H; rewrite H in Hb.
}
apply Hnd; flia He Hed.
Qed.

Theorem prime_decomp_nil_iff : ∀ n, prime_decomp n = [] ↔ n = 0 ∨ n = 1.
Proof.
intros.
split.
-intros Hn.
 unfold prime_decomp in Hn.
 destruct n; [ now left | ].
 destruct n; [ now right | exfalso ].
 revert Hn.
 apply prime_decomp_aux_not_nil; [ flia | easy | easy | ].
 intros e He; flia He.
-now intros [Hn| Hn]; subst n.
Qed.

Lemma prime_decomp_aux_cons_nil : ∀ cnt n d l,
  2 ≤ n
  → 2 ≤ d
  → n + 2 ≤ cnt + d
  → (∀ e, 2 ≤ e < d → n mod e ≠ 0)
  → prime_decomp_aux cnt n d = n :: l
  → l = [].
Proof.
intros * H2n H2d Hcnt Hdn Hnd.
revert d l H2d Hcnt Hdn Hnd.
induction cnt; intros; [ easy | ].
cbn in Hnd.
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b. {
  injection Hnd; clear Hnd; intros Hl Hd; subst d.
  rewrite Nat.div_same in Hl; [ | flia H2n ].
  now rewrite prime_decomp_aux_at_1 in Hl.
}
rewrite Nat.add_succ_comm in Hcnt.
apply (IHcnt (S d)); [ flia H2d | easy | | easy ].
intros e He.
destruct (Nat.eq_dec e d) as [Hed| Hed]. {
  now subst e; intros H; rewrite H in Hb.
}
apply Hdn; flia He Hed.
Qed.

Lemma prime_decomp_aux_cons : ∀ p b l n d cb cn,
  2 ≤ n
  → 2 ≤ b
  → 2 ≤ d
  → 2 ≤ p
  → b + 2 ≤ cb + d
  → n + 2 ≤ cn + d
  → n * p = b
  → prime_decomp_aux cb b d = p :: l
  → prime_decomp_aux cn n d = l.
Proof.
intros * H2n H2b H2d H2p Hcb Hcn Hb Hbp.
revert p b n d cn H2n H2b H2d H2p Hcb Hcn Hb Hbp.
induction cb; intros; [ easy | ].
cbn in Hbp.
remember (b mod d) as b1 eqn:Hb1; symmetry in Hb1.
destruct b1. {
  injection Hbp; clear Hbp; intros Hl Hp; subst d.
  rewrite <- Hb, Nat.div_mul in Hl; [ | flia H2b Hb ].
  rewrite (prime_decomp_aux_more_iter cn) in Hl; [ | easy | easy | ]. 2: {
    apply Nat.succ_le_mono.
    replace (S (cb + p)) with (S cb + p) by flia.
    transitivity (b + 2); [ | easy ].
    replace (S (n + 2)) with (S n + 2) by flia.
    apply Nat.add_le_mono_r.
    rewrite <- Hb.
    destruct p; [ flia H2p | ].
    destruct p; [ flia H2p | ].
    rewrite Nat.mul_comm; cbn.
    destruct n; [ easy | remember (p * S n); flia ].
  }
  rewrite Nat.add_comm in Hl.
  now rewrite (prime_decomp_aux_more_iter cb).
}
rewrite (prime_decomp_aux_more_iter 1); try easy.
rewrite Nat.add_1_r; cbn.
remember (n mod d) as b2 eqn:Hb2; symmetry in Hb2.
destruct b2. {
  apply Nat.mod_divides in Hb2; [ | flia H2d ].
  destruct Hb2 as (b2, Hb2).
  rewrite <- Hb, Hb2 in Hb1.
  rewrite <- Nat.mul_assoc, Nat.mul_comm in Hb1.
  rewrite Nat.mod_mul in Hb1; [ easy | flia H2d ].
}
rewrite Nat.add_succ_comm in Hcb.
apply (IHcb p b); try easy; [ flia H2d | flia Hcn ].
Qed.

Theorem prime_decomp_mul : ∀ n d l,
  2 ≤ d
  → prime_decomp (n * d) = d :: l
  → prime_decomp n = l.
Proof.
intros * H2d Hnd.
unfold prime_decomp in Hnd.
unfold prime_decomp.
destruct n; [ easy | ].
destruct n. {
  rewrite Nat.mul_1_l in Hnd.
  destruct d; [ easy | ].
  cbn - [ "/" "mod" ] in Hnd.
  destruct d; [ easy | ].
  remember (S (S d)) as d'.
  replace (S d) with (d' - 1) in Hnd by flia Heqd'.
  clear d Heqd'; rename d' into d; move H2d after Hnd.
  remember (d mod 2) as b eqn:Hb; symmetry in Hb.
  destruct b. {
    remember (prime_decomp_aux _ _ _) as x.
    injection Hnd; clear Hnd; intros Hl Hd; subst x.
    now subst d.
  }
  symmetry.
  apply prime_decomp_aux_cons_nil in Hnd; [ easy | easy | flia | flia | ].
  intros e He H.
  replace e with 2 in H by flia He.
  now rewrite H in Hb.
}
assert (H2n : 2 ≤ S (S n)) by flia.
remember (S (S n)) as n'; clear n Heqn'; rename n' into n.
remember (n * d) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
destruct b; [ easy | ].
assert (H2b : 2 ≤ S (S b)) by flia.
remember (S (S b)) as b'; clear b Heqb'; rename b' into b.
move H2n after Hb; move H2b after Hb.
now apply (prime_decomp_aux_cons) with (n := n) (cn := n) in Hnd.
Qed.

Theorem prime_decomp_cons : ∀ n a l,
  prime_decomp n = a :: l
  → prime_decomp (n / a) = l.
Proof.
intros * Hl.
assert (Hap : is_prime a = true). {
  specialize (first_in_decomp_is_prime n) as H1.
  now rewrite Hl in H1.
}
assert (H2a : 2 ≤ a) by now apply prime_ge_2.
apply (prime_decomp_mul (n / a) a); [ easy | ].
specialize (in_prime_decomp_divide n a) as H1.
rewrite Hl in H1.
specialize (H1 (or_introl eq_refl)).
destruct H1 as (b, Hb).
rewrite Hb, Nat.div_mul; [ | flia H2a ].
now rewrite <- Hb.
Qed.

Theorem prime_decomp_inj : ∀ a b,
  a ≠ 0 → b ≠ 0 → prime_decomp a = prime_decomp b → a = b.
Proof.
intros * Ha0 Hb0 Hab.
remember (prime_decomp b) as l eqn:Hb; symmetry in Hb.
rename Hab into Ha; move Ha after Hb.
revert a b Ha0 Hb0 Ha Hb.
induction l as [| d]; intros. {
  apply prime_decomp_nil_iff in Ha.
  apply prime_decomp_nil_iff in Hb.
  destruct Ha as [Ha| Ha]; [ easy | ].
  destruct Hb as [Hb| Hb]; [ easy | ].
  now subst a b.
}
specialize (in_prime_decomp_divide a d) as Hda.
rewrite Ha in Hda; cbn in Hda.
specialize (Hda (or_introl (eq_refl _))) as (da, Hda).
specialize (in_prime_decomp_divide b d) as Hdb.
rewrite Hb in Hdb; cbn in Hdb.
specialize (Hdb (or_introl (eq_refl _))) as (db, Hdb).
move db before da.
rewrite Hda, Hdb; f_equal.
apply IHl.
-now intros H; rewrite H in Hda.
-now intros H; rewrite H in Hdb.
-rewrite Hda in Ha.
 apply (prime_decomp_mul _ d); [ | easy ].
 destruct d; [ flia Ha0 Hda | ].
 destruct d; [ | flia ].
 apply (in_prime_decomp_ge_2 b 1).
 now rewrite Hb; left.
-rewrite Hdb in Hb.
 apply (prime_decomp_mul _ d); [ | easy ].
 destruct d; [ flia Ha0 Hda | ].
 destruct d; [ | flia ].
 apply (in_prime_decomp_ge_2 a 1).
 now rewrite Ha; left.
Qed.

Theorem in_prime_decomp_is_prime : ∀ n d,
  d ∈ prime_decomp n → is_prime d = true.
Proof.
intros * Hdn.
specialize (In_nth (prime_decomp n) d 2 Hdn) as (i & Hilen & Hid).
clear Hdn; subst d.
revert n Hilen.
induction i; intros. {
  rewrite <- List_hd_nth_0.
  apply first_in_decomp_is_prime.
}
remember (prime_decomp n) as l eqn:Hl; symmetry in Hl.
destruct l as [| a l]; [ easy | ].
cbn in Hilen; cbn.
apply Nat.succ_lt_mono in Hilen.
specialize (prime_decomp_cons n a l Hl) as H1.
rewrite <- H1.
apply IHi.
now rewrite H1.
Qed.

Theorem prime_decomp_prod : ∀ n, n ≠ 0 →
  fold_left Nat.mul (prime_decomp n) 1 = n.
Proof.
intros * Hnz.
remember (prime_decomp n) as l eqn:Hl; symmetry in Hl.
revert n Hnz Hl.
induction l as [| a l]; intros. {
  now apply prime_decomp_nil_iff in Hl; destruct Hl.
}
remember 1 as one; cbn; subst one.
specialize (in_prime_decomp_divide n a) as H1.
rewrite Hl in H1; specialize (H1 (or_introl eq_refl)).
destruct H1 as (k, Hk).
rewrite Hk in Hl.
assert (H2a : 2 ≤ a). {
  apply (in_prime_decomp_ge_2 (k * a)).
  now rewrite Hl; left.
}
apply prime_decomp_mul in Hl; [ | easy ].
apply IHl in Hl; [ | now intros H; subst k ].
apply (Nat.mul_cancel_r _ _ a) in Hl; [ | flia H2a ].
rewrite Hk, <- Hl.
symmetry; apply List_fold_left_mul_assoc.
Qed.

Theorem prime_relatively_prime : ∀ p n,
  is_prime p = true
  → 0 < n < p
  → Nat.gcd p n = 1.
Proof.
intros * Hp Hnp.
remember (Nat.gcd p n) as g eqn:Hg; symmetry in Hg.
destruct g; [ now apply Nat.gcd_eq_0 in Hg; rewrite (proj1 Hg) in Hp | ].
destruct g; [ easy | exfalso ].
specialize (Nat.gcd_divide_l p n) as H1.
rewrite Hg in H1.
destruct H1 as (d, Hd).
specialize (prime_divisors p Hp (S (S g))) as H1.
assert (H : Nat.divide (S (S g)) p). {
  rewrite Hd; apply Nat.divide_factor_r.
}
specialize (H1 H); clear H.
destruct H1 as [H1| H1]; [ easy | ].
destruct d; [ now rewrite Hd in Hp | ].
rewrite Hd in H1.
destruct d. {
  rewrite Nat.mul_1_l in Hd.
  rewrite <- Hd in Hg.
  specialize (Nat.gcd_divide_r p n) as H2.
  rewrite Hg in H2.
  destruct H2 as (d2, Hd2).
  destruct d2; [ rewrite Hd2 in Hnp; flia Hnp | ].
  rewrite Hd2 in Hnp; cbn in Hnp.
  remember (d2 * p); flia Hnp.
}
replace (S (S d)) with (1 + S d) in H1 by flia.
rewrite Nat.mul_add_distr_r, Nat.mul_1_l in H1.
rewrite <- (Nat.add_0_r (S (S g))) in H1 at 1.
now apply Nat.add_cancel_l in H1.
Qed.

Theorem prime_divides_fact_ge : ∀ n m,
  is_prime n = true
  → Nat.divide n (fact m)
  → n ≤ m.
Proof.
intros * Hn Hnm.
induction m; intros. {
  destruct Hnm as (c, Hc).
  symmetry in Hc.
  apply Nat.eq_mul_1 in Hc.
  now rewrite (proj2 Hc) in Hn.
}
rewrite Nat_fact_succ in Hnm.
specialize (Nat.gauss _ _ _ Hnm) as H1.
apply Nat.nlt_ge; intros Hnsm.
assert (H : Nat.gcd n (S m) = 1). {
  apply prime_relatively_prime; [ easy | ].
  split; [ flia | easy ].
}
specialize (H1 H); clear H.
apply Nat.nle_gt in Hnsm; apply Hnsm.
transitivity m; [ | flia ].
apply IHm, H1.
Qed.

(* https://en.wikipedia.org/wiki/Factorial#Number_theory *)
Theorem Wilson_on_composite :
  ∀ n, 5 < n → is_prime n = false ↔ fact (n - 1) mod n = 0.
Proof.
intros * H5n.
split.
-intros Hn.
 specialize (not_prime_decomp n) as H1.
 assert (H : 2 ≤ n) by flia H5n.
 specialize (H1 H Hn) as (a & b & Ha & Hb & Hab); clear H.
 apply Nat.mod_divide; [ flia H5n | ].
 assert (Han : 0 < a ≤ n - 1). {
   rewrite Hab.
   destruct a; [ easy | ].
   split; [ flia | ].
   destruct b; [ easy | ].
   destruct a; [ flia Ha | ].
   destruct b; [ flia Hb | ].
   rewrite Nat.mul_comm; cbn.
   remember (b * S (S a)); flia.
 }
 destruct (Nat.eq_dec a b) as [Haeb| Haeb]. {
   subst b; clear Hb.
   rewrite Hab at 1.
   remember (a * (a - 1)) as b eqn:Hb.
   apply (Nat.divide_trans _ (a * b)). {
     subst b.
     rewrite Nat.mul_assoc.
     apply Nat.divide_factor_l.
   }
   assert (Haa : a ≠ b). {
     intros H.
     rewrite <- (Nat.mul_1_r a) in H; subst b.
     apply Nat.mul_cancel_l in H; [ | flia Ha ].
     replace a with 2 in Hab by flia H.
     flia H5n Hab.
   }
   assert (Hbn : 0 < b ≤ n - 1). {
     rewrite Hb, Hab.
     split. {
       destruct a; [ easy | ].
       rewrite Nat.sub_succ, Nat.sub_0_r.
       destruct a; [ flia Ha | ].
       cbn; remember (a * S a); flia.
     }
     rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
     apply Nat.sub_le_mono_l; flia Ha.
   }
   clear - Haa Han Hbn.
   remember (n - 1) as m; clear n Heqm.
   rename m into n; move n at top.
   destruct (lt_dec a b) as [Hab| Hab].
   -now apply Nat_divide_mul_fact.
   -assert (H : b < a) by flia Haa Hab.
    rewrite Nat.mul_comm.
    now apply Nat_divide_mul_fact.
 }
 rewrite Hab at 1.
 assert (Hbn : 0 < b ≤ n - 1). {
   rewrite Hab.
   destruct b; [ easy | ].
   split; [ flia | ].
   destruct a; [ easy | ].
   destruct b; [ flia Hb | ].
   destruct a; [ flia Ha | ].
   cbn; remember (a * S (S b)); flia.
 }
 destruct (lt_dec a b) as [Halb| Halb].
 +now apply Nat_divide_mul_fact.
 +assert (H : b < a) by flia Halb Haeb.
  rewrite Nat.mul_comm.
  now apply Nat_divide_mul_fact.
-intros Hn.
 apply Bool.not_true_iff_false; intros Hp.
 apply Nat.mod_divide in Hn; [ | flia H5n ].
 specialize (prime_divides_fact_ge _ _ Hp Hn) as H1.
 flia H5n H1.
Qed.
