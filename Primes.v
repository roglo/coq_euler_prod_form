(* Euler Product Formula *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Misc.

Fixpoint prime_test cnt n d :=
  match cnt with
  | 0 => true
  | S c =>
      match n mod d with
      | 0 => false
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
  ↔ ∃ a b : nat, a < n ∧ b < n ∧ n = a * b.
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
     flia Han Hcnt.
   }
   specialize (H1 H).
   exfalso; apply H1; rewrite Hnab, Nat.mul_comm.
   apply Nat.mod_mul; flia H.
 }
 cbn.
 remember (n mod k) as m eqn:Hm; symmetry in Hm.
 destruct m; [ easy | ].
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
  → ∃ a b, a < n ∧ b < n ∧ n = a * b.
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
split; [ | easy ].
destruct a; [ flia Hab Hb | ].
destruct a; [ flia Hab Hb | flia ].
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

Theorem infinite_many_primes : ∀ n, ∃ m, m > n ∧ is_prime m = true.
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

Theorem prime_test_mod_ne_0 : ∀ n k,
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
destruct m; [ easy | ].
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
  split; [ flia Hp2 | rewrite <- Hk; cbn; flia ].
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
