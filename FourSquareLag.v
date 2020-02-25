(* Lagrange's four-square theorem *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
(*
Import List List.ListNotations.
*)
Require Import Misc Primes.
(*
Require Import Totient QuadRes.
*)

Lemma between_half_prime_square_diff : ∀ p a a',
   prime p
   → p mod 2 = 1
   → 0 ≤ a ≤ (p - 1) / 2
   → 0 ≤ a' ≤ (p - 1) / 2
   → a' < a
   → a ^ 2 ≢  a' ^ 2 mod p.
Proof.
intros * Hp Hp2 Ha Ha' Haa.
intros H1.
apply Nat_eq_mod_sub_0 in H1.
rewrite Nat_pow_sub_pow in H1; [ | easy | flia Haa ].
cbn in H1.
do 3 rewrite Nat.mul_1_r in H1.
rewrite Nat.add_0_r in H1.
apply Nat.mod_divide in H1; [ | now intros H2; subst p ].
specialize (Nat.gauss _ _ _ H1) as H2.
destruct Ha as (_, Ha).
destruct Ha' as (_, Ha').
apply (Nat.mul_le_mono_l _ _ 2) in Ha.
apply (Nat.mul_le_mono_l _ _ 2) in Ha'.
rewrite <- Nat.divide_div_mul_exact in Ha; [ | easy | ]. 2: {
  specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H3.
  rewrite Hp2 in H3.
  rewrite H3, Nat.add_sub.
  apply Nat.divide_factor_l.
}
rewrite (Nat.mul_comm _ (p - 1)), Nat.div_mul in Ha; [ | easy ].
rewrite <- Nat.divide_div_mul_exact in Ha'; [ | easy | ]. 2: {
  specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H3.
  rewrite Hp2 in H3.
  rewrite H3, Nat.add_sub.
  apply Nat.divide_factor_l.
}
rewrite (Nat.mul_comm _ (p - 1)), Nat.div_mul in Ha'; [ | easy ].
assert (H : Nat.gcd p (a - a') = 1). {
  apply eq_gcd_prime_small_1; [ easy | ].
  split; [ flia Haa | ].
  flia Ha Ha' Haa.
}
specialize (H2 H); clear H.
destruct H2 as (k, Hk).
destruct k. {
  apply Nat.eq_add_0 in Hk.
  now destruct Hk; subst a a'.
}
cbn in Hk.
apply (f_equal (Nat.mul 2)) in Hk.
do 2 rewrite Nat.mul_add_distr_l in Hk.
specialize (prime_ge_2 _ Hp) as Hpge2.
flia Ha Ha' Hk Hpge2.
Qed.

Lemma odd_prime_equal_sum_two_squares_plus_one : ∀ p,
  prime p → p mod 2 = 1 → ∃ a b, Nat.divide p (a ^ 2 + b ^ 2 + 1).
Proof.
intros * Hp Hp2.
assert
  (Ha :
   ∀ a a',
   0 ≤ a ≤ (p - 1) / 2
   → 0 ≤ a' ≤ (p - 1) / 2
   → a ≠ a'
   → a ^ 2 ≢ a' ^ 2 mod p). {
  intros * Ha Ha' Haa.
  destruct (lt_dec a' a) as [Haa'| Haa']. {
    now apply between_half_prime_square_diff.
  } {
    assert (H : a < a') by flia Haa Haa'.
    intros H1.
    symmetry in H1.
    revert H1.
    now apply between_half_prime_square_diff.
  }
}
assert
  (Hb :
   ∀ b b',
   0 ≤ b ≤ (p - 1) / 2
   → 0 ≤ b' ≤ (p - 1) / 2
   → b ≠ b'
   → (p - (b ^ 2 + 1) mod p) ≢ (p - (b' ^ 2 + 1) mod p) mod p). {
  intros * Hb Hb' Hbb.
  intros H.
  destruct (lt_dec b' b) as [Hbb'| Hbb']. {
    apply Nat_eq_mod_sub_0 in H.
Search (_ - (_ - _)).
    rewrite Nat_sub_sub_assoc in H.
Search (_ - _ - (_ - _)).
Search ((_ mod _ - _) mod _).
...
