(* Lagrange's four-square theorem *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Require Import Misc Primes.

Lemma le_half_prime_square_diff : ∀ p a a',
   prime p
   → p mod 2 = 1
   → a ≤ (p - 1) / 2
   → a' ≤ (p - 1) / 2
   → a' < a
   → a ^ 2 ≢  a' ^ 2 mod p.
Proof.
intros * Hp Hp2 Ha Ha' Haa.
intros H1.
apply Nat_eq_mod_sub_0 in H1.
rewrite Nat_sqr_sub_sqr, Nat.mul_comm in H1.
apply Nat.mod_divide in H1; [ | now intros H2; subst p ].
specialize (Nat.gauss _ _ _ H1) as H2.
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

Lemma le_half_prime_succ_square_diff : ∀ p b b',
  prime p
  → p mod 2 = 1
  → b ≤ (p - 1) / 2
  → b' ≤ (p - 1) / 2
  → b < b'
  → b' ^ 2 + 1 ≢ (b ^ 2 + 1) mod p.
Proof.
intros * Hp Hp2 Hb Hb' Hbb' Hb1.
assert (Hpz : p ≠ 0) by now intros H; subst p.
    apply Nat_eq_mod_sub_0 in Hb1.
    replace (b' ^ 2 + 1 - (b ^ 2 + 1)) with (b' ^ 2 - b ^ 2) in Hb1 by flia.
    rewrite Nat_sqr_sub_sqr, Nat.mul_comm in Hb1.
    apply Nat.mod_divide in Hb1; [ | easy ].
    specialize (Nat.gauss _ _ _ Hb1) as H2.
    apply (Nat.mul_le_mono_l _ _ 2) in Hb.
    apply (Nat.mul_le_mono_l _ _ 2) in Hb'.
    rewrite <- Nat.divide_div_mul_exact in Hb; [ | easy | ]. 2: {
      specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H3.
      rewrite Hp2 in H3.
      rewrite H3, Nat.add_sub.
      apply Nat.divide_factor_l.
    }
    rewrite (Nat.mul_comm _ (p - 1)), Nat.div_mul in Hb; [ | easy ].
    rewrite <- Nat.divide_div_mul_exact in Hb'; [ | easy | ]. 2: {
      specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H3.
      rewrite Hp2 in H3.
      rewrite H3, Nat.add_sub.
      apply Nat.divide_factor_l.
    }
    rewrite (Nat.mul_comm _ (p - 1)), Nat.div_mul in Hb'; [ | easy ].
    assert (H : Nat.gcd p (b' - b) = 1). {
      apply eq_gcd_prime_small_1; [ easy | ].
      split; [ flia Hbb' | ].
      flia Hb Hb' Hbb'.
    }
    specialize (H2 H); clear H.
    destruct H2 as (k, Hk).
    destruct k. {
      apply Nat.eq_add_0 in Hk.
      now destruct Hk; subst b b'.
    }
    cbn in Hk.
    apply (f_equal (Nat.mul 2)) in Hk.
    do 2 rewrite Nat.mul_add_distr_l in Hk.
    specialize (prime_ge_2 _ Hp) as Hpge2.
    flia Hb Hb' Hk Hpge2.
Qed.

Theorem pigeonhole : ∀ a b f,
  0 < b < a
  → (∀ x, x < a → f x < b)
  → ∃ x x' y, x < a ∧ x' < a ∧ x <> x' ∧ f x = y ∧ f x' = y.
Proof.
intros * Hba Hf.
...
intros * Hba Hf.
remember (a - S b) as len eqn:Hlen; symmetry in Hlen.
replace a with (len + S b) in * by flia Hlen Hba.
clear a Hba Hlen.
revert b f Hf.
induction len; intros. {
  cbn in Hf; cbn.
  revert f Hf.
  induction b; intros. {
    specialize (Hf 0 (Nat.lt_0_succ _)).
    flia Hf.
  }
  destruct b. {
    exists 0, 1, 0.
    split; [ flia | ].
    split; [ flia | ].
    split; [ easy | ].
    split. {
      specialize (Hf 0).
      assert (H : 0 < 2) by flia.
      specialize (Hf H); clear H.
      flia Hf.
    } {
      specialize (Hf 1).
      assert (H : 1 < 2) by flia.
      specialize (Hf H); clear H.
      flia Hf.
    }
  }
  specialize (IHb (λ i, f i - 1)).
  cbn in IHb.
  assert (H : ∀ x, x < S (S b) → f x - 1 < S b). {
    intros x Hx.
    specialize (Hf x).
    assert (H : x < S (S (S b))) by flia Hx.
    specialize (Hf H).
    flia Hf.
  }
  specialize (IHb H); clear H.
  destruct IHb as (x & x' & y & Hxxy).
  destruct (Nat.eq_dec (f x) 0) as [Hfxz| Hfxz]. {
    rewrite Hfxz in Hxxy.
    cbn in Hxxy.
...
  exists x, x', (f x).
  split; [ flia Hxxy | ].
  split; [ flia Hxxy | ].
  split; [ easy | ].
  split; [ easy | ].
...
  flia Hxxy.
  split. {
    flia Hxxy.
...
intros * Hba Hf.
revert a f Hba Hf.
induction b; intros; [ flia Hba | ].
destruct b. {
  exists 0, 1, 0.
  split; [ flia Hba | ].
  split; [ easy | ].
  split; [ easy | ].
  split. {
    specialize (Hf 0).
    assert (H : 0 < a) by flia Hba.
    specialize (Hf H); clear H.
    flia Hf.
  } {
    specialize (Hf 1).
    assert (H : 1 < a) by flia Hba.
    specialize (Hf H); clear H.
    flia Hf.
  }
}
specialize (IHb (a - 1) (λ i, f i - 1)).
cbn in IHb.
assert (H : 0 < S b < a - 1) by flia Hba.
specialize (IHb H); clear H.
assert (H : ∀ x : nat, x < a - 1 → f x - 1 < S b). {
  intros x Hx.
  assert (H : x < a) by flia Hx.
  specialize (Hf x H) as H1.
  flia H1.
}
specialize (IHb H); clear H.
destruct IHb as (x & x' & y & Hxy).
exists x, x', (y + 1).
destruct (Nat.eq_dec (f x) 0) as [Hxz| Hxz]. {
  rewrite Hxz in Hxy; cbn in Hxy.
...

Lemma odd_prime_equal_sum_two_squares_plus_one : ∀ p,
  prime p → p mod 2 = 1 → ∃ a b, Nat.divide p (a ^ 2 + b ^ 2 + 1).
Proof.
intros * Hp Hp2.
assert
  (Ha :
   ∀ a a',
   a ≤ (p - 1) / 2
   → a' ≤ (p - 1) / 2
   → a ≠ a'
   → a ^ 2 ≢ a' ^ 2 mod p). {
  intros * Ha Ha' Haa.
  destruct (lt_dec a' a) as [Haa'| Haa']. {
    now apply le_half_prime_square_diff.
  } {
    assert (H : a < a') by flia Haa Haa'.
    intros H1.
    symmetry in H1.
    revert H1.
    now apply le_half_prime_square_diff.
  }
}
assert
  (Hb :
   ∀ b b',
   b ≤ (p - 1) / 2
   → b' ≤ (p - 1) / 2
   → b ≠ b'
   → (p - (b ^ 2 + 1) mod p) ≢ (p - (b' ^ 2 + 1) mod p) mod p). {
  intros * Hb Hb' Hbb H.
  assert (Hpz : p ≠ 0) by now (intros H1; subst p).
  remember ((b ^ 2 + 1) mod p) as b1 eqn:Hb1.
  remember ((b' ^ 2 + 1) mod p) as b'1 eqn:Hb'1.
  destruct (lt_dec b1 b'1) as [Hbb'| Hbb']. {
    apply Nat_eq_mod_sub_0 in H.
    replace (p - b1 - (p - b'1)) with (b'1 - b1) in H. 2: {
      specialize (Nat.mod_upper_bound (b' ^ 2 + 1) p Hpz) as H1.
      rewrite <- Hb'1 in H1.
      flia Hbb' H1.
    }
    apply Nat.mod_divide in H; [ | easy ].
    destruct H as (k, Hk).
    destruct k; [ flia Hk Hbb' | ].
    apply Nat.add_sub_eq_nz in Hk. 2: {
      now apply Nat.neq_mul_0.
    }
    specialize (Nat.mod_upper_bound (b' ^ 2 + 1) p Hpz) as H1.
    rewrite <- Hb'1, <- Hk in H1.
    flia H1.
  }
  destruct (lt_dec b'1 b1) as [Hbb'1| Hbb'1]. {
    symmetry in H.
    apply Nat_eq_mod_sub_0 in H.
    replace (p - b'1 - (p - b1)) with (b1 - b'1) in H. 2: {
      specialize (Nat.mod_upper_bound (b ^ 2 + 1) p Hpz) as H1.
      rewrite <- Hb1 in H1.
      flia Hbb' H1.
    }
    apply Nat.mod_divide in H; [ | easy ].
    destruct H as (k, Hk).
    destruct k; [ flia Hk Hbb'1 | ].
    apply Nat.add_sub_eq_nz in Hk. 2: {
      now apply Nat.neq_mul_0.
    }
    specialize (Nat.mod_upper_bound (b ^ 2 + 1) p Hpz) as H1.
    rewrite <- Hb1, <- Hk in H1.
    flia H1.
  }
  replace b'1 with b1 in * by flia Hbb' Hbb'1.
  clear Hbb' Hbb'1 H.
  rewrite Hb'1 in Hb1.
  destruct (lt_dec b b') as [Hbb'| Hbb']. {
    revert Hb1.
    now apply le_half_prime_succ_square_diff.
  } {
    symmetry in Hb1.
    revert Hb1.
    apply le_half_prime_succ_square_diff; try easy.
    apply Nat.nlt_ge in Hbb'.
    flia Hbb Hbb'.
  }
}
(* pigeonhole *)
...
