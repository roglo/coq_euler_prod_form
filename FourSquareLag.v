(* Lagrange's four-square theorem *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Import List List.ListNotations.
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
  b < a
  → (∀ x, x < a → f x < b)
  → ∃ x x' y, x < a ∧ x' < a ∧ x <> x' ∧ f x = y ∧ f x' = y.
Proof.
intros * Hba Hf.
revert a f Hba Hf.
induction b; intros; [ now specialize (Hf 0 Hba) | ].
destruct a; [ flia Hba | ].
apply Nat.succ_lt_mono in Hba.
remember (filter (λ i, f i =? b) (seq 0 a)) as la eqn:Hla.
symmetry in Hla.
destruct la as [| x1]. {
  assert (H : ∀ x, x < a → f x < b). {
    intros x Hx.
    destruct (Nat.eq_dec (f x) b) as [Hfxb| Hfxb]. {
      specialize (List_filter_nil _ _ Hla x) as H1.
      assert (H : x ∈ seq 0 a). {
        apply in_seq.
        split; [ flia | easy ].
      }
      specialize (H1 H); clear H; cbn in H1.
      now apply Nat.eqb_neq in H1.
    }
    assert (H : x < S a) by flia Hx.
    specialize (Hf x H); clear H.
    flia Hf Hfxb.
  }
  specialize (IHb a f Hba H); clear H.
  destruct IHb as (x & x' & y & Hxxy).
  exists x, x', y.
  split; [ flia Hxxy | ].
  split; [ flia Hxxy | easy ].
}
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  subst b.
  destruct a; [ flia Hba | ].
  specialize (Hf 0 (Nat.lt_0_succ _)) as H1.
  specialize (Hf (S a) (Nat.lt_succ_diag_r _)) as H2.
  exists 0, (S a), 0.
  split; [ flia | ].
  split; [ flia | ].
  split; [ easy | ].
  split; [ flia H1 | flia H2 ].
}
destruct la as [| x2]. {
  specialize (IHb a (λ i, if lt_dec i x1 then f i else f (i + 1)) Hba).
  cbn in IHb.
  assert (H : ∀ x, x < a → (if lt_dec x x1 then f x else f (x + 1)) < b). {
    intros x Hx.
    destruct (lt_dec x x1) as [Hxx| Hxx]. {
      assert (H : f x <> b).
...
Search filter.
filter_In: ∀ (A : Type) (f : A → bool) (x : A) (l : list A), x ∈ filter f l ↔ x ∈ l ∧ f x = true
...
    }
    apply Nat.nlt_ge in Hxx.
...
... suite ok
  }
  specialize (IHb H); clear H.
  destruct IHb as (x & x' & y & Hxxy).
  destruct (lt_dec x x1) as [Hxx1| Hxx1]. {
    destruct (lt_dec x' x1) as [Hx'x1| Hx'x1]. {
      exists x, x', y.
      split; [ flia Hxxy | ].
      split; [ flia Hxxy | easy ].
    }
    apply Nat.nlt_ge in Hx'x1.
    exists x, (x' + 1), y.
    split; [ flia Hxxy | ].
    split; [ flia Hxxy | ].
    split; [ | easy ].
    flia Hxx1 Hx'x1.
  }
  apply Nat.nlt_ge in Hxx1.
  destruct (lt_dec x' x1) as [Hx'x1| Hx'x1]. {
    exists (x + 1), x', y.
    split; [ flia Hxxy | ].
    split; [ flia Hxxy | ].
    split; [ | easy ].
    flia Hxx1 Hx'x1.
  }
  apply Nat.nlt_ge in Hx'x1.
  exists (x + 1), (x' + 1), y.
  split; [ flia Hxxy | ].
  split; [ flia Hxxy | ].
  split; [ | easy ].
  flia Hxxy.
}
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
