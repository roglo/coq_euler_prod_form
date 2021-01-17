(* Lagrange's four-squares theorem
   ∀ n, ∃ a b c d, n = a² + b² + c² + d²
   This is computable, i.e. a function is given, Nat_four_square_sol
   which, for a given n, returns a solution for a, b, c and d. The
   ending theorem proves its correctness. *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith ZArith.
Import List List.ListNotations.
Require Import Misc Primes FourSquareEuler.
Require Import Pigeonhole.

Definition Nat2Z_quad '(a, b, c, d) :=
  (Z.of_nat a, Z.of_nat b, Z.of_nat c, Z.of_nat d).

Definition resolve_a2_b2_1 p :=
  let u := (p - 1) / 2 in
  let f i :=
    if le_dec i u then (i ^ 2) mod p
    else (p - ((i - (u + 1)) ^ 2 + 1) mod p) mod p
  in
  let (x, x') := pigeonhole_fun (p + 1) f in
  let (a, b) :=
    if le_dec x u then (x, x' - (u + 1))
    else (x', x - (u + 1))
  in
  (a, b, (a ^ 2 + b ^ 2 + 1) / p).

(* given a solution (x1, x2, x3, x4) of the almost four squares for p,
   i.e. x1^2 + x2^2 + x3^2 + x4^2 = m * p for some m, returns another
   solution with a smaller value of m; works if the initial value of
   m is not 1 *)

Definition smaller_4sq_sol p x1 x2 x3 x4 :=
  let m := (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) / p in
  let g x :=
    if le_dec (x mod m) (m / 2) then Z.of_nat (x mod m)
    else (Z.of_nat (x mod m) - Z.of_nat m)%Z
  in
  let '(z1, z2, z3, z4) :=
    Z_Euler_s_four_square_sol
      (Z.of_nat x1) (Z.of_nat x2) (Z.of_nat x3) (Z.of_nat x4)
      (g x1) (g x2) (g x3) (g x4)
  in
  let '(w1, w2, w3, w4) :=
    (Z.abs_nat z1 / m, Z.abs_nat z2 / m,
     Z.abs_nat z3 / m, Z.abs_nat z4 / m)
  in
  let r := Z.to_nat (g x1 ^ 2 + g x2 ^ 2 + g x3 ^ 2 + g x4 ^ 2) / m in
  (r, (w1, w2, w3, w4)).

Fixpoint four_sq_sol_for_prime_loop it p x1 x2 x3 x4 m :=
  match it with
  | 0 => (x1, x2, x3, x4)
  | S it' =>
      if Nat.eq_dec m 1 then (x1, x2, x3, x4)
      else
        let '(r, (y1, y2, y3, y4)) := smaller_4sq_sol p x1 x2 x3 x4 in
        four_sq_sol_for_prime_loop it' p y1 y2 y3 y4 r
  end.

Definition four_sq_sol_for_prime p :=
  let '(a, b, m) := resolve_a2_b2_1 p in
  four_sq_sol_for_prime_loop m p a b 1 0 m.

Definition f_4sq_sol p a :=
  let '(a1, a2, a3, a4) := a in
  let '(m1, m2, m3, m4) := four_sq_sol_for_prime p in
  Z_Euler_s_four_square_sol a1 a2 a3 a4
    (Z.of_nat m1) (Z.of_nat m2) (Z.of_nat m3) (Z.of_nat m4).

Definition Z_four_square_sol n :=
  match n with
  | 0 => (0, 0, 0, 0)%Z
  | _ =>
      fold_right f_4sq_sol (Nat2Z_quad (four_sq_sol_for_prime 1))
        (prime_decomp n)
  end.

Definition Nat_four_square_sol n :=
  let '(a, b, c, d) := Z_four_square_sol n in
  (Z.abs_nat a, Z.abs_nat b, Z.abs_nat c, Z.abs_nat d).

(* *)

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

Theorem Nat_eq_mod_divide_sum : ∀ n a b,
  n ≠ 0
  → a ≡ (n - b mod n) mod n
  → Nat.divide n (a + b).
Proof.
intros * Hnz Hab.
destruct (le_dec n (a + b mod n)) as [Hpx| Hpx]. {
  apply Nat_eq_mod_sub_0 in Hab.
  rewrite Nat_sub_sub_assoc in Hab. 2: {
    split; [ | easy ].
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite <- (Nat.mod_add _ 1) in Hab; [ | easy ].
  rewrite Nat.mul_1_l in Hab.
  rewrite Nat.sub_add in Hab; [ | easy ].
  rewrite Nat.add_mod_idemp_r in Hab; [ | easy ].
  now apply Nat.mod_divide in Hab.
} {
  apply Nat.nle_gt in Hpx.
  symmetry in Hab.
  apply Nat_eq_mod_sub_0 in Hab.
  rewrite Nat_sub_sub_swap, <- Nat.sub_add_distr in Hab.
  remember (a + b mod n) as v eqn:Hv.
  move Hab at bottom.
  destruct (Nat.eq_dec v 0) as [Hvz| Hvz]. 2: {
    destruct v; [ easy | ].
    rewrite Nat.mod_small in Hab; [ | flia Hpx ].
    flia Hpx Hab.
  }
  move Hvz at top; subst v.
  symmetry in Hv.
  apply Nat.eq_add_0 in Hv.
  destruct Hv as (Hxz, Hx'uz).
  subst a; cbn.
  now apply Nat.mod_divide in Hx'uz.
}
Qed.

Lemma odd_prime_sum_two_squares_plus_one_lt : ∀ x x' p (u := (p - 1) / 2) k,
  prime p
  → p mod 2 = 1
  → x' < p + 1
  → x ≤ u
  → u < x'
  → x ^ 2 + (x' - (u + 1)) ^ 2 + 1 = k * p
  → k < p.
Proof.
intros * Hp Hp2 Hx'p Hxu Hx'u Hk.
assert (Hpz : p ≠ 0) by now (intros H1; subst p).
  apply (Nat.mul_lt_mono_pos_r p); [ flia Hpz | ].
  rewrite <- Hk.
  apply (le_lt_trans _ (u ^ 2 + u ^ 2 + 1)). {
    apply Nat.add_le_mono_r.
    apply Nat.add_le_mono; [ now apply Nat.pow_le_mono_l | ].
    apply Nat.pow_le_mono_l.
    apply (Nat.add_le_mono_r _ _ (u + 1)).
    rewrite Nat.sub_add; [ | flia Hx'u ].
    rewrite Nat.add_assoc.
    replace (u + u) with (2 * u) by flia.
    unfold u.
    rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
      apply Nat.mod_divide; [ easy | ].
      specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H2.
      rewrite Hp2 in H2.
      rewrite H2, Nat.add_sub, Nat.mul_comm.
      now apply Nat.mod_mul.
    }
    rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
    flia Hx'p.
  } {
    specialize (prime_ge_2 p Hp) as H2p.
    specialize (Nat.div_mod (p - 1) 2 (Nat.neq_succ_0 _)) as H1.
    assert (H : (p - 1) mod 2 = 0). {
      specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H.
      rewrite H, Hp2, Nat.add_sub, Nat.mul_comm.
      now apply Nat.mod_mul.
    }
    rewrite H, Nat.add_0_r in H1; clear H.
    assert (H : p = 2 * u + 1). {
      unfold u.
      rewrite <- H1.
      rewrite Nat.sub_add; [ easy | flia H2p ].
    }
    rewrite H.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
    rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
    replace (u ^ 2 + u ^ 2) with (2 * u ^ 2) by flia.
    rewrite Nat.pow_2_r.
    rewrite Nat.add_assoc.
    apply Nat.add_lt_mono_r.
    rewrite Nat.mul_shuffle0.
    do 2 rewrite Nat.mul_assoc.
    enough (Hu : 0 < u) by flia Hu.
    unfold u.
    apply (Nat.mul_lt_mono_pos_r 2); [ flia | ].
    rewrite Nat.mul_0_l.
    rewrite Nat.mul_comm, <- H1.
    flia H2p.
  }
Qed.

(*
Definition check_resolve_a2_b2_1 p :=
  let '(a, b, n) := resolve_a2_b2_1 p in
  (p, n, (a, b)).

Compute (map check_resolve_a2_b2_1 (Primes.firstn_primes' 20)).
*)

Lemma prime_divides_sum_two_squares_plus_one : ∀ p a b n,
  prime p
  → resolve_a2_b2_1 p = (a, b, n)
  → 0 < n < p ∧ a ^ 2 + b ^ 2 + 1 = n * p.
Proof.
intros p aa bb n Hp Hr.
destruct (Nat.eq_dec (p mod 2) 0) as [Hp2| Hp2]. {
  destruct (Nat.eq_dec p 2) as [H2| H2]. {
    subst p.
    cbn in Hr.
    injection Hr; clear Hr; intros; subst aa bb n.
    split; [ flia | easy ].
  }
  specialize (odd_prime p Hp H2) as H1.
  now rewrite Hp2 in H1.
}
assert (Hp3 : p mod 2 = 1). {
  specialize (Nat.mod_upper_bound p 2 (Nat.neq_succ_0 _)) as H1.
  flia Hp2 H1.
}
clear Hp2; rename Hp3 into Hp2.
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
unfold resolve_a2_b2_1 in Hr.
assert (Hpz : p ≠ 0) by now (intros H1; subst p).
set (u := (p - 1) / 2) in *.
set
  (f i :=
     if le_dec i u then (i ^ 2) mod p
     else (p - ((i - (u + 1)) ^ 2 + 1) mod p) mod p) in Hr.
remember (pigeonhole_fun (p + 1) f) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (x, x').
specialize (pigeonhole (p + 1) p f) as H1.
assert (H : p < p + 1) by flia.
specialize (H1 H); clear H.
assert (H : ∀ x, x < p + 1 → f x < p). {
  intros x1 Hx.
  unfold f; cbn - [ "/" ].
  destruct (le_dec x1 u); now apply Nat.mod_upper_bound.
}
specialize (H1 H x x' Hxx); clear H.
destruct H1 as (Hxp & Hx'p & Hxx' & Hfxx).
unfold f in Hfxx.
destruct (le_dec x u) as [Hxu| Hxu]. {
  injection Hr; clear Hr; intros Hn Hbb Haa.
  rewrite Haa, Hbb in Hn.
  do 2 rewrite Nat.mul_1_r, <- Nat.pow_2_r in Hn.
  destruct (le_dec x' u) as [Hx'u| Hx'u]. {
    now specialize (Ha x x' Hxu Hx'u Hxx') as H1.
  }
  apply Nat.nle_gt in Hx'u.
  specialize (Nat_eq_mod_divide_sum p _ _ Hpz Hfxx) as H1.
  rewrite Nat.add_assoc in H1.
  destruct H1 as (k, Hk).
  rewrite Haa, Hbb in Hk.
  rewrite Hk, Nat.div_mul in Hn; [ | easy ].
  subst k.
  split; [ | easy ].
  rewrite <- Haa, <- Hbb in Hk.
  split. {
    destruct n; [ | flia ].
    now rewrite Nat.add_1_r in Hk.
  }
  now apply (odd_prime_sum_two_squares_plus_one_lt x x').
}
apply Nat.nle_gt in Hxu.
destruct (le_dec x' u) as [Hx'u| Hx'u]. {
  injection Hr; clear Hr; intros Hn Hbb Haa.
  rewrite Haa, Hbb in Hn.
  do 2 rewrite Nat.mul_1_r, <- Nat.pow_2_r in Hn.
  symmetry in Hfxx.
  specialize (Nat_eq_mod_divide_sum p _ _ Hpz Hfxx) as H1.
  rewrite Nat.add_assoc in H1.
  destruct H1 as (k, Hk).
  rewrite Haa, Hbb in Hk.
  rewrite Hk, Nat.div_mul in Hn; [ | easy ].
  subst k.
  split; [ | easy ].
  rewrite <- Haa, <- Hbb in Hk.
  split. {
    destruct n; [ | flia ].
    now rewrite Nat.add_1_r in Hk.
  }
  now apply (odd_prime_sum_two_squares_plus_one_lt x' x).
}
apply Nat.nle_gt in Hx'u.
specialize (Hb (x - (u + 1)) (x' - (u + 1))) as H1.
exfalso; apply H1; [ | | | easy ]. {
  apply (Nat.add_le_mono_r _ _ (u + 1)).
  rewrite Nat.sub_add; [ | flia Hxu ].
  replace (u + (u + 1)) with (2 * u + 1) by flia.
  unfold u.
  rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
    apply Nat.mod_divide; [ easy | ].
    specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H2.
    rewrite Hp2 in H2.
    rewrite H2, Nat.add_sub, Nat.mul_comm.
    now apply Nat.mod_mul.
  }
  rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
  flia Hxp.
} {
  apply (Nat.add_le_mono_r _ _ (u + 1)).
  rewrite Nat.sub_add; [ | flia Hx'u ].
  replace (u + (u + 1)) with (2 * u + 1) by flia.
  unfold u.
  rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
    apply Nat.mod_divide; [ easy | ].
    specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H2.
    rewrite Hp2 in H2.
    rewrite H2, Nat.add_sub, Nat.mul_comm.
    now apply Nat.mod_mul.
  }
  rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
  flia Hx'p.
} {
  intros H; apply Hxx'.
  apply (Nat.add_cancel_r _ _ (u + 1)) in H.
  rewrite Nat.sub_add in H; [ | flia Hxu ].
  rewrite Nat.sub_add in H; [ | flia Hx'u ].
  easy.
}
Qed.

Lemma sqr_y_from_x_le : ∀ m
  (f := λ x, (if le_dec (x mod m) (m / 2) then x mod m else m - x mod m) ^ 2),
  m ≠ 0
  → ∀ x, f x ≤ (m / 2) ^ 2.
Proof.
intros * Hmz x.
set (v := m / 2) in f.
unfold f.
destruct (le_dec (x mod m) v) as [Hx1v| Hx1v]. {
  now apply Nat.pow_le_mono_l.
} {
  apply Nat.nle_gt in Hx1v.
  apply Nat.pow_le_mono_l.
  apply (Nat.add_le_mono_r _ _ (x mod m)).
  rewrite Nat.sub_add. 2: {
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  transitivity (v + (v + 1)). 2: {
    apply Nat.add_le_mono_l.
    now rewrite Nat.add_1_r.
  }
  replace (v + (v + 1)) with (2 * v + 1) by flia.
  unfold v.
  specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
  rewrite H1 at 1.
  apply Nat.add_le_mono_l.
  apply lt_n_Sm_le.
  now apply Nat.mod_upper_bound.
}
Qed.

Lemma sum_sqr_y_r_le_m : ∀ m x1 x2 x3 x4
  (f := λ x, (if le_dec (x mod m) (m / 2) then x mod m else m - x mod m) ^ 2),
  m ≠ 0
  → ∀ r, f x1 + f x2 + f x3 + f x4 = r * m → r ≤ m.
Proof.
intros * Hmz r Hr.
set (v := m / 2) in f.
set (sqr_y1 := f x1).
set (sqr_y2 := f x2).
set (sqr_y3 := f x3).
set (sqr_y4 := f x4).
specialize (sqr_y_from_x_le m Hmz) as Hx.
cbn - [ "/" ] in Hx.
assert (Hy1 : sqr_y1 ≤ v ^ 2) by apply Hx.
assert (Hy2 : sqr_y2 ≤ v ^ 2) by apply Hx.
assert (Hy3 : sqr_y3 ≤ v ^ 2) by apply Hx.
assert (Hy4 : sqr_y4 ≤ v ^ 2) by apply Hx.
apply (Nat.mul_le_mono_pos_r _ _ m); [ flia Hmz | ].
rewrite <- Hr.
transitivity (v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2). {
  apply Nat.add_le_mono; [ | easy ].
  apply Nat.add_le_mono; [ | easy ].
  now apply Nat.add_le_mono.
}
unfold v.
specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
replace (_ + _ + _ + _) with (4 * (m / 2) ^ 2) by flia.
rewrite <- Nat.pow_2_r.
rewrite H1 at 2.
rewrite Nat_sqr_add.
rewrite Nat.pow_mul_l.
replace (2 ^ 2) with 4 by easy.
flia.
Qed.

Lemma sum_sqr_x_sum_sqr_y_mod : ∀ p m x1 x2 x3 x4
  (f := λ x, (if le_dec (x mod m) (m / 2) then x mod m else m - x mod m) ^ 2),
  m ≠ 0
  → x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 = m * p
  → (f x1 + f x2 + f x3 + f x4) mod m = 0.
Proof.
intros * Hmz Hm.
set (v := m / 2) in f.
assert (Hxy2 : ∀ x, x ^ 2 ≡ f x mod m). {
  intros x.
  unfold f.
  destruct (le_dec (x mod m) v) as [Hxv| Hxv]. {
    now rewrite Nat_mod_pow_mod.
  } {
    rewrite Nat_sqr_sub. 2: {
      now apply Nat.lt_le_incl, Nat.mod_upper_bound.
    }
    symmetry.
    rewrite <- (Nat.mod_add _ (2 * (x mod m))); [ | easy ].
    rewrite Nat.mul_shuffle0.
    rewrite Nat.sub_add. 2: {
      remember (x mod m) as y.
      replace m with (y + (m - y)). 2: {
        rewrite Nat.add_comm, Nat.sub_add; [ easy | ].
        rewrite Heqy.
        now apply Nat.lt_le_incl, Nat.mod_upper_bound.
      }
      rewrite Nat_sqr_add.
      rewrite Nat.mul_add_distr_l.
      rewrite <- Nat.mul_assoc, <- Nat.pow_2_r.
      flia.
    }
    rewrite <- Nat.add_mod_idemp_l; [ | easy ].
    rewrite <- Nat_mod_pow_mod.
    rewrite Nat.mod_same; [ | easy ].
    rewrite Nat.pow_0_l; [ | easy ].
    rewrite Nat.mod_0_l; [ | easy ].
    rewrite Nat.add_0_l.
    now rewrite Nat_mod_pow_mod.
  }
}
rewrite Nat.add_mod; [ | easy ].
rewrite (Nat.add_mod (_ + _)); [ | easy ].
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite (Nat.add_mod (f x1)); [ | easy ].
rewrite <- Nat.add_assoc.
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite Nat.add_assoc.
do 4 rewrite <- Hxy2.
rewrite Nat.add_mod_idemp_r; [ | easy ].
rewrite Nat.add_comm, Nat.add_assoc.
rewrite Nat.add_mod_idemp_r; [ | easy ].
rewrite Nat.add_comm.
do 2 rewrite Nat.add_assoc.
rewrite Nat.add_mod_idemp_r; [ | easy ].
rewrite Nat.add_comm, Nat.add_assoc.
rewrite Nat.add_mod_idemp_r; [ | easy ].
rewrite Nat.add_comm.
do 2 rewrite Nat.add_assoc.
rewrite Hm.
rewrite Nat.mul_comm.
now apply Nat.mod_mul.
Qed.

Lemma sum_sqr_x_eq_mp_sqr_y_eq_sqr_m : ∀ p m x1 x2 x3 x4
  (f := λ x, (if le_dec (x mod m) (m / 2) then x mod m else m - x mod m) ^ 2),
  prime p
  → 0 < m < p
  → x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 = m * p
  → f x1 + f x2 + f x3 + f x4 = m ^ 2
  → m = 1.
Proof.
intros * Hp Hmp Hm Hr.
assert (Hmz : m ≠ 0) by flia Hmp.
rewrite Nat.pow_2_r in Hr.
destruct Hmp as (_, Hmp).
set (sqr_y1 := f x1) in *.
set (sqr_y2 := f x2) in *.
set (sqr_y3 := f x3) in *.
set (sqr_y4 := f x4) in *.
set (v := m / 2) in *.
assert (Hx : ∀ x, f x ≤ v ^ 2). {
  intros; unfold f.
  destruct (le_dec (x mod m) v) as [Hx1v| Hx1v]. {
    now apply Nat.pow_le_mono_l.
  } {
    apply Nat.nle_gt in Hx1v.
    apply Nat.pow_le_mono_l.
    apply (Nat.add_le_mono_r _ _ (x mod m)).
    rewrite Nat.sub_add. 2: {
      now apply Nat.lt_le_incl, Nat.mod_upper_bound.
    }
    transitivity (v + (v + 1)). 2: {
      apply Nat.add_le_mono_l.
      now rewrite Nat.add_1_r.
    }
    replace (v + (v + 1)) with (2 * v + 1) by flia.
    unfold v.
    specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
    rewrite H1 at 1.
    apply Nat.add_le_mono_l.
    apply lt_n_Sm_le.
    now apply Nat.mod_upper_bound.
  }
}
assert (Hy1 : sqr_y1 ≤ v ^ 2) by apply Hx.
assert (Hy2 : sqr_y2 ≤ v ^ 2) by apply Hx.
assert (Hy3 : sqr_y3 ≤ v ^ 2) by apply Hx.
assert (Hy4 : sqr_y4 ≤ v ^ 2) by apply Hx.
specialize (Nat.div_mod x1 m Hmz) as Hx1.
specialize (Nat.div_mod x2 m Hmz) as Hx2.
specialize (Nat.div_mod x3 m Hmz) as Hx3.
specialize (Nat.div_mod x4 m Hmz) as Hx4.
  assert (Hme : m mod 2 = 0). {
    enough (H : m mod 2 ≠ 1). {
      specialize (Nat.mod_upper_bound m 2 (Nat.neq_succ_0 _)) as H1.
      flia H H1.
    }
    intros Hm21.
    specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
    rewrite Hm21 in H1.
    assert (sqr_y1 + sqr_y2 + sqr_y3 + sqr_y4 < m * m). {
      apply (le_lt_trans _ (4 * ((m - 1) / 2) ^ 2)). {
        rewrite H1, Nat.add_sub.
        rewrite (Nat.mul_comm 2), Nat.div_mul; [ | easy ].
        fold v.
        transitivity (v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2). {
          flia Hy1 Hy2 Hy3 Hy4.
        }
        flia.
      } {
        rewrite H1 at 1.
        rewrite Nat.add_sub.
        rewrite (Nat.mul_comm 2), Nat.div_mul; [ | easy ].
        rewrite Nat.pow_2_r.
        replace 4 with (2 * 2) by flia.
        rewrite Nat.mul_shuffle0.
        rewrite Nat.mul_assoc.
        rewrite <- Nat.mul_assoc.
        apply Nat.mul_lt_mono; flia H1.
      }
    }
    flia Hr H.
  }
  (* each sqr_yi must be equal to v², i.e. (m/2)²
     therefore xi mod m = m / 2,
     then Σ xi² = mp = Σ (mqi+m/2)² = Σ (m²qi²+(m/2)²+2mqim/2)
     = m²Σ qi² + m² + Σ m²qi = m² (Σ qi² + 1 + Σ qi) = mp
     → impossible since m < p *)
  assert
    (Hy :
     sqr_y1 = v ^ 2 ∧ sqr_y2 = v ^ 2 ∧ sqr_y3 = v ^ 2 ∧ sqr_y4 = v ^ 2). {
    enough
      (Hy :
       ¬ (sqr_y1 ≠ v ^ 2) ∧ ¬ (sqr_y2 ≠ v ^ 2) ∧
       ¬ (sqr_y3 ≠ v ^ 2) ∧ ¬ (sqr_y4 ≠ v ^ 2)). {
      destruct Hy as (H1 & H2 & H3 & H4).
      apply Nat.eq_dne in H1.
      apply Nat.eq_dne in H2.
      apply Nat.eq_dne in H3.
      apply Nat.eq_dne in H4.
      easy.
    }
    assert (Hvvmm : v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2 ≤ m * m). {
      unfold v.
      specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
      rewrite Hme, Nat.add_0_r in H1.
      rewrite H1 at 5 6.
      rewrite Nat.pow_2_r.
      flia.
    }
    rewrite <- and_assoc.
    split. {
      apply Decidable.not_or.
      intros [Hss| Hss]. {
        assert (Hs1 : sqr_y1 < v ^ 2) by flia Hy1 Hss.
        assert (H : sqr_y1 + sqr_y2 + sqr_y3 + sqr_y4 < m * m). {
          apply (Nat.lt_le_trans _ (v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2)). {
            flia Hs1 Hy2 Hy3 Hy4.
          }
          easy.
        }
        flia Hr H.
      } {
        assert (Hs1 : sqr_y2 < v ^ 2) by flia Hy2 Hss.
        assert (H : sqr_y1 + sqr_y2 + sqr_y3 + sqr_y4 < m * m). {
          apply (Nat.lt_le_trans _ (v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2)). {
            flia Hy1 Hs1 Hy3 Hy4.
          }
          easy.
        }
        flia Hr H.
      }
    } {
      apply Decidable.not_or.
      intros [Hss| Hss]. {
        assert (Hs1 : sqr_y3 < v ^ 2) by flia Hy3 Hss.
        assert (H : sqr_y1 + sqr_y2 + sqr_y3 + sqr_y4 < m * m). {
          apply (Nat.lt_le_trans _ (v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2)). {
            flia Hy1 Hy2 Hs1 Hy4.
          }
          easy.
        }
        flia Hr H.
      } {
        assert (Hs1 : sqr_y4 < v ^ 2) by flia Hy4 Hss.
        assert (H : sqr_y1 + sqr_y2 + sqr_y3 + sqr_y4 < m * m). {
          apply (Nat.lt_le_trans _ (v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2)). {
            flia Hy1 Hy2 Hy3 Hs1.
          }
          easy.
        }
        flia Hr H.
      }
    }
  }
  (* therefore xi mod m = m / 2 *)
  destruct Hy as (Hsy1 & Hsy2 & Hsy3 & Hsy4).
  clear Hy1 Hy2 Hy3 Hy4.
  unfold f in sqr_y1, sqr_y2, sqr_y3, sqr_y4.
  assert (Hsy : ∀ x, m / 2 < x mod m → m - x mod m = m / 2 → False). {
    clear - Hmz Hme.
    intros * Hxv Hsy.
    apply Nat.add_sub_eq_nz in Hsy. 2: {
      intros Hv.
      specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
      now rewrite Hv, Hme in H1.
    }
    assert (Hxm2 : x mod m = m / 2). {
      replace (m / 2) with (m - m / 2). {
        rewrite <- Hsy at 2.
        now rewrite Nat.add_sub.
      } {
        specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
        rewrite Hme, Nat.add_0_r in H1.
        flia H1.
      }
    }
    flia Hxv Hxm2.
  }
  destruct (le_dec (x1 mod m) v) as [Hx1v| Hx1v]. 2: {
    apply Nat.nle_gt in Hx1v.
    apply Nat.pow_inj_l in Hsy1; [ | easy ].
    subst sqr_y1 v.
    now exfalso; apply (Hsy x1).
  }
  destruct (le_dec (x2 mod m) v) as [Hx2v| Hx2v]. 2: {
    apply Nat.nle_gt in Hx2v.
    apply Nat.pow_inj_l in Hsy2; [ | easy ].
    subst sqr_y2 v.
    now exfalso; apply (Hsy x2).
  }
  destruct (le_dec (x3 mod m) v) as [Hx3v| Hx3v]. 2: {
    apply Nat.nle_gt in Hx3v.
    apply Nat.pow_inj_l in Hsy3; [ | easy ].
    subst sqr_y3 v.
    now exfalso; apply (Hsy x3).
  }
  destruct (le_dec (x4 mod m) v) as [Hx4v| Hx4v]. 2: {
    apply Nat.nle_gt in Hx4v.
    apply Nat.pow_inj_l in Hsy4; [ | easy ].
    subst sqr_y4 v.
    now exfalso; apply (Hsy x4).
  }
  move Hx2v before Hx1v.
  move Hx3v before Hx2v.
  move Hx4v before Hx3v.
  clear Hsy.
  unfold sqr_y1 in Hsy1.
  unfold sqr_y2 in Hsy2.
  unfold sqr_y3 in Hsy3.
  unfold sqr_y4 in Hsy4.
  apply Nat.pow_inj_l in Hsy1; [ | easy ].
  apply Nat.pow_inj_l in Hsy2; [ | easy ].
  apply Nat.pow_inj_l in Hsy3; [ | easy ].
  apply Nat.pow_inj_l in Hsy4; [ | easy ].
  clear Hx1v Hx2v Hx3v Hx4v.
  rewrite Hsy1 in Hx1.
  rewrite Hsy2 in Hx2.
  rewrite Hsy3 in Hx3.
  rewrite Hsy4 in Hx4.
  (* then Σ xi² = mp = Σ (mqi+m/2)² = Σ (m²qi²+(m/2)²+2mqim/2)
     = m²Σ qi² + m² + Σ m²qi = m² (Σ qi² + 1 + Σ qi) = mp *)
  move Hm at bottom.
  rewrite Hx1, Hx2, Hx3, Hx4 in Hm.
  do 4 rewrite Nat_sqr_add in Hm.
  remember (x1 / m) as q1 eqn:Hq1.
  remember (x2 / m) as q2 eqn:Hq2.
  remember (x3 / m) as q3 eqn:Hq3.
  remember (x4 / m) as q4 eqn:Hq4.
  move q4 before q1; move q3 before q1; move q2 before q1.
  move Hq4 before Hq1; move Hq3 before Hq1; move Hq2 before Hq1.
  unfold v in Hm.
  setoid_rewrite (Nat.mul_shuffle0 2) in Hm.
  rewrite <- (Nat.divide_div_mul_exact m) in Hm; [ | easy | ]. 2: {
    now apply Nat.mod_divide in Hme.
  }
  rewrite (Nat.mul_comm 2) in Hm.
  rewrite Nat.div_mul in Hm; [ | easy ].
  ring_simplify in Hm.
  do 7 rewrite <- Nat.add_assoc in Hm.
  rewrite Nat.add_comm in Hm.
  do 6 rewrite Nat.add_assoc in Hm.
  replace (4 * (m / 2) ^ 2) with (m ^ 2) in Hm. 2: {
    specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
    rewrite Hme, Nat.add_0_r in H1.
    replace 4 with (2 ^ 2) by easy.
    rewrite <- Nat.pow_mul_l.
    now rewrite <- H1.
  }
  rewrite <- Nat.pow_2_r in Hm.
  do 4 rewrite Nat.pow_mul_l in Hm.
  replace (m ^ 2) with (m ^ 2 * 1) in Hm at 1 by flia.
  do 8 rewrite <- Nat.mul_add_distr_l in Hm.
  rewrite Nat.pow_2_r, <- Nat.mul_assoc in Hm.
  apply Nat.mul_cancel_l in Hm; [ | easy ].
  destruct (Nat.eq_dec (q1 + q2 + q3 + q4) 0) as [Hqz| Hqz]. {
    apply Nat.eq_add_0 in Hqz.
    destruct Hqz as (Hqz, H); move H at top; subst q4.
    apply Nat.eq_add_0 in Hqz.
    destruct Hqz as (Hqz, H); move H at top; subst q3.
    apply Nat.eq_add_0 in Hqz.
    destruct Hqz as (Hqz, H); move H at top; subst q2.
    move Hqz at top; subst q1.
    cbn in Hm.
    rewrite Nat.mul_1_r in Hm.
    flia Hmp Hm.
  }
  move Hp at bottom.
  rewrite <- Hm in Hp.
  apply prime_not_mul in Hp.
  destruct Hp as [Hp| Hp]; [ easy | ].
  flia Hp Hqz.
Qed.

Local Ltac end_z1_case Hz :=
  try (
      rewrite <- Zminus_mod_idemp_l;
      rewrite Hz; cbn;
      apply Z.mod_opp_l_z; [
        intros H;
        replace 0%Z with (Z.of_nat 0) in H by easy;
        now apply Nat2Z.inj_iff in H
      |
        rewrite <- mod_Zmod; [ | easy ];
        now rewrite Nat.mod_mul
      ]
  ).

Local Ltac z1_case_1 Hz :=
  repeat rewrite <- Nat2Z.inj_mul;
  repeat rewrite <- Nat2Z.inj_add;
  repeat rewrite <- Z.add_sub_swap;
  repeat rewrite <- Nat2Z.inj_add;
  end_z1_case Hz.

Local Ltac z1_case_2 Hz :=
  repeat rewrite Z.mul_sub_distr_l;
  repeat rewrite Z.add_sub_assoc;
  repeat rewrite <- Nat2Z.inj_mul;
  repeat rewrite <- Nat2Z.inj_add;
  repeat rewrite <- Z.add_sub_swap;
  repeat rewrite <- Nat2Z.inj_add;
  repeat rewrite <- Z.sub_add_distr;
  repeat rewrite <- Nat2Z.inj_add;
  repeat rewrite <- Nat.mul_add_distr_r;
  end_z1_case Hz.

Lemma z1_divides_m : ∀ m x1 x2 x3 x4
  (f := Z.of_nat)
  (g := λ x,
     if le_dec (x mod m) (m / 2)
     then Z.of_nat (x mod m)
     else (Z.of_nat (x mod m) - Z.of_nat m)%Z),
  m ≠ 0
  → (x1 * (x1 mod m) + x2 * (x2 mod m) + x3 * (x3 mod m) +
      x4 * (x4 mod m)) mod m = 0
  → ((f x1 * g x1 + f x2 * g x2 + f x3 * g x3 + f x4 * g x4)
         mod Z.of_nat m)%Z = 0%Z.
Proof.
intros * Hmz Hz.
apply (f_equal Z.of_nat) in Hz.
rewrite mod_Zmod in Hz; [ | easy ].
set (v := m / 2) in g.
unfold g.
destruct (le_dec (x1 mod m) v) as [Hx1v| Hx1v]. {
  z1_case_1 Hz.
  destruct (le_dec (x2 mod m) v) as [Hx2v| Hx2v]. {
    z1_case_1 Hz.
    destruct (le_dec (x3 mod m) v) as [Hx3v| Hx3v]. {
      z1_case_1 Hz.
      destruct (le_dec (x4 mod m) v); [ now z1_case_1 Hz | z1_case_2 Hz ].
    } {
      z1_case_2 Hz.
      destruct (le_dec (x4 mod m) v); [ z1_case_1 Hz | z1_case_2 Hz ].
    }
  } {
    z1_case_2 Hz.
    destruct (le_dec (x3 mod m) v) as [Hx3v| Hx3v]. {
      z1_case_1 Hz.
      destruct (le_dec (x4 mod m) v); [ z1_case_1 Hz | z1_case_2 Hz ].
    } {
      z1_case_2 Hz.
      destruct (le_dec (x4 mod m) v); [ z1_case_1 Hz | z1_case_2 Hz ].
    }
  }
} {
  z1_case_2 Hz.
  destruct (le_dec (x2 mod m) v) as [Hx2v| Hx2v]. {
    z1_case_1 Hz.
    destruct (le_dec (x3 mod m) v) as [Hx3v| Hx3v]. {
      z1_case_1 Hz.
      destruct (le_dec (x4 mod m) v); [ now z1_case_1 Hz | z1_case_2 Hz ].
    } {
      z1_case_2 Hz.
      destruct (le_dec (x4 mod m) v); [ z1_case_1 Hz | z1_case_2 Hz ].
    }
  } {
    z1_case_2 Hz.
    destruct (le_dec (x3 mod m) v) as [Hx3v| Hx3v]. {
      z1_case_1 Hz.
      destruct (le_dec (x4 mod m) v); [ z1_case_1 Hz | z1_case_2 Hz ].
    } {
      z1_case_2 Hz.
      destruct (le_dec (x4 mod m) v); [ z1_case_1 Hz | z1_case_2 Hz ].
    }
  }
}
Qed.

Local Ltac end_z2_case :=
  setoid_rewrite Nat.add_mod; try easy;
  rewrite Nat.mul_mod_idemp_r; [ | easy ];
  rewrite Nat.mul_mod_idemp_r; [ | easy ];
  rewrite Nat.add_mod_idemp_l; [ | easy ];
  rewrite Nat.add_mod_idemp_r; [ | easy ];
  rewrite Nat.mul_mod_idemp_r; [ | easy ];
  rewrite Nat.mul_mod_idemp_r; [ | easy ];
  rewrite Nat.add_mod_idemp_l; [ | easy ];
  rewrite Nat.add_mod_idemp_r; [ | easy ];
  remember (Z.of_nat (_ mod _)) as x;
  setoid_rewrite Nat.mul_comm; subst x;
  rewrite Z.sub_diag;
  rewrite Z.mod_0_l; [ easy | ];
  intros H;
  replace 0%Z with (Z.of_nat 0) in H by easy;
  now apply Nat2Z.inj_iff in H.

Local Ltac z2_case_1 :=
  rewrite <- Nat2Z.inj_mul;
  repeat rewrite Z.add_sub_assoc;
  repeat rewrite <- Nat2Z.inj_add;
  try (
    rewrite <- Z.add_sub_swap;
    rewrite Z.sub_sub_distr;
    do 2 rewrite <- Z.add_sub_swap
  );
  try (
    rewrite Z.sub_add_distr;
    rewrite Z.sub_sub_distr;
    rewrite <- Z.add_sub_swap;
    rewrite <- Z.sub_add_distr;
    do 2 rewrite <- Nat2Z.inj_add
  );
  try (
    rewrite <- Z.sub_add_distr;
    repeat rewrite <- Nat2Z.inj_add
  );
  try (
    rewrite <- Z.add_sub_swap;
    rewrite <- Z.sub_add_distr;
    do 2 rewrite <- Nat2Z.inj_add
  );
  try (
    rewrite Zminus_mod;
    rewrite <- mod_Zmod; [ | easy ];
    rewrite <- mod_Zmod; [ | easy ];
    try (rewrite Nat.mod_add; [ | easy ]);
    repeat (rewrite Nat_mod_add_l_mul_r; [ | easy ]);
    end_z2_case
  ).

Local Ltac z2_case_2 :=
  rewrite Z.mul_sub_distr_l;
  do 2 rewrite <- Nat2Z.inj_mul;
  try (
    repeat rewrite Z.sub_add_distr;
    repeat rewrite Z.sub_sub_distr;
    repeat rewrite <- Z.add_sub_swap;
    repeat rewrite <- Z.sub_add_distr;
    repeat rewrite <- Nat2Z.inj_add;
    rewrite Zminus_mod;
    rewrite <- mod_Zmod; [ | easy ];
    rewrite <- mod_Zmod; [ | easy ];
    try (rewrite Nat.mod_add; [ | easy ]);
    repeat (rewrite Nat_mod_add_l_mul_r; [ | easy ]);
    repeat (
      rewrite <- Nat.add_mod_idemp_r; [ | easy ];
      rewrite Nat.mod_mul; [ rewrite Nat.add_0_r | easy ]
    );
    end_z2_case
  );
  repeat rewrite Z.add_sub_assoc;
  repeat rewrite <- Nat2Z.inj_add;
  try (
    rewrite <- Z.add_sub_swap;
    rewrite <- Nat2Z.inj_add
  ).

Lemma z2_z3_z4_divides_m : ∀ m x1 x2 x3 x4
  (f := Z.of_nat)
  (g := λ x,
     if le_dec (x mod m) (m / 2)
     then Z.of_nat (x mod m)
     else (Z.of_nat (x mod m) - Z.of_nat m)%Z),
  m ≠ 0
  → ((f x1 * g x2 + f x4 * g x3 - (f x2 * g x1 + f x3 * g x4))
         mod Z.of_nat m)%Z = 0%Z.
Proof.
intros * Hmz.
set (v := m / 2) in g.
unfold g.
destruct (le_dec (x2 mod m) v) as [Hx2v| Hx2v]. {
  z2_case_1.
  destruct (le_dec (x3 mod m) v) as [Hx3v| Hx3v]. {
    z2_case_1.
    destruct (le_dec (x1 mod m) v) as [Hx1v| Hx1v]. {
      z2_case_1.
      destruct (le_dec (x4 mod m) v); [ z2_case_1 | z2_case_2 ].
    } {
      z2_case_2.
      destruct (le_dec (x4 mod m) v); [ z2_case_1 | z2_case_2 ].
    }
  } {
    z2_case_2.
    destruct (le_dec (x1 mod m) v) as [Hx1v| Hx1v]. {
      z2_case_1.
      destruct (le_dec (x4 mod m) v); [ z2_case_1 | z2_case_2 ].
    } {
      z2_case_2.
      destruct (le_dec (x4 mod m) v); [ z2_case_1 | z2_case_2 ].
    }
  }
} {
  z2_case_2.
  destruct (le_dec (x3 mod m) v) as [Hx3v| Hx3v]. {
    z2_case_1.
    destruct (le_dec (x1 mod m) v) as [Hx1v| Hx1v]. {
      z2_case_1.
      destruct (le_dec (x4 mod m) v); [ z2_case_1 | z2_case_2 ].
    } {
      z2_case_2.
      destruct (le_dec (x4 mod m) v); [ z2_case_1 | z2_case_2 ].
    }
  } {
    z2_case_2.
    destruct (le_dec (x1 mod m) v) as [Hx1v| Hx1v]. {
      z2_case_1.
      destruct (le_dec (x4 mod m) v); [ z2_case_1 | z2_case_2 ].
    } {
      z2_case_2.
      destruct (le_dec (x4 mod m) v); [ z2_case_1 | z2_case_2 ].
    }
  }
}
Qed.

(*
Compute (smaller_4sq_sol 31 4 13 1 0).
Compute (check_resolve_a2_b2_1 29).
Compute (smaller_4sq_sol 29 0 12 1 0).

Compute (map check_resolve_a2_b2_1 (Primes.firstn_primes' 20)).
Compute (check_resolve_a2_b2_1 59).
Compute (smaller_4sq_sol 59 1 23 1 0).
Compute (smaller_4sq_sol 59 10 3 0 3).
Compute (check_resolve_a2_b2_1 239).
Compute (smaller_4sq_sol 239 5 90 1 0).
Compute (smaller_4sq_sol 239 31 15 0 3).
Compute (smaller_4sq_sol 239 5 3 6 13).
Compute (5 ^ 2 + 3 ^ 2 + 6 ^ 2 + 13 ^ 2).
Compute (31 ^ 2 + 15 ^ 2 + 3 ^ 2).
Compute (5 ^ 2 + 90 ^ 2 + 1).
*)

Theorem Z_sqr_abs_nat : ∀ x, Z.abs_nat x ^ 2 = Z.to_nat (x ^ 2).
Proof.
intros x.
unfold Z.abs_nat.
destruct x as [| px| px]; [ easy | | ]. {
  cbn.
  rewrite Nat.mul_1_r, Pos.mul_1_r; symmetry.
  apply Pos2Nat.inj_mul.
} {
  cbn.
  rewrite Nat.mul_1_r, Pos.mul_1_r; symmetry.
  apply Pos2Nat.inj_mul.
}
Qed.

Theorem Z_sqr_nonneg : ∀ x, (0 <= x ^ 2)%Z.
intros.
now apply Z.pow_even_nonneg, Zeven_equiv.
Qed.

Theorem smaller_4sq_sol_if_m_neq_1 : ∀ p x1 x2 x3 x4 m w1 w2 w3 w4 r,
  prime p
  → x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 = m * p
  → smaller_4sq_sol p x1 x2 x3 x4 = (r, (w1, w2, w3, w4))
  → 1 < m < p
  → 0 < r < m ∧ w1 ^ 2 + w2 ^ 2 + w3 ^ 2 + w4 ^ 2 = r * p.
Proof.
intros * Hp Hmp Hrw H1m.
assert (Hpz : p ≠ 0) by now (intros H; subst p).
assert (Hmz : m ≠ 0) by flia H1m.
unfold smaller_4sq_sol in Hrw.
rewrite Hmp in Hrw.
rewrite Nat.div_mul in Hrw; [ | easy ].
set (g := λ x,
  if le_dec (x mod m) (m / 2) then Z.of_nat (x mod m)
  else (Z.of_nat (x mod m) - Z.of_nat m)%Z).
replace
  (if le_dec (x1 mod m) (m / 2) then Z.of_nat (x1 mod m)
   else (Z.of_nat (x1 mod m) - Z.of_nat m)%Z)
with (g x1) in Hrw by easy.
replace
  (if le_dec (x2 mod m) (m / 2) then Z.of_nat (x2 mod m)
   else (Z.of_nat (x2 mod m) - Z.of_nat m)%Z)
with (g x2) in Hrw by easy.
replace
  (if le_dec (x3 mod m) (m / 2) then Z.of_nat (x3 mod m)
   else (Z.of_nat (x3 mod m) - Z.of_nat m)%Z)
with (g x3) in Hrw by easy.
replace
  (if le_dec (x4 mod m) (m / 2) then Z.of_nat (x4 mod m)
   else (Z.of_nat (x4 mod m) - Z.of_nat m)%Z)
with (g x4) in Hrw by easy.
set (v := m / 2) in g.
remember
  (Z_Euler_s_four_square_sol
     (Z.of_nat x1) (Z.of_nat x2) (Z.of_nat x3) (Z.of_nat x4)
     (g x1) (g x2) (g x3) (g x4)) as w eqn:Hw.
symmetry in Hw.
remember Z.pow as zp.
destruct w as (((z1, z2), z3), z4).
injection Hrw; clear Hrw; intros Hw4 Hw3 Hw2 Hw1 Hrm.
subst zp.
symmetry in Hw4, Hw3, Hw2, Hw1.
unfold Z_Euler_s_four_square_sol in Hw.
injection Hw; clear Hw; intros Hz4 Hz3 Hz2 Hz1.
symmetry in Hz1, Hz2, Hz3, Hz4.
specialize Z_Euler_s_four_square_identity as H1.
specialize (H1 (Z_of_nat x1) (Z_of_nat x2)) as H1.
specialize (H1 (Z_of_nat x3) (Z_of_nat x4)) as H1.
specialize (H1 (g x1) (g x2) (g x3) (g x4)).
unfold Z_Euler_s_four_square_sol in H1.
rewrite <- Hz1, <- Hz2, <- Hz3, <- Hz4 in H1.
assert
  (Hz :
     (x1 * (x1 mod m) + x2 * (x2 mod m) + x3 * (x3 mod m) +
      x4 * (x4 mod m)) mod m = 0). {
  rewrite <- Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.mul_mod_idemp_r; [ | easy ].
  rewrite Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.add_comm.
  do 2 rewrite Nat.add_assoc.
  rewrite <- Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.mul_mod_idemp_r; [ | easy ].
  rewrite Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.add_comm.
  do 2 rewrite Nat.add_assoc.
  rewrite <- Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.mul_mod_idemp_r; [ | easy ].
  rewrite Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.add_comm.
  do 2 rewrite Nat.add_assoc.
  rewrite <- Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.mul_mod_idemp_r; [ | easy ].
  rewrite Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.add_comm.
  do 2 rewrite Nat.add_assoc.
  do 4 rewrite <- Nat.pow_2_r.
  rewrite Hmp, Nat.mul_comm.
  now apply Nat.mod_mul.
}
rewrite (Z.add_comm (Z.of_nat x2 * g x3)%Z) in Hz4.
assert (Hz1m : (z1 mod Z.of_nat m = 0)%Z). {
  rewrite Hz1.
  now apply z1_divides_m.
}
assert (Hz2m : (z2 mod Z.of_nat m = 0)%Z). {
  rewrite Hz2.
  now apply z2_z3_z4_divides_m.
}
assert (Hz3m : (z3 mod Z.of_nat m = 0)%Z). {
  rewrite Hz3.
  now apply z2_z3_z4_divides_m.
}
assert (Hz4m : (z4 mod Z.of_nat m = 0)%Z). {
  rewrite Hz4.
  now apply z2_z3_z4_divides_m.
}
assert (Hzmz : Z.of_nat m ≠ 0%Z). {
  intros H.
  replace 0%Z with (Z.of_nat 0) in H by easy.
  now apply Nat2Z.inj_iff in H.
}
assert (Hzpz : Z.of_nat p ≠ 0%Z). {
  intros H.
  replace 0%Z with (Z.of_nat 0) in H by easy.
  now apply Nat2Z.inj_iff in H.
}
apply Z.mod_divide in Hz1m; [ | easy ].
apply Z.mod_divide in Hz2m; [ | easy ].
apply Z.mod_divide in Hz3m; [ | easy ].
apply Z.mod_divide in Hz4m; [ | easy ].
destruct Hz1m as (k1, Hz1m).
destruct Hz2m as (k2, Hz2m).
destruct Hz3m as (k3, Hz3m).
destruct Hz4m as (k4, Hz4m).
rewrite Hz1m in Hw1.
rewrite Hz2m in Hw2.
rewrite Hz3m in Hw3.
rewrite Hz4m in Hw4.
move k1 after k4; move k3 before k1; move k2 before k1.
rewrite Zabs2Nat.inj_mul in Hw1, Hw2, Hw3, Hw4.
rewrite Zabs2Nat.id in Hw1, Hw2, Hw3, Hw4.
rewrite Nat.div_mul in Hw1; [ | easy ].
rewrite Nat.div_mul in Hw2; [ | easy ].
rewrite Nat.div_mul in Hw3; [ | easy ].
rewrite Nat.div_mul in Hw4; [ | easy ].
specialize (sum_sqr_x_sum_sqr_y_mod p m x1 x2 x3 x4) as Hfx.
fold v in Hfx.
set (f x := (if le_dec (x mod m) v then x mod m else m - x mod m) ^ 2) in Hfx.
move f after g.
specialize (Hfx Hmz Hmp).
assert (Hgf : ∀ x, (g x ^ 2 = Z.of_nat (f x))%Z). {
  intros x.
  unfold g, f.
  destruct (le_dec (x mod m) v) as [Hxv| Hxv]. {
    rewrite Z.pow_2_r, Nat.pow_2_r.
    now rewrite Nat2Z.inj_mul.
  } {
    apply Nat.nle_gt in Hxv.
    rewrite Z.pow_2_r, Nat.pow_2_r.
    rewrite Nat2Z.inj_mul.
    rewrite Nat2Z.inj_sub. 2: {
      now apply Nat.lt_le_incl, Nat.mod_upper_bound.
    }
    rewrite <- Z.opp_involutive.
    rewrite <- Z.mul_opp_l.
    rewrite Z.opp_sub_distr.
    rewrite Z.add_comm.
    rewrite <- Z.mul_opp_r.
    rewrite Z.opp_sub_distr.
    rewrite (Z.add_comm (- Z.of_nat m)%Z).
    easy.
  }
}
do 4 rewrite Hgf in H1.
do 3 rewrite <- Nat2Z.inj_add in H1.
assert (Hzn : ∀ a, (Z.of_nat a ^ 2 = Z.of_nat (a ^ 2))%Z). {
  intros a.
  cbn; rewrite Nat.mul_1_r, Z.mul_1_r.
  symmetry; apply Nat2Z.inj_mul.
}
do 4 rewrite Hzn in H1; clear Hzn.
do 3 rewrite <- Nat2Z.inj_add in H1.
rewrite Hmp in H1.
rewrite Hz1m, Hz2m, Hz3m, Hz4m in H1.
do 4 rewrite Z.pow_mul_l in H1.
do 3 rewrite <- Z.mul_add_distr_r in H1.
move H1 at bottom.
do 4 rewrite Hgf in Hrm.
do 3 rewrite <- Nat2Z.inj_add in Hrm.
rewrite Nat2Z.id in Hrm.
move Hrm before Hfx.
specialize (Nat.div_mod (f x1 + f x2 + f x3 + f x4) m Hmz) as H2.
rewrite Hrm, Hfx, Nat.add_0_r in H2.
rewrite H2 in H1.
rewrite <- Nat2Z.inj_mul in H1.
replace (m * p * (m * r)) with (p * r * (m * m)) in H1 by flia.
rewrite Nat2Z.inj_mul in H1.
rewrite (Nat2Z.inj_mul m) in H1.
rewrite <- Z.pow_2_r in H1.
apply Z.mul_cancel_r in H1; [ | now apply Z.pow_nonzero ].
symmetry in H1.
assert (Hmr : r ≤ m). {
  rewrite Nat.mul_comm in H2.
  specialize sum_sqr_y_r_le_m as Hmr.
  specialize (Hmr m x1 x2 x3 x4 Hmz r).
  fold v in Hmr.
  fold f in Hmr.
  now specialize (Hmr H2).
}
destruct (Nat.eq_dec r m) as [Hrme| Hrme]. {
  exfalso.
  move Hrme at top; subst r; clear Hmr.
  specialize (sum_sqr_x_eq_mp_sqr_y_eq_sqr_m p m x1 x2 x3 x4) as H3.
  fold v in H3.
  fold f in H3.
  specialize (H3 Hp).
  assert (H : 0 < m < p) by flia H1m.
  rewrite <- Nat.pow_2_r in H2.
  specialize (H3 H Hmp H2); clear H.
  flia H1m H3.
}
destruct (Nat.eq_dec r 0) as [Hrz| Hrz]. {
  move Hrz at top; subst r; clear Hmr Hrme.
  rewrite Nat.mul_0_r in H2.
  apply Nat.eq_add_0 in H2.
  destruct H2 as (H2, Hx4).
  apply Nat.eq_add_0 in H2.
  destruct H2 as (H2, Hx3).
  apply Nat.eq_add_0 in H2.
  destruct H2 as (Hx1, Hx2).
  unfold f in Hx1, Hx2, Hx3, Hx4.
  apply Nat.pow_eq_0 in Hx1; [ | easy ].
  apply Nat.pow_eq_0 in Hx2; [ | easy ].
  apply Nat.pow_eq_0 in Hx3; [ | easy ].
  apply Nat.pow_eq_0 in Hx4; [ | easy ].
  destruct (le_dec (x1 mod m) v) as [Hx1v| Hx1v]. 2: {
    specialize (Nat.mod_upper_bound x1 m Hmz) as H.
    flia Hx1 H.
  }
  clear Hx1v.
  destruct (le_dec (x2 mod m) v) as [Hx2v| Hx2v]. 2: {
    specialize (Nat.mod_upper_bound x2 m Hmz) as H.
    flia Hx2 H.
  }
  clear Hx2v.
  destruct (le_dec (x3 mod m) v) as [Hx3v| Hx3v]. 2: {
    specialize (Nat.mod_upper_bound x3 m Hmz) as H.
    flia Hx3 H.
  }
  clear Hx3v.
  destruct (le_dec (x4 mod m) v) as [Hx4v| Hx4v]. 2: {
    specialize (Nat.mod_upper_bound x4 m Hmz) as H.
    flia Hx4 H.
  }
  clear Hx4v.
  move Hmp at bottom.
  apply Nat.mod_divide in Hx1; [ | easy ].
  apply Nat.mod_divide in Hx2; [ | easy ].
  apply Nat.mod_divide in Hx3; [ | easy ].
  apply Nat.mod_divide in Hx4; [ | easy ].
  destruct Hx1 as (l1, Hx1).
  destruct Hx2 as (l2, Hx2).
  destruct Hx3 as (l3, Hx3).
  destruct Hx4 as (l4, Hx4).
  rewrite Hx1, Hx2, Hx3, Hx4 in Hmp.
  do 4 rewrite Nat.pow_mul_l in Hmp.
  do 3 rewrite <- Nat.mul_add_distr_r in Hmp.
  rewrite Nat.mul_comm in Hmp.
  rewrite (Nat.pow_2_r m), <- Nat.mul_assoc in Hmp.
  apply Nat.mul_cancel_l in Hmp; [ | easy ].
  move Hp at bottom.
  rewrite <- Hmp in Hp.
  apply prime_not_mul in Hp.
  destruct Hp as [Hp| Hp]; [ flia H1m Hp | ].
  rewrite Hp, Nat.mul_1_r in Hmp.
  flia Hmp H1m.
}
split. {
  split; [ flia Hrz | flia Hmr Hrme ].
}
rewrite Hw1, Hw2, Hw3, Hw4.
do 4 rewrite Z_sqr_abs_nat.
rewrite <- Z2Nat.inj_add; [ | apply Z_sqr_nonneg | apply Z_sqr_nonneg ].
rewrite <- Z2Nat.inj_add; [ | | apply Z_sqr_nonneg ]. 2: {
  apply Z.add_nonneg_nonneg; apply Z_sqr_nonneg.
}
rewrite <- Z2Nat.inj_add; [ | | apply Z_sqr_nonneg ]. 2: {
  apply Z.add_nonneg_nonneg; [ | apply Z_sqr_nonneg ].
  apply Z.add_nonneg_nonneg; apply Z_sqr_nonneg.
}
rewrite H1.
now rewrite Nat2Z.id, Nat.mul_comm.
Qed.

(*
Compute (four_sq_sol_for_prime 239).
Compute (5 ^ 2 + 3 ^ 2 + 6 ^ 2 + 13 ^ 2).
*)

Lemma four_sq_for_prime_loop : ∀ x1 x2 x3 x4 m it p y1 y2 y3 y4,
  prime p
  → 0 < m < p
  → m ≤ it
  → four_sq_sol_for_prime_loop it p x1 x2 x3 x4 m = (y1, y2, y3, y4)
  → x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 = m * p
  → y1 ^ 2 + y2 ^ 2 + y3 ^ 2 + y4 ^ 2 = p.
Proof.
intros * Hp Hmp Hit H4s Hx.
revert x1 x2 x3 x4 m H4s Hx Hmp Hit.
induction it; intros; [ flia Hmp Hit | ].
cbn - [ smaller_4sq_sol ] in H4s.
destruct (Nat.eq_dec m 1) as [Hm1| Hm1]. {
  subst m.
  injection H4s; intros; subst y1 y2 y3 y4.
  now rewrite Nat.mul_1_l in Hx.
}
remember (smaller_4sq_sol p x1 x2 x3 x4) as ry eqn:Hry; symmetry in Hry.
destruct ry as (r, (((z1, z2), z3), z4)).
specialize (smaller_4sq_sol_if_m_neq_1) as H1.
specialize (H1 p x1 x2 x3 x4).
specialize (H1 m z1 z2 z3 z4 r Hp Hx Hry).
assert (H : 1 < m < p) by flia Hmp Hm1.
specialize (H1 H); clear H.
destruct H1 as (Hrm, Hz).
apply (IHit z1 z2 z3 z4 r); [ easy | easy | | ]. {
  flia Hmp Hrm.
} {
  flia Hrm Hit.
}
Qed.

Theorem four_sq_for_prime : ∀ p x1 x2 x3 x4,
  p = 1 ∨ prime p
  → four_sq_sol_for_prime p = (x1, x2, x3, x4)
  → x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 = p.
Proof.
intros * Hp H4s.
destruct Hp as [Hp| Hp]. {
  subst p; cbn in H4s; cbn - [ "^" ].
  now injection H4s; intros; subst.
}
unfold four_sq_sol_for_prime in H4s.
remember (resolve_a2_b2_1 p) as abm eqn:Habm; symmetry in Habm.
destruct abm as ((a, b), m).
specialize prime_divides_sum_two_squares_plus_one as H1.
specialize (H1 p a b m Hp Habm).
destruct H1 as (Hmp & Habm1).
assert (Habm4 : a ^ 2 + b ^ 2 + 1 ^ 2 + 0 ^ 2 = m * p). {
  rewrite Nat.pow_0_l; [ | easy ].
  now rewrite Nat.pow_1_l, Nat.add_0_r.
}
clear Habm1.
now apply (four_sq_for_prime_loop a b 1 0 m m).
Qed.

(*
Compute (four_square_sol 120).
Compute
  (let n := 120 in let '(a, b, c, d) := four_square_sol n in
   (a, b, c, d, n, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)).
Compute
  (map
     (λ n,
      let '(a, b, c, d) := four_square_sol n in
      (a, b, c, d, n, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) (seq 1 100)).
*)

Theorem Nat2Z_inj_sqr : ∀ n, Z.of_nat (n ^ 2) = (Z.of_nat n ^ 2)%Z.
Proof.
intros.
rewrite Nat.pow_2_r.
rewrite Nat2Z.inj_mul.
symmetry; apply Z.pow_2_r.
Qed.

Lemma Z_four_squares_loop :  ∀ a b c d p l,
  fold_right f_4sq_sol (Nat2Z_quad (four_sq_sol_for_prime p)) l =
    (a, b, c, d)
  → (∀ d, d ∈ p :: l → d = 1 ∨ prime d)
  → (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)%Z = Z.of_nat (fold_left Nat.mul l p).
Proof.
intros * Habcd Hpl.
revert a b c d p Hpl Habcd.
induction l as [| q]; intros. {
  cbn in Habcd; cbn - [ "^"%Z ].
  specialize (Hpl p (or_introl eq_refl)).
  specialize (four_sq_for_prime p) as H1.
  specialize (H1 (Z.abs_nat a) (Z.abs_nat b)).
  specialize (H1 (Z.abs_nat c) (Z.abs_nat d)).
  specialize (H1 Hpl).
  remember (four_sq_sol_for_prime p) as xyzt eqn:Hxyzt.
  symmetry in Hxyzt.
  destruct xyzt as (((x, y), z), t).
  cbn in Habcd.
  injection Habcd; clear Habcd; intros; subst a b c d.
  do 4 rewrite Zabs2Nat.id in H1.
  specialize (H1 eq_refl).
  rewrite <- H1.
  do 4 rewrite <- Nat2Z_inj_sqr.
  now do 3 rewrite <- Nat2Z.inj_add.
}
cbn in Habcd.
remember (fold_right f_4sq_sol (Nat2Z_quad (four_sq_sol_for_prime p)) l)
  as xyzt eqn:Hxyzt.
symmetry in Hxyzt.
destruct xyzt as (((x, y), z), t).
specialize (IHl x y z t p).
cbn - [ "^"%Z ].
assert (H : ∀ d, d ∈ p :: l → d = 1 ∨ prime d). {
  intros r Hr.
  apply Hpl.
  destruct Hr as [Hr| Hr]; [ now left | now right; right ].
}
specialize (IHl H Hxyzt); clear H.
rewrite fold_left_mul_from_1 in IHl.
rewrite fold_left_mul_from_1.
rewrite Nat.mul_shuffle0.
rewrite Nat2Z.inj_mul.
rewrite <- IHl.
unfold f_4sq_sol in Habcd.
remember (four_sq_sol_for_prime q) as mmmm eqn:Hmm.
symmetry in Hmm.
destruct mmmm as (((m1, m2), m3), m4).
specialize (four_sq_for_prime) as H1.
specialize (H1 q m1 m2 m3 m4).
assert (H : q = 1 ∨ prime q). {
  apply Hpl.
  now right; left.
}
specialize (H1 H Hmm); clear H.
rewrite <- H1.
specialize (Z_Euler_s_four_square_identity) as H2.
specialize (H2 x y z t).
specialize (H2 (Z.of_nat m1) (Z.of_nat m2) (Z.of_nat m3) (Z.of_nat m4)).
rewrite Habcd in H2.
rewrite <- H2; f_equal.
do 3 rewrite Nat2Z.inj_add.
now do 4 rewrite Nat2Z_inj_sqr.
Qed.

Theorem Z_four_squares : ∀ n,
  ∀ a b c d, Z_four_square_sol n = (a, b, c, d)
  → (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)%Z = Z.of_nat n.
Proof.
intros * H4s.
unfold Z_four_square_sol in H4s.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  now injection H4s; clear H4s; intros; subst.
}
replace n with (S (n - 1)) in H4s at 1 by flia Hnz.
rewrite <- (prime_decomp_prod n); [ | easy ].
specialize (in_prime_decomp_is_prime n) as Hp.
remember (prime_decomp n) as l eqn:Hl; clear n Hnz Hl.
apply Z_four_squares_loop; [ easy | ].
intros r Hr.
destruct Hr as [Hr| Hr]; [ now left | now right; apply Hp ].
Qed.

Theorem Nat_four_squares : ∀ n,
  ∀ a b c d, Nat_four_square_sol n = (a, b, c, d)
  → a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n.
Proof.
intros * H4s.
remember (Z_four_square_sol n) as pqrs eqn:Hpqrs.
symmetry in Hpqrs.
destruct pqrs as (((p, q), r), s).
unfold Nat_four_square_sol in H4s.
rewrite Hpqrs in H4s.
injection H4s; clear H4s; intros; subst.
specialize (Z_four_squares n p q r s Hpqrs) as H1.
apply Nat2Z.inj.
do 3 rewrite Nat2Z.inj_add.
do 4 rewrite Nat2Z_inj_sqr.
do 4 rewrite Zabs2Nat.id_abs.
rewrite <- Z.pow_even_abs; [ | now apply Zeven_equiv ].
rewrite <- Z.pow_even_abs; [ | now apply Zeven_equiv ].
rewrite <- Z.pow_even_abs; [ | now apply Zeven_equiv ].
rewrite <- Z.pow_even_abs; [ | now apply Zeven_equiv ].
easy.
Qed.
