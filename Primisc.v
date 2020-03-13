(* experiments with primes... *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Misc Primes.
Require Import Totient QuadRes.

Theorem prime_pow_φ : ∀ p, prime p →
  ∀ k, k ≠ 0 → φ (p ^ k) = p ^ (k - 1) * φ p.
Proof.
intros * Hp * Hk.
rewrite (prime_φ p); [ | easy ].
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ now subst p | ].
unfold φ.
unfold coprimes.
rewrite (filter_ext_in _ (λ d, negb (d mod p =? 0))). 2: {
  intros a Ha.
  apply in_seq in Ha.
  rewrite Nat.add_comm, Nat.sub_add in Ha. 2: {
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  remember (a mod p) as r eqn:Hr; symmetry in Hr.
  destruct r. {
    apply Nat.eqb_neq.
    apply Nat.mod_divides in Hr; [ | easy ].
    destruct Hr as (d, Hd).
    rewrite Hd.
    destruct k; [ easy | cbn ].
    rewrite Nat.gcd_mul_mono_l.
    intros H.
    apply Nat.eq_mul_1 in H.
    destruct H as (H, _).
    now subst p.
  } {
    apply Nat.eqb_eq.
    assert (Hg : Nat.gcd p a = 1). {
      rewrite <- Nat.gcd_mod; [ | easy ].
      rewrite Nat.gcd_comm.
      apply eq_gcd_prime_small_1; [ easy | ].
      split; [ rewrite Hr; flia | ].
      now apply Nat.mod_upper_bound.
    }
    clear - Hg.
    induction k; [ easy | ].
    now apply Nat_gcd_1_mul_l.
  }
}
clear Hp.
replace k with (k - 1 + 1) at 1 by flia Hk.
rewrite Nat.pow_add_r, Nat.pow_1_r.
remember (p ^ (k - 1)) as a eqn:Ha.
clear k Hk Ha Hpz.
induction a; [ easy | ].
cbn.
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]. {
  subst p; cbn.
  now rewrite Nat.mul_0_r.
}
destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
  subst a; cbn.
  do 2 rewrite Nat.add_0_r.
  rewrite (filter_ext_in _ (λ d, true)). 2: {
    intros a Ha.
    apply in_seq in Ha.
    rewrite Nat.mod_small; [ | flia Ha ].
    destruct a; [ flia Ha | easy ].
  }
  clear.
  destruct p; [ easy | ].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  induction p; [ easy | ].
  rewrite <- (Nat.add_1_r p).
  rewrite seq_app, filter_app, app_length.
  now rewrite IHp.
}
rewrite <- Nat.add_sub_assoc. 2: {
  apply Nat.neq_0_lt_0.
  now apply Nat.neq_mul_0.
}
rewrite Nat.add_comm.
rewrite seq_app, filter_app, app_length.
rewrite IHa, Nat.add_comm; f_equal.
rewrite Nat.add_comm, Nat.sub_add. 2: {
  apply Nat.neq_0_lt_0.
  now apply Nat.neq_mul_0.
}
replace p with (1 + (p - 1)) at 2 by flia Hpz.
rewrite seq_app, filter_app, app_length.
cbn.
rewrite Nat.mod_mul; [ | easy ]; cbn.
rewrite (filter_ext_in _ (λ d, true)). 2: {
  intros b Hb.
  remember (b mod p) as c eqn:Hc; symmetry in Hc.
  destruct c; [ | easy ].
  apply Nat.mod_divide in Hc; [ | easy ].
  destruct Hc as (c, Hc).
  subst b.
  apply in_seq in Hb.
  destruct Hb as (Hb1, Hb2).
  clear - Hb1 Hb2; exfalso.
  revert p a Hb1 Hb2.
  induction c; intros; [ flia Hb1 | ].
  cbn in Hb1, Hb2.
  destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
    subst a.
    cbn in Hb1, Hb2.
    destruct p; [ flia Hb1 | ].
    rewrite Nat.sub_succ, Nat.sub_0_r in Hb2.
    flia Hb2.
  }
  destruct (Nat.eq_dec p 0) as [Hpz| Hpz]. {
    subst p; flia Hb1.
  }
  specialize (IHc p (a - 1)) as H1.
  assert (H : (a - 1) * p + 1 ≤ c * p). {
    rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
    rewrite <- Nat.add_sub_swap. 2: {
      destruct a; [ easy | ].
      cbn; flia.
    }
    flia Hb1 Haz Hpz.
  }
  specialize (H1 H); clear H.
  apply H1.
  apply (Nat.add_lt_mono_l _ _ p).
  eapply lt_le_trans; [ apply Hb2 | ].
  ring_simplify.
  do 2 apply Nat.add_le_mono_r.
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
  rewrite Nat.sub_add. 2: {
    destruct a; [ easy | rewrite Nat.mul_succ_r; flia ].
  }
  now rewrite Nat.mul_comm.
}
clear.
remember (a * p + 1) as b; clear a Heqb.
destruct p; [ easy | ].
rewrite Nat.sub_succ, Nat.sub_0_r.
revert b.
induction p; intros; [ easy | ].
rewrite <- Nat.add_1_r.
rewrite seq_app, filter_app, app_length.
now rewrite IHp.
Qed.

Theorem divide_add_div_le : ∀ m p q,
  2 ≤ p
  → 2 ≤ q
  → Nat.divide p m
  → Nat.divide q m
  → m / p + m / q ≤ m.
Proof.
intros * H2p H2q Hpm Hqm.
destruct Hpm as (kp, Hkp).
destruct Hqm as (kq, Hkq).
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ flia Hpz H2p | ].
destruct (Nat.eq_dec q 0) as [Hqz| Hqz]; [ flia Hqz H2q | ].
rewrite Hkq at 2.
rewrite Nat.div_mul; [ | easy ].
rewrite Hkp at 1.
rewrite Nat.div_mul; [ | easy ].
apply (Nat.mul_le_mono_pos_r _ _ (p * q)). {
  destruct p; [ easy | ].
  destruct q; [ easy | cbn; flia ].
}
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_assoc, <- Hkp.
rewrite Nat.mul_assoc, Nat.mul_shuffle0, <- Hkq.
rewrite <- Nat.mul_add_distr_l.
apply Nat.mul_le_mono_l.
rewrite Nat.add_comm.
apply Nat.add_le_mul. {
  destruct p; [ easy | ].
  destruct p; [ easy | flia ].
} {
  destruct q; [ easy | ].
  destruct q; [ easy | flia ].
}
Qed.

Theorem length_filter_mod_seq : ∀ a b,
  a mod b ≠ 0
  → length (filter (λ d, negb (d mod b =? 0)) (seq a b)) = b - 1.
Proof.
intros a b Hab1.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
specialize (Nat.div_mod a b Hbz) as H1.
remember (a / b) as q eqn:Hq.
remember (a mod b) as r eqn:Hr.
move q after r; move Hq after Hr.
replace b with (b - r + r) at 1. 2: {
  apply Nat.sub_add.
  now rewrite Hr; apply Nat.lt_le_incl, Nat.mod_upper_bound.
}
rewrite seq_app, filter_app, app_length.
rewrite List_filter_all_true. 2: {
  intros c Hc.
  apply Bool.negb_true_iff, Nat.eqb_neq.
  apply in_seq in Hc.
  intros Hcon.
  specialize (Nat.div_mod c b Hbz) as H2.
  rewrite Hcon, Nat.add_0_r in H2.
  remember (c / b) as s eqn:Hs.
  subst a c.
  clear Hcon.
  destruct Hc as (Hc1, Hc2).
  rewrite Nat.add_sub_assoc in Hc2. 2: {
    rewrite Hr.
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Nat.add_sub_swap in Hc2; [ | flia ].
  rewrite Nat.add_sub in Hc2.
  replace b with (b * 1) in Hc2 at 3 by flia.
  rewrite <- Nat.mul_add_distr_l in Hc2.
  apply Nat.mul_lt_mono_pos_l in Hc2; [ | flia Hbz ].
  rewrite Nat.add_1_r in Hc2.
  apply Nat.succ_le_mono in Hc2.
  apply Nat.nlt_ge in Hc1.
  apply Hc1; clear Hc1.
  apply (le_lt_trans _ (b * q)); [ | flia Hab1 ].
  now apply Nat.mul_le_mono_l.
}
rewrite seq_length.
replace r with (1 + (r - 1)) at 3 by flia Hab1.
rewrite seq_app, filter_app, app_length; cbn.
rewrite H1 at 1.
rewrite Nat.add_sub_assoc. 2: {
  rewrite Hr.
  now apply Nat.lt_le_incl, Nat.mod_upper_bound.
}
rewrite Nat.add_sub_swap; [ | flia ].
rewrite Nat.add_sub.
rewrite Nat_mod_add_l_mul_l; [ | easy ].
rewrite Nat.mod_same; [ cbn | easy ].
rewrite List_filter_all_true. 2: {
  intros c Hc.
  apply Bool.negb_true_iff, Nat.eqb_neq.
  apply in_seq in Hc.
  intros Hcon.
  specialize (Nat.div_mod c b Hbz) as H2.
  rewrite Hcon, Nat.add_0_r in H2.
  remember (c / b) as s eqn:Hs.
  subst a c.
  clear Hcon.
  destruct Hc as (Hc1, Hc2).
  rewrite Nat.add_sub_assoc in Hc2. 2: {
    rewrite Hr.
    rewrite Nat_mod_add_l_mul_l; [ | easy ].
    rewrite Nat.mod_small; [ flia Hab1 | ].
    rewrite Hr.
    now apply Nat.mod_upper_bound.
  }
  rewrite Nat.add_sub_swap in Hc2; [ | flia ].
  rewrite Nat.add_sub in Hc2.
  rewrite Nat.add_sub_assoc in Hc2. 2: {
    rewrite Hr.
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Nat.sub_add in Hc2; [ | flia ].
  rewrite Nat.add_sub_assoc in Hc1. 2: {
    rewrite Hr.
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Nat.add_sub_swap in Hc1; [ | flia ].
  rewrite Nat.add_sub in Hc1.
  rewrite Nat.add_shuffle0 in Hc2.
  apply Nat.nlt_ge in Hc1; apply Hc1; clear Hc1.
  rewrite Nat.add_1_r.
  apply -> Nat.succ_le_mono.
  replace b with (b * 1) at 3 by flia.
  rewrite <- Nat.mul_add_distr_l.
  apply Nat.mul_le_mono_l.
  replace b with (b * 1) in Hc2 at 3 by flia.
  rewrite <- Nat.mul_add_distr_l in Hc2.
  apply Nat.nlt_ge; intros Hc1.
  replace s with ((q + 1) + S (s - (q + 2))) in Hc2 by flia Hc1.
  rewrite Nat.mul_add_distr_l in Hc2.
  apply Nat.add_lt_mono_l in Hc2.
  apply Nat.nle_gt in Hc2; apply Hc2; clear Hc2.
  rewrite Nat.mul_comm; cbn.
  transitivity b; [ | flia Hc1 ].
  rewrite Hr.
  now apply Nat.lt_le_incl, Nat.mod_upper_bound.
}
rewrite seq_length.
rewrite Nat.add_sub_assoc; [ | flia Hab1 ].
rewrite Nat.sub_add; [ easy | ].
rewrite Hr.
now apply Nat.lt_le_incl, Nat.mod_upper_bound.
Qed.

Theorem gcd_1_div_mul_exact : ∀ m p q kp kq,
  q ≠ 0
  → Nat.gcd p q = 1
  → m = kp * p
  → m = kq * q
  → kp = q * (kp / q).
Proof.
intros * Hqz Hg Hkp Hkq.
rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
  apply (Nat.gauss _ p). {
    rewrite Nat.mul_comm, <- Hkp, Hkq.
    now exists kq.
  } {
    now rewrite Nat.gcd_comm.
  }
}
now rewrite Nat.mul_comm, Nat.div_mul.
Qed.

Theorem Nat_gcd_1_mul_divide : ∀ m p q,
  Nat.gcd p q = 1
  → Nat.divide p m
  → Nat.divide q m
  → Nat.divide (p * q) m.
Proof.
intros * Hg Hpm Hqm.
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
  subst m; cbn.
  now exists 0.
}
assert (Hpz : p ≠ 0). {
  destruct Hpm as (k, Hk).
  now intros H; rewrite H, Nat.mul_0_r in Hk.
}
assert (Hqz : q ≠ 0). {
  destruct Hqm as (k, Hk).
  now intros H; rewrite H, Nat.mul_0_r in Hk.
}
destruct Hpm as (kp, Hkp).
destruct Hqm as (kq, Hkq).
exists (kp * kq / m).
rewrite Nat.mul_comm.
rewrite Hkp at 2.
rewrite Nat.div_mul_cancel_l; [ | easy | ]. 2: {
  intros H; subst kp.
  rewrite Hkp in Hkq; cbn in Hkq.
  symmetry in Hkq.
  apply Nat.eq_mul_0 in Hkq.
  destruct Hkq as [H| H]; [ | now subst q ].
  now subst kq.
}
rewrite (Nat.mul_comm p), <- Nat.mul_assoc.
rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
  exists (kq / p).
  rewrite Nat.mul_comm.
  rewrite Nat.gcd_comm in Hg.
  now apply (gcd_1_div_mul_exact m q p kq kp).
}
rewrite (Nat.mul_comm p).
rewrite Nat.div_mul; [ | easy ].
now rewrite Nat.mul_comm.
Qed.

Theorem prime_divisors_decomp : ∀ n a,
  a ∈ prime_divisors n ↔ a ∈ prime_decomp n.
Proof.
intros.
split; intros Ha. {
  apply filter_In in Ha.
  destruct Ha as (Ha, H).
  apply Bool.andb_true_iff in H.
  destruct H as (Hpa, Hna).
  apply Nat.eqb_eq in Hna.
  apply in_seq in Ha.
  apply Nat.mod_divide in Hna; [ | flia Ha ].
  apply prime_decomp_in_iff.
  split; [ | split ]; [ flia Ha | easy | easy ].
} {
  apply filter_In.
  apply prime_decomp_in_iff in Ha.
  destruct Ha as (Hnz & Ha & Han).
  split. {
    apply in_seq.
    split. {
      transitivity 2; [ flia | ].
      now apply prime_ge_2.
    } {
      destruct Han as (k, Hk); subst n.
      destruct k; [ easy | flia ].
    }
  }
  apply Bool.andb_true_iff.
  split; [ easy | ].
  apply Nat.eqb_eq.
  apply Nat.mod_divide in Han; [ easy | ].
  now intros H1; subst a.
}
Qed.

Theorem prime_divisors_nil_iff: ∀ n, prime_divisors n = [] ↔ n = 0 ∨ n = 1.
Proof.
intros.
split; intros Hn. {
  apply prime_decomp_nil_iff.
  remember (prime_decomp n) as l eqn:Hl; symmetry in Hl.
  destruct l as [| a l]; [ easy | ].
  specialize (proj2 (prime_divisors_decomp n a)) as H1.
  rewrite Hl, Hn in H1.
  now exfalso; apply H1; left.
} {
  now destruct Hn; subst n.
}
Qed.

(* primitive roots *)

Fixpoint prim_root_cycle_loop n g gr it :=
  match it with
  | 0 => []
  | S it' =>
      let gr' := (g * gr) mod n in
      if gr' =? g then [gr]
      else gr :: prim_root_cycle_loop n g gr' it'
  end.

Definition prim_root_cycle n g := prim_root_cycle_loop n g g (n - 1).

Definition is_prim_root n g :=
  match Nat.gcd g n with
  | 1 => length (prim_root_cycle n g) =? φ n
  | _ => false
  end.

Definition prim_roots n := filter (is_prim_root n) (seq 1 (n - 1)).

Compute (prim_roots 14, φ (φ 14)).
Compute (prim_root_cycle 14 5).
Compute (sort Nat.leb (map (λ i, Nat_pow_mod 5 i 14) (seq 1 14))).

Fixpoint in_list_nat n l :=
  match l with
  | [] => false
  | a :: l => if n =? a then true else in_list_nat n l
  end.

Definition is_quad_res p n := in_list_nat n (quad_res p).

Theorem fold_φ : ∀ n, length (coprimes n) = φ n.
Proof. easy. Qed.

Theorem φ_interv : ∀ n, 2 ≤ n → 1 ≤ φ n < n.
Proof.
intros * H2n.
unfold φ.
unfold coprimes.
split. {
  destruct n; [ easy | ].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  destruct n; [ flia H2n | ].
  remember (S (S n)) as ssn.
  cbn; rewrite Nat.gcd_1_r; cbn; flia.
} {
  rewrite List_length_filter_negb; [ | apply seq_NoDup ].
  rewrite seq_length.
  flia H2n.
}
Qed.

(* multiplicative order modulo *)

Fixpoint ord_mod_aux it n a i :=
  match it with
  | 0 => 0
  | S it' =>
      if Nat.eq_dec (Nat_pow_mod a i n) 1 then i
      else ord_mod_aux it' n a (i + 1)
  end.

Definition ord_mod n a := ord_mod_aux n n a 1.

Theorem List_seq_eq_nil : ∀ a b, seq a b = [] → b = 0.
Proof.
intros * Hs.
now destruct b.
Qed.

Lemma ord_mod_aux_prop : ∀ it n a i,
  n + 1 ≤ it + i
  → (∀ j, 1 ≤ j < i → (a ^ j) mod n ≠ 1)
  → 2 ≤ n
  → Nat.gcd a n = 1
  → a ^ ord_mod_aux it n a i mod n = 1 ∧
     ∀ m, 0 < m < ord_mod_aux it n a i → (a ^ m) mod n ≠ 1.
Proof.
intros * Hnit Hj H2n Hg.
assert (Hnz : n ≠ 0) by flia H2n.
destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
  subst a.
  rewrite Nat.gcd_0_l in Hg; flia H2n Hg.
}
revert i Hnit Hj.
induction it; intros. {
  cbn; cbn in Hnit.
  specialize (euler_fermat_little n a Hnz Haz Hg) as H1.
  rewrite (Nat.mod_small 1) in H1; [ | easy ].
  specialize (Hj (φ n)) as H2.
  assert (H : 1 ≤ φ n < i). {
    specialize (φ_interv n H2n) as H3.
    split; [ easy | ].
    transitivity n; [ easy | flia Hnit ].
  }
  now specialize (H2 H).
}
cbn.
rewrite Nat_pow_mod_is_pow_mod; [ | easy ].
destruct (Nat.eq_dec (a ^ i mod n) 1) as [Ha1| Ha1]. {
  split; [ easy | ].
  intros m Hm.
  now apply Hj.
}
apply IHit; [ flia Hnit | ].
intros k Hk.
destruct (Nat.eq_dec k i) as [Hki| Hki]; [ now subst k | ].
apply Hj; flia Hk Hki.
Qed.

Theorem ord_mod_prop : ∀ n a,
  2 ≤ n
  → Nat.gcd a n = 1
  → (a ^ ord_mod n a) mod n = 1 ∧
     ∀ m, 0 < m < ord_mod n a → (a ^ m) mod n ≠ 1.
Proof.
intros * H2n Hg.
apply ord_mod_aux_prop; [ easy | | easy | easy ].
intros j Hj.
flia Hj.
Qed.

Theorem ord_mod_1_r : ∀ n, 2 ≤ n → ord_mod n 1 = 1.
Proof.
intros * H2n.
destruct n; [ easy | ].
cbn - [ Nat_pow_mod ].
rewrite Nat_pow_mod_is_pow_mod; [ | easy ].
rewrite Nat.pow_1_r.
rewrite Nat.mod_1_l; [ easy | flia H2n ].
Qed.

Lemma eq_ord_mod_aux_0 : ∀ it n a i,
  n ≠ 0
  → i ≠ 0
  → ord_mod_aux it n a i = 0
  → ∀ j, i ≤ j < i + it → a ^ j mod n ≠ 1.
Proof.
intros * Hnz Hiz Ho * Hj.
revert i Hiz Ho Hj.
induction it; intros; [ flia Hj | ].
cbn in Ho.
rewrite Nat_pow_mod_is_pow_mod in Ho; [ | easy ].
destruct (Nat.eq_dec (a ^ i mod n) 1) as [Hai| Hai]; [ easy | ].
destruct (Nat.eq_dec i j) as [Hij| Hij]; [ now subst i | ].
apply (IHit (i + 1)); [ flia | easy | ].
split; [ flia Hj Hij | flia Hj ].
Qed.

Theorem ord_mod_neq_0 : ∀ n a, 2 ≤ n → Nat.gcd a n = 1 → ord_mod n a ≠ 0.
Proof.
intros * H2n Hg Ho.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
  subst a.
  rewrite Nat.gcd_0_l in Hg.
  flia Hg H2n.
}
unfold ord_mod in Ho.
specialize (eq_ord_mod_aux_0 n n a 1 Hnz (Nat.neq_succ_0 _) Ho) as H1.
specialize (euler_fermat_little n a Hnz Haz Hg) as H2.
rewrite (Nat.mod_small 1) in H2; [ | easy ].
revert H2; apply H1.
specialize (φ_interv n H2n) as H2.
flia H2.
Qed.

Theorem ord_mod_divisor : ∀ n a b,
  Nat.gcd a n = 1
  → a ^ b mod n = 1
  → Nat.divide (ord_mod n a) b.
Proof.
intros * Hg Habn.
destruct (lt_dec n 2) as [H2n| H2n]. {
  destruct n; [ easy | ].
  destruct n; [ easy | flia H2n ].
}
apply Nat.nlt_ge in H2n.
specialize (ord_mod_prop n a H2n Hg) as H1.
destruct H1 as (Han, Ham).
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  now subst b; exists 0.
}
destruct (lt_dec b (ord_mod n a)) as [Hbo| Hbo]. {
  apply Nat.neq_0_lt_0 in Hbz.
  now specialize (Ham b (conj Hbz Hbo)) as H1.
}
apply Nat.nlt_ge in Hbo.
destruct (Nat.eq_dec (ord_mod n a) 0) as [Hoz| Hoz]. {
  now apply ord_mod_neq_0 in Hoz.
}
specialize (Nat.div_mod b (ord_mod n a) Hoz) as H1.
destruct (Nat.eq_dec (b mod ord_mod n a) 0) as [Hmz| Hmz]. {
  rewrite Hmz, Nat.add_0_r in H1.
  exists (b / ord_mod n a).
  now rewrite Nat.mul_comm.
}
exfalso; apply Hmz; clear Hmz.
assert (H2 : a ^ (b mod ord_mod n a) ≡ 1 mod n). {
  rewrite H1 in Habn.
  rewrite Nat.pow_add_r in Habn.
  rewrite Nat.pow_mul_r in Habn.
  rewrite <- Nat.mul_mod_idemp_l in Habn; [ | flia H2n ].
  rewrite <- Nat_mod_pow_mod in Habn.
  rewrite Han in Habn.
  rewrite Nat.pow_1_l in Habn.
  rewrite Nat.mod_1_l in Habn; [ | easy ].
  rewrite Nat.mul_1_l in Habn.
  now rewrite <- (Nat.mod_1_l n) in Habn.
}
rewrite Nat.mod_1_l in H2; [ | easy ].
specialize (Ham (b mod ord_mod n a)) as H3.
remember (ord_mod n a) as x eqn:Hx.
remember (b mod x) as r eqn:Hr.
destruct (Nat.eq_dec r 0) as [Hrz| Hzr]; [ easy | exfalso ].
assert (H : 0 < r < x). {
  split; [ flia Hzr | ].
  rewrite Hr.
  now apply Nat.mod_upper_bound.
}
now specialize (H3 H).
Qed.

(* https://wstein.org/edu/2007/spring/ent/ent-html/node29.html *)

Theorem ord_mod_mul_divide : ∀ n a b r s,
  Nat.gcd a n = 1
  → Nat.gcd b n = 1
  → Nat.gcd r s = 1
  → ord_mod n a = r
  → ord_mod n b = s
  → Nat.divide (ord_mod n (a * b)) (r * s).
Proof.
intros * Han Hbn Hg Hoa Hob.
destruct (lt_dec n 2) as [H2n| H2n]. {
  destruct n. {
    cbn in Hoa, Hob; cbn.
    now subst r s.
  }
  destruct n; [ | flia H2n ].
  cbn in Hoa, Hob.
  now subst r s.
}
apply Nat.nlt_ge in H2n.
destruct (lt_dec a 2) as [H2a| H2a]. {
  destruct a. {
    rewrite Nat.gcd_0_l in Han; flia Han H2n.
  }
  destruct a; [ | flia H2a ].
  rewrite ord_mod_1_r in Hoa; [ | easy ].
  subst r.
  do 2 rewrite Nat.mul_1_l.
  now rewrite Hob.
}
apply Nat.nlt_ge in H2a.
destruct (lt_dec b 2) as [H2b| H2b]. {
  destruct b. {
    rewrite Nat.gcd_0_l in Hbn; flia Hbn H2n.
  }
  destruct b; [ | flia H2b ].
  rewrite ord_mod_1_r in Hob; [ | easy ].
  subst s.
  do 2 rewrite Nat.mul_1_r.
  now rewrite Hoa.
}
apply Nat.nlt_ge in H2b.
assert (H2 : (a * b) ^ (r * s) = a ^ (r * s) * b ^ (r * s)). {
  apply Nat.pow_mul_l.
}
specialize (ord_mod_prop n a H2n Han) as Har.
rewrite Hoa in Har.
destruct Har as (Har, Harn).
specialize (ord_mod_prop n b H2n Hbn) as Hbs.
rewrite Hob in Hbs.
destruct Hbs as (Hbs, Hbsn).
apply (f_equal (λ x, x mod n)) in H2.
rewrite (Nat.pow_mul_r a) in H2.
rewrite (Nat.mul_comm r s) in H2.
rewrite (Nat.pow_mul_r b) in H2.
rewrite Nat.mul_mod in H2; [ | flia H2n ].
rewrite <- (Nat_mod_pow_mod (a ^ r)) in H2.
rewrite <- (Nat_mod_pow_mod (b ^ s)) in H2.
rewrite Har, Hbs in H2.
do 2 rewrite Nat.pow_1_l in H2.
rewrite (Nat.mod_small 1) in H2; [ | easy ].
rewrite Nat.mul_1_l in H2.
rewrite (Nat.mod_small 1) in H2; [ | easy ].
rewrite (Nat.mul_comm s r) in H2.
move H2 at bottom.
apply ord_mod_divisor; [ | easy ].
now apply Nat_gcd_1_mul_l.
Qed.

Theorem order_multiplicative : ∀ n a b r s,
  Nat.gcd a n = 1
  → Nat.gcd b n = 1
  → ord_mod n a = r
  → ord_mod n b = s
  → Nat.gcd r s = 1
  → ord_mod n (a * b) = r * s.
Proof.
intros * Han Hbn Hoa Hob Hg.
destruct (lt_dec n 2) as [H2n| H2n]. {
  destruct n. {
    cbn in Hoa; cbn.
    now subst r.
  }
  destruct n; [ | flia H2n ].
  cbn in Hoa; cbn.
  now subst r.
}
apply Nat.nlt_ge in H2n.
specialize (ord_mod_mul_divide n a b r s Han Hbn Hg Hoa Hob) as H1.
(* https://wstein.org/edu/2007/spring/ent/ent-html/node29.html *)
remember (ord_mod n (a * b)) as d eqn:Hd.
specialize (Nat.divide_mul_split d r s) as H2.
assert (Habn : Nat.gcd (a * b) n = 1) by now apply Nat_gcd_1_mul_l.
assert (H : d ≠ 0). {
  rewrite Hd.
  now apply ord_mod_neq_0.
}
specialize (H2 H H1); clear H.
destruct H2 as (r1 & s1 & Hrs & Hr & Hs).
specialize (ord_mod_prop n a H2n Han) as (Hao & Ham).
rewrite Hoa in Hao, Ham.
specialize (ord_mod_prop n b H2n Hbn) as (Hbo & Hbm).
rewrite Hob in Hbo, Hbm.
specialize (ord_mod_prop n (a * b) H2n Habn) as (Habo & Habm).
rewrite <- Hd in Habo, Habm.
rewrite Hrs in Habo.
assert (Hrr : r1 = r). {
  apply (f_equal (λ x, x ^ (s / s1))) in Habo.
  rewrite Nat.pow_1_l in Habo.
  apply (f_equal (λ x, x mod n)) in Habo.
  rewrite Nat_mod_pow_mod in Habo.
  rewrite Nat.mod_1_l in Habo; [ | easy ].
  rewrite <- Nat.pow_mul_r in Habo.
  rewrite <- Nat.mul_assoc in Habo.
  assert (Hs1z : s1 ≠ 0). {
    intros H; subst s1.
    destruct Hs as (k, Hk).
    rewrite Nat.mul_0_r in Hk.
    rewrite Hk in Hob.
    now apply ord_mod_neq_0 in Hob.
  }
  rewrite <- Nat.divide_div_mul_exact in Habo; [ | easy | easy ].
  rewrite (Nat.mul_comm s1), Nat.div_mul in Habo; [ | easy ].
  rewrite (Nat.mul_comm r1) in Habo.
  rewrite Nat.pow_mul_r in Habo.
  rewrite Nat.pow_mul_l in Habo.
  rewrite <- Nat_mod_pow_mod in Habo.
  rewrite <- Nat.mul_mod_idemp_r in Habo; [ | flia H2n ].
  rewrite Hbo, Nat.mul_1_r in Habo.
  rewrite Nat_mod_pow_mod in Habo.
  rewrite <- Nat.pow_mul_r in Habo.
  assert (H2 : Nat.divide r (s * r1)). {
    rewrite <- Hoa.
    now apply ord_mod_divisor.
  }
  apply Nat.gauss in H2; [ | easy ].
  move Hr at bottom.
  now apply Nat.divide_antisym.
}
assert (Hss : s1 = s). {
  clear Hrr.
  apply (f_equal (λ x, x ^ (r / r1))) in Habo.
  rewrite Nat.pow_1_l in Habo.
  apply (f_equal (λ x, x mod n)) in Habo.
  rewrite Nat_mod_pow_mod in Habo.
  rewrite Nat.mod_1_l in Habo; [ | easy ].
  rewrite <- Nat.pow_mul_r in Habo.
  rewrite Nat.mul_shuffle0 in Habo.
  assert (Hr1z : r1 ≠ 0). {
    intros H; subst r1.
    destruct Hr as (k, Hk).
    rewrite Nat.mul_0_r in Hk.
    rewrite Hk in Hoa.
    now apply ord_mod_neq_0 in Hoa.
  }
  rewrite <- Nat.divide_div_mul_exact in Habo; [ | easy | easy ].
  rewrite (Nat.mul_comm r1), Nat.div_mul in Habo; [ | easy ].
  rewrite Nat.pow_mul_r in Habo.
  rewrite Nat.pow_mul_l in Habo.
  rewrite <- Nat_mod_pow_mod in Habo.
  rewrite <- Nat.mul_mod_idemp_l in Habo; [ | flia H2n ].
  rewrite Hao, Nat.mul_1_l in Habo.
  rewrite Nat_mod_pow_mod in Habo.
  rewrite <- Nat.pow_mul_r in Habo.
  assert (H2 : Nat.divide s (r * s1)). {
    rewrite <- Hob.
    now apply ord_mod_divisor.
  }
  apply Nat.gauss in H2; [ | now rewrite Nat.gcd_comm ].
  move Hs at bottom.
  now apply Nat.divide_antisym.
}
now subst r1 s1.
Qed.

Fixpoint list_with_occ l :=
  match l with
  | [] => []
  | x :: l' =>
      match list_with_occ l' with
      | [] => [(x, 1)]
      | (y, c) :: l' =>
          if Nat.eq_dec x y then (x, c + 1) :: l'
          else (x, 1) :: (y, c) :: l'
      end
  end.

Definition prime_decomp_pow p := list_with_occ (prime_decomp p).

(* roots of equation x^n ≡ 1 mod p *)
Definition nth_roots_of_unity_modulo n p :=
  filter (λ x, Nat_pow_mod x n p =? 1) (seq 1 (p - 1)).

Compute (let '(n, p) := (2, 13) in nth_roots_of_unity_modulo n p).
Compute (let '(n, p) := (4, 13) in nth_roots_of_unity_modulo n p).
Compute (let '(n, p) := (3, 13) in nth_roots_of_unity_modulo n p).

Theorem Couteau : ∀ a b n, Nat.gcd a n = 1 → a ^ (b mod φ n) ≡ a ^ b mod n.
Proof.
intros * Hg.
destruct (lt_dec n 2) as [H2n| H2n]. {
  destruct n; [ easy | ].
  destruct n; [ easy | flia H2n ].
}
apply Nat.nlt_ge in H2n.
destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
  subst a; cbn in Hg; flia Hg H2n.
}
specialize (Nat.div_mod b (φ n)) as H1.
assert (H : φ n ≠ 0). {
  specialize (φ_interv n H2n) as H2.
  flia H2.
}
specialize (H1 H); clear H.
apply (f_equal (λ x, a ^ x mod n)) in H1.
rewrite Nat.pow_add_r in H1.
rewrite Nat.pow_mul_r in H1.
rewrite <- Nat.mul_mod_idemp_l in H1; [ | flia H2n ].
rewrite <- (Nat_mod_pow_mod (a ^ φ n)) in H1.
rewrite euler_fermat_little in H1; [ | flia H2n | easy | easy ].
rewrite Nat.mod_1_l in H1; [ | easy ].
rewrite Nat.pow_1_l in H1.
rewrite Nat.mod_1_l in H1; [ | easy ].
now rewrite Nat.mul_1_l in H1.
Qed.

Definition prim_roots' p :=
  let l := prime_decomp_pow (p - 1) in
  let l'' :=
    map
      (λ '(d, q),
       let l1 := nth_roots_of_unity_modulo (d ^ q) p in
       let l2 := nth_roots_of_unity_modulo (d ^ (q - 1)) p in
       fold_left (λ l x2, remove Nat.eq_dec x2 l) l2 l1)
    l
  in
  fold_left (λ l1 l2, map (λ '(x, y), x * y mod p) (list_prod l1 l2))
     l'' [1].

Compute (let p := 31 in (sort Nat.leb (prim_roots' p), (prim_roots p))).
Compute (let p := 31 in combine (sort Nat.leb (prim_roots' p)) (prim_roots p)).

(* j'aimerais bien prouver que prim_roots'(p) donne les racines primitives
   modulo p et/ou qu'il en existe au moins une (prim_roots'(p)≠[]) *)

(* c'est censé marcher pour 1,2,4,p^α,2p^α mais ça a pas l'air : ça ne
   marche que pour les nombres premiers *)

(* mmm... tout dépend de ce qu'on appelle "racine primitive": pour les
   nombres composés, il s'agit de générateurs uniquement des nombres
   premiers avec eux. Pour 14, ils ne génèrent que 1,3,5,9,11,13 *)

(* donc, mes définitions prim_roots et prim_roots' ne vont pas *)

Compute (prim_roots 29, prim_roots' 29).
Compute (prim_roots 14, prim_roots' 14).
Compute (sort Nat.leb (map (λ i, Nat_pow_mod 5 i 14) (seq 1 14))).

Compute (let n := 9 in (prim_roots n, length (prim_roots n), φ (φ n))).
Compute (let n := 9 in (prim_roots' n, length (prim_roots' n), φ (φ n))).

Compute (nth_roots_of_unity_modulo 2 27, nth_roots_of_unity_modulo 1 27).
Compute (nth_roots_of_unity_modulo 13 27, nth_roots_of_unity_modulo 13 27).

(* prim_root(n) ≠ [] ↔ n=2,4,p^α,2p^α *)

(* prim_roots seem to work but not prim_roots' (that works only on primes) *)

Compute (let n := 26 in (prim_roots n, sort Nat.leb (prim_roots' n))).
Compute (let n := 6 in sort Nat.leb (map (λ i, Nat_pow_mod 5 i n) (seq 1 (n - 1)))).

Require Import Ring2 Rpolynomial2 Rsummation.

Section In_ring_A.

Context {A : Type}.
Context {rng : ring A}.

Theorem xpow_0 : (ⓧ^0 = 1)%pol.
Proof. now apply eq_poly_eq. Qed.

Theorem lap_convol_mul_succ_r : ∀ la lb i len,
  lap_convol_mul la lb i (S len) =
  (Σ (j = 0, i), nth j la 0 * nth (i - j) lb 0)%Rng ::
  lap_convol_mul la lb (S i) len.
Proof. easy. Qed.

(* http://math.univ-lille1.fr/~fricain/M1-ARITHMETIQUE/chap2.pdf *)

Theorem lt_unique : ∀ a b (lt_ab1 lt_ab2 : a < b), lt_ab1 = lt_ab2.
Proof.
intros.
apply (le_unique (S a) b lt_ab1 lt_ab2).
Qed.

(* representing a natural greater or equal to 2 *)
Class nat2 := mknat2 { number_minus_2 : nat }.
Definition n2 {n : nat2} := number_minus_2 + 2.
Definition mkn n := mknat2 (n - 2).

Class Zn (n : nat2) := mkZn { zn : nat; zn_prop : zn < n2 }.

Arguments zn {_} Zn%nat.

Theorem eq_Zn_eq n : ∀ a b : Zn n, zn a = zn b ↔ a = b.
Proof.
intros (a, apr) (b, bpr).
split; intros Hab; [ | now rewrite Hab ].
cbn in Hab.
subst b.
specialize (lt_unique a n2 apr bpr) as H1.
now subst bpr.
Qed.

Theorem Zn_prop {n : nat2} : ∀ op, op mod n2 < n2.
Proof.
intros.
apply Nat.mod_upper_bound, Nat.neq_0_lt_0.
apply (lt_le_trans _ 2); [ apply Nat.lt_0_succ | ].
unfold n2; flia.
Qed.

Definition Zn_x (n : nat2) x := mkZn n (x mod n2) (Zn_prop x).

Definition Zn_zero {n : nat2} := Zn_x n 0.
Definition Zn_one {n : nat2} := Zn_x n 1.
Definition Zn_add {n : nat2} (a b : Zn n) := Zn_x n (zn a + zn b).
Definition Zn_mul {n : nat2} (a b : Zn n) := Zn_x n (zn a * zn b).
Definition Zn_opp {n : nat2} (a : Zn n) := Zn_x n (n2 - zn a).

Theorem Zn_add_comm n : ∀ a b : Zn n, Zn_add a b = Zn_add b a.
Proof.
intros.
unfold Zn_add.
now rewrite Nat.add_comm.
Qed.

Theorem Zn_add_assoc n : ∀ a b c : Zn n,
  Zn_add a (Zn_add b c) = Zn_add (Zn_add a b) c.
Proof.
intros.
destruct (Nat.eq_dec n2 0) as [Hnz| Hnz]. {
  now unfold n2 in Hnz; rewrite Nat.add_comm in Hnz.
}
apply eq_Zn_eq; cbn.
rewrite Nat.add_mod_idemp_r; [ | easy ].
rewrite Nat.add_mod_idemp_l; [ | easy ].
now rewrite Nat.add_assoc.
Qed.

Theorem Zn_add_0_l n : ∀ a : Zn n, Zn_add Zn_zero a = a.
Proof.
intros.
destruct (Nat.eq_dec n2 0) as [Hnz| Hnz]. {
  now unfold n2 in Hnz; rewrite Nat.add_comm in Hnz.
}
apply eq_Zn_eq; cbn.
rewrite Nat.mod_0_l; [ | easy ].
rewrite Nat.add_0_l.
apply Nat.mod_small.
now destruct a.
Qed.

Theorem Zn_add_opp_l n : ∀ a : Zn n, Zn_add (Zn_opp a) a = Zn_zero.
Proof.
intros.
destruct (Nat.eq_dec n2 0) as [Hnz| Hnz]. {
  now unfold n2 in Hnz; rewrite Nat.add_comm in Hnz.
}
apply eq_Zn_eq; cbn.
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite Nat.sub_add; [ | now destruct a; apply Nat.lt_le_incl ].
rewrite Nat.mod_0_l; [ | easy ].
now apply Nat.mod_same.
Qed.

Theorem Zn_mul_comm n : ∀ a b : Zn n, Zn_mul a b = Zn_mul b a.
Proof.
intros.
unfold Zn_mul.
now rewrite Nat.mul_comm.
Qed.

Theorem Zn_mul_assoc n : ∀ a b c : Zn n,
  Zn_mul a (Zn_mul b c) = Zn_mul (Zn_mul a b) c.
Proof.
intros.
destruct (Nat.eq_dec n2 0) as [Hnz| Hnz]. {
  now unfold n2 in Hnz; rewrite Nat.add_comm in Hnz.
}
apply eq_Zn_eq; cbn.
rewrite Nat.mul_mod_idemp_r; [ | easy ].
rewrite Nat.mul_mod_idemp_l; [ | easy ].
now rewrite Nat.mul_assoc.
Qed.

Theorem Zn_mul_1_l n : ∀ a : Zn n, Zn_mul Zn_one a = a.
Proof.
intros.
destruct (le_dec n2 1) as [Hn1| Hn1]. {
  unfold n2 in Hn1; flia Hn1.
}
apply Nat.nle_gt in Hn1.
apply eq_Zn_eq; cbn.
rewrite Nat.mod_1_l; [ | easy ].
rewrite Nat.mul_1_l.
apply Nat.mod_small.
now destruct a.
Qed.

Theorem Zn_mul_add_distr_l n : ∀ a b c : Zn n,
  Zn_mul a (Zn_add b c) = Zn_add (Zn_mul a b) (Zn_mul a c).
Proof.
intros.
destruct (Nat.eq_dec n2 0) as [Hnz| Hnz]. {
  unfold n2 in Hnz; flia Hnz.
}
apply eq_Zn_eq; cbn.
rewrite Nat.mul_mod_idemp_r; [ | easy ].
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite Nat.add_mod_idemp_r; [ | easy ].
now rewrite Nat.mul_add_distr_l.
Qed.

Theorem Zn_1_neq_0 {n : nat2} : Zn_one ≠ Zn_zero.
Proof.
destruct (le_dec n2 1) as [Hn1| Hn1]. {
  unfold n2 in Hn1; flia Hn1.
}
apply Nat.nle_gt in Hn1.
intros H10.
injection H10; intros H.
rewrite Nat.mod_1_l in H; [ | easy ].
rewrite Nat.mod_0_l in H; [ easy | flia Hn1 ].
Qed.

Theorem Zn_eq_dec {n : nat2} : ∀ a b : Zn n, {a = b} + {a ≠ b}.
Proof.
intros (a, apr) (b, bpr).
destruct (Nat.eq_dec a b) as [Hab| Hab]. {
  left; subst b.
  now apply eq_Zn_eq.
} {
  right.
  intros H; apply Hab.
  now injection H.
}
Qed.

Definition Zn_ring (n : nat2) : ring (Zn n) :=
  {| rng_zero := Zn_zero;
     rng_one := Zn_one;
     rng_add := Zn_add;
     rng_mul := Zn_mul;
     rng_opp := Zn_opp;
     rng_1_neq_0 := Zn_1_neq_0;
     rng_eq_dec := Zn_eq_dec;
     rng_add_comm := Zn_add_comm n;
     rng_add_assoc := Zn_add_assoc n;
     rng_add_0_l := Zn_add_0_l n;
     rng_add_opp_l := Zn_add_opp_l n;
     rng_mul_comm := Zn_mul_comm n;
     rng_mul_assoc := Zn_mul_assoc n;
     rng_mul_1_l := Zn_mul_1_l n;
     rng_mul_add_distr_l := Zn_mul_add_distr_l n |}.

Canonical Structure Zn_ring.

End In_ring_A.

(* degree of a polynomial *)

Definition degree {A} {rng : ring A} pol := length (lap pol) - 1.

Definition lt_succ_add a b := proj1 (Nat.succ_lt_mono b (1 + a + b)).

Definition lt2_7 : 2 < 7 :=
  let m := 4 in
  let f := lt_succ_add m in
  f 1 (f 0 (Nat.lt_0_succ m)).

Definition lt3_7 : 3 < 7 :=
  let m := 3 in
  let f := lt_succ_add m in
  f 2 (f 1 (f 0 (Nat.lt_0_succ m))).

Definition lt4_7 : 4 < 7 :=
  let m := 2 in
  let f := lt_succ_add m in
  f 3 (f 2 (f 1 (f 0 (Nat.lt_0_succ m)))).

Definition lt5_7 : 5 < 7 :=
  let m := 1 in
  let f := lt_succ_add m in
  f 4 (f 3 (f 2 (f 1 (f 0 (Nat.lt_0_succ m))))).

Definition m7_2 := mkZn (mkn 7) 2 lt2_7.
Definition m7_3 := mkZn (mkn 7) 3 lt3_7.
Definition m7_4 := mkZn (mkn 7) 4 lt4_7.
Definition m7_5 := mkZn (mkn 7) 5 lt5_7.

Theorem m7_5_ne_0 (rng := Zn_ring (mkn 7)) : rng_eqb m7_5 0%Rng = false.
Proof.
unfold rng_eqb; cbn.
now destruct (rng_eq_dec m7_5 0).
Qed.

Compute (degree (mkpoly [m7_3; m7_4; m7_5] m7_5_ne_0)).
Compute (mkpoly [m7_3; m7_4; m7_5] m7_5_ne_0).

Section In_ring_A.

Context {A : Type}.
Context {rng : ring A}.

Example xk_1 : ∀ k, degree (ⓧ^k - 1)%pol = k.
Proof.
intros; cbn.
rewrite rev_length.
destruct (rng_eq_dec (-1%Rng) 0) as [H10|H10]; [ | clear H10 ]. {
  cbn in H10.
  apply (f_equal rng_opp) in H10.
  rewrite rng_opp_involutive in H10.
  rewrite rng_opp_0 in H10.
  now apply rng_1_neq_0 in H10.
}
cbn.
destruct k. {
  cbn.
  rewrite fold_rng_sub.
  rewrite rng_add_opp_r.
  now destruct (rng_eq_dec 0 0).
}
cbn.
rewrite lap_add_0_r.
rewrite rng_add_0_l.
rewrite strip_0s_app.
remember (strip_0s _) as la eqn:Hla; symmetry in Hla.
destruct la as [| a]. {
  cbn.
  specialize (proj1 (eq_strip_0s_rev_nil _) Hla k) as H1.
  rewrite app_nth2 in H1. 2: {
    rewrite repeat_length.
    now unfold "≥".
  }
  rewrite repeat_length, Nat.sub_diag in H1.
  now apply rng_1_neq_0 in H1.
}
cbn.
rewrite Nat.sub_0_r.
rewrite app_length; cbn.
rewrite Nat.add_comm; cbn; f_equal.
rewrite rev_app_distr in Hla.
cbn - [ "++" ] in Hla.
rewrite app_nil_l in Hla.
cbn in Hla.
destruct (rng_eq_dec 1 0) as [H1| H1]. {
  now apply rng_1_neq_0 in H1.
}
injection Hla; clear Hla; intros; subst a la.
now rewrite rev_length, repeat_length.
Qed.

Definition is_polynomial_root pol x :=
  (eval_poly pol x = 0)%Rng.

Definition lap_divrem_by_x_sub_a la a :=
  fold_right
    (λ ai bl, match bl with [] => ai | b :: _ => (ai + a * b)%Rng end :: bl)
    [] la.

Definition lap_quot_by_x_sub_a la a :=
  tl (lap_divrem_by_x_sub_a la a).

Definition lap_rem_by_x_sub_a la a :=
  hd 0%Rng (lap_divrem_by_x_sub_a la a).

Theorem fold_lap_divrem_by_x_sub_a : ∀ la a,
  fold_right
    (λ ai bl, match bl with [] => ai | b :: _ => (ai + a * b)%Rng end :: bl)
    [] la = lap_divrem_by_x_sub_a la a.
Proof. easy. Qed.

Theorem last_lap_quot_neq_0 : ∀ a pol,
  rng_eqb (last (lap_quot_by_x_sub_a (lap pol) a) 1%Rng) 0%Rng = false.
Proof.
intros a (la, lapr).
apply eq_poly_prop; cbn.
apply eq_poly_prop in lapr.
induction la as [| a2]; [ apply rng_1_neq_0 | ].
unfold lap_quot_by_x_sub_a.
unfold lap_divrem_by_x_sub_a; cbn.
rewrite fold_lap_divrem_by_x_sub_a.
unfold lap_quot_by_x_sub_a in IHla.
cbn in lapr.
destruct la as [| a3]; [ apply rng_1_neq_0 | ].
specialize (IHla lapr).
remember (a3 :: la) as lb eqn:Hlb.
clear a2 a3 la Hlb.
induction lb as [| b]; [ apply rng_1_neq_0 | ].
cbn in IHla.
rewrite fold_lap_divrem_by_x_sub_a in IHla.
cbn in lapr.
destruct lb as [| b2]; [ easy | ].
specialize (IHlb lapr).
remember (b2 :: lb) as lc eqn:Hlc; symmetry in Hlc.
cbn; rewrite fold_lap_divrem_by_x_sub_a.
remember (lap_divrem_by_x_sub_a lc a) as ld eqn:Hld.
symmetry in Hld.
destruct ld as [| d]; [ now rewrite <- Hlc in Hld | easy ].
Qed.

Definition poly_divrem_by_x_sub_a pol a :=
  (mkpoly (lap_quot_by_x_sub_a (lap pol) a) (last_lap_quot_neq_0 a pol),
   lap_rem_by_x_sub_a (lap pol) a).

Definition poly_quot_by_x_sub_a pol a :=
  mkpoly (lap_quot_by_x_sub_a (lap pol) a) (last_lap_quot_neq_0 a pol).

End In_ring_A.

(**)
Require Import ZArith.
Example ex_pol1 (r := Z_ring) :
  rng_eqb (last [1%Z; 2%Z; 1%Z] 1%Rng) 0%Rng = false.
Proof.
now apply eq_poly_prop.
Qed.
Check (let r := Z_ring in mkpoly [1; 2; 1]%Z ex_pol1).
Compute (let r := Z_ring in poly_divrem_by_x_sub_a (mkpoly [1; 2; 1]%Z ex_pol1) 1%Z).
(* x2+2x+1 = (x-1)(x+3)+4 *)
Compute (let r := Z_ring in lap_divrem_by_x_sub_a [1;2;1]%Z 1%Z).
Compute (let r := Z_ring in lap_divrem_by_x_sub_a [1;-2;1]%Z 1%Z).
(**)

Section In_ring_A2.

Context {A : Type}.
Context {rng : ring A}.

Lemma rem_is_eval_a : ∀ la a, (lap_rem_by_x_sub_a la a = eval_lap la a)%Rng.
Proof.
intros.
unfold lap_rem_by_x_sub_a.
unfold lap_divrem_by_x_sub_a, eval_lap.
induction la as [| b]; intros; [ easy | cbn ].
remember (fold_right _ _ _) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| c]. {
  cbn in Hlb, IHla.
  rewrite <- IHla.
  now rewrite rng_mul_0_l, rng_add_0_l.
}
cbn in IHla.
rewrite <- IHla.
now rewrite rng_add_comm, rng_mul_comm.
Qed.

(*
Lemma lap_div_rem_x_sub_a : ∀ la a q r,
  q = lap_quot_by_x_sub_a la a
  → r = lap_rem_by_x_sub_a la a
  → (lap_norm la = [(-a)%Rng; 1%Rng] * q + lap_norm [r])%lap.
Proof.
intros * Hq Hr.
cbn.
rewrite rng_add_0_r.
(*
rewrite lap_add_0_r.
*)
unfold lap_quot_by_x_sub_a in Hq.
unfold lap_rem_by_x_sub_a in Hr.
remember (lap_divrem_by_x_sub_a la a) as qr eqn:Hqr.
subst q r.
(*
unfold lap_divrem_by_x_sub_a in Hqr.
*)
revert a qr Hqr.
induction la as [| b]; intros. {
  cbn in Hqr.
  subst qr; cbn.
  now destruct (rng_eq_dec 0 0).
}
cbn in Hqr.
rewrite fold_lap_divrem_by_x_sub_a in Hqr.
remember (lap_divrem_by_x_sub_a la a) as qr' eqn:Hqr'.
specialize (IHla _ qr' Hqr').
symmetry in Hqr'.
destruct qr' as [| b2]. {
  subst qr; cbn.
  cbn in IHla.
  destruct (rng_eq_dec 0 0) as [H| H]; [ clear H | easy ].
  cbn in IHla.
  unfold lap_norm in IHla.
  apply List_eq_rev_nil in IHla.
  rewrite strip_0s_app.
  now rewrite IHla.
}
cbn in IHla.
rewrite Hqr; cbn.
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as [| b3]. {
  cbn.
  destruct (rng_eq_dec b 0) as [Hbz| Hbz]. {
    exfalso.
    subst b.
    rewrite rng_add_0_l in Hqr.
    destruct (rng_eq_dec b2 0) as [Hb2z| Hb2z]. {
      subst b2; cbn in IHla; rewrite lap_add_0_r in IHla.
      unfold lap_norm in IHla.
      rewrite Hlb in IHla; cbn in IHla.
      destruct qr'; [ | easy ].
      clear IHla qr Hqr.
      (* mouais, rien à en tirer *)
...
rewrite Hqr, <- Hqr'.
cbn.
rewrite strip_0s_app.
...
apply lap_eq_cons. {
  destruct qr' as [| c]. {
    subst qr; cbn.
    now rewrite rng_mul_0_r, rng_add_0_l.
  }
  subst qr; cbn.
  rewrite rng_add_comm.
  rewrite rng_mul_opp_l.
  rewrite fold_rng_sub.
  now rewrite rng_add_sub.
} {
  rewrite IHla.
  destruct qr' as [| c]. {
    subst qr; cbn.
    cbn.
    rewrite rng_mul_0_r, rng_add_0_l.
    now constructor.
  }
  subst qr; cbn.
  rewrite rng_mul_1_l, rng_add_0_r.
  apply lap_eq_cons; [ easy | ].
  rewrite lap_convol_mul_cons_succ; [ easy | cbn; flia ].
}
Qed.
*)

(*
Lemma lap_div_by_x_sub_a : ∀ la a,
  (la = [-a; 1]%Rng * lap_quot_by_x_sub_a la a + [eval_lap la a])%lap.
Proof.
intros.
rewrite <- rem_is_eval_a.
now apply lap_div_rem_x_sub_a.
Qed.
*)

(*
Lemma al_mkpol : ∀ la, (al (mkpol la) = la)%lap.
Proof. now intros. Qed.

Lemma mkpol_eq : ∀ la lb, (la = lb)%lap → (mkpol la = mkpol lb)%pol.
Proof. now intros * Hll. Qed.
*)

(*
Theorem poly_div_rem_by_x_sub_a : ∀ pol a,
  (pol =
   mkpoly [- a; 1]%Rng * poly_quot_by_x_sub_a pol a +
   mkpoly [eval_poly pol a])%pol.
Proof.
intros (la) a.
unfold "+"%pol.
cbn - [ "+"%lap "*"%lap eval_poly ].
apply mkpol_eq.
apply lap_div_by_x_sub_a.
Qed.

Lemma lap_x_sub_root_divides : ∀ lap a,
  is_polynomial_root {| al := lap |} a
  → (lap = [- a; 1]%Rng * lap_quot_by_x_sub_a lap a)%lap.
Proof.
intros * Hr.
unfold is_polynomial_root in Hr.
unfold eval_poly in Hr.
rewrite al_mkpol in Hr.
specialize (lap_div_by_x_sub_a lap a) as H1.
rewrite Hr in H1.
rewrite lap_add_compat in H1; [ | easy | apply lap_eq_0 ].
now rewrite lap_add_0_r in H1.
Qed.

Theorem x_sub_root_divides : ∀ pol a,
  is_polynomial_root pol a
  → (pol = mkpol [- a; 1]%Rng * poly_quot_by_x_sub_a pol a)%pol.
Proof.
intros * Hr.
unfold is_polynomial_root in Hr.
specialize (poly_div_rem_by_x_sub_a pol a) as H1.
rewrite Hr in H1.
rewrite rng_add_compat in H1; [ | easy | ]. {
  now rewrite rng_add_0_r in H1.
}
now constructor.
Qed.

Theorem pol_pow_sub_1' (pr := polynomial_ring) : ∀ k,
  k ≠ 0
  → (ⓧ^k - 1 = (ⓧ - 1) * (Σ (i = 0, k - 1), ⓧ^(k-i-1))%Rng)%pol.
Proof.
intros k Hkz.
specialize (x_sub_root_divides (ⓧ^k - 1)%pol 1%Rng) as H1.
assert (H : is_polynomial_root (ⓧ^k - 1)%pol 1%Rng). {
  unfold is_polynomial_root; cbn.
  subst pr; clear.
  destruct k; cbn. {
    rewrite rng_mul_0_l, rng_add_0_l.
    apply rng_add_opp_r.
  }
  rewrite lap_add_0_r.
  rewrite rng_mul_1_r.
  rewrite rng_add_0_l.
  rewrite fold_rng_sub.
  induction k; cbn. {
    rewrite rng_mul_0_l, rng_add_0_l.
    apply rng_add_opp_r.
  }
  now rewrite rng_mul_1_r, rng_add_0_r.
}
specialize (H1 H); clear H.
rewrite H1.
unfold poly_quot_by_x_sub_a.
unfold "*"%pol.
cbn - [ "*"%lap summation ].
apply mkpol_eq.
rewrite rng_add_0_l.
apply lap_mul_compat_l.
unfold lap_quot_by_x_sub_a.
rewrite <- fold_left_is_summation.
unfold lap_divrem_by_x_sub_a; cbn.
rewrite Nat.sub_0_r.
(* seems difficult to prove *)
...
*)

(*
Theorem glop : ∀ la roots n,
  (∀ a b, (a * b = 0)%Rng → (a = 0)%Rng ∨ (b = 0)%Rng)
  → n ≠ 0
  → (∀ x, x ∈ roots ↔ (eval_lap la x = 0)%Rng)
  → NoDup roots
  → lap_has_degree la n
  → length roots ≤ n.
Proof.
intros * Hintegr Hnz Hr Hnd Hdeg.
remember (length roots) as nroot eqn:Hnroot.
symmetry in Hnroot.
revert la n roots Hnz Hr Hdeg Hnd Hnroot.
induction nroot; intros; [ flia | ].
destruct roots as [| r]; [ cbn in Hnroot; flia Hnroot | ].
specialize (proj1 (Hr r) (or_introl eq_refl)) as H1.
specialize (lap_x_sub_root_divides la r H1) as H2.
destruct n; [ easy | clear Hnz ].
specialize (IHnroot (lap_quot_by_x_sub_a la r) (n - 1)) as H3.
destruct n. {
  inversion Hdeg. {
    subst n la; rename la0 into la.
    rename H into H4.
    rename H0 into H5.
    symmetry in H5.
    destruct la as [| b lb]; [ cbn in H5; flia H5 | ].
    destruct lb; [ | easy ].
    clear H5.
    cbn in H1.
    rewrite rng_mul_0_l, rng_add_0_l in H1.
    clear H2. (* because just implies b=-r*a *)
    cbn in Hnroot.
    destruct roots as [| r2]. {
      cbn in Hnroot; flia Hnroot.
    }
    specialize (proj1 (Hr r2) (or_intror (or_introl eq_refl))) as H2.
    cbn in H2.
    rewrite rng_mul_0_l, rng_add_0_l in H2.
    rewrite <- H2 in H1.
    apply rng_add_reg_r in H1.
    apply (rng_sub_compat_l _ _ (a * r2)%Rng) in H1.
    rewrite rng_add_opp_r in H1.
    rewrite <- rng_mul_sub_distr_l in H1.
    apply Hintegr in H1.
    destruct H1 as [H1| H1]; [ easy | ].
    apply (rng_add_compat_r _ _ r2) in H1.
    rewrite rng_sub_add, rng_add_0_l in H1.
Print NoDup.
(* ah, crotte, c'est l'égalité de Leibnitz *)
...
    rewrite <- H1 in Hnd.
...

Theorem glop : ∀ pol roots n,
  n ≠ 0
  → (∀ x, x ∈ roots ↔ is_polynomial_root pol x)
  → NoDup roots
  → poly_has_degree pol n
  → length roots ≤ n.
Proof.
intros (la) * Hnz Hr Hnd Hdeg.
unfold poly_has_degree in Hdeg; cbn in Hdeg.
assert (H : ∀ x, x ∈ roots ↔ (eval_lap la x = 0)%Rng). {
  intros x.
  split; intros H. {
    now specialize (proj1 (Hr x) H) as H1.
  } {
    now specialize (proj2 (Hr x) H) as H1.
  }
}
move H before Hr; clear Hr; rename H into Hr.
...

Theorem glop : ∀ pol roots n,
  (∀ x, x ∈ roots ↔ is_polynomial_root pol x)
  → NoDup roots
  → poly_has_degree pol n
  → length roots ≤ n.
(* the (required) NoDup prevents to take multiple roots into account;
   this is not a serious issue, because of "≤", but it means that
   this theorem is not perfect *)
Proof.
intros * Hr Hnd Hdeg.
remember (length roots) as nroot eqn:Hnroot.
symmetry in Hnroot.
revert pol n roots Hr Hdeg Hnd Hnroot.
induction nroot; intros; [ flia | ].
destruct roots as [| r]; [ cbn in Hnroot; flia Hnroot | ].
specialize (proj1 (Hr r) (or_introl eq_refl)) as H1.
specialize (x_sub_root_divides pol r H1) as H2.
destruct n. {
Search lap_has_degree.
...
specialize (IHnroot (poly_quot_by_x_sub_a pol r) (n - 1)) as H3.
...

Definition roots_of_pol pol := ... (* mmm... no way to compute them *)

Theorem toto : length (roots_of_pol pol) ≤ poly_deg pol.
...

Theorem number_of_nth_roots_of_unity : ∀ p d,
  prime p
  → Nat.divide d (p - 1)
  → length (nth_roots_of_unity_modulo d p) = d.
Proof.
intros * Hp Hdp.
set (pr := Zn_ring p).
specialize (pol_pow_sub_1 (p - 1)) as H1.
assert (H : p - 1 ≠ 0). {
  destruct p; [ easy | ].
  destruct p; [ easy | flia ].
}
specialize (H1 H); clear H.
destruct Hdp as (e, He).
specialize (fermat_little _ Hp) as H2.
assert
  (H3 : ∀ x,
   (x ^ (p - 1) - 1 = (x - 1) * (Σ (i = 0, p - 1 - 1), x^(p - 1 - i - 1)))%Rng). {
  intros.
  specialize (eval_poly_morph _ _ H1 x x (rng_eq_refl _)) as H3.
  rewrite eval_poly_sub in H3.
  rewrite eval_poly_xpow in H3.
  rewrite eval_poly_one in H3.
  rewrite eval_poly_mul in H3.
  rewrite eval_poly_sub in H3.
  rewrite eval_poly_xpow in H3.
  rewrite eval_poly_one in H3.
  rewrite rng_pow_1_r in H3.
  rewrite eval_poly_sum in H3.
  rewrite H3.
  apply rng_mul_compat_l.
  apply summation_compat.
  intros i Hi.
  now rewrite eval_poly_xpow.
}
...

Theorem eq_list_with_occ_nil : ∀ l, list_with_occ l = [] → l = [].
Proof.
intros * Hl.
destruct l as [| a l]; [ easy | exfalso ].
cbn in Hl.
destruct (list_with_occ l); [ easy | ].
destruct p.
now destruct (Nat.eq_dec a n).
Qed.

Lemma map_mul_1_l_mod : ∀ p l,
  (∀ x, x ∈ l → x < p)
  → map (λ x, (1 * x) mod p) l = l.
Proof.
intros * Hlt.
induction l as [| a l]; [ easy | ].
cbn - [ Nat.mul ].
rewrite Nat.mul_1_l.
f_equal. {
  apply Nat.mod_small.
  now apply Hlt; left.
}
apply IHl.
intros x Hx.
now apply Hlt; right.
Qed.

Theorem List_in_remove {A} : ∀ eq_dec x y (l : list A),
  y ∈ remove eq_dec x l → y ∈ l.
Proof.
intros * Hy.
induction l as [| z l]; [ easy | ].
cbn in Hy; cbn.
destruct (eq_dec x z) as [Hxz| Hxz]. {
  now right; subst z; apply IHl.
} {
  destruct Hy as [Hy| Hy]; [ now left | ].
  now right; apply IHl.
}
Qed.
*)

(*
Theorem prim_roots'_are_prim_roots :
  ∀ p a, a ∈ prim_roots' p ↔
  (∀ i, 1 ≤ i ≤ p - 1 → ∃ j, a ^ j ≡ i mod p).
Proof.
intros.
split. {
  intros Hap * Hip.
  unfold prim_roots' in Hap.
  remember (prime_decomp_pow (p - 1)) as l eqn:Hl; symmetry in Hl.
  remember
    (fold_left (λ l1 l2, map (λ '(x, y), (x * y) mod p) (list_prod l1 l2))
       (map
          (λ '(d, q),
           fold_left (λ (l : list nat) (x2 : nat), remove Nat.eq_dec x2 l)
           (nth_roots_of_unity_modulo (d ^ (q - 1)) p)
           (nth_roots_of_unity_modulo (d ^ q) p)) l)) as f eqn:Hf.
...
  induction l as [| x l]. {
    cbn in Hap.
    destruct Hap as [Hap| Hap]; [ | easy ].
    unfold prime_decomp_pow in Hl.
    apply eq_list_with_occ_nil in Hl.
    apply prime_decomp_nil_iff in Hl.
    destruct Hl as [Hp| Hp]; [ flia Hp Hip | ].
    replace i with 1 by flia Hp Hip; subst a.
    exists 1.
    now rewrite Nat.pow_1_r.
  }
  cbn in Hap.
  rewrite app_nil_r in Hap.
  destruct x as (d, q).
  rewrite (map_map _ (λ '(x, y), (x * y) mod p)) in Hap.
  rewrite map_mul_1_l_mod in Hap. 2: {
    intros x Hx.
    remember (nth_roots_of_unity_modulo (d ^ q) p) as l1 eqn:Hl1.
    remember (nth_roots_of_unity_modulo (d ^ (q - 1)) p) as l2 eqn:Hl2.
    assert (H : ∀ x, x ∈ l1 → x < p). {
      intros y Hy.
      rewrite Hl1 in Hy.
      unfold nth_roots_of_unity_modulo in Hy.
      apply filter_In in Hy.
      destruct Hy as (Hy, _).
      apply in_seq in Hy.
      flia Hy.
    }
    clear - Hx H.
    revert l1 Hx H.
    induction l2 as [| a l2]; intros; cbn in Hx; [ now apply H | ].
    eapply IHl2; [ apply Hx | ].
    intros y Hy.
    apply List_in_remove in Hy.
    apply H, Hy.
  }
  apply IHl; [ ... | ].
  clear IHl.
...
*)

Theorem glop : ∀ p, prime p → ∃ a, is_prim_root p a = true.
Proof.
intros * Hp.
unfold is_prim_root.
Check Nat_pow_mod.
Search Nat_pow_mod.
Compute (map (λ i, Nat_pow_mod i 21 43) (seq 1 42)).
Compute (map (λ i, Nat_pow_mod i 14 43) (seq 1 42)).
Compute (map (λ i, Nat_pow_mod i 6 43) (seq 1 42)).
Compute (map (λ i, Nat_pow_mod i 7 43) (seq 1 42)).
Compute (map (λ i, Nat_pow_mod i 2 43) (seq 1 42)).
Compute (map (λ i, Nat_pow_mod i 11 43) (seq 1 42)).
Compute (map (λ i, Nat_pow_mod i 2 3) (seq 1 2)).
Compute (map (λ i, Nat_pow_mod i 2 5) (seq 1 4)).
Compute (map (λ i, Nat_pow_mod i 4 5) (seq 1 4)).
Compute (map (λ i, Nat_pow_mod i 2 7) (seq 1 6)).
Compute (map (λ i, Nat_pow_mod i 3 7) (seq 1 6)).
Compute (let p := 11 in let d := 2 in map (λ i, Nat_pow_mod i d p) (seq 1 (p - 1))).
Compute (let p := 11 in let d := 5 in map (λ i, Nat_pow_mod i d p) (seq 1 (p - 1))).
Compute (let p := 13 in let d := 2 in map (λ i, Nat_pow_mod i d p) (seq 1 (p - 1))).
Compute (let p := 13 in let d := 3 in map (λ i, Nat_pow_mod i d p) (seq 1 (p - 1))).
Compute (let p := 13 in let d := 4 in map (λ i, Nat_pow_mod i d p) (seq 1 (p - 1))).
Compute (let p := 13 in let d := 6 in map (λ i, Nat_pow_mod i d p) (seq 1 (p - 1))).
Compute (let p := 13 in let d := 12 in map (λ i, Nat_pow_mod i d p) (seq 1 (p - 1))).
Compute (prim_root_cycle 43 2).
Check Nat_pow_mod.
Compute (let p := 5 in let d := 2 in map (λ x, Nat_pow_mod x d p) (seq 1 (p - 1))).
Compute (let p := 7 in let d := 3 in map (λ x, Nat_pow_mod x d p) (seq 1 (p - 1))).
Compute (let p := 11 in let d := 5 in map (λ x, Nat_pow_mod x d p) (seq 1 (p - 1))).
Compute (divisors 12).
Compute (let p := 19 in map (λ d, (d, map (λ x, Nat_pow_mod x d p) (seq 1 (p - 1)))) (divisors (p - 1))).
Compute (prim_roots 19).
Compute (sort Nat.ltb (map (λ n, (n * 18) mod 19) [4; 5; 6; 9; 16; 17])).
Compute (sort Nat.ltb (prim_roots' 71)).
Compute (length (prim_roots 71)).
Compute (φ (φ 71)).
...
enough (H : ∃ a, length (prim_root_cycle p a) = p - 1). {
  destruct H as (a, H); exists a.
  now apply Nat.eqb_eq in H.
}
remember (prime_divisors (p - 1)) as pd eqn:Hpd.
(* https://wstein.org/edu/2007/spring/ent/ent-html/node29.html *)
Compute (prim_roots 13, quad_res 13).
Compute (map (prim_root_cycle 13) [1; 5; 8; 12]).
Compute (map (prim_root_cycle 13) [1; 3; 9]).
Compute (map (λ x, x mod 13) [15; 45; 24; 72]).
Compute (map (prim_root_cycle 13) [2; 6; 11; 7]).
Compute (prime_decomp 12).
About prime_decomp.
...

Theorem glop : ∀ p, prime p → ∃ a, a ^ ((p - 1) / 2) mod p = p - 1.
Proof.
intros * Hp.
destruct (Nat.eq_dec p 2) as [Hp2| Hp2]; [ now exists 1; subst p | ].
assert (H2p : 2 ≤ p) by now apply prime_ge_2.
assert (H3p : 3 ≤ p) by flia Hp2 H2p.
clear Hp2 H2p.
...
remember (prime_divisors (p - 1)) as pd eqn:Hpd.
(* https://wstein.org/edu/2007/spring/ent/ent-html/node29.html *)
...
(* a must be a quadratic nonresidue of p *)
(* https://en.wikipedia.org/wiki/Euler%27s_criterion *)
...
intros * Hp.
destruct (Nat.eq_dec p 2) as [Hp2| Hp2]; [ now exists 1; subst p | ].
assert (H2p : 2 ≤ p) by now apply prime_ge_2.
assert (H3p : 3 ≤ p) by flia Hp2 H2p.
clear Hp2 H2p.
specialize (pow_prime_sub_1_div_2 p Hp) as H1.
apply (not_forall_in_interv_imp_exist 1 (p - 1)); [ | flia H3p | ]. {
  intros; apply Nat.eq_decidable.
}
intros H2.
assert (Hap1 : ∀ a, 1 ≤ a ≤ p - 1 → a ^ ((p - 1) / 2) mod p = 1). {
  intros a Ha.
  specialize (H2 a Ha).
  assert (H : 1 ≤ a < p) by flia Ha.
  now destruct (H1 a H).
}
clear H1 H2.
Compute (let p := 3 in map (λ n, Nat_pow_mod n ((p - 1)/2) p) (seq 1 (p - 1))).
...
specialize (not_all_div_2_mod_add_1_eq_1 (p - 1)) as H1.
assert (H : 2 ≤ p - 1) by flia H3p.
specialize (H1 H); clear H.
rewrite Nat.sub_add in H1; [ easy | flia H3p ].
Qed.
