Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith Init.Nat.
Require Import Misc Primes QuadRes_1.

Require Import RingLike.Core.
Require Import RingLike.IterAdd.
Require Import RingLike.Nat_algebra.

Check quadratic_reciprocity_2.

Theorem mul_div_le_pred_div_2 :
  ∀ p q x, Nat.Odd p → Nat.Odd q → x ≤ (q - 1) / 2 → p * x / q ≤ (p - 1) / 2.
Proof.
intros * Hop Hoq Hx.
assert (Hpz : p ≠ 0). {
  intros H; rewrite H in Hop.
  now apply Nat.odd_spec in Hop.
}
assert (Hqz : q ≠ 0). {
  intros H; rewrite H in Hoq.
  now apply Nat.odd_spec in Hoq.
}
assert (H5 : 2 * p * x  ≤ p * (q - 1) < p * q). {
  split. {
    rewrite (Nat.mul_comm 2), <- Nat.mul_assoc.
    apply Nat.mul_le_mono_l.
    apply (Nat.mul_le_mono_pos_l _ _ 2) in Hx; [ | easy ].
    eapply Nat.le_trans; [ apply Hx | ].
    apply Nat.Div0.mul_div_le.
  }
  apply Nat.mul_lt_mono_pos_l; [ now apply Nat.neq_0_lt_0 | ].
  apply Nat.sub_lt; [ now apply Nat.neq_0_lt_0 | easy ].
}
assert (H6 : p * x / q ≤ p / 2). {
  destruct Hop as (a, Hop).
  destruct Hoq as (b, Hoq).
  assert (H6 : p * x ≤ (2 * a + 1) * b). {
    rewrite Hop.
    apply Nat.mul_le_mono_l.
    rewrite Hoq, Nat.add_sub in Hx.
    now rewrite (Nat.mul_comm 2), Nat.div_mul in Hx.
  }
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l in H6.
  assert (H7 : q * (a + 1) = (2 * b + 1) * (a + 1)). {
    now rewrite Hoq.
  }
  rewrite (Nat.mul_add_distr_l (2 * b + 1)) in H7.
  rewrite Nat.mul_1_r in H7.
  rewrite Nat.mul_add_distr_r in H7.
  rewrite Nat.mul_1_l in H7.
  rewrite Nat.mul_shuffle0 in H7.
  rewrite Nat.add_shuffle0 in H7.
  rewrite Nat.add_assoc in H7.
  rewrite Nat.add_shuffle0 in H7.
  assert (H8 : 0 < a + b + 1 ≤ q * (a + 1) - p * x). {
    split; [ now rewrite Nat.add_1_r | ].
    rewrite H7.
    apply Nat.le_add_le_sub_l.
    rewrite Nat.add_assoc.
    apply Nat.add_le_mono_r.
    rewrite (Nat.add_comm a), Nat.add_assoc.
    apply Nat.add_le_mono_r.
    rewrite (Nat_mul_2_l b).
    rewrite Nat.add_assoc.
    now apply Nat.add_le_mono_r.
  }
  assert (H9 : p * x < q * (a + 1)) by flia H8.
  apply Nat.lt_succ_r.
  rewrite <- Nat.add_1_r.
  apply Nat.Div0.div_lt_upper_bound.
  rewrite Hop at 2.
  rewrite (Nat.mul_comm 2).
  rewrite Nat.div_add_l; [ | easy ].
  now rewrite Nat.add_0_r.
}
destruct Hop as (p', Hop).
rewrite Hop at 2.
rewrite Nat.add_sub, (Nat.mul_comm 2), Nat.div_mul; [ | easy ].
rewrite Hop in H6 at 2.
rewrite (Nat.mul_comm 2) in H6.
rewrite Nat.div_add_l in H6; [ | easy ].
now rewrite Nat.add_0_r in H6.
Qed.

Theorem mul_div_eq_mul_sub_1_div :
  ∀ p q x,
  prime p
  → coprimes p q
  → 1 ≤ x ≤ (p - 1) / 2
  → x * q / p = (x * q - 1) / p.
Proof.
intros * Hp Hcpq Hx.
assert (Hpz : p ≠ 0) by now intros H; subst p.
specialize (Nat.div_mod (x * q) p) as H5.
rewrite H5; [ | now intros H; subst p ].
rewrite <- Nat.add_sub_assoc; cycle 1. {
  apply Nat.neq_0_lt_0.
  intros H.
  apply Nat.Lcm0.mod_divide in H.
  apply Nat.gauss in H; cycle 1. {
    apply eq_gcd_prime_small_1; [ easy | ].
    split; [ easy | ].
    eapply Nat.le_lt_trans; [ apply Hx | ].
    apply Nat.Div0.div_lt_upper_bound.
    apply (Nat.lt_le_trans _ p).
    apply Nat.sub_lt; [ now apply Nat.neq_0_lt_0 | easy ].
    rewrite Nat_mul_2_l.
    apply Nat.le_add_l.
  }
  progress unfold coprimes in Hcpq.
  destruct H as (c, Hc).
  rewrite Hc in Hcpq.
  rewrite Nat.mul_comm in Hcpq.
  rewrite Nat.gcd_mul_diag_l in Hcpq.
  now rewrite Hcpq in Hp.
}
rewrite (Nat.mul_comm p).
rewrite Nat.div_add_l; [ | easy ].
rewrite Nat.div_add_l; [ | easy ].
progress f_equal.
rewrite Nat.div_small; [ | now apply Nat.mod_upper_bound ].
symmetry.
apply Nat.div_small.
apply (Nat.le_lt_trans _ ((x * q) mod p)); cycle 1. {
  now apply Nat.mod_upper_bound.
}
apply Nat.le_sub_l.
Qed.

Theorem quadratic_reciprocity :
  ∀ p q, prime p → prime q → p ≠ 2 → q ≠ 2 → p ≠ q →
  is_quadratic_residue p q = is_quadratic_residue q p ↔
    p mod 4 = 1 ∨ q mod 4 = 1.
Proof.
intros * Hp Hq Hp2 Hq2 Hpneq.
assert (Hop : Nat.Odd p). {
  specialize (odd_prime _ Hp Hp2) as H1.
  apply Nat_eq_mod_1 in H1.
  destruct H1 as (H1, _).
  apply Nat.Div0.mod_divides in H1.
  destruct H1 as (c, Hc).
  exists c.
  rewrite <- Hc; symmetry.
  apply Nat.sub_add.
  apply Nat.neq_0_lt_0.
  now intros H1; subst p.
}
assert (Hoq : Nat.Odd q). {
  specialize (odd_prime _ Hq Hq2) as H1.
  apply Nat_eq_mod_1 in H1.
  destruct H1 as (H1, _).
  apply Nat.Div0.mod_divides in H1.
  destruct H1 as (c, Hc).
  exists c.
  rewrite <- Hc; symmetry.
  apply Nat.sub_add.
  apply Nat.neq_0_lt_0.
  now intros H1; subst q.
}
assert (Hcpq : coprimes p q). {
  progress unfold coprimes.
  now apply eq_primes_gcd_1.
}
assert (Hcqp : coprimes q p). {
  progress unfold coprimes.
  now rewrite Nat.gcd_comm.
}
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
assert (Hqz : q ≠ 0) by now intros H; rewrite H in Hq.
specialize (Gauss_lemma p q Hq Hcpq _ eq_refl) as H1.
specialize (Gauss_lemma q p Hp Hcqp _ eq_refl) as H2.
specialize (Eisenstein_lemma p q Hcpq Hop Hoq) as H3.
specialize (Eisenstein_lemma q p Hcqp Hoq Hop) as H4.
progress unfold is_quadratic_residue.
rewrite H1, H2.
remember (∑ (k = 1, _), _) as spq eqn:Hspq in H3.
remember (∑ (k = 1, _), _) as sqp eqn:Hsqp in H4.
move sqp before spq; move Hsqp before Hspq.
remember (∑ (x = 1, (p - 1) / 2), ∑ (y = 1, (q - 1) / 2), 1) as r eqn:Hrv.
assert (Hrl : r = (p - 1) / 2 * ((q - 1) / 2)). {
  rewrite rngl_summation_const in Hrv; [ | easy ].
  rewrite Nat_sub_succ_1 in Hrv.
  rewrite rngl_summation_const in Hrv; [ | easy ].
  rewrite Nat_sub_succ_1 in Hrv.
  rewrite rngl_mul_1_r in Hrv.
  rewrite <- rngl_of_nat_mul in Hrv; [ | easy ].
  rewrite <- (rngl_of_nat_nat r) in Hrv.
  now apply rngl_of_nat_inj in Hrv.
}
generalize Hrv; intros Hr.
clear Hrv.
erewrite rngl_summation_eq_compat in Hr; cycle 1. {
  intros x Hx.
  erewrite rngl_summation_eq_compat; cycle 1. {
    intros y Hy.
    replace 1%L with 1 by easy.
    replace 1 with (Nat.b2n (p * y <? q * x) + Nat.b2n (q * x <? p * y));
    cycle 1. {
      progress unfold Nat.b2n.
      remember (p * y <? q * x) as b eqn:Hb.
      symmetry in Hb.
      remember (q * x <? p * y) as c eqn:Hc.
      symmetry in Hc.
      destruct b, c; [ | easy | easy | ]; exfalso. {
        apply Nat.ltb_lt in Hb.
        apply Nat.ltb_lt in Hc.
        flia Hb Hc.
      }
      apply Nat.ltb_ge in Hb.
      apply Nat.ltb_ge in Hc.
      apply Nat.le_antisymm in Hb; [ clear Hc | easy ].
      assert (H5 : Nat.divide p (q * x)). {
        rewrite <- Hb.
        apply Nat.divide_factor_l.
      }
      apply Nat.gauss in H5; [ | easy ].
      destruct H5 as (u, H5).
      rewrite H5 in Hx.
      destruct Hx as (H6, H7).
      apply Nat.nlt_ge in H7.
      apply H7; clear H7.
      destruct u; [ easy | ].
      cbn - [ "/" ].
      apply (Nat.lt_le_trans _ p); [ | apply Nat.le_add_r ].
      apply Nat.Div0.div_lt_upper_bound.
      rewrite Nat_mul_2_l.
      apply (Nat.lt_le_trans _ p); [ | apply Nat.le_add_r ].
      apply Nat.sub_lt; [ | easy ].
      now apply Nat.neq_0_lt_0.
    }
    replace Nat.mul with rngl_mul by easy.
    easy.
  }
  cbn - [ "<?" "/" ].
  replace Nat.add with rngl_add by easy.
  rewrite rngl_summation_add_distr.
  remember (∑ (y = _, _), _) as xx in |-*.
  remember (∑ (y = _, _), _) as yy in |-*.
  subst xx yy.
  easy.
}
cbn - [ "<?" "/" ] in Hr.
rewrite rngl_summation_add_distr in Hr.
remember (∑ (x = _, _), _) as xx in Hr.
remember (∑ (x = _, _), _) as yy in Hr.
subst xx yy.
subst r; symmetry in Hr.
erewrite rngl_summation_eq_compat in Hr; cycle 1. {
  intros x Hx.
  rewrite summation_b2n_mul_lt; cycle 1. {
    now apply Nat.neq_0_lt_0.
  } {
    now apply mul_div_le_pred_div_2.
  }
  rewrite Nat.mul_comm.
  replace ((x * q - 1) / p) with (x * q / p); cycle 1. {
    now apply mul_div_eq_mul_sub_1_div.
  }
  replace Nat.div with rngl_div by easy.
  replace Nat.mul with rngl_mul by easy.
  easy.
}
cbn - [ "<?" rngl_mul rngl_div "/" ] in Hr.
rewrite <- Hsqp in Hr.
rewrite rngl_summation_summation_exch in Hr.
erewrite rngl_summation_eq_compat in Hr; cycle 1. {
  intros x Hx.
  rewrite summation_b2n_mul_lt; cycle 1. {
    now apply Nat.neq_0_lt_0.
  } {
    now apply mul_div_le_pred_div_2.
  }
  rewrite Nat.mul_comm.
  replace ((x * p - 1) / q) with (x * p / q); cycle 1. {
    now apply mul_div_eq_mul_sub_1_div.
  }
  replace Nat.div with rngl_div by easy.
  replace Nat.mul with rngl_mul by easy.
  easy.
}
cbn - [ "<?" rngl_mul rngl_div "/" ] in Hr.
rewrite <- Hspq in Hr.
replace rngl_add with Nat.add in Hr by easy.
rewrite Nat_sub_1_pow_mod; cycle 1. {
  apply Nat_le_neq_lt.
  now apply Nat.neq_0_lt_0.
  now intros H; subst q.
}
rewrite Nat_sub_1_pow_mod; cycle 1. {
  apply Nat_le_neq_lt.
  now apply Nat.neq_0_lt_0.
  now intros H; subst p.
}
rewrite H3, H4.
rewrite <- Nat_sub_1_pow_mod; cycle 1. {
  apply Nat_le_neq_lt.
  now apply Nat.neq_0_lt_0.
  now intros H; subst q.
}
rewrite <- Nat_sub_1_pow_mod; cycle 1. {
  apply Nat_le_neq_lt.
  now apply Nat.neq_0_lt_0.
  now intros H; subst p.
}
rewrite Nat_sub_1_pow_mod_eq_even; cycle 1. {
  destruct q; [ easy | ].
  destruct q; [ easy | ].
  destruct q; [ | now do 2 apply -> Nat.succ_lt_mono ].
  apply Nat.odd_spec in Hoq.
  now rewrite Nat.odd_2 in Hoq.
}
rewrite Nat_sub_1_pow_mod_eq_even; cycle 1. {
  destruct p; [ easy | ].
  destruct p; [ easy | ].
  destruct p; [ | now do 2 apply -> Nat.succ_lt_mono ].
  apply Nat.odd_spec in Hop.
  now rewrite Nat.odd_2 in Hop.
}
assert (H : p ≠ 2). {
  intros H; subst p.
  now apply Nat.odd_spec in Hop.
}
specialize (odd_prime_mod_4 p Hp H) as H4p; clear H.
assert (H : q ≠ 2). {
  intros H; subst q.
  now apply Nat.odd_spec in Hoq.
}
specialize (odd_prime_mod_4 q Hq H) as H4q; clear H.
destruct H4p as [H4p| H4p]. {
  split; intros Hpq; [ now left | clear Hpq ].
  apply Nat_eq_mod_1 in H4p.
  destruct H4p as (H4p & _ & _).
  apply Nat.Div0.mod_divides in H4p.
  destruct H4p as (p', H4p).
  rewrite H4p in Hr.
  rewrite (Nat.mul_comm 4) in Hr.
  progress replace 4 with (2 * 2) in Hr by easy.
  rewrite Nat.mul_assoc in Hr.
  rewrite Nat.div_mul in Hr; [ | easy ].
  rewrite (Nat.mul_comm _ 2) in Hr.
  rewrite <- Nat.mul_assoc in Hr.
  remember (Nat.even sqp) as esqp eqn:Hesqp.
  symmetry in Hesqp.
  destruct esqp. {
    apply Nat.even_spec in Hesqp.
    destruct Hesqp as (c, H); move H at top; subst sqp.
    apply Nat.add_sub_eq_l in Hr.
    rewrite <- Nat.mul_sub_distr_l in Hr.
    rewrite <- Hr.
    apply Nat.even_even.
  } {
    apply Bool.not_true_iff_false in Hesqp.
    apply Bool.not_true_iff_false.
    intros H; apply Hesqp; clear Hesqp.
    apply Nat.even_spec in H.
    destruct H as (c, H); move H at top; subst spq.
    apply Nat.add_sub_eq_r in Hr.
    rewrite <- Nat.mul_sub_distr_l in Hr.
    rewrite <- Hr.
    apply Nat.even_even.
  }
}
destruct H4q as [H4q| H4q]. {
  split; intros Hpq; [ now right | clear Hpq ].
  apply Nat_eq_mod_1 in H4q.
  destruct H4q as (H4q & _ & _).
  apply Nat.Div0.mod_divides in H4q.
  destruct H4q as (q', H4q).
  rewrite H4q in Hr.
  rewrite Nat.mul_comm in Hr.
  rewrite (Nat.mul_comm 4) in Hr.
  progress replace 4 with (2 * 2) in Hr by easy.
  rewrite Nat.mul_assoc in Hr.
  rewrite Nat.div_mul in Hr; [ | easy ].
  rewrite (Nat.mul_comm _ 2) in Hr.
  rewrite <- Nat.mul_assoc in Hr.
  remember (Nat.even sqp) as esqp eqn:Hesqp.
  symmetry in Hesqp.
  destruct esqp. {
    apply Nat.even_spec in Hesqp.
    destruct Hesqp as (c, H); move H at top; subst sqp.
    apply Nat.add_sub_eq_l in Hr.
    rewrite <- Nat.mul_sub_distr_l in Hr.
    rewrite <- Hr.
    apply Nat.even_even.
  } {
    apply Bool.not_true_iff_false in Hesqp.
    apply Bool.not_true_iff_false.
    intros H; apply Hesqp; clear Hesqp.
    apply Nat.even_spec in H.
    destruct H as (c, H); move H at top; subst spq.
    apply Nat.add_sub_eq_r in Hr.
    rewrite <- Nat.mul_sub_distr_l in Hr.
    rewrite <- Hr.
    apply Nat.even_even.
  }
}
split; intros Hpq; [ exfalso | now destruct Hpq; congruence ].
apply Nat_eq_mod_exists in H4p, H4q.
destruct H4p as ((p', H4p), _).
destruct H4q as ((q', H4q), _).
rewrite H4p, H4q in Hr.
rewrite <- Nat.add_sub_assoc in Hr; [ | now apply -> Nat.succ_le_mono ].
rewrite <- Nat.add_sub_assoc in Hr; [ | now apply -> Nat.succ_le_mono ].
rewrite Nat_sub_succ_1 in Hr.
progress replace 4 with (2 * 2) in Hr by easy.
do 2 rewrite Nat.mul_assoc in Hr.
rewrite Nat.div_add_l in Hr; [ | easy ].
rewrite Nat.div_add_l in Hr; [ | easy ].
rewrite Nat.div_same in Hr; [ | easy ].
remember (Nat.even sqp) as esqp eqn:Hqp.
symmetry in Hqp.
destruct esqp. {
  apply Nat.even_spec in Hpq, Hqp.
  destruct Hpq as (sp', Hpq).
  destruct Hqp as (sq', Hqp).
  move Hpq at top; move Hqp at top.
  subst spq sqp.
  rewrite <- Nat.mul_add_distr_l in Hr.
  assert (H : Nat.divide 2 (2 * (sq' + sp'))). {
    apply Nat.divide_factor_l.
  }
  rewrite Hr in H.
  apply prime_divide_mul in H; [ | easy ].
  destruct H as [H| H]. {
    apply Nat.divide_add_cancel_r in H; [ | apply Nat.divide_factor_r ].
    now apply Nat.divide_1_r in H.
  } {
    apply Nat.divide_add_cancel_r in H; [ | apply Nat.divide_factor_r ].
    now apply Nat.divide_1_r in H.
  }
} {
  rewrite <- Nat.negb_odd in Hqp, Hpq.
  apply Bool.negb_false_iff in Hpq, Hqp.
  apply Nat.odd_spec in Hpq, Hqp.
  destruct Hpq as (sp', Hpq).
  destruct Hqp as (sq', Hqp).
  move Hpq at top; move Hqp at top.
  subst spq sqp.
  rewrite Nat.add_shuffle0 in Hr.
  do 2 rewrite <- Nat.add_assoc in Hr.
  rewrite Nat.add_succ_comm in Hr.
  rewrite Nat.add_0_l in Hr.
  rewrite Nat.add_assoc in Hr.
  rewrite <- Nat.mul_add_distr_l in Hr.
  rewrite <- Nat.mul_succ_r in Hr.
  assert (H : Nat.divide 2 (2 * S (sq' + sp'))). {
    apply Nat.divide_factor_l.
  }
  rewrite Hr in H.
  apply prime_divide_mul in H; [ | easy ].
  destruct H as [H| H]. {
    apply Nat.divide_add_cancel_r in H; [ | apply Nat.divide_factor_r ].
    now apply Nat.divide_1_r in H.
  } {
    apply Nat.divide_add_cancel_r in H; [ | apply Nat.divide_factor_r ].
    now apply Nat.divide_1_r in H.
  }
}
Qed.

Inspect 1.

(* to be completed
(* attempt to define it with Legendre symbols but the problem is that
   my Legendre symbol is not "1 or -1" but "1 or p-1".
Theorem quadratic_reciprocity :
  ∀ p q, prime p → prime p →
  Legendre_symbol p q * Legendre_symbol q p =
  opp_1_pow (((p -1) / 2) * ((q - 1) / 2)).
*)
*)
