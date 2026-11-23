Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith Init.Nat.
Require Import Misc Primes QuadRes_1.

Require Import RingLike.Core.
Require Import RingLike.IterAdd.
Require Import RingLike.Nat_algebra.

Check Euler_criterion.
Check Gauss_lemma.
Check quadratic_reciprocity_2.

(* to be completed
Theorem quadratic_reciprocity :
  ∀ p q, prime p → prime q → 2 < p < q →
  is_quadratic_residue p q = is_quadratic_residue q p ↔
    p mod 4 = 1 ∨ q mod 4 = 1.
Proof.
intros * Hp Hq Hpq.
assert (Hop : Nat.Odd p). {
  assert (H : p ≠ 2). {
    destruct Hpq as (H, _).
    intros H1; subst p.
    now apply Nat.lt_irrefl in H.
  }
  specialize (odd_prime _ Hp H) as H1.
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
  assert (H : q ≠ 2). {
    intros H1; subst q.
    destruct Hpq as (H1, H2).
    apply Nat.lt_le_incl in H1.
    now apply Nat.nlt_ge in H1.
  }
  specialize (odd_prime _ Hq H) as H1.
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
  rewrite Nat.gcd_comm.
  apply (eq_gcd_prime_small_1 q p Hq); flia Hpq.
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
(*
    progress unfold Nat.b2n.
    do 2 rewrite nat_ltb_rngl_ltb.
*)
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
    apply Nat.Div0.div_le_upper_bound.
    rewrite <- Nat.Lcm0.divide_div_mul_exact; cycle 1. {
      destruct Hoq as (c, H).
      rewrite H, Nat.add_sub.
      apply Nat.divide_factor_l.
    }
    destruct Hx as (H1x, Hx).
    apply (Nat.mul_le_mono_l _ _ q) in Hx.
    eapply Nat.le_trans; [ apply Hx | ].
    rewrite <- Nat.Lcm0.divide_div_mul_exact; cycle 1. {
      destruct Hop as (c, H).
      rewrite H, Nat.add_sub.
      apply Nat.divide_factor_l.
    }
    apply Nat.Div0.div_le_mono.
    rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
    rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
    rewrite Nat.mul_comm.
    apply Nat.sub_le_mono_l.
Check Hpq.
(* should be proven without Hpq; see further *)
    now apply Nat.lt_le_incl.
  }
  clear Hpq.
  rewrite Nat.mul_comm.
  replace ((x * q - 1) / p) with (x * q / p); cycle 1. {
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
  }
  replace Nat.div with rngl_div by easy.
  replace Nat.mul with rngl_mul by easy.
  easy.
}
cbn - [ "<?" rngl_mul rngl_div "/" ] in Hr.
rewrite <- Hsqp in Hr.
rewrite rngl_summation_summation_exch in Hr.
clear Hpq.
erewrite rngl_summation_eq_compat in Hr; cycle 1. {
  intros x Hx.
  rewrite summation_b2n_mul_lt; cycle 1. {
    now apply Nat.neq_0_lt_0.
  } {
    assert (H5 : 2 * p * x  ≤ p * (q - 1) < p * q). {
      split. {
        rewrite (Nat.mul_comm 2), <- Nat.mul_assoc.
        apply Nat.mul_le_mono_l.
        destruct Hx as (H1x, Hx).
        apply (Nat.mul_le_mono_pos_l _ _ 2) in Hx; [ | easy ].
        eapply Nat.le_trans; [ apply Hx | ].
        apply Nat.Div0.mul_div_le.
      }
      apply Nat.mul_lt_mono_pos_l; [ now apply Nat.neq_0_lt_0 | ].
      apply Nat.sub_lt; [ now  apply Nat.neq_0_lt_0 | easy ].
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
  }
  rewrite Nat.mul_comm.
  replace ((x * p - 1) / q) with (x * p / q); cycle 1. {
    specialize (Nat.div_mod (x * p) q) as H5.
    rewrite H5; [ | now intros H; subst q ].
    rewrite <- Nat.add_sub_assoc; cycle 1. {
      apply Nat.neq_0_lt_0.
      intros H.
      apply Nat.Lcm0.mod_divide in H.
      apply Nat.gauss in H; cycle 1. {
        apply eq_gcd_prime_small_1; [ easy | ].
        split; [ easy | ].
        eapply Nat.le_lt_trans; [ apply Hx | ].
        apply Nat.Div0.div_lt_upper_bound.
        apply (Nat.lt_le_trans _ q).
        apply Nat.sub_lt; [ now apply Nat.neq_0_lt_0 | easy ].
        rewrite Nat_mul_2_l.
        apply Nat.le_add_l.
      }
      progress unfold coprimes in Hcpq.
      destruct H as (c, Hc).
      rewrite Hc in Hcpq.
      rewrite Nat.gcd_comm in Hcpq.
      rewrite Nat.mul_comm in Hcpq.
      rewrite Nat.gcd_mul_diag_l in Hcpq.
      now rewrite Hcpq in Hq.
    }
    rewrite (Nat.mul_comm q).
    rewrite Nat.div_add_l; [ | easy ].
    rewrite Nat.div_add_l; [ | easy ].
    progress f_equal.
    rewrite Nat.div_small; [ | now apply Nat.mod_upper_bound ].
    symmetry.
    apply Nat.div_small.
    apply (Nat.le_lt_trans _ ((x * p) mod q)); cycle 1. {
      now apply Nat.mod_upper_bound.
    }
    apply Nat.le_sub_l.
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
...
  destruct H4q as [H4q| H4q]. {
    apply Nat_eq_mod_1 in H4q.
    destruct H4q as (H4q & _ & _).
    apply Nat.Div0.mod_divides in H4p, H4q.
    destruct H4p as (p', H4p).
    destruct H4q as (q', H4q).
    rewrite H4p, H4q in Hr.
    do 2 rewrite (Nat.mul_comm 4) in Hr.
    progress replace 4 with (2 * 2) in Hr by easy.
    do 2 rewrite Nat.mul_assoc in Hr.
    rewrite Nat.div_mul in Hr; [ | easy ].
    rewrite Nat.div_mul in Hr; [ | easy ].
    rewrite (Nat.mul_comm _ 2), Nat.mul_assoc in Hr.
    rewrite Nat.mul_comm, Nat.mul_assoc in Hr.
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
  } {
...
    apply Nat_eq_mod_exists in H4q.
    destruct H4q as ((q', H4q) & _).
    apply Nat.Div0.mod_divides in H4p, H4q.
    destruct H4p as (p', H4p).
    destruct H4q as (q', H4q).
    rewrite H4p, H4q in Hr.
    do 2 rewrite (Nat.mul_comm 4) in Hr.
    progress replace 4 with (2 * 2) in Hr by easy.
    do 2 rewrite Nat.mul_assoc in Hr.
    rewrite Nat.div_mul in Hr; [ | easy ].
    rewrite Nat.div_mul in Hr; [ | easy ].
    rewrite (Nat.mul_comm _ 2), Nat.mul_assoc in Hr.
    rewrite Nat.mul_comm, Nat.mul_assoc in Hr.
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
...
rewrite Nat_sub_1_pow_mod in H1; cycle 1. {
  apply Nat_le_neq_lt.
  now apply Nat.neq_0_lt_0.
  now intros H; subst q.
}
rewrite Nat_sub_1_pow_mod in H2; cycle 1. {
  apply Nat_le_neq_lt.
  now apply Nat.neq_0_lt_0.
  now intros H; subst p.
}
rewrite H3 in H1.
rewrite H4 in H2.
move sqp before spq.
rewrite <- Nat_even_mod_2.
rewrite <- (Nat_even_mod_2 sqp).
remember (spq mod 2) as spq2 eqn:Hspq2.
remember (sqp mod 2) as sqp2 eqn:Hsqp2.
move sqp2 before spq2.
move Hsqp2 before Hspq2.
remember (Nat.even sqp2) as esqp eqn:Hesqp.
symmetry in Hesqp.
destruct esqp. {
  split; intros Hespq. {
...
(*
destruct Hx as (H1x, Hx).
apply (Nat.mul_le_mono_l _ _ p) in Hx.
eapply Nat.le_lt_trans; [ apply Hx | ].
destruct Hoq as (q', Hoq).
rewrite Hoq, Nat.add_sub, (Nat.mul_comm 2).
rewrite Nat.div_mul; [ | easy ].
rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
destruct Hop as (p', Hop).
rewrite Hop at 1 2.
rewrite (Nat.mul_comm 2).
rewrite Nat.div_add_l; [ | easy ].
rewrite Nat.div_small; [ | easy ].
rewrite Nat.add_0_r.
...
  p * ((q - 1) / 2) < q * (p / 2)
...
*)
      apply (Nat.mul_lt_mono_pos_l 2); [ easy | ].
      rewrite Nat.mul_assoc.
      eapply Nat.le_lt_trans; [ apply H5 | ].
      rewrite (Nat.mul_comm q).
rewrite Nat.mul_assoc.
destruct Hoq as (q', Hoq).
rewrite Hoq, Nat.add_sub.
rewrite Nat.mul_assoc, (Nat.mul_comm p).
rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
destruct Hop as (p', Hop).
rewrite Hop.
rewrite (Nat.mul_comm 2 p').
rewrite Nat.div_add_l; [ | easy ].
rewrite (Nat.div_small 1 2); [ | easy ].
rewrite Nat.add_0_r.
do 2 rewrite <- Nat.mul_assoc.
rewrite <- Nat.mul_add_distr_l.
apply Nat.mul_lt_mono_pos_l; [  easy | ].
...
(*
...
rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
apply (Nat.add_lt_mono_r _ _ p).
rewrite Nat.sub_add; cycle 1. {
destruct q; [ easy | ].
rewrite Nat.mul_succ_r.
apply Nat.le_add_l.
}
      rewrite (Nat.mul_comm p), (Nat.mul_comm 2).
      rewrite <- Nat.mul_assoc.
apply Nat.lt_sub_lt_add_l.
rewrite <- Nat.mul_sub_distr_l.
...
*)
      eapply Nat.lt_le_trans; [ apply H5 | ].
      rewrite (Nat.mul_comm p), (Nat.mul_comm 2).
      rewrite <- Nat.mul_assoc.
      apply Nat.mul_le_mono_l.
      destruct Hop as (p', Hop); rewrite Hop.
      rewrite Nat.mul_comm.
      rewrite Nat.div_add_l; [ | easy ].
      cbn; rewrite Nat.add_0_r.
...
    apply Nat.Div0.div_le_upper_bound.
    destruct Hx as (H1x, Hx).
    apply (Nat.mul_le_mono_l _ _ p) in Hx.
    eapply Nat.le_trans; [ apply Hx | ].
...
    destruct Hop as (p', Hop); rewrite Hop at 2.
    destruct Hoq as (q', Hoq); rewrite Hoq at 1.
    do 2 rewrite Nat.add_sub.
    rewrite (Nat.mul_comm 2), Nat.div_mul; [ | easy ].
    rewrite (Nat.mul_comm 2), Nat.div_mul; [ | easy ].
...
    replace ((p - 1) / 2) with (p / 2); cycle 1. {
      destruct Hop as (p', Hop); rewrite Hop.
      rewrite Nat.add_sub.
      rewrite Nat.mul_comm, Nat.div_add_l; [ | easy ].
      rewrite Nat.div_mul; [ | easy ].
      apply Nat.add_0_r.
    }
    replace ((q - 1) / 2) with (q / 2) in Hx; cycle 1. {
      destruct Hoq as (q', Hoq); rewrite Hoq.
      rewrite Nat.add_sub.
      rewrite Nat.mul_comm, Nat.div_add_l; [ | easy ].
      rewrite Nat.div_mul; [ | easy ].
      apply Nat.add_0_r.
    }
    apply Nat.Div0.div_le_upper_bound.
    destruct Hx as (H1x, Hx).
    apply (Nat.mul_le_mono_l _ _ p) in Hx.
    eapply Nat.le_trans; [ apply Hx | ].
...
destruct Hop as (p', Hop); rewrite Hop.
destruct Hoq as (q', Hoq); rewrite Hoq.
rewrite Nat.add_sub.
do 2 rewrite (Nat.mul_comm 2).
rewrite Nat.div_add_l; [ | easy ].
rewrite Nat.div_mul; [ | easy ].
cbn; rewrite Nat.add_0_r.
rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
...
Search (_ * (_ / _) ≤ _).
eapply Nat.le_trans.
apply Nat.Div0.div_mul_le.
rewrite Nat.mul_comm.
Check Nat.Div0.div_mul_le.
...
    rewrite <- Nat.Lcm0.divide_div_mul_exact; cycle 1. {
      destruct Hoq as (c, H).
      rewrite H, Nat.add_sub.
      apply Nat.divide_factor_l.
    }
...
    destruct Hop as (p', Hop).
    destruct Hoq as (q', Hoq).
    rewrite Hop, Nat.add_sub.
    rewrite Hoq, Nat.add_sub.
    rewrite (Nat.mul_comm _ q'), Nat.mul_assoc.
    rewrite Nat.div_mul; [ | easy ].
    rewrite (Nat.mul_comm _ p'), Nat.mul_assoc.
    rewrite Nat.div_mul; [ | easy ].
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
...
    apply Nat.Div0.div_le_mono.
    rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
    rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
    rewrite Nat.mul_comm.
    apply Nat.sub_le_mono_l.
...
    now apply Nat.lt_le_incl.
  }
  rewrite Nat.mul_comm.
  replace ((x * q - 1) / p) with (x * q / p); cycle 1. {
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
  }
  replace Nat.div with rngl_div by easy.
  replace Nat.mul with rngl_mul by easy.
  easy.
}
...
...
}
cbn - [ "<?" "/" ] in Hr.
...
  specialize (summation_b2n_mul_lt (q * x) ((q - 1) / 2)) as H5.
  rewrite H5.
...
assert (Hxy : spq + sqp = (p - 1) / 2 * (q - 1) / 2). {
  rewrite Hspq, Hsqp.
...
  erewrite rngl_summation_eq_compat; cycle 1. {
    intros x Hx.
  erewrite rngl_summation_eq_compat; cycle 1. {
    intros x Hx.
...
remember (_ =? 1) as x eqn:Hx.
remember (_ =? 1) as y eqn:Hy in |-*.
move y before x.
symmetry in Hx, Hy.
destruct x. {
  apply Nat.eqb_eq in Hx.
  apply Nat_sub_1_pow_mod_is_even in Hx; [ | flia Hpq ].
  destruct Hx as (x, Hx).
  generalize Hx; intros Hx1.
  apply (f_equal (λ x, x mod 2)) in Hx1.
  rewrite H3 in Hx1.
  rewrite Nat.mul_comm, Nat.Div0.mod_mul in Hx1.
  destruct y. {
    split; [ intros _ | easy ].
    apply Nat.eqb_eq in Hy.
    apply Nat_sub_1_pow_mod_is_even in Hy; [ | flia Hpq ].
    destruct Hy as (y, Hy).
    generalize Hy; intros Hy1.
    apply (f_equal (λ x, x mod 2)) in Hy1.
    rewrite H4 in Hy1.
    rewrite Nat.mul_comm, Nat.Div0.mod_mul in Hy1.
...
rewrite <- 
Check Nat_sub_1_squ
...
  apply Nat.add_sub_eq_nz in H4; cycle 1. {
    intros H5.
    apply Nat.eq_mul_0 in H5.
    destruct H5 as [H5| H5]; [ now subst n | ].
    subst d.
    rewrite Nat.mul_0_r in H4.
    flia H2n H4.
  }
...
  enough (n ≠ 2).
  rewrite Nat.mul_comm in H4.
  destruct d; [ flia H4 H1n H | ].
  cbn in H4.
  apply Nat.add_sub_eq_nz in H4.
  rewrite Nat.add_comm in H4.
  apply Nat.add_sub_eq_l in H4.
...
  apply Nat.sub_le in H4.
...
  destruct n; [ easy | ].
  rewrite Nat_sub_succ_1 in H4, H2, H1.
  destruct n; [ easy | ].
  clear H1n H3.
  apply Nat_eq_succ_mod_1 in H4.
  apply Nat.Div0.mod_divides in H4.
  destruct H4 as (d, H4).
...
Search ((_ - _) mod _).
  apply Nat_eq_mod_1 in H4.
...
  rewrite Nat.mod_pow_l in H4.
  rewrite Nat_sub_1_squ in H4.
...
  rewrite Nat.mod_1_l in H4; [ | easy ].

Search (_ mod _ = 1).
  apply Nat_eq_mod_1 in H4.
  destruct H4 as (H4 & H5 & H6).
  apply Nat.Div0.mod_divides in H4.
...
Search ((_ - _)²).
rewrite Nat_sub_1_squ in H4.
...
remember (_ ^ _ mod _) as x eqn:Hx; symmetry in Hx.
remember (_ ^ _ mod _) as y eqn:Hy in |-*; symmetry in Hy.
move y before x; move Hy before Hx.
destruct (Nat.eq_dec x 1) as [Hx1| Hx1]. {
  move Hx1 at top; subst x.
  apply glop in Hx.
  destruct (Nat.eq_dec y 1) as [Hy1| Hy1]. {
    move Hy1 at top; subst y.
    apply glop in Hy.
...
specialize (Euler_criterion p Hp q) as H1.
progress unfold Legendre_symbol in H1.
symmetry in H1.
specialize (Euler_criterion q Hq p) as H2.
progress unfold Legendre_symbol in H2.
symmetry in H2.
assert (H : coprimes p q). {
  progress unfold coprimes.
  rewrite Nat.gcd_comm.
  apply (eq_gcd_prime_small_1 q p Hq); flia Hpq.
}
specialize (Gauss_lemma p q Hq H _ eq_refl) as H3; clear H.
assert (H : coprimes q p). {
  apply (eq_gcd_prime_small_1 q p Hq); flia Hpq.
}
specialize (Gauss_lemma q p Hp H _ eq_refl) as H4; clear H.
symmetry in H3, H4.
progress unfold Legendre_symbol in H3.
progress unfold Legendre_symbol in H4.
progress unfold Legendre_symbol.
remember (p =? 2) as p2 eqn:Hp2; symmetry in Hp2.
destruct p2; [ apply Nat.eqb_eq in Hp2; flia Hpq Hp2 | ].
clear Hp2.
remember (q =? 2) as q2 eqn:Hq2; symmetry in Hq2.
destruct q2; [ apply Nat.eqb_eq in Hq2; flia Hpq Hq2 | ].
clear Hq2.
remember (q mod p =? 0) as qpz eqn:Hqpz; symmetry in Hqpz.
destruct qpz. {
  apply Nat.eqb_eq in Hqpz.
  apply Nat.Div0.mod_divides in Hqpz.
  destruct Hqpz as (c, Hc).
  subst q.
  destruct c; [ flia Hpq | cbn in Hpq ].
  destruct c; [ flia Hpq | cbn in Hpq ].
  apply prime_not_mul in Hq.
  now destruct Hq; [ subst p  | ].
}
clear Hqpz.
remember (p mod q =? 0) as pqz eqn:Hpqz; symmetry in Hpqz.
destruct pqz. {
  apply Nat.eqb_eq in Hpqz.
  apply Nat.Div0.mod_divides in Hpqz.
  destruct Hpqz as (c, Hc).
  subst p.
  destruct c; flia Hpq.
}
clear Hpqz.
remember (sqrt_mod q p) as mqp eqn:Hmqp; symmetry in Hmqp.
destruct mqp as [a| ]. {
  move a before q.
  rewrite Nat.eqb_refl.
  apply eq_sqrt_mod_Some in Hmqp.
  destruct Hmqp as (Hap, Ha2).
  remember (sqrt_mod p q) as mpq eqn:Hmpq; symmetry in Hmpq.
(*
  destruct mpq as [b| ]; cycle 1. {
    assert (H : q ≠ 0) by flia Hap Hpq.
    specialize (eq_sqrt_mod_None p q H Hmpq) as Hb2; clear H Hmpq.
...
*)
  destruct mpq as [b| ]. {
    move b before a.
    move H2 before H1.
    rewrite Nat.eqb_refl.
    split; [ intros _ | easy ].
    apply eq_sqrt_mod_Some in Hmpq.
    destruct Hmpq as (Hbp, Hb2).
    move Hbp before Hap.
    move Hb2 before Ha2.
    assert (H : p ≠ 2) by flia Hpq.
    specialize (odd_prime_mod_4 p Hp H) as Hp4; clear H.
    assert (H : q ≠ 2) by flia Hpq.
    specialize (odd_prime_mod_4 q Hq H) as Hq4; clear H.
    destruct Hp4 as [Hp4| Hp4]; [ now left | right ].
    destruct Hq4 as [Hq4| Hq4]; [ easy | exfalso ].
Check Eisenstein_lemma.
...
rewrite Nat.sub_sub_distr in H3.
rewrite Nat.sub_add_distr in H3.
rewrite Nat.add_sub in H3.
...
rewrite <- rngl_mul_sub_distr_l in H1; [ | ].
...
remember (∑ (k = 1, _), (if _ <=? _ then (k * a)%L mod l else 0)) as m eqn:Hm.
remember (∑ (k = 1, _), (if _ <=? _ then 0 else (k * a)%L mod l)) as n eqn:Hn.
move n before m.
rewrite eq_nb_of_mult_gt_half_summation.
progress unfold Nat.b2n.
...
Search (List.map _ (List.seq _ _)).
rewrite Misc.List_map_seq.
rewrite List.seq_map.
Check permutation_seq_map_abs_seq.
...
specialize (mul_all_different_multiples a p Hap) as H1.
rewrite Nat_sub_succ_1.
rewrite List.map_id.
(*
Compute (
  let l := 100 in
List.map (λ a,
is_permutation eqb
 (List.seq 1 ((l - 1) / 2))
 (List.map (λ i, abs ((i * a) mod l) l) (List.seq 1 ((l - 1) / 2))))
(List.filter (are_coprimes l) (List.seq 1 (l - 1)))).
*)
Check permutation_seq_map_abs_seq.
...
    apply Nat.le_sub_le_add_r.
    eapply Nat.le_trans; [ | apply Nat.lt_le_incl, Hu ].
...
      specialize congruence_inverse_has_unique_solution as H1.
      specialize (H1 l (a mod l)).
      assert (H : 0 < a mod l < l). {
        split; [ | now apply Nat.mod_upper_bound ].
        apply Nat.neq_0_lt_0.
        intros H.
        rewrite <- Nat.Div0.mul_mod_idemp_r in Hialm.
        rewrite H, Nat.mul_0_r in Hialm.
        symmetry in Hialm.
        rewrite Nat.Div0.mod_0_l in Hialm.
        now  subst m; rewrite Nat.mul_0_r in Hm.
      }
      specialize (H1 H); clear H.
      specialize (H1 a Hal).
      destruct H1 as (z & (H1, H2) & H3).
...
    rewrite Hm at  3.
    rewrite Hm in Hi.
    rewrite Hm in Hu at 1.
    replace ((2 * m - 1) / 2) with (m - 1) in Hi, Hu |-*; cycle 1. {
      symmetry.
      destruct m; [ easy | ].
      rewrite Nat.mul_succ_r.
      rewrite <- Nat.add_sub_assoc; [ | now apply -> Nat.succ_le_mono ].
      do 2 rewrite Nat_sub_succ_1.
      rewrite Nat.mul_comm.
      rewrite Nat.div_add_l; [ | easy ].
      rewrite Nat.div_small; [ | now apply -> Nat.succ_lt_mono ].
      apply Nat.add_0_r.
    }
    rewrite Nat.add_comm in Hi.
    destruct (Nat.eq_dec m 0) as [Hmz| Hmz]; [ now subst m | ].
    rewrite Nat.sub_add in Hi; [ | now apply Nat.neq_0_lt_0 ].
    rewrite Nat.add_comm.
    rewrite <- Nat.add_sub_swap; [ | now apply Nat.neq_0_lt_0 ].
    rewrite <- Nat.add_sub_assoc; cycle 1. {
      apply Nat.neq_0_lt_0.
      now intros H; rewrite H in Hu.
    }
    rewrite Hm at 1.
    rewrite Nat_mul_2_l.
    apply Nat.add_le_mono_l.
    apply Nat.le_add_le_sub_l.
    apply Nat.le_succ_l.
    apply Nat.lt_sub_lt_add_l in Hu.
    apply -> Nat.lt_succ_r in Hu.
    apply Nat_le_neq_lt; [ easy | ].
    intros H; clear Hu.
    symmetry in H.
    rewrite Hm in H.
    rewrite (Nat.mul_comm 2) in H.
    rewrite Nat.Div0.mod_mul_r in H.
    remember ((i * a) / m mod 2) as u eqn:Hu.
    symmetry in Hu.
    destruct u. {
      rewrite Nat.mul_0_r, Nat.add_0_r in H.
      specialize (Nat.mod_upper_bound (i * a) m Hmz) as H1.
      rewrite H in H1.
      now apply Nat.lt_irrefl in H1.
    }
    rewrite Nat.mul_succ_r in H.
    rewrite Nat.add_assoc in H.
    apply Nat.add_sub_eq_r in H.
    rewrite Nat.sub_diag in H; symmetry in H.
    apply Nat.eq_add_0 in H.
    destruct H as (H1, H2).
    apply Nat.eq_mul_0 in H2.
    destruct H2 as [H2| H2]; [ easy | ].
    subst u.
    apply Nat.Div0.mod_divides in H1.
    destruct H1  as (c, Hc).
    rewrite Hc, Nat.mul_comm, Nat.div_mul in Hu; [ | easy ].
    apply Nat_eq_mod_1 in Hu.
    destruct Hu as (H1 & H2 & _).
    apply Nat.Div0.mod_divides in H1.
    destruct H1 as (n, H1).
    destruct c; [ easy |  ].
    rewrite Nat_sub_succ_1 in H1.
    clear H2.
    subst c.
    rewrite <- Nat.add_1_r in Hc.
    assert (H : Nat.divide m (i * a)). {
      rewrite Hc.
      apply Nat.divide_factor_l.
    }
(**)
Compute (
let m := 7 in
let i := 2 in
let n := 1 in
List.map (λ a,
((2*m, a),
  i * a = m * (2 * n + 1)
)
) (List.filter (are_coprimes (2 * m)) (List.seq 1 (2 * m)))
).
(**)
...
    apply Nat.add_sub_eq_nz in H1; cycle 1. {
      intros H.
      apply Nat.eq_mul_0 in H.
      destruct H as [H| H]; [ easy | subst n ].
      rewrite Nat.mul_0_r in H1.
      replace c with 1 in Hc  by flia H1 H2.
      clear c H1 H2.
      rewrite Nat.mul_1_r in Hc.
...
    destruct m; [ easy | ].
(*
Compute (
let m := 20 in
let i := 1 in
List.map (λ a,
(
a,
  2 * S m ≤ (i * a) mod (2 * S m) + (2 * S m - 1) / 2
)
)
(List.filter (λ a,
  Nat.ltb ((2 * S m - 1) / 2) ((i * a) mod (2 * S m))

)
  (List.filter (are_coprimes (2 * S m)) (List.seq 1 (2 * S m)))
)
).
*)
    rewrite Hm at 3.
    rewrite Nat.mul_succ_r.
    rewrite <- Nat.add_sub_assoc; [ | now apply -> Nat.succ_le_mono ].
    rewrite Nat_sub_succ_1.
    rewrite (Nat.mul_comm _ m), Nat.div_add_l; [ | easy ].
    rewrite Nat.div_small; [ | easy ].
    rewrite Nat.add_0_r.
    rewrite Hm in Hu at 1.
    rewrite Nat.mul_succ_r in Hu.
    rewrite <- Nat.add_sub_assoc in Hu; [ | now apply -> Nat.succ_le_mono ].
    rewrite Nat_sub_succ_1 in Hu.
    rewrite (Nat.mul_comm _ m), Nat.div_add_l in Hu; [ | easy ].
    rewrite Nat.div_small in Hu; [ | easy ].
    rewrite Nat.add_0_r in Hu.
    rewrite Hm in Hi.
    rewrite Nat.mul_succ_r in Hi.
    rewrite <- Nat.add_sub_assoc in Hi; [ | now apply -> Nat.succ_le_mono ].
    rewrite Nat_sub_succ_1 in Hi.
    rewrite (Nat.mul_comm _ m), Nat.div_add_l in Hi; [ | easy ].
    rewrite Nat.div_small in Hi; [ | easy ].
    rewrite Nat.add_0_r in Hi.
    destruct m; [ flia Hi | ].
    destruct m. {
      cbn in Hi.
      replace i with 1 in Hu by flia Hi.
      cbn in Hu.
      rewrite Nat.add_0_r in Hu.
      cbn in Hm.
      replace i with 1 by flia Hi.
      rewrite Nat.mul_1_l.
      subst l.
      clear i Hi.
      clear Hlz.
      remember (a mod 4) as a4 eqn:Ha4.
      symmetry in Ha4.
      destruct a4; [ easy | ].
      destruct a4; [ now apply Nat.lt_irrefl in Hu | ].
      clear Hu.
      destruct a4. {
        exfalso.
        progress unfold coprimes in Hal.
        rewrite Nat.gcd_comm in Hal.
        rewrite <- Nat.Lcm0.gcd_mod in Hal.
        rewrite Ha4 in Hal.
        easy.
      }
      rewrite Nat.add_1_r.
      now do 4 apply -> Nat.succ_le_mono.
    }
    progress unfold coprimes in Hal.
    destruct m. {
      cbn in Hm.
      subst l.
      clear Hlz.
      cbn in Hi.
      destruct i; [ easy | ].
      destruct i. {
        rewrite Nat.mul_1_l in Hu |-*.
        rewrite Nat.gcd_comm in Hal.
        rewrite <- Nat.Lcm0.gcd_mod in Hal.
        remember (a mod 6) as b.
        clear a Heqb.
        destruct b; [ easy | ].
        destruct b; [ cbn in Hu; flia Hu | ].
        destruct b; [ easy | ].
        destruct b; [ easy | flia ].
      }
      destruct i; [ clear Hi | flia Hi ].
      remember ((2 * a) mod 6) as b.
      symmetry in Heqb.
      destruct b; [ easy | ].
      destruct b; [ flia Hu | ].
      destruct b; [ flia Hu | clear Hu ].
      destruct b; [ exfalso | flia ].
      clear Hal.
      replace 3 with (3 mod 6) in Heqb at 2 by easy.
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      apply Nat_eq_mod_sub_0 in Heqb; [ | flia ].
      cbn - [ "mod" ] in Heqb.
      rewrite Nat.add_0_r in Heqb.
      rewrite Nat.add_succ_r in Heqb.
      rewrite Nat_sub_succ_1 in Heqb.
      rewrite Nat.add_succ_r in Heqb.
      rewrite <- Nat_mul_2_l in Heqb.
      rewrite <- Nat.add_1_r in Heqb.
      apply Nat.Lcm0.mod_divide in Heqb.
      destruct Heqb as (m, Hm).
      assert (H : Nat.Even (m * 6)). {
        rewrite Nat.mul_comm.
        replace 6 with (2 * 3) by easy.
        rewrite <- Nat.mul_assoc.
        apply Nat.Even_mul_l.
        exists 1; symmetry.
        apply Nat.mul_1_r.
      }
      rewrite <- Hm in H.
      rewrite Nat.add_1_r in H.
      apply Nat.Even_succ in H.
      apply Nat.Odd_mul_inv_l in H.
      apply Nat.Odd_succ in H.
      apply Nat.Even_succ in H.
      destruct H as (i, H).
      now rewrite Nat.add_1_r in H.
    }
    destruct m. {
      cbn in Hm; subst l.
...
      generalize Heqb; intros H1.
      apply Nat_eq_mod_sub_0 in Heqb; cycle 1. {
        destruct a; [ easy | ].
        destruct a; [ easy | flia ].
      }
      destruct a; [ easy | ].
      destruct a; [ easy | ].
...
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      destruct a; [ easy | ].
      destruct a; [ easy | ].
...
      rewrite Nat.gcd_comm in Hal.
      rewrite <- Nat.Lcm0.gcd_mod in Hal.
      rewrite <- Nat.Div0.mul_mod_idemp_r in Hu.
      rewrite <- Nat.Div0.mul_mod_idemp_r.
      remember (a mod 6) as b.
      clear a Heqb.
      rename b into a.
...
progress unfold abs.
remember 42 as z.
exists z.
split. {
  remember (_ <=? _) as u eqn:Hu.
  symmetry in Hu.
  destruct u. {
    apply Nat.leb_le in Hu.
...
  }
  apply Nat.leb_gt in Hu.
  rewrite <- H2.
  apply (Nat.add_cancel_r _ _ ((z * a) mod l)).
  rewrite Nat.sub_add; cycle 1. {
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  symmetry.
...
  specialize congruence_inverse_has_unique_solution as H4.
  specialize (H4 l (y - (l - 1) / 2)).
  assert (H : 0 < y - (l - 1) / 2 < l). {
    split; [ now apply Nat.lt_add_lt_sub_r | ].
    eapply Nat.le_lt_trans; [ | apply H1 ].
    apply Nat.le_sub_l.
  }
  specialize (H4 H); clear H.
  specialize (H4 a Hal).
  destruct H4 as (z & (H4, H5) & H6).
  exists z.
  rewrite Nat.mul_comm, H5.
  progress unfold abs.
  remember (_ <=? _) as u eqn:Hu.
  symmetry in Hu.
  destruct u. {
    apply Nat.leb_le in Hu.
    exfalso.
    apply Nat.nlt_ge in Hu.
    apply Hu; clear Hu.
    apply Nat.lt_add_lt_sub_l.
    destruct Hx as (H7, H8).
    apply (Nat.add_lt_mono_r _ _ ((l - 1) / 2)) in H8.
    eapply Nat.lt_le_trans; [ apply H8 | ].
    rewrite <- Nat.add_assoc.
    rewrite <- Nat_mul_2_l.
    apply Nat.le_succ_l.
    destruct Hl as (k, Hk).
    rewrite Hk.
    rewrite Nat.add_sub.
    rewrite (Nat.mul_comm _ k), Nat.div_mul; [ | easy ].
    rewrite Nat.mul_comm.
    now apply Nat.lt_add_pos_r.
  }
  rewrite Nat.sub_sub_distr; [ | | easy ]; cycle 1. {
    eapply Nat.le_trans. {
      apply Nat.lt_le_incl, Hx.
    }
    apply Nat.le_succ_l.
    apply Nat.Div0.div_lt_upper_bound.
    rewrite Nat_mul_2_l.
    apply (Nat.lt_le_trans _ l); [ | apply Nat.le_add_r ].
    flia Hlz.
  }
  rewrite Nat.sub_diag.
  split; [ easy | ].
  apply List.in_seq.
  split. {
    apply Nat.neq_0_lt_0; intros H; subst z.
    rewrite Nat.mul_0_r in H5.
    rewrite Nat.Div0.mod_0_l in H5.
    symmetry in H5.
    apply Nat.sub_0_le in H5.
    apply Nat.nlt_ge in H5.
    apply H5; clear H5.
    eapply Nat.lt_le_trans; [ apply Hx | ].
    apply Nat.le_succ_l.
    apply Nat.Div0.div_lt_upper_bound.
    rewrite Nat_mul_2_l.
    apply (Nat.lt_le_trans _ l); [ | apply Nat.le_add_r ].
    flia Hlz.
  }
(* bon, c'est pas bon *)
...
  exists (l - y).
  split. {
    progress unfold abs.
    rewrite Nat.mul_sub_distr_r.

Search ((_ - _) mod _).
(* chais pas *)
...
  eapply Nat.lt_le_trans; [ apply H1 | ].
  apply Nat.le_succ_l.
    apply Nat.Div0.div_lt_upper_bound.
    rewrite Nat_mul_2_l.
    destruct l; [ easy | ].
    rewrite Nat_sub_succ_1.
    apply Nat.le_add_r.
...
apply nat_bijection_Permutation. {
  intros i Hi; cbn.
  destruct (lt_dec i n) as [Hin| Hin]; [ | easy ].
  now apply Hn.
} {
  intros i j Hfij; cbn in Hfij.
  destruct (lt_dec i n) as [Hin| Hin]. {
...
Theorem permutation_map_if_lt :
  ∀ n f,
  (∀ i, i < n → f i < n)
  → (∀ i j, i < j < n → f i ≠ f j)
  → Permutation (List.seq 0 n)
    (ListDef.map (λ i, if lt_dec i n then f i else i) (List.seq 0 n)).
...
  erewrite rngl_summation_eq_compat; cycle 1. {
    intros  k Hk.
    replace k with
       ((if (k * a) mod l <=? (l - 1) / 2 then k else 0) +
        (if (k * a) mod l <=? (l - 1) / 2 then 0 else k)) at 1  by
      now destruct (_ <=? _).
    easy.
  }
  cbn - [ "/" "mod" ].
...
Check Gauss_lemma.
Theorem glop :
  ∀ a l,
  ∑ (k = 1, (l - 1) / 2), k =
  ∑ (k = 1, (l - 1) / 2), abs (k * a) l.
Proof.
intros.
specialize mul_all_different_multiples as H1.
progress unfold Utils.iter_seq.
rewrite Nat_sub_succ_1.
apply permutation_same_list_summation.
rewrite List.map_id.
progress unfold abs.
...
rewrite <- rngl_summation_list_map.
Check summation_list_permut.
...
rewrite summation_mod_idemp.
erewrite rngl_summation_eq_compat; cycle 1. {
  intros k Hk.
  now rewrite H.
}
cbn - [ nb_of_mult_gt_half "*" "/" "mod" ].
clear H.
rewrite <- summation_mod_idemp.
replace Nat.add with rngl_add by easy.
rewrite rngl_summation_add_distr.
replace Nat.mul with rngl_mul by easy.
rewrite <- rngl_mul_summation_distr_r; [ | easy ].
rewrite Nat.mul_comm.
generalize Ha; intros H.
destruct H as (m, H).
rewrite H at 2; clear H.
rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
rewrite <- Nat.mul_assoc.
rewrite <- Nat.add_assoc.
rewrite Nat_mod_add_l_mul_l.
clear m.
set (r := λ i, (i * a)%L mod l).
set (m := λ i, min (r i) (l - r i)).
rewrite Nat.add_comm.
erewrite rngl_summation_eq_compat; cycle 1. {
  intros i Hi.
  now fold (r i).
}
rewrite Nat.add_comm.
specialize (coprimes_all_different_multiples _ _ Hal) as H1.
rewrite eq_nb_of_mult_gt_half_summation.
remember (∑ (i = 1, (l - 1) / 2), i) as T.
remember (nb_of_mult_gt_half a l) as μ.
move μ before T.
assert
  (∑ (i = 1, (l - 1) / 2), r i =
     (T - ∑ (j = 1, (l - 1) / 2), m j) +
     (μ * l - ∑ (j = 1, (l - 1) / 2), m j)). {
  progress unfold r.
rewrite HeqT.
...
Compute (
    let l := 17 in
    let a := 5 in
(∑ (i = 1, (l - 1) / 2), i,
 ∑ (j = 1, (l - 1) / 2), min ((j * a)%L mod l) (l - (j * a)%L mod l))
).
(**)
  remember (∑ (i = _, _), _) as x in |-*.
  erewrite rngl_summation_eq_compat; cycle 1. {
    intros i Hi.
    progress unfold m.
    now rewrite <- abs_eq_min.
  }
  cbn - [ "/" ].
  subst x.
  progress unfold r.
rewrite HeqT.
...
    exfalso; apply Hx; clear Hx.
    apply Nat.div_le_lower_bound; [ easy | ].
    eapply Nat.le_trans; [ apply Hy | ].
    destruct (le_dec a b) as [Hab| Hab]. {
      rewrite Nat.sub_add; [ | easy ].
      rewrite Nat.sub_add in Hy; [ | easy ].
...
    apply Nat.le_add_le_sub_l.
    apply (Nat.mul_le_mono_pos_r _ _ 2) in Hx; [ | easy ].
    rewrite <- Nat_mul_2_l, Nat.mul_comm.
    eapply Nat.le_trans; [ apply Hx | ].
    rewrite Nat.mul_comm.
    eapply Nat.le_trans.
    apply Nat.Div0.mul_div_le.
    apply Nat.le_sub_l.
...
    apply Nat.lt_sub_lt_add_l in Hy.
...
assert (∑ (i = 1, (l - 1) /2), m i = ∑ (i = 1, (l - 1) / 2), i).
progress unfold m, r.
Theorem glop :
  ∀ l a,
  ∑ (i = 1, (l - 1) / 2), min ((i * a) mod l) (l - (i * a) mod l) =
  ∑ (i = 1, (l - 1) / 2), i.
Proof.
intros.
specialize @summation_list_map as H2.
specialize (H2 _ _ (λ i, min ((i * a) mod l) (l - (i * a) mod l))).
progress unfold Utils.iter_seq.
rewrite <- (H2 (λ i, i)).
clear H2.
rewrite Nat_sub_succ_1.
apply (rngl_summation_list_permut Nat.eqb_eq).
...
rewrite iter_list_cons; [ | easy | easy | easy ].
rewrite iter_list_cons; [ | easy | easy | easy ].
destruct (Nat.eq_dec a b) as [Hab| Hab]. {
  subst a.
  apply Permutation_cons_inv in Hp.
  f_equal.
  now apply (IHl1 n).
}
...
Search (List.fold_left _ _ _ = List.fold_left _ _ _).
Theorem iter_list_permut :
  ∀ {T} (d : T) (op : T → T → T) (l1 l2 : list nat) f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_comm : ∀ a b, op a b = op b a)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  Permutation l1 l2
  → iter_list l1 (λ (c : T) i, op c (f i)) d =
    iter_list l2 (λ (c : T) i, op c (f i)) d.
Proof.
intros * op_d_l op_d_r op_comm op_assoc Hp.
...
destruct n. {
  apply List.length_zero_iff_nil in H1.
  apply List.length_zero_iff_nil in H2.
  now subst l1 l2.
}
induction l1 as [| a]; intros; [ easy | ].
apply permutation_cons_l_iff in Hl.
...

apply (iter_list_permut Heqb); [ | | | | easy ].
apply rngl_add_0_l.
apply rngl_add_0_r.
apply rngl_add_comm.
apply rngl_add_assoc.
Qed.
...
specialize permutation_map_if_lt as H1.

rewrite <- summation_list_map.
... ...
rewrite <- HeqT in H.
rewrite H.
rewrite Nat.sub_diag, Nat.add_0_l.
...
  erewrite summation_eq_compat; cycle 1. {
    intros i Hi.
    remember ((i * a) mod l) as x.
    replace x with
      ((if x <=? (l - 1) / 2 then x else 0) +
       (if x <=? (l - 1) / 2 then 0 else x)); cycle 1. {
      destruct (_ <=? _); [ | easy ].
      apply Nat.add_0_r.
    }
    now subst x.
  }
  cbn - [ "/" ].
  rewrite summation_add.
rewrite <- HeqT in H.
rewrite H.
rewrite Nat.sub_diag, Nat.add_0_l.
...
  f_equal. {
    erewrite summation_eq_compat; cycle 1. {
      intros i Hi.
      progress fold (r i).
      easy.
    }
    cbn - [ "/" ].

...
  rewrite HeqT, Heqμ.
  progress unfold m.
  progress unfold r.
  erewrite (summation_eq_compat _ _ (λ _, min _ _)); cycle 1. {
    intros i Hi.
    rewrite Nat_min_if_then_else.
    rewrite Nat_leb_sub_r; cycle 1. {
      now apply Nat.lt_le_incl, Nat.mod_upper_bound.
    }
    rewrite <- Nat_mul_2_l.
    rewrite Nat_leb_neq_ltb; cycle 1. {
      apply Nat.eqb_eq in Hl.
      apply Nat_eq_mod_exists in Hl.
      destruct Hl as ((u, Hl), _).
      rewrite Hl at 2.
      intros H.
      symmetry in H.
      apply Nat.add_sub_eq_l in H.
      rewrite Nat.mul_comm, <- Nat.mul_sub_distr_r in H.
      now apply Nat.eq_mul_1 in H.
    }
    rewrite Nat_ltb_leb_pred; [ | easy ].
    rewrite Nat_leb_mul_l; [ | easy | ]; cycle 1. {
      apply Nat.eqb_eq in Hl.
      apply Nat_eq_mod_exists in Hl.
      destruct Hl as ((u, Hl), _).
      rewrite Hl, Nat.add_1_r; cbn.
      apply Nat.divide_factor_r.
    }
    rewrite <- Nat.sub_1_r.
    progress fold (abs ((i * a) mod l) l).
    easy.
  }
  cbn - [ nb_of_mult_gt_half "*" "/" "mod" ].
  rewrite eq_nb_of_mult_gt_half_summation.
...
remember ((a + l) / 2) as c eqn:Hc.
assert (H2al : Nat.divide 2 (a + l)). {
  apply Nat.eqb_eq in Ha, Hl.
  apply Nat_eq_mod_exists in Ha, Hl.
  destruct Ha as ((u, Ha), _).
  destruct Hl as ((v, Hb), _).
  subst a l.
  rewrite Nat.add_shuffle0, Nat.add_assoc.
  rewrite <- Nat.add_assoc, Nat.add_1_r.
  rewrite <- Nat.mul_add_distr_r.
  rewrite <- (Nat.mul_1_l 2) at 3.
  rewrite <- Nat.mul_add_distr_r.
  apply Nat.divide_factor_r.
}
assert (H1 : a + l = 2 * c). {
  subst c.
  rewrite <- Nat.Lcm0.divide_div_mul_exact; [ | easy ].
  now rewrite Nat.mul_comm, Nat.div_mul.
}
assert (H2 : a = 2 * c - l). {
  rewrite <- H1.
  symmetry; apply Nat.add_sub.
}
(*
specialize (Eisenstein_lemma c l) as H3.
enough (H4 : prime l).
enough (H5 : coprimes c l).
specialize (H3 H4 H5).
erewrite summation_eq_compat in H3; cycle 1. {
  intros k Hk.
  specialize (Nat.div_mod (2 * k * c) l Hlz) as H6.
  rewrite H6.
...
*)
erewrite summation_eq_compat; cycle 1. {
  intros k Hk.
  rewrite H2 at 1.
  rewrite Nat.mul_sub_distr_l.
  rewrite Nat_div_sub; [ | easy | ]; cycle 1. {
    rewrite Hc.
    rewrite <- Nat.Lcm0.divide_div_mul_exact; [ | easy ].
    rewrite (Nat.mul_comm 2), Nat.div_mul; [ | easy ].
    rewrite Nat.mul_add_distr_l.
    apply Nat.le_add_l.
  }
  now rewrite Nat.mul_comm.
}
cbn - [ nb_of_mult_gt_half "*" "/" "mod" ].
rewrite summation_sub; cycle 1. {
  intros k Hk.
  rewrite Hc.
  rewrite H1.
  rewrite (Nat.mul_comm _ c), Nat.div_mul; [ | easy ].
  rewrite <- H1.
  rewrite Nat.mul_comm.
  rewrite Nat.mul_add_distr_l.
  rewrite Nat.div_add; [ | easy ].
  apply Nat.le_add_l.
}
erewrite summation_eq_compat; cycle 1. {
  intros k Hk.
  now rewrite Nat.mul_shuffle0.
}
cbn - [ nb_of_mult_gt_half "*" "/" "mod" ].
...
symmetry.
apply Nat_add_sub_eq_l_mod; cycle 1. {
  rewrite <- Eisenstein_lemma.
...
  intros  k Hk.
  specialize (Nat.div_mod (k * a) l Hlz) as H1.
  apply (f_equal (λ a, a mod 2)) in H1.
  assert (H2 : k * a ≡ ((k * a / l) + (k * a) mod l) mod 2). {
    rewrite H1.
    rewrite <- Nat.Div0.add_mod_idemp_l; symmetry.
    rewrite <- Nat.Div0.add_mod_idemp_l; symmetry.
    f_equal.
    f_equal.
    progress unfold is_odd in Hl.
    apply Nat.eqb_eq in Hl.
    apply Nat_eq_mod_exists in Hl.
    destruct Hl as ((u, Hl), _); rewrite Hl at 1.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
    rewrite (Nat.mul_comm u), <- Nat.mul_assoc.
    now rewrite Nat_mod_add_l_mul_l.
  }
  clear H1; rename H2 into H1.
  assert
    (H2 :
       k * a ≡ ((if k * a <=? (l - 1) / 2 then 1 else l) * (k * a)) mod 2). {
    destruct (k * a <=? (l - 1) / 2); [ now rewrite Nat.mul_1_l | ].
    progress unfold is_odd in Hl.
    apply Nat.eqb_eq in Hl.
    apply Nat_eq_mod_exists in Hl.
    destruct Hl as ((u, Hl), _); rewrite Hl at 1.
    rewrite <- (Nat.Div0.mul_mod_idemp_l (_ + _)).
    rewrite Nat_mod_add_l_mul_r.
    rewrite Nat.mod_1_l; [ | apply Nat.lt_1_2 ].
    now rewrite Nat.mul_1_l.
  }
  symmetry in H1.
  rewrite Nat.add_comm in H1.
  rewrite H2 in H1 at  1.
  apply Nat_add_sub_eq_l_mod in H1; cycle 1. {
    destruct (_ <=? _). {
      rewrite Nat.mul_1_l.
      apply Nat.Div0.mod_le.
    }
    apply (Nat.le_trans _ (k * a)).
    apply Nat.Div0.mod_le.
    now apply Nat.le_mul_l.
  }
  rewrite <- H1.
  easy.
}
...
cbn - [ nb_of_mult_gt_half "/" "mod" ].
rewrite <- summation_mod_idemp.
rewrite summation_sub; cycle 1. {
  intros k Hk.
  destruct (_ <=? _). {
    rewrite Nat.mul_1_l.
    apply Nat.Div0.mod_le.
  }
  apply (Nat.le_trans _ (k * a)).
  apply Nat.Div0.mod_le.
  now apply Nat.le_mul_l.
}
symmetry.
apply Nat_add_sub_eq_l_mod. {
  apply summation_le_compat.
  intros k Hk.
  destruct (_ <=? _). {
    rewrite Nat.mul_1_l.
    apply Nat.Div0.mod_le.
  }
  apply (Nat.le_trans _ (k * a)).
  apply Nat.Div0.mod_le.
  now apply Nat.le_mul_l.
}
symmetry.
erewrite summation_eq_compat; cycle 1. {
  intros k Hk.
  rewrite (Nat.div_mod (k * a) l Hlz) at 2.
  rewrite Nat.mul_add_distr_l.
  now rewrite Nat.add_comm.
}
cbn - [ nb_of_mult_gt_half "/" "mod" ].
rewrite summation_add.
rewrite <- Nat.Div0.add_mod_idemp_r; symmetry.
rewrite <- Nat.Div0.add_mod_idemp_r.
f_equal.
f_equal.
remember (∑ (k = _, _), _) as x; subst x.
...
  remember ((k * a) mod l) as ka eqn:Hka.
  assert (H2 : ka ≡ (if ka <=? (l - 1) / 2 then ka else l - 1 - ka) mod 2). {
    remember (_ <=? _) as x eqn:Hx; symmetry in Hx.
    destruct x; [ easy | ].
    apply Nat.leb_gt in Hx.
    apply Nat_div_lt_mul in Hx; [ | easy ].
    apply Nat.lt_sub_lt_add_l in Hx.
    apply -> Nat.lt_succ_r in Hx.
    rewrite Nat_mul_2_l in Hx.
    apply Nat_eq_sub_mod_0. {
      apply Nat.le_sub_le_add_l.
      apply (Nat.le_trans _ l); [ | easy ].
      apply Nat.le_sub_l.
    }
    rewrite Nat_sub_sub_assoc; cycle 1. {
      split. {
        rewrite Hka.
        rewrite Nat.sub_1_r.
        apply Nat.lt_le_pred.
        now apply Nat.mod_upper_bound.
      }
      apply (Nat.le_trans _ l); [ | easy ].
      apply Nat.le_sub_l.
    }
    progress unfold is_odd in Hl.
    apply Nat.eqb_eq in Hl.
    apply Nat_eq_mod_exists in Hl.
    destruct Hl as ((u, Hl), _).
    rewrite Hl, Nat.add_sub.
    rewrite <- Nat_mul_2_l.
    rewrite (Nat.mul_comm 2).
    rewrite <- Nat.mul_sub_distr_r.
    apply Nat.Div0.mod_mul.
  }
  subst ka.
Search (_ - _ ≡ _ mod _).
Search (_ ≡ (_ - _) mod _).
...
    apply Nat_eq_mod_exists in Hp4, Hq4.
    destruct Hp4 as (u, Hp4).
    destruct Hq4 as (v, Hq4).
    move u before b; move v before u.
    rewrite Nat.mul_comm in Hp4, Hq4.
    rewrite Hp4 in H1 at 1.
    rewrite Hq4 in H2 at 1.
    rewrite <- Nat.add_sub_assoc in H1; [ | now apply -> Nat.succ_le_mono ].
    rewrite <- Nat.add_sub_assoc in H2; [ | now apply -> Nat.succ_le_mono ].
    rewrite Nat_sub_succ_1 in H1, H2.
    rewrite Nat.mul_comm in H1, H2.
    rewrite <- Nat_2_mul_2_eq_4 in H1, H2.
    rewrite Nat.mul_assoc in H1, H2.
    rewrite Nat.div_add_l in H1; [ | easy ].
    rewrite Nat.div_add_l in H2; [ | easy ].
    rewrite Nat.div_same in H1; [ | easy ].
    rewrite Nat.div_same in H2; [ | easy ].
    rewrite Nat.mul_comm in H1, H2.
    rewrite Nat.mod_1_l in H1; [ | flia Hpq ].
    rewrite Nat.mod_1_l in H2; [ | flia Hpq ].
    rewrite Nat.pow_add_r in H1, H2.
    rewrite Nat.pow_1_r in H1, H2.
    rewrite (Nat.mul_comm 2) in H1, H2.
    rewrite Nat.pow_mul_r in H1, H2.
    apply Nat_eq_mod_exists in H1, H2.
    destruct H1 as (x, H1).
    destruct H2 as (y, H2).
    move x before v; move y before x.
    apply (f_equal (λ x, x mod p)) in H1.
    apply (f_equal (λ x, x mod q)) in H2.
    rewrite <- Nat.Div0.mul_mod_idemp_r in H1, H2.
    rewrite <- Ha2 in H1.
    rewrite <- Hb2 in H2.
    rewrite Nat.Div0.mul_mod_idemp_r in H1, H2.
    rewrite <- Nat.pow_mul_l in H1, H2.
    rewrite Nat_mod_add_l_mul_r in H1, H2.
    rewrite Nat.mod_1_l in H1; [ | flia Hpq ].
    rewrite Nat.mod_1_l in H2; [ | flia Hpq ].
    rewrite eq_nb_of_mult_gt_half_summation in H3, H4.
    rewrite Nat_pow_summation_r in H3, H4.
...
    replace ((q - 1) / 2) with (2 * v + 1) in H3; cycle 1. {
      rewrite Hq4, <- Nat.add_sub_assoc; [ | now apply -> Nat.succ_le_mono ].
      rewrite Nat_sub_succ_1.
      rewrite <- Nat_2_mul_2_eq_4, <- Nat.mul_assoc.
      now rewrite (Nat.mul_comm _ (_ * _)), Nat.div_add_l.
    }
...
progress unfold is_quadratic_residue.
erewrite (Gauss_lemma _ p Hp); [ | | easy ]; cycle 1. {
  apply eq_primes_gcd_1; [ easy | easy | flia Hpq ].
}
erewrite (Gauss_lemma _ q Hq); [ | | easy ]; cycle 1. {
  apply eq_primes_gcd_1; [ easy | easy | flia Hpq ].
}
remember (_ mod _ =? 1) as q1 eqn:Hq1; symmetry in Hq1.
remember (_ mod _ =? 1) as p1 eqn:Hp1 in |-*; symmetry in Hp1.
move p1 after q1.
destruct q1. {
  apply Nat.eqb_eq in Hq1.
  apply Nat_eq_mod_1 in Hq1.
  destruct Hq1 as (Hq1, _).
  apply Nat.Div0.mod_divides in Hq1.
  destruct Hq1 as (c, Hq1).
  destruct p1. {
    apply Nat.eqb_eq in Hp1.
    split; [ intros _ | easy ].
    apply Nat_eq_mod_1 in Hp1.
    destruct Hp1 as (Hp1, _).
    apply Nat.Div0.mod_divides in Hp1.
    destruct Hp1 as (d, Hp1).
    move c before q; move d before c.
    remember (nb_of_mult_gt_half p q) as npq eqn:Hnpq.
    remember (nb_of_mult_gt_half q p) as nqp eqn:Hnqp.
    symmetry in Hnpq, Hnqp.
    destruct (Nat.eq_dec nqp 0) as [Hnqpz| Hnqpz]. {
      move Hnqpz at top; subst nqp.
Theorem nb_of_mult_gt_half_neq_0 :
  ∀ a b, 1 < a → nb_of_mult_gt_half a b ≠ 0.
Proof.
intros * Haz H1.
(**)
unfold nb_of_mult_gt_half in H1.
apply List.length_zero_iff_nil in H1.
specialize (List_filter_nil _ _ H1) as H2; clear H1.
cbn - [ "<?" "/" ] in H2.
remember (∀ i, _) as P; subst P.
remember ((b - 1) / 2) as h eqn:Hh.
assert (H : ∀ i, i ∈ List.seq 1 h → (i * a mod b ≤ h)). {
  intros i Hi.
  apply H2 in Hi.
  now apply Nat.ltb_ge in Hi.
}
clear H2.
Compute (
List.map (λ a,
  List.map (λ b,
let h := (b - 1) / 2 in
List.map (λ i,
(
a, b, i,
  Nat.leb
    ((i * a) mod b)
    h
)
) (List.filter (λ i, h <? ((i * a) mod b)) (List.seq 1 h))
) (List.filter (λ b, Nat.gcd a b =? 1) (List.seq 1 10))
) (List.seq 2 10)
).
... ...
      apply nb_of_mult_gt_half_neq_0 in Hnqp; [ easy | flia Hpq ].
    }
    move npq before d; move nqp before npq.
    move Hnqp before Hnpq.
    rewrite <- (Nat.pow_1_l npq) in Hq1 at 2.
    rewrite <- (Nat.pow_1_l nqp) in Hp1 at 2.
    rewrite Nat_pow_sub_pow in Hq1; cycle 1. {
      apply Nat.le_add_le_sub_l; cbn.
      flia Hpq.
    }
    rewrite <- Nat.sub_add_distr in Hq1.
    rewrite Nat.add_1_r in Hq1.
    rewrite Nat_pow_sub_pow in Hp1; cycle 1. {
      apply Nat.le_add_le_sub_l; cbn.
      flia Hpq.
    }
    rewrite <- Nat.sub_add_distr in Hp1.
    rewrite Nat.add_1_r in Hp1.
    rewrite summation_rtl in Hq1, Hp1.
    erewrite summation_eq_compat in Hq1; cycle 1. {
      intros i Hi.
      rewrite Nat.pow_1_l, Nat.mul_1_r.
      rewrite Nat.add_sub_swap; [ | easy ].
      rewrite Nat.sub_add_distr.
      rewrite Nat.sub_sub_distr; [ | easy | easy ].
      now rewrite Nat.sub_diag, Nat.add_0_l.
    }
    erewrite summation_eq_compat in Hp1; cycle 1. {
      intros i Hi.
      rewrite Nat.pow_1_l, Nat.mul_1_r.
      rewrite Nat.add_sub_swap; [ | easy ].
      rewrite Nat.sub_add_distr.
      rewrite Nat.sub_sub_distr; [ | easy | easy ].
      now rewrite Nat.sub_diag, Nat.add_0_l.
    }
    cbn in Hq1, Hp1.
    specialize Nat.gauss as H1.
    specialize (H1 (p - 2) p d).
... 1
Theorem glop :
  ∀ p q a b,
  a² ≡ q mod p
  → b² ≡ p mod q
  → p mod 4 = 3
  → q mod 4 = 3
  → False.
Proof.
intros * Ha2  Hb2 Hp4 Hq4.
...
    apply Nat_eq_mod_exists in Hp4, Hq4.
    destruct Hp4 as (u, Hu); rewrite Nat.mul_comm in Hu.
    destruct Hq4 as (v, Hv); rewrite Nat.mul_comm in Hv.
    move u before b; move v before u.
    apply Nat_eq_mod_exists in Ha2, Hb2.
    destruct Ha2 as (c, Hc).
    destruct Hb2 as (d, Hd).
    move c before b; move d before c.
    assert (c = a² / p). {
      assert (H : p ≠ 0) by now intros H; rewrite H in Hp.
      specialize (Nat.div_mod a² p H) as H1; clear H.
      rewrite Hc in H1 at 1.
      rewrite (Nat.mul_comm c) in H1.
      apply Nat.div_mod_unique in H1; [ easy | | ]. {
        apply Nat.mod_upper_bound.
        now intros H; rewrite H in Hp.
      } {
        apply Nat.mod_upper_bound.
        now intros H; rewrite H in Hp.
      }
    }
    subst c; rewrite Nat.mul_comm in Hc.
    assert (d = b² / q). {
      assert (H : q ≠ 0) by now intros H; rewrite H in Hq.
      specialize (Nat.div_mod b² q H) as H1; clear H.
      rewrite Hd in H1 at 1.
      rewrite (Nat.mul_comm d) in H1.
      apply Nat.div_mod_unique in H1; [ easy | | ]. {
        apply Nat.mod_upper_bound.
        now intros H; rewrite H in Hq.
      } {
        apply Nat.mod_upper_bound.
        now intros H; rewrite H in Hq.
      }
    }
    subst d; rewrite Nat.mul_comm in Hd.
...
intros * Hp Hq Hpq.
split; intros H1. {
  assert (H : p ≠ 2) by flia Hpq.
  specialize (odd_prime_mod_4 p Hp H) as Hp4; clear H.
  assert (H : q ≠ 2) by flia Hpq.
  specialize (odd_prime_mod_4 q Hq H) as Hq4; clear H.
  destruct Hp4 as [Hp4| Hp4]; [ now left | right ].
  destruct Hq4 as [Hq4| Hq4]; [ easy | exfalso ].
  rename H1 into Hx.
  remember (is_quadratic_residue q p) as b eqn:Hy; symmetry in Hy.
  move Hx after Hy.
  destruct b. {
    progress unfold is_quadratic_residue in Hx, Hy.
    apply Nat.eqb_eq in Hx, Hy.
    progress unfold Legendre_symbol in Hy.
    remember (p =? 2) as p2 eqn:Hp2; symmetry in Hp2.
    destruct p2; [ apply Nat.eqb_eq in Hp2; flia Hpq Hp2 | ].
    clear Hp2.
    remember (q mod p =? 0) as qpz eqn:Hqpz; symmetry in Hqpz.
    destruct qpz; [ easy | ].
    apply Nat.eqb_neq in Hqpz.
    remember (sqrt_mod q p) as mqp eqn:Hmqp; symmetry in Hmqp.
    destruct mqp as [a| ]; [ | flia Hy Hpq ].
    clear Hy; move a before q.
    apply eq_sqrt_mod_Some in Hmqp.
    destruct Hmqp as (Hap, Ha2).
...
*)

(* attempt to define it with Legendre symbols but the problem is that
   my Legendre symbol is not "1 or -1" but "1 or p-1".
Theorem quadratic_reciprocity :
  ∀ p q, prime p → prime p →
  Legendre_symbol p q * Legendre_symbol q p =
  opp_1_pow (((p -1) / 2) * ((q - 1) / 2)).
*)
