Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith(* Init.Nat*).

Require Import RingLike.Core.
Require Import RingLike.IterAdd.
Require Import RingLike.Nat_algebra.
(*
Require Import RingLike.PermutationFun.
*)

Require Import Misc Primes EulerCriterion GaussLemma.

Theorem fold_iter_seq : ∀ A b len f (d : A),
  Utils.iter_list (List.seq b len) f d =
    if b + len =? 0 then d
    else Utils.iter_seq b (b + len - 1) f d.
Proof.
intros.
progress unfold Utils.iter_seq.
f_equal; f_equal.
remember (b + len =? 0) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Nat.eqb_eq in Hx.
  now apply Nat.eq_add_0 in Hx; destruct Hx; subst b len.
}
apply Nat.eqb_neq in Hx.
destruct len. {
  rewrite Nat.add_0_r in Hx.
  destruct b; [ easy | cbn ].
  now rewrite Nat.add_sub, Nat.sub_diag.
}
rewrite Nat.sub_succ_l; [ cbn | flia ].
f_equal; f_equal; f_equal.
flia.
Qed.

Theorem Nat_2_mul_2_eq_4 : 2 * 2 = 4.
Proof. easy. Qed.

Theorem Nat_mul_add_1_distr_l : ∀ a b, a * (b + 1) = a * b + a.
Proof.
intros.
rewrite Nat.mul_add_distr_l.
now rewrite Nat.mul_1_r.
Qed.

Theorem Nat_mul_ltb_mono_pos_r :
  ∀ p n m : nat, 0 < p → (n <? m) = (n * p <? m * p).
Proof.
intros * Hp.
remember (_ * _ <? _) as b eqn:Hb; symmetry in Hb.
destruct b. {
  apply Nat.ltb_lt in Hb.
  apply Nat.ltb_lt.
  now apply Nat.mul_lt_mono_pos_r in Hb.
} {
  apply Nat.ltb_nlt in Hb.
  apply Nat.ltb_nlt.
  intros H; apply Hb; clear Hb.
  now apply Nat.mul_lt_mono_pos_r.
}
Qed.

Theorem Nat_sub_1_squ : ∀ a, a ≠ 0 → (a - 1)² ≡ 1 mod a.
Proof.
intros * Haz.
destruct (Nat.eq_dec a 1) as [Ha1| Ha1]; [ now subst a | ].
rewrite Nat_squ_sub; [ | now apply Nat.neq_0_lt_0 ].
cbn.
do 2 rewrite Nat.mul_1_r.
rewrite Nat.add_0_r.
rewrite <- Nat_mul_2_l.
rewrite Nat.add_sub_swap; cycle 1. {
  apply Nat.mul_le_mono_r.
  destruct a; [ easy | ].
  destruct a; [ easy | ].
  now do 2 apply -> Nat.succ_le_mono.
}
rewrite <- Nat.mul_sub_distr_r.
apply Nat_mod_add_l_mul_r.
Qed.

Theorem Nat_eq_mod_1 : ∀ a b, a mod b = 1 ↔ (a - 1) mod b = 0 ∧ a ≠ 0 ∧ b ≠ 1.
Proof.
intros.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  subst b; cbn.
  split; intros Ha; [ now subst a; rewrite Nat.sub_diag | ].
  destruct Ha as (Ha & Haz & _).
  apply Nat.sub_0_le in Ha.
  destruct a; [ easy | ].
  apply Nat.succ_le_mono in Ha.
  now apply Nat.le_0_r in Ha; subst a.
}
split; intros Hab. {
  split. {
    specialize (Nat.div_mod a b Hbz) as H1.
    rewrite Hab in H1.
    rewrite H1, Nat.add_sub, Nat.mul_comm.
    apply Nat.Div0.mod_mul.
  }
  split. {
    intros H; subst a.
    now rewrite Nat.Div0.mod_0_l in Hab.
  }
  now intros H; subst b.
}
destruct Hab as (Hab & Haz & Hb1).
specialize (Nat.div_mod (a - 1) b Hbz) as H1.
rewrite Hab, Nat.add_0_r in H1.
apply (f_equal S) in H1.
rewrite <- Nat.add_1_r in H1.
rewrite Nat.sub_add in H1; [ | now apply Nat.neq_0_lt_0 ].
rewrite H1, <- Nat.add_1_r.
rewrite <- Nat.Div0.add_mod_idemp_l.
rewrite Nat.mul_comm, Nat.Div0.mod_mul; cbn.
destruct b; [ easy | ].
destruct b; [ easy | ].
apply Nat.mod_1_l.
now do 2 apply -> Nat.succ_le_mono.
Qed.

Theorem Nat_sub_1_pow_mod :
  ∀ a b, 1 < a → (a - 1) ^ b mod a = (a - 1) ^ (b mod 2).
Proof.
intros * H1a.
remember (b mod 2) as b2 eqn:Hb2.
symmetry in Hb2.
destruct b2; cbn. {
  apply Nat.Div0.mod_divides in Hb2.
  destruct Hb2 as (c, Hb); subst b.
  rewrite Nat.pow_mul_r.
  rewrite <- Nat_mod_pow_mod.
  rewrite Nat_sub_1_squ; [ | now intros H; subst a ].
  rewrite Nat.mod_1_l; [ | easy ].
  rewrite Nat.pow_1_l.
  now apply Nat.mod_1_l.
}
destruct b2; cbn. {
  rewrite Nat.mul_1_r.
  destruct b; [ easy | ].
  apply Nat_eq_succ_mod_1 in Hb2.
  apply Nat.Div0.mod_divides in Hb2.
  destruct Hb2 as (c, H); subst b.
  rewrite Nat.pow_succ_r; [ | easy ].
  rewrite Nat.pow_mul_r.
  rewrite <- Nat.Div0.mul_mod_idemp_r.
  rewrite <- Nat_mod_pow_mod.
  rewrite Nat_sub_1_squ; [ | flia H1a ].
  rewrite (Nat.mod_small 1); [ | easy ].
  rewrite Nat.pow_1_l.
  rewrite Nat.mod_1_l; [ | easy ].
  rewrite Nat.mul_1_r.
  apply Nat.mod_small.
  flia H1a.
}
specialize (Nat.mod_upper_bound b 2 (Nat.neq_succ_0 _)) as H1.
rewrite Hb2 in H1.
flia H1.
Qed.

Theorem Nat_eq_mod_exists : ∀ a b c,
  a mod b = c ↔ (∃ k, a = k * b + c) ∧ (b = 0 ∨ c < b).
Proof.
intros.
split; intros Habc. {
  destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
    subst b.
    split; [ | now left ].
    cbn in Habc; subst c.
    now exists 0.
  }
  split. {
    exists (a / b).
    rewrite Nat.mul_comm, <- Habc.
    now apply Nat.div_mod.
  }
  right.
  rewrite <- Habc.
  now apply Nat.mod_upper_bound.
} {
  destruct Habc as ((k, Ha), Hb).
  subst a.
  rewrite Nat_mod_add_l_mul_r.
  destruct Hb as [Hb| Hb]; [ now subst b | ].
  now apply Nat.mod_small.
}
Qed.

Theorem Nat_le_mul_div_add :
  ∀ a b,
  b ≠ 0 → a ≤ b * ((a - 1) / b) + b.
Proof.
intros * Hbz.
destruct (Nat.eq_dec a 0) as [Haz| Haz]; [ now subst a | ].
specialize (Nat.div_mod (a - 1) b Hbz) as H1.
symmetry in H1.
apply Nat.add_sub_eq_r in H1.
rewrite <- H1.
rewrite <- Nat.add_sub_swap; [ | apply Nat.Div0.mod_le ].
rewrite <- Nat.add_sub_swap; [ | now apply Nat.neq_0_lt_0 ].
rewrite <- Nat.add_sub_assoc; [ | now apply Nat.neq_0_lt_0 ].
rewrite <- Nat.add_sub_assoc; [ apply Nat.le_add_r | ].
apply Nat.le_add_le_sub_l.
apply Nat.le_succ_l.
now apply Nat.mod_upper_bound.
Qed.

Theorem odd_prime_mod_4 : ∀ p, prime p → p ≠ 2 → p mod 4 = 1 ∨ p mod 4 = 3.
Proof.
intros * Hp Hp2.
remember (p mod 4) as p4 eqn:Hp4; symmetry in Hp4.
destruct p4. {
  apply Nat.Lcm0.mod_divide in Hp4.
  destruct Hp4 as (k, H); subst p.
  rewrite <- Nat_2_mul_2_eq_4, Nat.mul_assoc in Hp.
  apply prime_not_mul in Hp.
  destruct Hp as [Hp| ]; [ | easy ].
  now apply Nat.eq_mul_1 in Hp.
}
destruct p4; [ now left | right ].
destruct p4. {
  specialize (odd_prime p Hp Hp2) as H1.
  rewrite <- Nat_2_mul_2_eq_4 in Hp4.
  rewrite Nat.Div0.mod_mul_r in Hp4.
  rewrite H1 in Hp4.
  apply Nat.succ_inj in Hp4.
  now apply Nat.eq_mul_1 in Hp4.
}
destruct p4; [ easy | ].
specialize (Nat.mod_upper_bound p 4 (Nat.neq_succ_0 _)) as H1.
rewrite Hp4 in H1.
now do 4 apply Nat.succ_lt_mono in H1.
Qed.

Definition is_quadratic_residue a p := Legendre_symbol a p =? 1.

Theorem nb_of_mult_gt_half_0_l : ∀ n, nb_of_mult_gt_half 0 n = 0.
Proof.
intros.
progress unfold nb_of_mult_gt_half.
erewrite List.filter_ext; cycle 1. {
  intros; rewrite Nat.mul_0_r.
  rewrite Nat.Div0.mod_0_l.
  remember (_ <? 0) as x eqn:Hx; symmetry in Hx.
  destruct x; [ | easy ].
  apply Nat.ltb_lt in Hx.
  now apply Nat.nlt_0_r in Hx.
}
now rewrite List.filter_false.
Qed.

Theorem Nat_same_parity_same_opp_1_pow :
  ∀ n, n ≠ 0 → ∀ a b,
  a ≡ b mod 2
  → (n - 1) ^ a ≡ (n - 1) ^ b mod n.
Proof.
intros * Hnz * Hab.
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n.
  rewrite Nat.sub_diag.
  now do 2 rewrite Nat.mod_1_r.
}
remember (a mod 2) as a2 eqn:Ha2; symmetry in Ha2.
remember (b mod 2) as b2 eqn:Hb2; symmetry in Hb2.
move b2 before a2.
destruct a2. {
  move Hab at top; subst b2.
  apply Nat.Lcm0.mod_divide in Ha2.
  apply Nat.Lcm0.mod_divide in Hb2.
  destruct Ha2 as (u, Hu).
  destruct Hb2 as (v, Hv).
  subst a b.
  do 2 rewrite (Nat.mul_comm _ 2).
  do 2 rewrite Nat.pow_mul_r.
  do 2 rewrite <- (Nat_mod_pow_mod _²).
  rewrite Nat_sub_1_squ; [ | easy ].
  rewrite Nat.mod_1_l; [ | flia Hnz Hn1 ].
  now do 2 rewrite Nat.pow_1_l.
}
destruct a2. {
  move Hab at top; subst b2.
  specialize (Nat.div_mod a 2 (Nat.neq_succ_0 _)) as Ha.
  specialize (Nat.div_mod b 2 (Nat.neq_succ_0 _)) as Hb.
  rewrite Ha, Hb, Ha2, Hb2.
  do 2 rewrite Nat.pow_add_r.
  rewrite Nat.pow_1_r.
  do 2 rewrite Nat.pow_mul_r.
  do 2 rewrite <- (Nat.Div0.mul_mod_idemp_l (_ ^ _)).
  do 2 rewrite <- (Nat_mod_pow_mod _²).
  rewrite Nat_sub_1_squ; [ | easy ].
  rewrite Nat.mod_1_l; [ | flia Hnz Hn1 ].
  now do 2 rewrite Nat.pow_1_l.
}
specialize (Nat.mod_upper_bound a 2 (Nat.neq_succ_0 _)) as H.
flia Ha2 H.
Qed.

Theorem quadratic_reciprocity_2 :
  ∀ p, prime p → Legendre_symbol 2 p = (p - 1) ^ ((p² - 1) / 8) mod p.
Proof.
intros * Hp.
destruct (Nat.eq_dec p 2) as [Hp2| Hp2]; [ now subst p | ].
erewrite (Gauss_lemma _ p Hp); [ | | easy ]; cycle 1. {
  now apply eq_primes_gcd_1.
}
apply Nat_same_parity_same_opp_1_pow; [ now destruct p | ].
progress unfold nb_of_mult_gt_half.
erewrite List.filter_ext_in; cycle 1. {
  intros * Ha.
  rewrite Nat.mod_small; cycle 1. {
    apply List.in_seq in Ha.
    destruct Ha as (_, Ha).
    apply -> Nat.lt_succ_r in Ha.
    apply (Nat.mul_le_mono_pos_r _ _ 2) in Ha; [ | easy ].
    eapply Nat.le_lt_trans; [ apply Ha | ].
    rewrite Nat.mul_comm.
    eapply Nat.le_lt_trans; [ apply Nat.Div0.mul_div_le | ].
    apply Nat.sub_lt; [ | easy ].
    destruct p; [ easy | ].
    now apply -> Nat.succ_le_mono.
  }
  replace ((p - 1) / 2 <? a * 2) with (p - 1 <? a * 4); cycle 1. {
    remember (p - 1 <? a * 4) as a4 eqn:Ha4; symmetry in Ha4.
    remember ((p - 1) / 2 <? a * 2) as a2 eqn:Ha2; symmetry in Ha2.
    destruct a4, a2; [ easy | | | easy ]; exfalso. {
      apply Nat.ltb_lt in Ha4.
      apply Nat.ltb_nlt in Ha2.
      apply Ha2; clear Ha2.
      apply Nat.Div0.div_lt_upper_bound.
      now rewrite Nat.mul_comm, <- Nat.mul_assoc.
    } {
      apply Nat.ltb_nlt in Ha4.
      apply Nat.ltb_lt in Ha2.
      apply Ha4; clear Ha4.
      apply Nat_div_lt_mul in Ha2; [ | easy ].
      now rewrite Nat.mul_comm, <- Nat.mul_assoc in Ha2.
    }
  }
  easy.
}
destruct (Nat.eq_dec ((p - 1) mod 4) 0) as [Hp4z| Hp4z]. {
  apply Nat.Lcm0.mod_divide in Hp4z.
  destruct Hp4z as (k, Hk).
  rewrite Hk.
  erewrite List.filter_ext_in; cycle 1. {
    intros a Ha.
    replace (k * 4 <? a * 4) with (k <? a); cycle 1. {
      remember (k <? a) as ka eqn:Hka; symmetry in Hka |-*.
      destruct ka. {
        apply Nat.ltb_lt in Hka.
        apply Nat.ltb_lt.
        now apply Nat.mul_lt_mono_pos_r.
      }
      apply Nat.ltb_nlt in Hka.
      apply Nat.ltb_nlt.
      intros H; apply Hka; clear Hka.
      now apply Nat.mul_lt_mono_pos_r in H.
    }
    easy.
  }
  rewrite <- Nat_2_mul_2_eq_4 at 1.
  rewrite Nat.mul_assoc, Nat.div_mul; [ | easy ].
  rewrite Nat.mul_comm, Nat_mul_2_l.
  (* k = (p - 1) / 4 *)
  rewrite List.seq_app.
  rewrite List.filter_app.
  rewrite List_filter_all_false; cycle 1. {
    intros a Ha.
    apply List.in_seq in Ha.
    apply Nat.ltb_ge.
    now apply Nat.lt_succ_r.
  }
  rewrite List.app_nil_l.
  rewrite List_filter_all_true; cycle 1. {
    intros a Ha.
    apply List.in_seq in Ha.
    now apply Nat.ltb_lt.
  }
  rewrite List.length_seq.
  apply Nat.add_sub_eq_nz in Hk; cycle 1. {
    destruct p; [ easy | ].
    destruct p; [ easy | ].
    rewrite Nat.sub_succ, Nat.sub_0_r in Hk.
    congruence.
  }
  rewrite Nat.add_comm in Hk.
  subst p.
  rewrite Nat_squ_add.
  cbn - [ "/" "mod" ].
  do 2 rewrite Nat.mul_1_r.
  rewrite Nat.add_0_r.
  rewrite Nat.add_shuffle0, Nat.add_sub.
  rewrite <- Nat_mul_2_l.
  rewrite <- Nat.mul_add_distr_r.
  rewrite Nat.mul_assoc.
  replace 8 with (4 * 2) by easy.
  rewrite <- Nat.Div0.div_div.
  rewrite Nat.div_mul; [ | easy ].
  rewrite Nat.mul_comm.
  rewrite <- (Nat.mul_1_l 2) at 3.
  rewrite <- Nat_2_mul_2_eq_4.
  rewrite Nat.mul_assoc, <- Nat.mul_add_distr_r.
  rewrite Nat.mul_assoc.
  rewrite Nat.div_mul; [ | easy ].
  rewrite <- Nat.Div0.mul_mod_idemp_r.
  rewrite <- (Nat.Div0.add_mod_idemp_l (k * 2)).
  rewrite Nat.Div0.mod_mul.
  rewrite Nat.add_0_l.
  rewrite Nat.mod_1_l; [ | flia ].
  now rewrite Nat.mul_1_r.
}
destruct (Nat.eq_dec ((p - 1) mod 4) 1) as [Hp41| Hp41]. {
  exfalso; clear - Hp Hp2 Hp41.
  specialize (Nat.div_mod (p - 1) 4 (Nat.neq_succ_0 _)) as Ha.
  rewrite Hp41 in Ha.
  rewrite Nat.add_comm in Ha.
  apply Nat.add_sub_eq_nz in Ha; [ | easy ].
  rewrite Nat.add_assoc in Ha.
  rewrite Nat.add_comm in Ha.
  cbn - [ "/" "*" ] in Ha.
  rewrite <- Nat_2_mul_2_eq_4 in Ha at 1.
  rewrite <- Nat.mul_assoc in Ha.
  rewrite <- Nat_mul_add_1_distr_l in Ha.
  specialize (odd_prime _ Hp Hp2) as H1.
  rewrite <- Ha in H1.
  now rewrite Nat.mul_comm, Nat.Div0.mod_mul in H1.
}
destruct (Nat.eq_dec ((p - 1) mod 4) 2) as [Hp42| Hp42]. {
  specialize (Nat.div_mod (p - 1) 4 (Nat.neq_succ_0 _)) as H1.
  rewrite Hp42 in H1.
  remember ((p - 1) / 4) as k eqn:Hk.
  generalize H1; intros H2.
  apply Nat.add_sub_eq_nz in H1; [ | flia ].
  symmetry in H1.
  rewrite Nat.add_comm, <- Nat.add_assoc in H1.
  apply (f_equal (λ a, a + 1)) in H1.
  rewrite <- Nat.add_assoc in H1.
  cbn - [ "*" ] in H1.
  rewrite <- Nat_2_mul_2_eq_4 in H2.
  rewrite <- Nat.mul_assoc in H2.
  rewrite <- Nat_mul_add_1_distr_l in H1, H2.
  rewrite Nat_squ_sub_1.
  rewrite H1, H2.
  rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
  rewrite (Nat.mul_comm 4), Nat.mul_shuffle0.
  rewrite Nat.mul_assoc.
  rewrite <- Nat.mul_assoc.
  rewrite Nat.div_mul; [ | easy ].
  erewrite List.filter_ext_in; cycle 1. {
    intros a Ha.
    rewrite <- Nat_2_mul_2_eq_4.
    rewrite Nat.mul_assoc.
    now rewrite <- Nat_mul_ltb_mono_pos_r.
  }
  (* k = (p + 1) / 4 - 1 *)
  replace (2 * k + 1) with (k + (k + 1)) at 1 by flia.
  rewrite List.seq_app.
  rewrite List.filter_app.
  rewrite List_filter_all_false; cycle 1. {
    intros a Ha.
    apply List.in_seq in Ha.
    apply Nat.ltb_ge.
    flia Ha.
  }
  rewrite List.app_nil_l.
  rewrite List_filter_all_true; cycle 1. {
    intros a Ha.
    apply List.in_seq in Ha.
    apply Nat.ltb_lt.
    flia Ha.
  }
  rewrite List.length_seq.
  rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
  rewrite (Nat.mul_comm 2), Nat.mul_assoc.
  now rewrite Nat_mod_add_l_mul_r.
}
destruct (Nat.eq_dec ((p - 1) mod 4) 3) as [Hp43| Hp43]. {
  exfalso; clear - Hp Hp2 Hp43.
  specialize (Nat.div_mod (p - 1) 4 (Nat.neq_succ_0 _)) as Ha.
  rewrite Hp43 in Ha.
  rewrite Nat.add_comm in Ha.
  apply Nat.add_sub_eq_nz in Ha; [ | easy ].
  rewrite Nat.add_assoc in Ha.
  rewrite Nat.add_comm in Ha.
  cbn - [ "/" "*" ] in Ha.
  rewrite <- Nat_mul_add_1_distr_l in Ha.
  specialize (odd_prime _ Hp Hp2) as H1.
  rewrite <- Ha in H1.
  rewrite <- Nat_2_mul_2_eq_4 in H1.
  rewrite <- Nat.mul_assoc in H1.
  now rewrite Nat.mul_comm, Nat.Div0.mod_mul in H1.
}
specialize (Nat.mod_upper_bound (p - 1) 4 (Nat.neq_succ_0 _)) as H1.
destruct ((p - 1) mod 4) as [| n]; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
do 4 apply Nat.succ_lt_mono in H1.
easy.
Qed.

Theorem Nat_sub_1_pow_mod_is_even :
  ∀ a n, 2 < n → (n - 1) ^ a mod n = 1 ↔ Nat.Even a.
Proof.
intros * H2n.
split; intros Ha. {
  apply Nat_eq_mod_1 in Ha.
  destruct Ha as (H1 & H2 & H3).
  apply Nat.Div0.mod_divides in H1.
  destruct H1 as (c, H1).
  destruct (Nat.Even_Odd_dec a) as [H4| H4]; [ easy | exfalso ].
  destruct H4 as (m, Hm).
  generalize H1; intros H4.
  apply (f_equal (λ x, x mod n)) in H4.
  rewrite Nat.mul_comm, Nat.Div0.mod_mul in H4.
  subst a.
  rewrite Nat.pow_add_r in H4.
  rewrite Nat.pow_1_r in H4.
  rewrite Nat.pow_mul_r in H4.
  apply Nat_eq_mod_sub_0 in H4; cycle 1. {
    apply Nat.neq_0_lt_0.
    intros H5.
    apply Nat.eq_mul_0 in H5.
    destruct H5 as [H5| H5]. {
      apply Nat.pow_nonzero in H5; [ easy | ].
      intros H6.
      progress unfold "²" in H6.
      rewrite Nat.mul_1_r in H6.
      apply -> Nat.eq_square_0 in H6.
      apply Nat.sub_0_le in H6.
      flia H2n H6.
    }
    apply Nat.sub_0_le in H5.
    flia H2n H5.
  }
  rewrite <- Nat.Div0.mul_mod_idemp_l in H4.
  rewrite <- Nat_mod_pow_mod in H4.
  rewrite Nat_sub_1_squ in H4; [ | now intros H; subst n ].
  rewrite Nat.mod_1_l in H4; [ | flia H2n ].
  rewrite Nat.pow_1_l in H4.
  rewrite Nat.mod_1_l in H4; [ | flia H2n ].
  rewrite Nat.mul_1_l in H4.
  apply Nat_eq_mod_1 in H4.
  destruct H4 as (H4, _).
  rewrite <- Nat.sub_add_distr in H4.
  rewrite Nat.add_1_r in H4.
  apply Nat.Div0.mod_divides in H4.
  destruct H4 as (d, H4).
  clear H2 H3.
  assert (n - 2 < n * d). {
    destruct d. {
      rewrite Nat.mul_0_r in H4.
      flia H2n H4.
    }
    apply (Nat.lt_le_trans _ n). {
      apply Nat.sub_lt; [ | easy ].
      now apply Nat.lt_le_incl.
    }
    rewrite Nat.mul_succ_r.
    apply Nat.le_add_l.
  }
  rewrite H4 in H.
  now apply Nat.lt_irrefl in H.
}
destruct Ha as (c, H); subst a.
rewrite Nat.pow_mul_r.
induction c. {
  cbn.
  apply Nat.mod_1_l.
  flia H2n.
}
rewrite Nat.pow_succ_r; [ | easy ].
rewrite <- Nat.Div0.mul_mod_idemp_r.
rewrite IHc, Nat.mul_1_r.
apply Nat_sub_1_pow_mod.
flia H2n.
Qed.

Theorem Nat_sub_1_pow_mod_eq_even :
  ∀ a n, 2 < n → (n - 1) ^ a mod n =? 1 = Nat.even a.
Proof.
intros * H2n.
remember (Nat.even a) as ea eqn:Hea.
symmetry in Hea.
destruct ea. {
  apply Nat.even_spec in Hea.
  apply Nat.eqb_eq.
  now apply Nat_sub_1_pow_mod_is_even.
} {
  apply Bool.not_true_iff_false in Hea.
  apply Bool.not_true_iff_false.
  intros H1; apply Hea; clear Hea.
  apply Nat.even_spec.
  apply Nat.eqb_eq in H1.
  now apply Nat_sub_1_pow_mod_is_even in H1.
}
Qed.

Theorem rngl_of_nat_nat : ∀ n, rngl_of_nat n = n.
Proof.
intros.
induction n; [ easy | ].
rewrite rngl_of_nat_succ.
now rewrite IHn.
Qed.

Theorem summation_b2n_mul_lt :
  ∀ N m p,
  0 < p
  → N / p ≤ m
  → ∑ (y = 1, m), Nat.b2n (p * y <? N)%nat = (N - 1) / p.
Proof.
intros * Hzp Hpm.
destruct (Nat.eq_dec N 0) as [Hnz| Hnz]. {
  subst N; cbn.
  rewrite Nat.Div0.div_0_l.
  replace 0 with rngl_zero by easy.
  now apply all_0_rngl_summation_0.
}
rewrite (rngl_summation_split ((N - 1) / p)); cycle 1. {
  split; apply -> Nat.succ_le_mono; [ easy | ].
  apply (Nat.le_trans _ (N / p)); [ | easy ].
  apply Nat.Div0.div_le_mono.
  apply Nat.le_sub_l.
}
erewrite rngl_summation_eq_compat; cycle 1. {
  intros y Hy.
  progress unfold Nat.b2n.
  remember (p * y <? N) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ easy | exfalso ].
  apply Bool.not_true_iff_false in Hb.
  apply Hb; clear Hb.
  apply Nat.leb_le.
  destruct Hy as (H1y, Hy).
  apply (Nat.mul_le_mono_r _ _ p) in Hy.
  rewrite Nat.mul_comm in Hy.
  apply Nat.succ_le_mono in Hy.
  eapply Nat.le_trans; [ apply Hy | ].
  apply Nat.le_succ_l.
  apply (Nat.le_lt_trans _ (N - 1)); cycle 1. {
    apply Nat.sub_lt; [ | easy ].
    now apply Nat.neq_0_lt_0.
  }
  rewrite Nat.mul_comm.
  apply Nat.Div0.mul_div_le.
}
cbn - [ "<?" ].
rewrite rngl_summation_const; [ | easy ].
rewrite Nat.mul_1_r.
rewrite rngl_of_nat_nat.
rewrite Nat_sub_succ_1.
rewrite all_0_rngl_summation_0; [ apply Nat.add_0_r | ].
intros y Hy.
progress unfold Nat.b2n.
remember (p * y <? N) as b eqn:Hb.
symmetry in Hb.
destruct b; [ exfalso | easy ].
apply Nat.ltb_lt in Hb.
destruct Hy as (Hy, Hym).
apply Nat.nle_gt in Hb.
apply Hb; clear Hb.
apply (Nat.mul_le_mono_l _ _ p) in Hy.
eapply Nat.le_trans; [ | apply Hy ].
rewrite Nat.add_1_r.
rewrite Nat.mul_succ_r.
apply Nat_le_mul_div_add.
now apply Nat.neq_0_lt_0.
Qed.
