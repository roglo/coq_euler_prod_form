Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith Init.Nat.

Require Import RingLike.Core.
Require Import RingLike.IterAdd.
Require Import RingLike.Nat_algebra.
Require Import RingLike.PermutationFun.

Require Import Misc Primes EulerCriterion GaussLemma.

Theorem List_eq_length_filter_summation :
  ∀ l f,
  List.length (List.filter f l) =
  ∑ (i = 1, List.length l), Nat.b2n (f (List.nth (i - 1) l 0)).
Proof.
intros.
induction l as [| a]; [ easy | ].
cbn - [ List.nth rngl_zero rngl_add ].
rewrite rngl_summation_split_first; [ | now apply -> Nat.succ_le_mono ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat; cycle 1. {
  intros k Hk.
  rewrite Nat.sub_succ_l; [ | easy ].
  now cbn.
}
remember (f a) as fa eqn:Hfa; symmetry in Hfa.
now destruct fa; cbn; rewrite Hfa, IHl.
Qed.

Theorem nat_ltb_rngl_ltb : ∀ a b, (a <? b) = (a <? b)%L.
Proof.
intros.
remember (a <? b)%L as x eqn:Hx.
symmetry in Hx.
destruct x. {
  apply rngl_ltb_lt in Hx; [ | easy ].
  apply Nat.ltb_lt.
  progress unfold rngl_lt in Hx.
  cbn in Hx.
  destruct Hx as (H1, H2).
  apply Nat.leb_le in H1.
  now apply Nat_le_neq_lt.
}
apply rngl_ltb_ge_iff in Hx; [ | easy ].
apply Nat.ltb_ge.
cbn in Hx.
now apply Nat.leb_le.
Qed.

Theorem eq_nb_of_mult_gt_half_summation :
  ∀ a p,
  nb_of_mult_gt_half a p =
    ∑ (i = 1, (p - 1) / 2), Nat.b2n ((p - 1) / 2 <? (i * a) mod p).
Proof.
intros.
progress unfold nb_of_mult_gt_half.
remember ((p - 1) / 2) as h eqn:Hh.
rewrite List_eq_length_filter_summation.
rewrite List.length_seq.
apply rngl_summation_eq_compat.
intros k Hk.
rewrite List.seq_nth; cycle 1. {
  progress unfold "<".
  rewrite <- Nat.sub_succ_l; [ | easy ].
  now rewrite Nat_sub_succ_1.
}
rewrite Hh.
rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
replace Nat.mul with rngl_mul by easy.
progress f_equal.
now rewrite nat_ltb_rngl_ltb.
Qed.

Theorem rngl_le_Nat_le : ∀ a b, (a ≤ b)%L ↔ (a ≤ b).
Proof.
intros.
apply Nat.leb_le.
Qed.

Theorem summation_list_map :
  ∀ {A B} (f : A → B) (g : B → _) l,
  ∑ (j ∈ List.map f l), g j = ∑ (i ∈ l), g (f i).
Proof.
intros.
unfold Utils.iter_list.
now rewrite List_fold_left_map.
Qed.

Theorem summation_list_permut :
  ∀ (la lb : list nat) f,
  permutation Nat.eqb la lb
  → ∑ (i ∈ la), f i = ∑ (i ∈ lb), f i.
Proof.
intros * Hp.
specialize @rngl_summation_list_permut as H1.
specialize (H1 nat _ _ nat Nat.eqb).
apply H1; [ | easy ].
progress unfold Misc.equality.
apply Nat.eqb_eq.
Qed.

Theorem permutation_same_list_summation :
  ∀ {A} (la : list A) f g,
  permutation eqb (List.map f la) (List.map g la)
  → ∑ (i ∈ la), f i = ∑ (i ∈ la), g i.
Proof.
intros * Hp.
rewrite <- (summation_list_map f (λ i, i)); symmetry.
rewrite <- (summation_list_map g (λ i, i)); symmetry.
now apply summation_list_permut.
Qed.

Theorem lt_mul_all_different_multiples : ∀ a p,
  coprimes a p
  → ∀ i j, i < j < p → i * a mod p ≠ j * a mod p.
Proof.
intros * Hap * Hijp.
rewrite <- Nat.Div0.mul_mod_idemp_r; symmetry.
rewrite <- Nat.Div0.mul_mod_idemp_r; symmetry.
intros Haa; symmetry in Haa.
apply Nat_mul_mod_cancel_r in Haa; cycle 1. {
  now rewrite Nat.Lcm0.gcd_mod, Nat.gcd_comm.
}
rewrite Nat.mod_small in Haa; [ | easy ].
rewrite Nat.mod_small in Haa; [ | flia Hijp ].
subst j.
destruct Hijp as (H, _).
now apply Nat.lt_irrefl in H.
Qed.

Theorem mul_all_different_multiples : ∀ a p,
  coprimes a p
  → ∀ i j, i ≠ j → i < p → j < p → i * a mod p ≠ j * a mod p.
Proof.
intros * Hap * Hij Hi Hj.
destruct (lt_dec i j) as [H1| H1]. {
  now apply lt_mul_all_different_multiples.
} {
  apply Nat.nlt_ge in H1.
  symmetry.
  apply lt_mul_all_different_multiples; [ easy | ].
  split; [ | easy ].
  now apply Nat_le_neq_lt.
}
Qed.

Theorem coprimes_mul_mod :
  ∀ a l x y,
  coprimes a l
  → 1 ≤ x < 1 + (l - 1) / 2
  → 1 ≤ y < 1 + (l - 1) / 2
  → (x * a) mod l = l - (y * a) mod l
  → x = y.
Proof.
intros * Hal Hx Hy Hxy.
symmetry in Hxy.
apply Nat.add_sub_eq_nz in Hxy; cycle 1. {
  intros H1.
  apply Nat.Lcm0.mod_divide in H1.
  rewrite Nat.mul_comm in H1.
  apply Nat.gauss in H1; [ | now rewrite Nat.gcd_comm ].
  destruct H1 as (m, Hm).
  subst x.
  destruct (Nat.eq_dec m 0) as [Hmz| Hmz]; [ now subst m | ].
  destruct Hx as (_, Hx).
  apply -> Nat.lt_succ_r in Hx.
  apply Nat.nlt_ge in Hx.
  apply Hx; clear Hx.
  apply Nat.Div0.div_lt_upper_bound.
  destruct l; [ cbn in Hy; flia Hy | ].
  rewrite Nat_sub_succ_1.
  rewrite Nat_mul_2_l.
  rewrite Nat.mul_comm; cbn.
  destruct m; [ easy | flia ].
}
apply (f_equal (λ x, x mod l)) in Hxy.
rewrite Nat.Div0.mod_same in Hxy.
rewrite Nat.Div0.add_mod_idemp_l in Hxy.
rewrite Nat.Div0.add_mod_idemp_r in Hxy.
rewrite <- Nat.mul_add_distr_r in Hxy.
apply Nat.Lcm0.mod_divide in Hxy.
rewrite Nat.mul_comm in Hxy.
apply Nat.gauss in Hxy; [ | now rewrite Nat.gcd_comm ].
destruct Hxy as (m, Hm).
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
  subst m; cbn in Hm.
  apply Nat.eq_add_0 in Hm.
  now destruct Hm; subst x y.
}
destruct Hx as (_, Hx).
destruct Hy as (_, Hy).
apply -> Nat.lt_succ_r in Hx.
apply Nat.nlt_ge in Hx.
destruct (Nat.eq_dec x y) as [Hxey| Hxey]; [ easy | ].
exfalso; apply Hx; clear Hx.
apply Nat.add_sub_eq_l in Hm.
subst x.
apply Nat.lt_add_lt_sub_r.
apply Nat.lt_add_lt_sub_l.
eapply Nat.lt_le_trans; [ apply Hy | ].
apply Nat.le_succ_l.
apply Nat.lt_add_lt_sub_r.
rewrite <- Nat_mul_2_l.
eapply Nat.le_lt_trans.
apply Nat.Div0.mul_div_le.
destruct m; [ easy | cbn ].
destruct l. {
  cbn in Hy.
  apply Nat.lt_1_r in Hy; subst y.
  cbn in Hxey.
  now rewrite Nat.mul_0_r in Hxey.
}
rewrite Nat_sub_succ_1; cbn.
apply Nat.lt_succ_r.
apply Nat.le_add_r.
Qed.

Theorem NoDup_map_mul_mod_seq :
  ∀ a l,
  coprimes a l
  → List.NoDup
      (ListDef.map (λ i : nat, abs ((i * a) mod l) l)
         (ListDef.seq 1 ((l - 1) / 2))).
Proof.
intros * Hal.
apply FinFun.Injective_map_NoDup_in; [ | apply List.seq_NoDup ].
intros * Hx Hy Hxy.
destruct (Nat.eq_dec l 0) as [Hlz| Hlz]; [ now subst l | ].
apply List.in_seq in Hx.
apply List.in_seq in Hy.
progress unfold abs in Hxy.
remember (_ <=? _) as u eqn:Hu in Hxy.
remember (_ <=? _) as v eqn:Hv in Hxy.
symmetry in Hu, Hv.
destruct (Nat.eq_dec x y) as [Hxey| Hxey]; [ easy | ].
destruct u, v. {
  apply mul_all_different_multiples in Hxy; [ easy | easy | easy | | ]. {
    eapply Nat.lt_le_trans; [ apply Hx | ].
    apply Nat.le_succ_l.
    apply Nat.Div0.div_lt_upper_bound.
    rewrite Nat_mul_2_l.
    destruct l; [ easy | ].
    rewrite Nat_sub_succ_1.
    apply Nat.le_add_r.
  } {
    eapply Nat.lt_le_trans; [ apply Hy | ].
    apply Nat.le_succ_l.
    apply Nat.Div0.div_lt_upper_bound.
    rewrite Nat_mul_2_l.
    destruct l; [ easy | ].
    rewrite Nat_sub_succ_1.
    apply Nat.le_add_r.
  }
} {
  now apply (coprimes_mul_mod a l).
} {
  apply (coprimes_mul_mod a l); [ easy | easy | easy | ].
  rewrite <- Hxy.
  rewrite Nat.sub_sub_distr; [ | | easy ].
  now rewrite Nat.sub_diag.
  now apply Nat.lt_le_incl, Nat.mod_upper_bound.
} {
  apply Nat.leb_gt in Hu.
  apply Nat.leb_gt in Hv.
  apply Nat.add_sub_eq_nz in Hxy; cycle 1. {
    intros H.
    apply Nat.sub_0_le in H.
    apply Nat.nlt_ge in H.
    now apply H, Nat.mod_upper_bound.
  }
  rewrite Nat.add_sub_assoc in Hxy; cycle 1. {
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  apply Nat.add_sub_eq_nz in Hxy; [ | easy ].
  apply Nat.add_cancel_r in Hxy.
  apply Nat_mul_mod_cancel_r in Hxy; [ | easy ].
  rewrite Nat.mod_small in Hxy; cycle 1. {
    eapply Nat.lt_le_trans; [ apply Hy | ].
    apply Nat.le_succ_l.
    apply Nat.Div0.div_lt_upper_bound.
    rewrite Nat_mul_2_l.
    destruct l; [ easy | ].
    rewrite Nat_sub_succ_1.
    apply Nat.le_add_r.
  }
  rewrite Nat.mod_small in Hxy; cycle 1. {
    eapply Nat.lt_le_trans; [ apply Hx | ].
    apply Nat.le_succ_l.
    apply Nat.Div0.div_lt_upper_bound.
    rewrite Nat_mul_2_l.
    destruct l; [ easy | ].
    rewrite Nat_sub_succ_1.
    apply Nat.le_add_r.
  }
  easy.
}
Qed.

Theorem incl_seq_map_mul :
  ∀ a l x,
  coprimes a l
  → x ∈ List.seq 1 ((l - 1) / 2)
  → x ∈ List.map (λ i, abs ((i * a) mod l) l) (List.seq 1 ((l - 1) / 2)).
Proof.
intros * Hal Hx.
destruct (Nat.eq_dec l 0) as [Hlz| Hlz]; [ now subst l | ].
apply List.in_seq in Hx.
apply List.in_map_iff.
assert (Hxl : x < l). {
  eapply Nat.lt_le_trans; [ apply Hx | ].
  apply Nat.le_succ_l.
  apply Nat.Div0.div_lt_upper_bound.
  rewrite Nat_mul_2_l.
  destruct l; [ easy | ].
  rewrite Nat_sub_succ_1.
  apply Nat.le_add_r.
}
specialize congruence_inverse_has_unique_solution as H1.
specialize (H1 l x).
assert (H : 0 < x < l) by easy.
specialize (H1 H); clear H.
specialize (H1 a Hal).
destruct H1 as (y & (H1, H2) & H3).
destruct (le_dec (y mod l) ((l - 1) / 2)) as [Hyl| Hyl]. {
  exists (y mod l).
  rewrite Nat.Div0.mul_mod_idemp_l.
  rewrite Nat.mul_comm, H2.
  split. {
    progress unfold abs.
    destruct Hx as (_, H4).
    apply -> Nat.lt_succ_r in H4.
    apply Nat.leb_le in H4.
    now rewrite H4.
  }
  apply List.in_seq.
  split. {
    apply Nat.neq_0_lt_0.
    intros H.
    apply Nat.Lcm0.mod_divide in H.
    destruct H as (m, Hm); subst y.
    destruct m; [ | flia H1 ].
    rewrite Nat.mul_0_r in H2.
    rewrite Nat.Div0.mod_0_l in H2; subst x.
    flia Hx.
  }
  now apply Nat.lt_succ_r.
}
apply Nat.nle_gt in Hyl.
specialize congruence_inverse_has_unique_solution as H4.
specialize (H4 l (l - x)).
assert (H : 0 < l - x < l). {
  split. {
    apply (Nat.add_lt_mono_r _ _ x).
    rewrite Nat.sub_add; [ easy | now apply Nat.lt_le_incl ].
  }
  apply Nat.sub_lt; [ | easy ].
  now apply Nat.lt_le_incl.
}
specialize (H4 H a Hal); clear H.
destruct H4 as (z & (H4, H5) & H6).
destruct (le_dec (z mod l) ((l - 1) / 2)) as [Hzl| Hzl]. {
  exists (z mod l).
  rewrite Nat.Div0.mul_mod_idemp_l.
  rewrite Nat.mul_comm, H5.
  split. {
    progress unfold abs.
    remember (_ <=? _) as u eqn:Hu.
    symmetry in Hu.
    destruct u; cycle 1. {
      rewrite Nat.sub_sub_distr; [ | now apply Nat.lt_le_incl | easy ].
      now rewrite Nat.sub_diag.
    }
    apply Nat.leb_le in Hu.
    apply Nat.le_sub_le_add_r in Hu.
    apply Nat.le_sub_le_add_l in Hu.
    destruct (Nat.Even_Odd_dec l) as [Hl| Hl]. {
      destruct Hl as (m, Hl).
      subst l.
      destruct m; [ easy | ].
      rewrite Nat.mul_succ_r in Hu at 2.
      rewrite <- Nat.add_sub_assoc in Hu; [ | now apply -> Nat.succ_le_mono ].
      rewrite Nat_sub_succ_1 in Hu.
      rewrite (Nat.mul_comm _ m), Nat.div_add_l in Hu; [ | easy ].
      rewrite Nat.div_small in Hu; [ | easy ].
      rewrite Nat.add_0_r in Hu.
      rewrite Nat.mul_succ_r in Hu.
      rewrite Nat.add_sub_swap in Hu; [ | flia ].
      rewrite Nat_mul_2_l, Nat.add_sub in Hu.
      rewrite Nat.mul_succ_r in Hx.
      rewrite <- Nat.add_sub_assoc in Hx; [ | now apply -> Nat.succ_le_mono ].
      rewrite Nat_sub_succ_1 in Hx.
      rewrite (Nat.mul_comm _ m), Nat.div_add_l in Hx; [ | easy ].
      rewrite Nat.div_small in Hx; [ | easy ].
      rewrite Nat.add_0_r in Hx.
      flia Hx Hu.
    }
    destruct Hl as (m, Hl).
    subst l.
    rewrite Nat.add_sub in Hx, Hu.
    rewrite Nat.mul_comm, Nat.div_mul in Hx; [ | easy ].
    rewrite Nat.mul_comm, Nat.div_mul in Hu; [ | easy ].
    rewrite Nat.add_sub_swap in Hu; [ | flia ].
    rewrite Nat.mul_comm in Hu.
    rewrite Nat_mul_2_l, Nat.add_sub in Hu.
    flia Hx Hu.
  }
  apply List.in_seq.
  split. {
    apply Nat.neq_0_lt_0.
    intros H7.
    apply Nat.Lcm0.mod_divide in H7.
    destruct H7 as (m, Hm).
    subst z.
    destruct m; [ | flia  H4 ].
    rewrite Nat.mul_0_r in H5.
    rewrite Nat.Div0.mod_0_l in H5.
    symmetry in H5.
    apply Nat.sub_0_le in H5.
    now apply Nat.nlt_ge in H5.
  }
  now apply Nat.lt_succ_r.
}
apply Nat.nle_gt in Hzl.
progress unfold abs.
assert (H7 : (a * y) mod l + (a * z) mod l = l) by flia H2 H5 Hxl.
apply (f_equal (λ u, u mod l)) in H7.
rewrite Nat.Div0.mod_same in H7.
rewrite Nat.Div0.add_mod_idemp_l in H7.
rewrite Nat.Div0.add_mod_idemp_r in H7.
rewrite <- Nat.mul_add_distr_l in H7.
apply Nat.Lcm0.mod_divide in H7.
apply Nat.gauss in H7; [ | now rewrite Nat.gcd_comm ].
destruct H7 as (m, Hm).
apply (f_equal (λ u, u mod l)) in Hm.
rewrite Nat.Div0.mod_mul in Hm.
rewrite <- Nat.Div0.add_mod_idemp_l in Hm.
rewrite <- Nat.Div0.add_mod_idemp_r in Hm.
apply Nat.Lcm0.mod_divide in Hm.
clear m.
destruct Hm as (m, Hm).
destruct m. {
  apply Nat.eq_add_0 in Hm.
  destruct Hm as (Hm, _).
  now rewrite Hm in Hyl.
}
destruct m; cycle 1. {
  specialize (Nat.mod_upper_bound y l Hlz) as H7.
  specialize (Nat.mod_upper_bound z l Hlz) as H8.
  flia Hm H7 H8.
}
rewrite Nat.mul_1_l in Hm.
destruct (Nat.Even_Odd_dec l) as [Hl| Hl]; cycle 1. {
  destruct Hl as (m, Hl).
  subst l.
  exfalso; clear - Hyl Hzl Hm.
  rewrite Nat.add_sub in Hyl, Hzl.
  rewrite Nat.mul_comm, Nat.div_mul in Hyl; [ | easy ].
  rewrite Nat.mul_comm, Nat.div_mul in Hzl; [ | easy ].
  rewrite Nat.mul_comm in Hm.
  flia Hyl Hzl Hm.
} {
  destruct Hl as (m, Hl).
  subst l.
  assert ((2 * m - 1) / 2 = m - 1). {
    destruct m; [ easy | ].
    cbn - [ "/" ].
    rewrite Nat.add_0_r, Nat.sub_0_r.
    rewrite Nat.add_succ_r.
    rewrite <- Nat.add_1_r.
    rewrite <- Nat_mul_2_l.
    rewrite Nat.mul_comm.
    rewrite Nat.div_add_l; [ | easy ].
    now rewrite Nat.add_0_r, Nat.sub_0_r.
  }
  rewrite H in Hx, Hyl, Hzl |-*.
  clear H.
  rewrite Nat.add_comm, Nat.sub_add in Hx; cycle 1. {
    apply Nat.neq_0_lt_0.
    now intros H; subst m.
  }
  move Hyl at bottom.
  move Hzl at bottom.
  move Hm at bottom.
  apply Nat.lt_sub_lt_add_l in Hyl, Hzl.
  apply -> Nat.lt_succ_r in Hyl.
  apply -> Nat.lt_succ_r in Hzl.
  rewrite Nat_mul_2_l in Hm at 3.
  assert (Hy : y mod (2 * m) = m) by flia Hyl Hzl Hm.
  assert (Hz : z mod (2 * m) = m) by flia Hyl Hzl Hm.
  clear Hyl Hzl Hm.
  rewrite Nat.mod_small in Hy; [ | easy ].
  rewrite Nat.mod_small in Hz; [ | easy ].
  subst y z.
  rewrite H2 in H5.
  flia Hx H5.
}
Qed.

Theorem incl_map_mul_seq :
  ∀ a l x,
  coprimes a l
  → x ∈ ListDef.map (λ i : nat, abs ((i * a) mod l) l)
        (ListDef.seq 1 ((l - 1) / 2))
  → x ∈ ListDef.seq 1 ((l - 1) / 2).
Proof.
intros * Hal Hx.
destruct (Nat.eq_dec l 0) as [Hlz| Hlz]; [ now subst l | ].
apply List.in_map_iff in Hx.
apply List.in_seq.
destruct  Hx as (i & Hx & Hi).
apply List.in_seq in Hi.
subst x.
progress unfold abs.
remember (_ <=? _) as u eqn:Hu.
symmetry in Hu.
destruct u. {
  apply Nat.leb_le in Hu.
  split. {
    apply Nat.neq_0_lt_0.
    intros H.
    clear  Hu.
    apply Nat.Lcm0.mod_divide in H.
    rewrite Nat.mul_comm in H.
    apply Nat.gauss in H; [ | now rewrite Nat.gcd_comm ].
    destruct H as (m, Hm).
    subst i.
    destruct (Nat.eq_dec m 0) as [Hmz| Hmz]; [ now subst m | ].
    destruct Hi as (H1, Hi).
    apply Nat.nle_gt in Hi.
    apply Hi; clear Hi.
    destruct m; [ easy | ].
    cbn - [ "/" ].
    apply (Nat.le_trans _ l); [ | apply Nat.le_add_r ].
    apply Nat.le_succ_l.
    apply Nat.Div0.div_lt_upper_bound.
    flia Hlz.
  }
  now apply Nat.lt_succ_r.
} {
  apply Nat.leb_gt in Hu.
  split. {
    apply Nat.le_add_le_sub_r.
    now apply Nat.mod_upper_bound.
  }
  apply Nat.lt_succ_r.
  apply Nat.le_sub_le_add_l.
  destruct (Nat.Even_Odd_dec l) as [Hl| Hl]; cycle 1. {
    destruct Hl as (m, Hm).
    rewrite Hm at 3.
    rewrite Nat.add_sub, (Nat.mul_comm 2), Nat.div_mul; [ | easy ].
    rewrite Hm in Hu at 1.
    rewrite Nat.add_sub in Hu.
    rewrite (Nat.mul_comm 2), Nat.div_mul in Hu; [ | easy ].
    eapply Nat.le_trans; cycle 1. {
      apply Nat.add_le_mono_r.
      apply Nat.le_succ_l.
      apply Hu.
    }
    rewrite Hm, Nat.add_comm.
    now rewrite Nat_mul_2_l.
  }
  destruct Hl as (m, Hm).
  destruct (Nat.eq_dec ((i * a) mod l) m) as [Hialm| Hialm]. {
    exfalso.
    specialize congruence_inverse_has_unique_solution as H1.
    specialize (H1 l 1).
    assert (H : 0 < 1 < l). {
      split; [ easy | ].
      subst l.
      destruct m; [ easy | ].
      rewrite Nat.mul_succ_r, Nat.add_comm.
      apply (Nat.lt_le_trans _ 2); [ easy | ].
      apply Nat.le_add_r.
    }
    specialize (H1 H); clear H.
    specialize (H1 a Hal).
    destruct H1 as (a' & (H1, H2) & H3).
    apply (f_equal (λ x, 2 * x * a')) in Hialm.
    apply (f_equal (λ x, x mod l)) in Hialm.
    rewrite <- Hm, (Nat.mul_comm l) in Hialm.
    rewrite Nat.Div0.mod_mul in Hialm.
    rewrite Nat.mul_shuffle0 in Hialm.
    rewrite Nat.Div0.mul_mod_idemp_r in Hialm.
    rewrite Nat.mul_shuffle0 in Hialm.
    rewrite Nat.mul_assoc in Hialm.
    rewrite <- Nat.mul_assoc in Hialm.
    rewrite <- Nat.Div0.mul_mod_idemp_r in Hialm.
    rewrite H2, Nat.mul_1_r in Hialm.
    apply Nat.Lcm0.mod_divide in Hialm.
    rewrite Hm in Hialm.
    apply Nat.mul_divide_cancel_l in Hialm; [ | easy ].
    destruct Hialm as (c, Hc).
    subst i.
    destruct c; [ easy | ].
    destruct Hi as (H4, H5).
    apply Nat.nle_gt in H5.
    apply H5; clear H5.
    apply Nat.le_succ_l.
    apply Nat.Div0.div_lt_upper_bound.
    rewrite (Nat.mul_comm _ m), Nat.mul_assoc.
    rewrite <- Hm.
    rewrite Nat.mul_succ_r.
    apply (Nat.lt_le_trans _ l); [ | apply Nat.le_add_l ].
    apply Nat.sub_lt; [ | easy ].
    now apply Nat.neq_0_lt_0.
  }
  rewrite Hm in Hu, Hialm |-*.
  replace ((2 * m - 1) / 2) with (m - 1) in Hu |-*; cycle 1. {
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
  apply Nat.le_sub_le_add_r.
  rewrite Nat.sub_sub_distr; cycle 1. {
    apply Nat.neq_0_lt_0.
    intros H; subst m.
    now rewrite Nat.mul_0_r in Hm.
  } {
    rewrite Nat_mul_2_l.
    apply Nat.le_add_l.
  }
  rewrite Nat_mul_2_l at 1.
  rewrite Nat.add_sub.
  rewrite Nat.add_1_r.
  apply Nat.le_succ_l.
  apply Nat_le_neq_lt; [ | easy ].
  apply Nat.lt_sub_lt_add_l in Hu.
  now apply -> Nat.lt_succ_r in Hu.
}
Qed.

Theorem permutation_seq_map_abs_seq :
  ∀ a l, coprimes a l →
  permutation eqb
    (List.seq 1 ((l - 1) / 2))
    (List.map (λ i, abs ((i * a) mod l) l) (List.seq 1 ((l - 1) / 2))).
Proof.
intros * Hal.
apply incl_incl_permutation. {
  progress unfold Misc.equality.
  apply Nat.eqb_eq.
} {
  apply List.seq_NoDup.
} {
  now apply NoDup_map_mul_mod_seq.
} {
  intros x Hx.
  now apply incl_seq_map_mul.
} {
  intros x Hx.
  now apply incl_map_mul_seq in Hx.
}
Qed.

Theorem summation_up_to_half :
  ∀ a l, coprimes a l →
  ∑ (i = 1, (l - 1) / 2), i = ∑ (i = 1, (l - 1) / 2), (abs ((i * a) mod l) l).
Proof.
intros * Hap.
apply permutation_same_list_summation.
rewrite Nat_sub_succ_1.
rewrite List.map_id.
now apply permutation_seq_map_abs_seq.
Qed.

Theorem rngl_summation_if_then_else :
  ∀ {T} {ro : ring_like_op T} {rp : ring_like_prop T},
  ∀ b e (f : nat → bool) (g h : nat → T),
  (∑ (i = b, e), (if f i then g i else h i) =
     (∑ (i = b, e), (if f i then g i else 0) +
      ∑ (i = b, e), (if f i then 0 else h i)))%L.
Proof.
intros.
rewrite <- rngl_summation_add_distr.
apply rngl_summation_eq_compat.
intros i Hi.
symmetry.
destruct (f i).
apply rngl_add_0_r.
apply rngl_add_0_l.
Qed.

Theorem Nat_add_if_if :
  ∀ (a : bool) b c d e,
  (if a then b else c) + (if a then d else e) =
  if a then b + d else c + e.
Proof. now intros; now destruct a. Qed.

Theorem Nat_inj_succ_mod_le : ∀ a b c, a ≤ b → S a ≡ S b mod c → a ≡ b mod c.
Proof.
intros * Hba Hab.
  cbn in Hab.
symmetry in Hab; symmetry.
apply Nat_eq_mod_sub_0 in Hab; cycle 1. {
  now apply -> Nat.succ_le_mono.
}
cbn in Hab.
revert b Hab Hba.
induction a; intros. {
  rewrite Nat.sub_0_r in Hab.
  now rewrite Nat.Div0.mod_0_l.
}
destruct b; [ easy | ].
apply Nat.succ_le_mono in Hba.
cbn in Hab.
rewrite <- (Nat.add_1_l a).
rewrite <- (Nat.add_1_l b).
rewrite <- Nat.Div0.add_mod_idemp_r; symmetry.
rewrite <- Nat.Div0.add_mod_idemp_r; symmetry.
f_equal; f_equal.
now apply IHa.
Qed.

Theorem Nat_inj_succ_mod : ∀ a b c, S a ≡ S b mod c → a ≡ b mod c.
Proof.
intros * Hab.
destruct (le_dec b a) as [Hba| Hba]. {
  symmetry.
  now apply Nat_inj_succ_mod_le.
} {
  apply Nat.nle_gt in Hba.
  apply Nat.lt_le_incl in Hba.
  now apply Nat_inj_succ_mod_le.
}
Qed.

Theorem Nat_add_cancel_r_mod :
  ∀ a b c d, a + c ≡ (b + c) mod d ↔ a ≡ b mod d.
Proof.
intros.
split; intros Hab; cycle 1. {
  rewrite <- Nat.Div0.add_mod_idemp_l.
  rewrite Hab.
  apply Nat.Div0.add_mod_idemp_l.
} {
  revert a b Hab.
  induction c; intros; [ now do 2 rewrite Nat.add_0_r in Hab | ].
  do 2 rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hab.
  apply IHc in Hab.
  now apply Nat_inj_succ_mod in Hab.
}
Qed.

Theorem nat_leb_rngl_leb : ∀ a b, (a <=? b) = (a ≤? b)%L.
Proof. easy. Qed.

Theorem Nat_add_cancel_l_mod :
  ∀ a b c d, c + a ≡ (c + b) mod d ↔ a ≡ b mod d.
Proof.
intros.
split; intros Hab; cycle 1. {
  rewrite <- Nat.Div0.add_mod_idemp_r.
  rewrite Hab.
  apply Nat.Div0.add_mod_idemp_r.
} {
  revert a b Hab.
  induction c; intros; [ now do 2 rewrite Nat.add_0_l in Hab | ].
  do 2 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hab.
  apply IHc in Hab.
  now apply Nat_inj_succ_mod in Hab.
}
Qed.

Theorem Eisenstein_lemma : ∀ a l,
  coprimes a l
  → Nat.Odd a
  → Nat.Odd l
  → nb_of_mult_gt_half a l ≡ (∑ (k = 1, (l - 1) / 2), k * a / l) mod 2.
Proof.
intros * Hal Ha Hl.
destruct (Nat.eq_dec l 0) as [Hlz| Hlz]; [ now subst l | ].
assert (Hka : ∀ k, k * a / l ≡ (k * a + k * a mod l) mod 2). {
  intros k.
  specialize (Nat.div_mod (k * a) l Hlz) as H.
  destruct Hl as (m, Hl).
  rewrite H, Hl at 2.
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
  rewrite <- Nat.add_assoc.
  rewrite <- Nat_mul_2_l.
  rewrite Nat_mod_add_r_mul_l.
  rewrite <- Nat.mul_assoc.
  now rewrite Nat_mod_add_l_mul_l.
}
assert
  (H1 :
    ∑ (k = 1, (l - 1) / 2), k * a =
      l * (∑ (k = 1, (l - 1) / 2), k * a / l) +
      (∑ (k = 1, (l - 1) / 2),
         if (k * a) mod l <=? (l - 1) / 2 then (k * a)%L mod l else 0) +
      (∑ (k = 1, (l - 1) / 2),
         if (k * a) mod l <=? (l - 1) / 2 then 0 else (k * a)%L mod l)). {
  erewrite rngl_summation_eq_compat; cycle 1. {
    intros k Hk.
    unfold rngl_mul.
    cbn.
    rewrite (Nat.div_mod (k * a) l Hlz).
    replace Nat.add with rngl_add by easy.
    replace Nat.mul with rngl_mul by easy.
    easy.
  }
  cbn - [ "/" rngl_mul ].
  rewrite rngl_summation_add_distr.
  rewrite <- rngl_mul_summation_distr_l; [ | easy ].
  rewrite <- Nat.add_assoc.
  replace Nat.add with rngl_add by easy.
  progress f_equal.
  rewrite <- rngl_summation_add_distr.
  apply rngl_summation_eq_compat.
  intros k Hk.
  symmetry.
  destruct (_ <=? _)%L.
  apply rngl_add_0_r.
  apply rngl_add_0_l.
}
assert
  (H2 :
     ∑ (k = 1, (l - 1) / 2), k =
       ∑ (k = 1, (l - 1) / 2),
         (if (k * a) mod l <=? (l - 1) / 2 then (k * a)%L mod l else 0) +
       nb_of_mult_gt_half a l * l -
       ∑ (k = 1, (l - 1) / 2),
         (if (k * a) mod l <=? (l - 1) / 2 then 0 else (k * a)%L mod l)). {
  rewrite <- Nat.add_sub_assoc; cycle 1. {
    rewrite eq_nb_of_mult_gt_half_summation.
    progress replace Nat.mul with rngl_mul by easy.
    rewrite rngl_mul_summation_distr_r; [ | easy ].
    apply rngl_le_Nat_le.
    apply rngl_summation_le_compat; [ easy | easy | ].
    intros k Hk.
    progress unfold Nat.b2n.
    replace rngl_zero with 0 by easy.
    replace rngl_mul with Nat.mul by easy.
    apply Nat.leb_le.
    remember (_ <=? _)%L as x eqn:Hx.
    remember (_ <? _)%L as y eqn:Hy in |-*.
    symmetry in Hx, Hy.
    destruct x; [ easy | ].
    destruct y. {
      rewrite Nat.mul_1_l.
      apply Nat.lt_le_incl.
      now apply Nat.mod_upper_bound.
    }
    apply Nat.leb_nle in Hx.
    apply rngl_ltb_ge_iff in Hy; [ | easy ].
    now apply rngl_le_Nat_le in Hy.
  }
  rewrite (summation_up_to_half a); [ | easy ].
  progress unfold abs.
  rewrite rngl_summation_if_then_else.
  replace Nat.add with rngl_add by easy.
  progress f_equal.
  symmetry.
  apply Nat.add_sub_eq_l.
  replace Nat.add with rngl_add by easy.
  rewrite <- rngl_summation_add_distr.
  erewrite rngl_summation_eq_compat; cycle 1. {
    intros i Hi.
    rewrite Nat_add_if_if.
    replace rngl_zero with 0 by easy.
    rewrite Nat.add_0_l.
    rewrite Nat.add_sub_assoc; cycle 1. {
      now apply Nat.lt_le_incl, Nat.mod_upper_bound.
    }
    rewrite Nat.add_comm, Nat.add_sub.
    easy.
  }
  cbn - [ "/" "mod" nb_of_mult_gt_half ].
  rewrite eq_nb_of_mult_gt_half_summation.
  progress replace Nat.mul with rngl_mul by easy.
  rewrite rngl_mul_summation_distr_r; [ | easy ].
  apply rngl_summation_eq_compat.
  intros k Hk.
  progress unfold Nat.b2n.
  rewrite Nat.leb_antisym.
  rewrite Bool.negb_if.
  rewrite nat_ltb_rngl_ltb.
  replace rngl_mul with Nat.mul by easy.
  replace rngl_div with Nat.div by easy.
  replace rngl_sub with Nat.sub by easy.
  symmetry.
  now destruct (_ <? _)%L.
}
rewrite <- rngl_mul_summation_distr_r in H1; [ | easy ].
remember (∑ (i = 1, (l - 1) / 2), i) as m eqn:Hm.
remember (_ + _) as x eqn:Hx in H1.
remember (_ - _) as y eqn:Hy in H2.
assert (H3 : (m * a - m = x - y)%L) by now rewrite H1, H2.
replace (m * a - m)%L with (m * (a - 1))%L in H3; cycle 1. {
  cbn.
  replace rngl_mul with Nat.mul by easy.
  replace rngl_one with 1 by easy.
  now rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
}
subst x y; move H3 at bottom.
progress replace Nat.add with rngl_add in H3 by easy.
progress replace Nat.sub with rngl_sub in H3 by easy.
remember (∑ (k = 1, _), _)%L as u eqn:Hu in H3.
remember (∑ (k = 1, _), _)%L as v eqn:Hv in H3.
remember (∑ (k = 1, _), _)%L as w eqn:Hw in H3.
move u before m; move v before u; move w before v.
progress replace rngl_sub with Nat.sub in Hu by easy.
progress replace rngl_add with Nat.add in H3 by easy.
progress replace rngl_sub with Nat.sub in H3 by easy.
progress replace rngl_mul with Nat.mul in H3 by easy.
rewrite <- Hu.
progress replace rngl_one with 1 in H3 by easy.
rewrite Nat.add_shuffle0 in H3.
symmetry in H3.
apply (f_equal (λ x, x mod 2)) in H3.
rewrite (proj2 (Nat.Lcm0.mod_divide (_ * _) 2)) in H3; cycle 1. {
  destruct Ha as (k, H); rewrite H, Nat.add_sub.
  rewrite Nat.mul_comm, <- Nat.mul_assoc.
  apply Nat.divide_factor_l.
}
rewrite <- (Nat.Div0.mod_0_l 2) in H3 at 2.
apply Nat_eq_mod_sub_0 in H3; cycle 1. {
  destruct (le_dec w (nb_of_mult_gt_half a l * l)) as [H4| H4]. {
    rewrite <- Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm.
    apply Nat.add_le_mono_r.
    apply Nat.le_sub_le_add_r.
    rewrite <- Nat.add_assoc.
    rewrite eq_nb_of_mult_gt_half_summation.
    progress unfold Nat.b2n.
    erewrite rngl_summation_eq_compat; cycle 1. {
      intros k Hk.
      rewrite <- nat_ltb_rngl_ltb.
      rewrite Nat.ltb_antisym.
      rewrite Bool.if_negb.
      easy.
    }
    cbn - [ "/" ].
    rewrite <- (Nat_mul_2_l w), Hw.
    replace Nat.mul with rngl_mul by easy.
    rewrite rngl_mul_summation_distr_l; [ | easy ].
    rewrite Hu.
    rewrite rngl_mul_summation_distr_l; [ | easy ].
    replace rngl_sub with Nat.sub by easy.
    replace Nat.add with rngl_add by easy.
    rewrite <- rngl_summation_add_distr.
    rewrite rngl_mul_summation_distr_r; [ | easy ].
    apply rngl_le_Nat_le.
    apply rngl_summation_le_compat; [ easy | easy | ].
    intros k Hk.
    remember (_ <=? _) as x eqn:Hx.
    symmetry in Hx.
    destruct x; [ easy | ].
    rewrite Nat.mul_1_l.
    apply Nat.leb_gt in Hx.
    progress replace rngl_mul with Nat.mul by easy.
    progress replace rngl_div with Nat.div by easy.
    progress replace rngl_add with Nat.add by easy.
    apply rngl_le_Nat_le.
    progress replace rngl_mul with Nat.mul in Hx by easy.
    progress replace rngl_one with 1 in Hx by easy.
    rewrite Nat.add_1_r in Hx.
    eapply Nat.le_trans; [ | apply Nat.le_add_l ].
    apply Nat_div_lt_mul in Hx; [ | easy ].
    apply Nat.lt_sub_lt_add_r in Hx.
    rewrite Nat.add_1_r in Hx.
    now apply -> Nat.lt_succ_r in Hx.
  }
  apply Nat.nle_gt in H4.
  eapply Nat.le_trans; [ apply Nat.le_sub_l | ].
  rewrite Nat.add_comm.
  apply Nat.add_le_mono_r.
  eapply Nat.le_trans; [ | apply Nat.le_add_l ].
  now apply Nat.lt_le_incl.
}
apply (Nat_add_cancel_r_mod _ _ w) in H3.
rewrite Nat.sub_add in H3; cycle 1. {
  eapply Nat.le_trans; [ | apply Nat.le_add_l ].
  rewrite eq_nb_of_mult_gt_half_summation.
  replace Nat.mul with rngl_mul by easy.
  rewrite rngl_mul_summation_distr_r; [ | easy ].
  rewrite Hw.
  progress unfold Nat.b2n.
  apply rngl_le_Nat_le.
  replace rngl_sub with Nat.sub by easy.
  apply rngl_summation_le_compat; [ easy | easy | ].
  intros k Hk.
  rewrite rngl_ltb_neg_leb; [ | easy ].
  rewrite Bool.negb_if.
  replace Nat.div with rngl_div by easy.
  rewrite nat_leb_rngl_leb.
  destruct (_ ≤? _)%L; [ easy | ].
  apply rngl_le_Nat_le.
  rewrite Nat.mul_1_l.
  apply Nat.lt_le_incl.
  now apply Nat.mod_upper_bound.
}
rewrite (Nat.add_shuffle0 _ w) in H3.
rewrite <- Nat.add_assoc in H3.
rewrite <- Nat_mul_2_l in H3.
rewrite Nat_mod_add_r_mul_l in H3.
rewrite Nat.add_comm in H3.
apply Nat_add_cancel_l_mod in H3.
symmetry in H3.
rewrite Nat.mul_comm in H3.
apply Nat_mul_mod_cancel_l in H3; [ easy | ].
destruct Hl as (n, Hn).
rewrite Hn.
rewrite Nat.gcd_comm.
rewrite Nat.add_comm, Nat.mul_comm.
now rewrite Nat.gcd_add_mult_diag_r.
Qed.
