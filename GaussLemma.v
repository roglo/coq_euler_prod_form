Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import Sorting.Permutation.

Require Import RingLike.Core.
Require Import RingLike.IterMul.
Require Import RingLike.Nat_algebra.

Require Import Misc Primes EulerCriterion.

Definition nb_of_mult_gt_half a p :=
  List.length
    (List.filter (λ m, (p - 1) / 2 <? ((m * a) mod p))
       (List.seq 1 ((p - 1) / 2))).

Theorem nb_of_mult_gt_half_mod :
  ∀ a p, nb_of_mult_gt_half a p = nb_of_mult_gt_half (a mod p) p.
Proof.
intros.
progress unfold nb_of_mult_gt_half.
f_equal.
apply List.filter_ext.
intros m.
now rewrite Nat.Div0.mul_mod_idemp_r.
Qed.

Theorem Legendre_symbol_mod_r :
  ∀ a p, Legendre_symbol a p = Legendre_symbol (a mod p) p.
Proof.
intros.
progress unfold Legendre_symbol.
rewrite Nat.Div0.mod_mod.
now rewrite sqrt_mod_mod.
Qed.

Theorem List_fold_left_mul_const_r :
  ∀ c d l,
  List.fold_left (λ a b, a * b * c) l d =
  List.fold_left Nat.mul l d * c ^ List.length l.
Proof.
intros.
revert d.
induction l as [| a]; intros; [ symmetry; apply Nat.mul_1_r | cbn ].
rewrite IHl.
rewrite Nat.mul_assoc.
f_equal.
symmetry.
apply List_fold_left_mul_assoc.
Qed.

Theorem List_fold_left_mul_mul_seq :
  ∀ a n, ∏ (i = 1, n), (i * a) = a ^ n * fact n.
Proof.
intros.
progress unfold Utils.iter_seq.
progress unfold Utils.iter_list.
rewrite Nat_sub_succ_1.
erewrite List_fold_left_ext_in; cycle 1. {
  intros * Hb.
  now rewrite Nat.mul_assoc.
}
rewrite List_fold_left_mul_const_r.
rewrite List.length_seq, Nat.mul_comm.
f_equal; symmetry.
apply fact_eq_fold_left.
Qed.

Theorem Nat_mul_pred_mod : ∀ a n, a < n → (n - a) * (n - 1) mod n = a.
Proof.
intros * Han.
rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
rewrite Nat.mul_sub_distr_r.
rewrite Nat_sub_sub_swap.
rewrite Nat.sub_sub_distr; [ | now apply Nat.lt_le_incl | ]; cycle 1. {
  destruct n; [ easy | cbn ].
  apply -> Nat.succ_le_mono.
  apply Nat.le_add_r.
}
rewrite <- Nat.mul_pred_r.
rewrite <- Nat.sub_1_r.
rewrite Nat.add_comm, Nat.mul_comm.
rewrite <- Nat.add_sub_assoc; cycle 1. {
  apply Nat.mul_le_mono_r.
  flia Han.
}
rewrite <- Nat.mul_sub_distr_r.
rewrite Nat.Div0.mod_add.
now apply Nat.mod_small.
Qed.

Definition sign a p := if a <=? (p - 1) / 2 then 1 else p - 1.
Definition abs a p := if a <=? (p - 1) / 2 then a else p - a.

Theorem sign_abs : ∀ a n, a < n → a = (sign a n * abs a n) mod n.
Proof.
intros * Han.
progress unfold sign.
progress unfold abs.
destruct (_ <=? _). {
  rewrite Nat.mul_1_l; symmetry.
  now apply Nat.mod_small.
}
rewrite Nat.mul_comm; symmetry.
now apply Nat_mul_pred_mod.
Qed.

Theorem List_fold_left_mod :
  ∀ A a b (f : nat → A → nat) l,
  (∀ a l, List.fold_left f l a ≡ List.fold_left f l (a mod b) mod b)
  → List.fold_left f l a ≡ List.fold_left (λ x y, f x y mod b) l a mod b.
Proof.
intros * Hf.
revert a.
induction l as [| c]; intros; [ easy | cbn ].
rewrite <- IHl.
apply Hf.
Qed.

Theorem List_fold_left_mul_mul :
  ∀ A c l f (g : A → _),
  List.fold_left (λ a b, a * f b * g b) l c =
  List.fold_left (λ a b, a * f b) l c *
  ∏ (b ∈ l), g b.
Proof.
intros.
progress unfold Utils.iter_list.
revert c.
induction l as [| a]; intros; [ symmetry; apply Nat.mul_1_r | cbn ].
rewrite IHl.
rewrite Nat.mul_1_l.
do 4 rewrite <- (List_fold_left_map  _ _ _ _ _ l).
do 2 rewrite <- List_fold_left_mul_assoc.
do 3 rewrite <- Nat.mul_assoc.
progress f_equal.
progress f_equal.
symmetry.
apply List_fold_left_mul_from_1.
Qed.

Theorem fold_iter_list : ∀ {A B} (f : A → B → A) l d,
  List.fold_left f l d = Utils.iter_list l f d.
Proof. easy. Qed.

Theorem fold_iter_seq_1_succ_sub : ∀ A len f (d : A),
  Utils.iter_list (List.seq 1 (S len - 1)) f d = Utils.iter_seq 1 len f d.
Proof. easy. Qed.

Theorem List_fold_left_mul_filter_filter :
  ∀ A c l (f : A → _) g,
  List.fold_left (λ a b, a * f b) l c =
  List.fold_left (λ a b, a * f b) (List.filter g l) c *
  ∏ (b ∈ List.filter (λ a : A, negb (g a)) l), f b.
Proof.
intros.
progress unfold Utils.iter_list.
revert c.
induction l as [| a]; intros; cbn. {
  symmetry; apply Nat.mul_1_r.
}
rewrite IHl.
rename a into d.
remember (g d) as gd eqn:Hgd; symmetry in Hgd.
destruct gd; [ easy | cbn ].
rewrite Nat.mul_1_l.
rewrite (List_fold_left_mul_fun_from_1 (c * f d)).
rewrite (List_fold_left_mul_fun_from_1 c).
rewrite (List_fold_left_mul_fun_from_1 (f d)).
do 3 rewrite <- Nat.mul_assoc.
progress f_equal.
rewrite Nat.mul_comm.
rewrite <- Nat.mul_assoc.
progress f_equal.
apply Nat.mul_comm.
Qed.

Theorem List_fold_left_filter :
  ∀ A B a (f : A → B → A) g l,
  List.fold_left f (List.filter g l) a =
  List.fold_left (λ b c, if g c then f b c else b) l a.
Proof.
intros.
revert a.
induction l as [| b]; intros; [ easy | cbn ].
destruct (g b); [ apply IHl | easy ].
Qed.

Theorem List_fold_left_const :
  ∀ A B (b : A) (l : list B), List.fold_left (λ a _, a) l b = b.
Proof. now intros; induction l. Qed.

Theorem if_mul_negb :
  ∀ a (b : bool) c d e,
  (if b then a * (if negb b then c else d) else e) =
  (if b then a * d else e).
Proof. now intros; destruct b. Qed.

Theorem List_fold_left_if_equiv_filter  :
  ∀ a p l (g : _ → bool),
  List.fold_left (λ c b : nat, if g b then c * (p - 1) else c) l a
  ≡ (a * (p - 1) ^ length (List.filter g l)) mod p.
Proof.
intros.
revert a.
induction l as [| b]; intros; cbn; [ now rewrite Nat.mul_1_r | ].
destruct (g b); cbn; [ | easy ].
now rewrite IHl, Nat.mul_assoc.
Qed.

Theorem List_fold_left_mul_sign :
  ∀ a p n h,
  n = nb_of_mult_gt_half a p
  → h = (p - 1) / 2
  → ∏ (i = 1, h), sign ((i * a) mod p) p ≡ (p - 1) ^ n mod p.
Proof.
intros * Hn Hh.
progress unfold nb_of_mult_gt_half in Hn.
rewrite <- Hh in Hn.
set (g := λ m, h <? (m * a) mod p) in Hn.
progress unfold sign.
rewrite <- Hh.
progress unfold Utils.iter_seq.
progress unfold Utils.iter_list.
rewrite Nat_sub_succ_1.
rewrite (List_fold_left_mul_filter_filter _ _ _ _ g).
progress unfold Utils.iter_list.
do 2 rewrite List_fold_left_filter.
unfold g.
erewrite List_fold_left_ext_in; [ | now intros; rewrite Nat.leb_antisym ].
rewrite Nat.mul_comm.
erewrite List_fold_left_ext_in; [ | now intros; rewrite Nat.leb_antisym ].
rewrite List_fold_left_ext_in with (g := λ c _, c). 2: {
  intros * Hb.
  destruct (h <? (b * a) mod p); [ easy | cbn ].
  apply Nat.mul_1_r.
}
rewrite List_fold_left_const, Nat.mul_1_l.
erewrite List_fold_left_ext_in; cycle 1. {
  intros * Hb.
  fold (g b).
  now rewrite if_mul_negb.
}
subst n.
now rewrite List_fold_left_if_equiv_filter, Nat.mul_1_l.
Qed.

Theorem List_fold_left_mul_mul_seq_fold_left_abs :
  ∀ a p n h,
  p ≠ 0
  → n = nb_of_mult_gt_half a p
  → h = (p - 1) / 2
  → ∏ (i = 1, h), (i * a) ≡
      ((p - 1) ^ n * ∏ (i = 1, h), abs ((i * a) mod p) p) mod p.
Proof.
intros  * Hpz Hn Hh.
progress unfold Utils.iter_seq.
progress unfold Utils.iter_list.
rewrite List_fold_left_mod; cycle 1. {
  intros b l.
  revert b.
  induction l as [| d]; intros; cbn. {
    symmetry; apply Nat.Div0.mod_mod.
  }
  rewrite IHl.
  rewrite <- Nat.Div0.mul_mod_idemp_l.
  symmetry.
  now rewrite IHl.
}
erewrite List_fold_left_ext_in; cycle 1. {
  intros * Hb.
  rewrite <- Nat.Div0.mul_mod_idemp_r.
  easy.
}
rewrite <- List_fold_left_mod; cycle 1. {
  intros b l.
  revert b.
  induction l as [| d]; intros; cbn. {
    symmetry; apply Nat.Div0.mod_mod.
  }
  rewrite IHl.
  rewrite <- Nat.Div0.mul_mod_idemp_l.
  symmetry.
  rewrite IHl.
  rewrite <- Nat.Div0.mul_mod_idemp_r.
  easy.
}
erewrite List_fold_left_ext_in; cycle 1. {
  intros * Hb.
  rewrite (sign_abs ((b * a)%L mod p) p); cycle 1. {
    now apply Nat.mod_upper_bound.
  }
  easy.
}
rewrite List_fold_left_mod; cycle 1. {
  intros b l.
  revert b.
  induction l as [| d]; intros; cbn. {
    symmetry; apply Nat.Div0.mod_mod.
  }
  rewrite IHl.
  rewrite <- Nat.Div0.mul_mod_idemp_l.
  symmetry.
  rewrite IHl.
  rewrite <- Nat.Div0.mul_mod_idemp_r.
  easy.
}
erewrite List_fold_left_ext_in; cycle 1. {
  intros * Hb.
  rewrite Nat.Div0.mul_mod_idemp_r.
  rewrite Nat.mul_assoc.
  easy.
}
rewrite <- List_fold_left_mod; cycle 1. {
  intros b l.
  revert b.
  induction l as [| d]; intros; cbn. {
    symmetry; apply Nat.Div0.mod_mod.
  }
  rewrite IHl.
  rewrite <- Nat.Div0.mul_mod_idemp_l.
  symmetry.
  rewrite IHl.
  rewrite <- Nat.Div0.mul_mod_idemp_r.
  remember (λ c l, _) as f eqn:Hf in |-*.
  f_equal.
  f_equal.
  remember ((d * a) mod p) as da.
  rewrite <- (Nat.Div0.mul_mod_idemp_l b).
  rewrite <- Nat.Div0.mul_mod_idemp_l.
  rewrite Nat.Div0.mul_mod_idemp_r.
  easy.
}
rewrite List_fold_left_mul_mul.
remember (λ acc i, _) as x in |-*.
remember (λ acc i, _) as y in |-*; subst x y.
rewrite <- Nat.Div0.mul_mod_idemp_l.
do 2 rewrite fold_iter_list.
do 2 rewrite fold_iter_seq_1_succ_sub.
rewrite (List_fold_left_mul_sign _ _ n); [ | easy | easy ].
now rewrite Nat.Div0.mul_mod_idemp_l.
Qed.

Theorem Legendre_symbol_mod :
  ∀ a p, 2 ≤ p → Legendre_symbol a p = Legendre_symbol a p mod p.
Proof.
intros * H2p.
progress unfold Legendre_symbol.
symmetry.
remember (p =? 2) as p2 eqn:Hp2; symmetry in Hp2.
destruct p2; [ now apply Nat.eqb_eq in Hp2; subst p | ].
destruct (a mod p =? 0); [ apply Nat.Div0.mod_0_l | ].
apply Nat.eqb_neq in Hp2.
destruct (sqrt_mod a p); [ now apply Nat.mod_small | ].
apply Nat.mod_small.
flia H2p.
Qed.

Theorem abs_all_different_multiples : ∀ p,
  prime p
  → ∀ a, 1 ≤ a < p
  → ∀ i j, i < j < p → (i * abs a p) mod p ≠ (j * abs a p) mod p.
Proof.
intros * Hp * Hap * Hijp.
intros Haa; symmetry in Haa.
apply Nat_mul_mod_cancel_r in Haa. 2: {
  rewrite Nat.gcd_comm.
  apply eq_gcd_prime_small_1; [ easy | ].
  progress unfold abs.
  destruct (_ <=? _); [ easy | ].
  flia Hap.
}
rewrite Nat.mod_small in Haa; [ | easy ].
rewrite Nat.mod_small in Haa; [ | flia Hijp ].
flia Hijp Haa.
Qed.

Theorem Nat_eq_succ_mod_1 : ∀ a b, S a mod b = 1 → a mod b = 0.
Proof.
intros * Hab.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  subst b; cbn in Hab |-*.
  now apply Nat.succ_inj in Hab.
}
specialize (Nat.div_mod (S a) b Hbz) as H1.
rewrite Hab, Nat.add_comm in H1.
apply Nat.succ_inj in H1.
rewrite H1, Nat.mul_comm.
apply Nat.Div0.mod_mul.
Qed.

Theorem Nat_mul_2_l : ∀ a, 2 * a = a + a.
Proof. flia. Qed.

Theorem eq_product_abs_fact_mod :
  ∀ h a p,
  prime p
  → 0 < a < p
  → h = (p - 1) / 2
  → ∏ (i = 1, h), abs ((i * a) mod p) p ≡ fact h mod p.
Proof.
intros * Hp (Haz, Hap) Hh.
assert (Hcp : coprimes a p). {
  progress unfold coprimes.
  rewrite Nat.gcd_comm.
  now apply eq_gcd_prime_small_1.
}
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ now subst p | ].
specialize abs_all_different_multiples as H4.
assert (H: 1 ≤ a < p) by easy.
specialize (H4 p Hp a H); clear H.
rewrite fact_eq_fold_left.
progress unfold Utils.iter_seq.
progress unfold Utils.iter_list.
rewrite <- List_fold_left_map.
f_equal.
rewrite Nat_sub_succ_1.
apply Permutation_fold_mul.
apply Permutation_map_same_l; cycle 1. {
  intros b Hb.
  apply List.in_map_iff in Hb.
  destruct Hb as (c & Hcb & Hc).
  subst b.
  progress unfold abs.
  rewrite <- Hh.
  remember (_ <=? _) as x eqn:Hx; symmetry in Hx.
  destruct x. {
    apply Nat.leb_le in Hx.
    apply List.in_seq.
    split; [ | flia Hx ].
    apply Nat.neq_0_lt_0.
    intros H.
    clear Hx.
    apply Nat.Lcm0.mod_divide in H.
    apply prime_divide_mul in H; [ | easy ].
    destruct H as [H| H]. {
      destruct H as (d, Hd).
      apply List.in_seq in Hc.
      destruct a; [ easy | clear Haz ].
      destruct d; [ flia Hd Hc | ].
      destruct Hc as (H1c, Hch).
      apply Nat.nle_gt in Hch; apply Hch; clear Hch.
      subst c h.
      destruct p; [ easy | ].
      rewrite Nat.sub_succ, Nat.sub_0_r.
      cbn - [ "/" ].
      apply -> Nat.succ_le_mono.
      apply Nat.Div0.div_le_upper_bound; cbn.
      do 2 rewrite <- Nat.add_assoc.
      apply Nat.le_add_r.
    } {
      destruct H as (d, Hd).
      apply Nat.nle_gt in Hap; apply Hap; clear Hap.
      subst a.
      destruct d; [ easy | cbn ].
      apply Nat.le_add_r.
    }
  }
  apply Nat.leb_gt in Hx.
  apply List.in_seq.
  split. {
    apply Nat.le_add_le_sub_r.
    now apply Nat.mod_upper_bound.
  }
  destruct (Nat.eq_dec p 1) as [Hp1| Hp1]; [ now subst p | ].
  destruct (Nat.eq_dec p 2) as [Hp2| Hp2]. {
    now subst p; cbn in Hh; subst h.
  }
  destruct p; [ easy | ].
  rewrite Nat.sub_succ, Nat.sub_0_r in Hh; subst h.
  apply Nat.lt_succ_r.
  apply Nat.le_sub_le_add_l.
  apply (Nat.le_trans _ (1 + p / 2 + p / 2)); cycle 1. {
    now apply Nat.add_le_mono_r.
  }
  rewrite <- Nat.add_assoc.
  rewrite Nat_add_div_same; cycle 1. {
    specialize (odd_prime (S p) Hp Hp2) as Hpo.
    apply Nat_eq_succ_mod_1 in Hpo.
    now apply Nat.Lcm0.mod_divide in Hpo.
  }
  cbn - [ "/" ].
  rewrite <- Nat_mul_2_l.
  now rewrite Nat.mul_comm, Nat.div_mul.
}
apply (NoDup_map_iff 0).
rewrite List.length_seq.
intros i j Hi Hj Hij.
do 2 rewrite List.seq_nth in Hij; [ | easy | easy | easy ].
cbn - [ "*" ] in Hij.
remember ((S i) * a mod p <=? h) as x eqn:Hx in Hij; symmetry in Hx.
remember ((S j) * a mod p <=? h) as y eqn:Hy in Hij; symmetry in Hy.
assert (Hija :
  ∀ i j,
    i < h
    → j < h
    → S i * a ≡ (S j * a) mod p
    → i = j). {
  clear i j Hi Hj Hij Hx Hy.
  intros * Hi Hj Hij.
  destruct (lt_dec (S i mod p) (S j mod p)) as [Hlij| Hlij]. {
    rewrite <- (Nat.Div0.mul_mod_idemp_l (S i)) in Hij.
    rewrite <- (Nat.Div0.mul_mod_idemp_l (S j)) in Hij.
    exfalso; revert Hij.
    apply coprimes_all_different_multiples; [ easy | ].
    split; [ easy | ].
    now apply Nat.mod_upper_bound.
  }
  destruct (lt_dec (S j mod p) (S i mod p)) as [Hlji| Hlji]. {
    rewrite <- (Nat.Div0.mul_mod_idemp_l (S i)) in Hij.
    rewrite <- (Nat.Div0.mul_mod_idemp_l (S j)) in Hij.
    symmetry in Hij.
    exfalso; revert Hij.
    apply coprimes_all_different_multiples; [ easy | ].
    split; [ easy | ].
    now apply Nat.mod_upper_bound.
  }
  apply Nat.nlt_ge in Hlij, Hlji.
  apply Nat.le_antisymm in Hlij; [ clear Hlji | easy ].
  rewrite Nat.mod_small in Hlij; cycle 1. {
    apply (Nat.lt_le_trans _ (S h)); [ now apply -> Nat.succ_lt_mono | ].
    subst h.
    apply Nat.le_succ_l.
    apply Nat.Div0.div_lt_upper_bound.
    flia Hpz.
  }
  rewrite Nat.mod_small in Hlij; cycle 1. {
    apply (Nat.lt_le_trans _ (S h)); [ now apply -> Nat.succ_lt_mono | ].
    subst h.
    apply Nat.le_succ_l.
    apply Nat.Div0.div_lt_upper_bound.
    flia Hpz.
  }
  now injection Hlij.
}
assert (Hijap :
  ∀ i j,
    i < (p - 1) / 2
    → j < (p - 1) / 2
    → (S i * a) mod p = p - (S j * a) mod p
    → i = j). {
  clear i j Hj Hi Hij Hx Hy.
  intros * Hi Hj Hij.
  apply (f_equal (λ x, x + (S j * a mod p))) in Hij.
  rewrite Nat.sub_add in Hij; cycle 1. {
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  apply (f_equal (λ x, x mod p)) in Hij.
  rewrite Nat.Div0.mod_same in Hij.
  rewrite Nat.Div0.add_mod_idemp_l in Hij.
  rewrite Nat.Div0.add_mod_idemp_r in Hij.
  rewrite <- Nat.mul_add_distr_r in Hij.
  apply Nat.Lcm0.mod_divide in Hij.
  apply (prime_divide_mul _ Hp) in Hij.
  destruct Hij as [Hij| Hij]; cycle 1. {
    destruct Hij as (k, Hpa).
    destruct k; [ now apply Nat.neq_0_lt_0 in Hpa | ].
    rewrite Hpa in Hap.
    flia Hap.
  }
  destruct Hij as (k, Hij).
  destruct k; [ easy | ].
  destruct p; [ easy | ].
  rewrite Nat.sub_succ, Nat.sub_0_r in Hi, Hj.
  assert (H2i : 2 * i < p). {
    apply (Nat.mul_lt_mono_pos_l 2) in Hi; [ | easy ].
    rewrite <- Nat.Lcm0.divide_div_mul_exact in Hi; cycle 1. {
      destruct p; [ easy | ].
      destruct p; [ easy | ].
      specialize (odd_prime _ Hp) as H5.
      assert (H : S (S (S p)) ≠ 2) by easy.
      specialize (H5 H); clear H.
      apply Nat_eq_succ_mod_1 in H5.
      now apply Nat.Lcm0.mod_divide.
    }
    now rewrite (Nat.mul_comm 2 p), Nat.div_mul in Hi.
  }
  assert (H2j : 2 * j < p). {
    apply (Nat.mul_lt_mono_pos_l 2) in Hj; [ | easy ].
    rewrite <- Nat.Lcm0.divide_div_mul_exact in Hj; cycle 1. {
      destruct p; [ easy | ].
      destruct p; [ easy | ].
      specialize (odd_prime _ Hp) as H5.
      assert (H : S (S (S p)) ≠ 2) by easy.
      specialize (H5 H); clear H.
      apply Nat_eq_succ_mod_1 in H5.
      now apply Nat.Lcm0.mod_divide.
    }
    now rewrite (Nat.mul_comm 2 p), Nat.div_mul in Hj.
  }
  flia H2i H2j Hij.
}
destruct x, y. {
  progress unfold abs in Hij.
  rewrite <- Hh in Hij.
  rewrite Hx, Hy in Hij.
  now apply Hija.
} {
  apply Hijap; [ now subst h | now subst h | ].
  progress unfold abs in Hij.
  rewrite <- Hh in Hij.
  now rewrite Hx, Hy in Hij.
} {
  symmetry.
  apply Hijap; [ now subst h | now subst h | ].
  progress unfold abs in Hij.
  rewrite <- Hh in Hij.
  now rewrite Hx, Hy in Hij.
} {
  progress unfold abs in Hij.
  rewrite <- Hh in Hij.
  rewrite Hx, Hy in Hij.
  apply (f_equal (λ x, p - x)) in Hij.
  rewrite Nat.sub_sub_distr in Hij; [ | | easy ]; cycle 1. {
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Nat.sub_sub_distr in Hij; [ | | easy ]; cycle 1. {
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Nat.sub_diag in Hij.
  do 2 rewrite Nat.add_0_l in Hij.
  now apply Hija.
}
Qed.

Theorem Gauss_lemma :
  ∀ a p, prime p → coprimes a p →
  ∀ n, n = nb_of_mult_gt_half a p →
  Legendre_symbol a p = (p - 1) ^ n mod p.
Proof.
intros * Hp Hap * Hn.
rewrite nb_of_mult_gt_half_mod in Hn.
rewrite Legendre_symbol_mod_r.
remember (a mod p) as b eqn:Hb.
assert (H : 0 < b < p). {
  subst b.
  destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ now subst p | ].
  split; [ | now apply Nat.mod_upper_bound ].
  apply Nat.neq_0_lt_0.
  intros H.
  apply Nat.Div0.mod_divides in H.
  destruct H as (c, H); subst a.
  progress unfold coprimes in Hap.
  rewrite <- (Nat.mul_1_r p) in Hap at 2.
  rewrite Nat.gcd_mul_mono_l in Hap.
  rewrite Nat_gcd_1_r, Nat.mul_1_r in Hap.
  now subst p.
}
move H before Hap; clear Hap; rename H into Hap.
clear a Hb; rename b into a.
move n before a.
destruct Hap as (Haz, Hap).
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ now subst p | ].
remember ((p - 1) / 2) as h eqn:Hh.
remember (∏ (i = 1, h), (i * a)) as z eqn:Hz.
assert (H1 : z = a ^ h * fact h). {
  subst z.
  apply List_fold_left_mul_mul_seq.
}
assert (H2 : z ≡ ((p - 1) ^ n * ∏ (i = 1, h), abs ((i * a) mod p) p) mod p). {
  subst z.
  now apply List_fold_left_mul_mul_seq_fold_left_abs.
}
specialize (Euler_criterion p Hp a) as H3.
rewrite <- Legendre_symbol_mod in H3; cycle 1. {
  destruct p; [ easy | ].
  destruct p; [ easy | ].
  now do 2 apply -> Nat.succ_le_mono.
}
rewrite H3, <- Hh.
assert (H4 : ∏ (i = 1, h), abs ((i * a) mod p) p ≡ fact h mod p). {
  now apply eq_product_abs_fact_mod.
}
rewrite <- Nat.Div0.mul_mod_idemp_r in H2.
rewrite H4 in H2.
rewrite H1 in H2.
rewrite Nat.Div0.mul_mod_idemp_r in H2.
apply Nat_mul_mod_cancel_r in H2; [ easy | ].
rewrite Nat.gcd_comm.
apply Nat_gcd_prime_fact_lt; [ easy | ].
subst h.
apply Nat.Div0.div_lt_upper_bound.
cbn; rewrite Nat.add_0_r.
apply (Nat.lt_le_trans _ p); [ | apply Nat.le_add_l ].
apply Nat.sub_lt; [ | easy ].
now apply Nat.neq_0_lt_0.
Qed.
