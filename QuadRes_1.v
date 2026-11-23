Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith Init.Nat.
From Stdlib Require Import Sorting.Permutation.
Import List.ListNotations.
Require Import Misc Primes.

Require Import RingLike.Core.
Require Import RingLike.IterAdd.
Require Import RingLike.IterMul.
Require Import RingLike.Nat_algebra.
Require Import RingLike.PermutationFun.

Theorem fold_iter_list : ∀ {A B} (f : A → B → A) l d,
  List.fold_left f l d = Utils.iter_list l f d.
Proof. easy. Qed.

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

Theorem fold_iter_seq_succ_l : ∀ A b len f (d : A),
  Utils.iter_list (List.seq (S b) (S len - 1)) f d =
    Utils.iter_seq (S b) (b + len) f d.
Proof.
intros.
rewrite fold_iter_seq; cbn.
now do 2 rewrite Nat.sub_0_r.
Qed.

Theorem fold_iter_seq_1 : ∀ A len f (d : A),
  Utils.iter_list (List.seq 1 len) f d = Utils.iter_seq 1 len f d.
Proof.
intros.
progress unfold Utils.iter_seq.
now rewrite Nat_sub_succ_1.
Qed.

Theorem fold_iter_seq_1_succ_sub : ∀ A len f (d : A),
  Utils.iter_list (List.seq 1 (S len - 1)) f d = Utils.iter_seq 1 len f d.
Proof. easy. Qed.

Theorem if_mul_negb :
  ∀ a (b : bool) c d e,
  (if b then a * (if negb b then c else d) else e) =
  (if b then a * d else e).
Proof. now intros; destruct b. Qed.

Theorem Nat_2_mul_2_eq_4 : 2 * 2 = 4.
Proof. easy. Qed.

Theorem Nat_mul_2_l : ∀ a, 2 * a = a + a.
Proof. flia. Qed.

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

Theorem Nat_eq_pow_1 : ∀ a b, a ^ b = 1 → a = 1 ∨ b = 0.
Proof.
intros * Hab.
destruct b; [ now right | left ].
cbn in Hab.
now apply Nat.eq_mul_1 in Hab.
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

Theorem Nat_add_if_distr_l :
  ∀ a (b : bool) c d, (a + if b then c else d) = if b then a + c else a + d.
Proof. now intros; destruct b. Qed.

Theorem Nat_mul_if_distr_l :
  ∀ a (b : bool) c d, (a * if b then c else d) = if b then a * c else a * d.
Proof. now intros; destruct b. Qed.

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

Theorem List_fold_left_const :
  ∀ A B (b : A) (l : list B), List.fold_left (λ a _, a) l b = b.
Proof. now intros; induction l. Qed.

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

Theorem summation_list_map :
  ∀ {A B} (f : A → B) (g : B → _) l,
  ∑ (j ∈ List.map f l), g j = ∑ (i ∈ l), g (f i).
Proof.
intros.
unfold Utils.iter_list.
now rewrite List_fold_left_map.
Qed.

(* Euler criterion *)

Theorem permutation_map_if_lt :
  ∀ n f,
  (∀ i, i < n → f i < n)
  → (∀ i j, i < j < n → f i ≠ f j)
  → Permutation (List.seq 0 n)
    (ListDef.map (λ i, if lt_dec i n then f i else i) (List.seq 0 n)).
Proof.
intros * Hn Hf.
apply Permutation_sym.
apply nat_bijection_Permutation. {
  intros i Hi; cbn.
  destruct (lt_dec i n) as [Hin| Hin]; [ | easy ].
  now apply Hn.
} {
  intros i j Hfij; cbn in Hfij.
  destruct (lt_dec i n) as [Hin| Hin]. {
    destruct (lt_dec j n) as [Hjn| Hjn]. {
      destruct (lt_dec i j) as [Hij| Hij]. {
        now specialize (Hf i j (conj Hij Hjn)).
      } {
        apply Nat.nlt_ge in Hij.
        destruct (Nat.eq_dec i j) as [Heij| Heij]; [ easy | ].
        assert (H : j < i) by flia Hij Heij.
        specialize (Hf j i (conj H Hin)).
        now symmetry in Hfij.
      }
    } {
      subst j.
      now specialize (Hn _ Hin).
    }
  } {
    destruct (lt_dec j n) as [Hjn| Hjn]; [ | easy ].
    subst i.
    now specialize (Hn _ Hjn).
  }
}
Qed.

Theorem all_different_exist : ∀ f n,
  (∀ i, i < n → f i < n)
  → (∀ i j, i < j < n → f i ≠ f j)
  → ∀ a, a < n → ∃ x, f x = a.
Proof.
intros * Hn Hf * Han.
remember (List.seq 0 n) as l eqn:Hl.
set (g := λ i, if lt_dec i n then f i else i).
assert (Hperm : Permutation l (List.map g l)). {
  subst l g.
  now apply permutation_map_if_lt.
}
specialize (Permutation_in a Hperm) as H1.
assert (H : a ∈ l). {
  subst l.
  apply List.in_seq; flia Han.
}
specialize (H1 H); clear H.
subst g; cbn in H1.
apply List.in_map_iff in H1.
destruct H1 as (x & Hax & Hx).
destruct (lt_dec x n) as [Hxn| Hxn]; [ now exists x | now subst x ].
Qed.

(* https://proofwiki.org/wiki/Euler%27s_Criterion *)
(* The congruence 𝑏𝑥≡𝑎(mod𝑝) has (modulo 𝑝) a unique solution 𝑏′ by Solution
   of Linear Congruence. *)

Theorem congruence_inverse_has_unique_solution :
  ∀ p a,
  0 < a < p
  → ∀ b, coprimes b p
  → ∃! b', (b' < p ∧ (b * b') mod p = a).
Proof.
intros * (Ha, Hap) * Hcp.
assert (Hpz : p ≠ 0) by now intros H; subst p.
apply Nat.neq_0_lt_0 in Ha.
specialize (coprimes_all_different_multiples b p Hcp) as H1.
specialize (not_forall_in_interv_imp_exist 1 (p - 1)) as H2.
specialize (H2 (λ b', (b * b') mod p = a)).
cbn in H2.
assert (H : ∀ n, Decidable.decidable ((b * n) mod p = a)). {
  intros n.
  apply Nat.eq_decidable.
}
specialize (H2 H); clear H.
assert (H : 1 ≤ p - 1). {
  destruct p; [ easy | ].
  destruct p; [ flia Ha Hap | flia ].
}
specialize (H2 H); clear H.
assert (Hb' : ¬ (∀ b', (b * b') mod p ≠ a)). {
  move H1 at bottom.
  intros H3.
  specialize (all_different_exist (λ b', (b' * b) mod p)) as H4.
  cbn in H4.
  specialize (H4 p).
  assert (H : ∀ i, i < p → (i * b) mod p < p). {
    intros.
    now apply Nat.mod_upper_bound.
  }
  specialize (H4 H H1 a Hap); clear H.
  destruct H4 as (b', Hb').
  specialize (H3 b').
  now rewrite Nat.mul_comm in H3.
}
assert (H : ¬ (∀ n : nat, 1 ≤ n ≤ p - 1 → (b * n) mod p ≠ a)). {
  intros H; apply Hb'; intros b'.
  destruct (Nat.eq_dec (b' mod p) 0) as [Hb'z| Hb'z]. {
    rewrite <- Nat.Div0.mul_mod_idemp_r.
    rewrite Hb'z, Nat.mul_0_r; cbn.
    rewrite Nat.Div0.mod_0_l.
    now apply Nat.neq_sym.
  }
  rewrite <- Nat.Div0.mul_mod_idemp_r.
  apply H.
  split; [ flia Hb'z | ].
  rewrite Nat.sub_1_r.
  apply Nat.lt_le_pred.
  now apply Nat.mod_upper_bound.
}
specialize (H2 H); clear H.
destruct H2 as (b', H2).
exists (b' mod p).
split. {
  split; [ now apply Nat.mod_upper_bound | ].
  now rewrite Nat.Div0.mul_mod_idemp_r.
} {
  intros x (Hxp & Hxa).
  rewrite <- Nat.Div0.mul_mod_idemp_r in H2.
  rewrite <- H2 in Hxa.
  destruct (le_dec (b' mod p) x) as [Hbx| Hbx]. {
    apply Nat_mul_mod_cancel_l in Hxa; [ | easy ].
    rewrite Nat.Div0.mod_mod in Hxa.
    rewrite <- Hxa.
    now apply Nat.mod_small.
  } {
    apply Nat.nle_gt in Hbx.
    symmetry in Hxa.
    apply Nat_mul_mod_cancel_l in Hxa; [ | easy ].
    rewrite Nat.Div0.mod_mod in Hxa.
    symmetry in Hxa.
    now rewrite Nat.mod_small in Hxa.
  }
}
Qed.

Theorem congruence_inverse_has_unique_different_solution :
  ∀ p a,
  prime p
  → 0 < a < p
  → (∀ n, 1 ≤ n ≤ p - 1 → n² mod p ≠ a)
  → ∀ b, 1 ≤ b < p
  → ∃! b' : nat, (b' < p ∧ (b * b') mod p = a ∧ b ≠ b').
Proof.
intros * Hp (Haz, Hap) Hnres.
apply Nat.neq_0_lt_0 in Haz.
intros b Hbp.
assert (Hbb : ∀ b, 1 ≤ b < p → ∃! b', (b' < p ∧ (b * b') mod p = a)). {
  clear b Hbp.
  intros b Hb.
  apply congruence_inverse_has_unique_solution; cycle 1. {
    progress unfold coprimes.
    rewrite Nat.gcd_comm.
    now apply eq_gcd_prime_small_1.
  }
  split; [ | easy ].
  now apply Nat.neq_0_lt_0.
}
specialize (Hbb b Hbp).
destruct Hbb as (b' & (H1 & H2) & H3).
exists b'.
split. {
  split; [ easy | ].
  split; [ easy | ].
  intros H; subst b'.
  revert H2.
  rewrite <- Nat.pow_2_r.
  apply Hnres; flia Hbp.
} {
  intros x' (Hx1 & Hx2 & Hx3).
  now apply H3.
}
Qed.

(* https://proofwiki.org/wiki/Euler%27s_Criterion *)
(* It follows that the residue classes {1,2,…,𝑝−1} modulo 𝑝 fall into
   (𝑝−1)/2 pairs 𝑏,𝑏′ such that 𝑏𝑏′≡𝑎(mod𝑝). *)

Theorem fact_pred_p_equiv :
  ∀ p a,
  prime p
  → 0 < a < p
  → (∀ n, 1 ≤ n ≤ p - 1 → n² mod p ≠ a)
  → fact (p - 1) ≡ a ^ ((p - 1) / 2) mod p.
Proof.
intros * Hp (Haz, Hap) Hnres.
assert
  (Hbb : ∀ b, 1 ≤ b < p → ∃! b', (b' < p ∧ (b * b') mod p = a ∧ b ≠ b')). {
  now apply congruence_inverse_has_unique_different_solution.
}
rewrite fact_eq_fold_left.
(* very similar with eq_fold_left_mul_seq_2_prime_sub_3_1;
   perhaps a common lemma could be useful *)
specialize (List.seq_NoDup (p - 1) 1) as Hnd.
remember (List.seq 1 (p - 1)) as l eqn:Hl.
assert
  (Hij : ∀ i, i ∈ l →
   ∃j, j ∈ l ∧ i ≠ j ∧ (i * j) mod p = a ∧
    ∀ k, k ∈ l → k ≠ i → (k * j) mod p ≠ a). {
  intros i Hi.
  specialize (Hbb i) as H1.
  assert (H : 1 ≤ i < p). {
    subst l.
    apply List.in_seq in Hi; flia Hi.
  }
  specialize (H1 H); clear H.
  destruct H1 as (j & (Hj1 & Hj2 & Hj3) & Hj4).
  exists j.
  split. {
    subst l; apply List.in_seq.
    split; [ | flia Hj1 ].
    destruct j; [ | flia ].
    symmetry in Hj2.
    apply Nat.neq_0_lt_0 in Haz.
    now rewrite Nat.mul_0_r, Nat.Div0.mod_0_l in Hj2.
  }
  split; [ easy | ].
  split; [ easy | ].
  intros k Hk Hki.
  specialize (Hj4 k) as H1.
  destruct (Nat.eq_dec ((i * k) mod p) a) as [Hka| Hka]. {
    assert (H : k < p ∧ (i * k) mod p = a ∧ i ≠ k). {
      apply Nat.neq_sym in Hki.
      split; [ | easy ].
      rewrite Hl in Hk.
      apply List.in_seq in Hk.
      flia Hk.
    }
    specialize (H1 H); clear H.
    subst k.
    rewrite <- Nat.pow_2_r.
    apply Hnres.
    split; [ | flia Hj1 ].
    destruct j; [ | flia ].
    symmetry in Hj2.
    apply Nat.neq_0_lt_0 in Haz.
    now rewrite Nat.mul_0_r, Nat.Div0.mod_0_l in Hj2.
  } {
    intros Hkj.
    move Hj2 at bottom.
    rewrite <- Hkj in Hj2.
    destruct (le_dec k i) as [Hik| Hik]. {
      apply Nat_mul_mod_cancel_r in Hj2. 2: {
        rewrite Nat.gcd_comm.
        apply eq_gcd_prime_small_1; [ easy | ].
        split; [ | easy ].
        destruct j; [ | flia ].
        rewrite Nat.mul_0_r, Nat.Div0.mod_0_l in Hkj.
        apply Nat.neq_0_lt_0 in Haz.
        now symmetry in Hkj.
      }
      rewrite Nat.mod_small in Hj2. 2: {
        rewrite Hl in Hi; apply List.in_seq in Hi; flia Hi.
      }
      rewrite Nat.mod_small in Hj2. 2: {
        rewrite Hl in Hk; apply List.in_seq in Hk; flia Hk.
      }
      now symmetry in Hj2.
    } {
      apply Nat.nle_gt in Hik.
      symmetry in Hj2.
      apply Nat_mul_mod_cancel_r in Hj2. 2: {
        rewrite Nat.gcd_comm.
        apply eq_gcd_prime_small_1; [ easy | ].
        split; [ | easy ].
        destruct j; [ | flia ].
        rewrite Nat.mul_0_r, Nat.Div0.mod_0_l in Hkj.
        apply Nat.neq_0_lt_0 in Haz.
        now symmetry in Hkj.
      }
      rewrite Hl in Hk; apply List.in_seq in Hk.
      rewrite Nat.mod_small in Hj2; [ | flia Hk ].
      rewrite Nat.mod_small in Hj2; [ flia Hj2 Hik | ].
      rewrite Hl in Hi; apply List.in_seq in Hi; flia Hi.
    }
  }
}
clear Hbb Hnres.
replace (p - 1) with (length l). 2: {
  now subst l; rewrite List.length_seq.
}
clear Hl.
remember (length l) as len eqn:Hlen; symmetry in Hlen.
revert l Hnd Hij Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len. {
  apply List.length_zero_iff_nil in Hlen.
  now rewrite Hlen.
}
destruct l as [| b l]; [ easy | ].
specialize (Hij b (or_introl (eq_refl _))) as H1.
destruct H1 as (i2 & Hi2l & Hai2 & Hai2p & Hk).
destruct Hi2l as [Hi2l| Hi2l]; [ easy | ].
specialize (List.in_split i2 l Hi2l) as (l1 & l2 & Hll).
rewrite Hll.
cbn - [ "/" ]; rewrite Nat.add_0_r.
rewrite List.fold_left_app; cbn - [ "/" ].
rewrite List_fold_left_mul_from_1.
rewrite Nat.mul_shuffle0, Nat.mul_comm.
rewrite List_fold_left_mul_from_1.
do 2 rewrite Nat.mul_assoc.
remember (i2 * 2) as x.
rewrite <- Nat.mul_assoc; subst x.
rewrite <- Nat.Div0.mul_mod_idemp_l.
rewrite (Nat.mul_comm i2).
rewrite Hai2p.
replace (S len) with (len - 1 + 1 * 2). 2: {
  destruct len; [ | flia ].
  cbn in Hlen.
  apply Nat.succ_inj in Hlen.
  rewrite Hll in Hlen.
  rewrite List.length_app in Hlen; cbn in Hlen.
  now rewrite Nat.add_comm in Hlen.
}
rewrite Nat.div_add; [ | easy ].
rewrite Nat.add_comm, Nat.pow_add_r, Nat.pow_1_r.
rewrite <- Nat.Div0.mul_mod_idemp_r.
rewrite <- (Nat.Div0.mul_mod_idemp_r _ (a ^ _)).
f_equal; f_equal.
rewrite Nat.mul_comm.
rewrite List_fold_left_mul_assoc, Nat.mul_1_l.
rewrite <- List.fold_left_app.
apply (IHlen (len - 1)); [ flia | | | ]. 3: {
  cbn in Hlen.
  apply Nat.succ_inj in Hlen.
  rewrite <- Hlen, Hll.
  do 2 rewrite List.length_app.
  cbn; flia.
} {
  apply List.NoDup_cons_iff in Hnd.
  destruct Hnd as (_, Hnd).
  rewrite Hll in Hnd.
  now apply List.NoDup_remove_1 in Hnd.
}
intros i Hi.
specialize (Hij i) as H1.
assert (H : i ∈ b :: l). {
  right; rewrite Hll.
  apply List.in_app_or in Hi.
  apply List.in_or_app.
  destruct Hi as [Hi| Hi]; [ now left | now right; right ].
}
specialize (H1 H); clear H.
destruct H1 as (j & Hjall & Hinj & Hijp & Hk').
exists j.
split. {
  destruct Hjall as [Hjall| Hjall]. {
    subst j; exfalso.
    specialize (Hk' i2) as H1.
    assert (H : i2 ∈ b :: l). {
      now rewrite Hll; right; apply List.in_or_app; right; left.
    }
    specialize (H1 H); clear H.
    assert (H : i2 ≠ i). {
      intros H; subst i2.
      move Hnd at bottom; move Hi at bottom.
      apply List.NoDup_cons_iff in Hnd.
      destruct Hnd as (_, Hnd).
      rewrite Hll in Hnd.
      now apply List.NoDup_remove_2 in Hnd.
    }
    specialize (H1 H).
    now rewrite Nat.mul_comm in H1.
  }
  rewrite Hll in Hjall.
  apply List.in_app_or in Hjall.
  apply List.in_or_app.
  destruct Hjall as [Hjall| Hjall]; [ now left | ].
  destruct Hjall as [Hjall| Hjall]; [ | now right ].
  subst j.
  destruct (Nat.eq_dec b i) as [Hbi| Hbi]. {
    subst i.
    move Hnd at bottom.
    apply List.NoDup_cons_iff in Hnd.
    destruct Hnd as (Hnd, _).
    exfalso; apply Hnd; clear Hnd.
    rewrite Hll.
    apply List.in_app_or in Hi.
    apply List.in_or_app.
    destruct Hi as [Hi| Hi]; [ now left | now right; right ].
  }
  now specialize (Hk' b (or_introl eq_refl) Hbi) as H2.
}
split; [ easy | ].
split; [ easy | ].
intros k Hkll Hki.
apply Hk'; [ | easy ].
right.
rewrite Hll.
apply List.in_app_or in Hkll.
apply List.in_or_app.
destruct Hkll as [Hkll| Hkll]; [ now left | now right; right ].
Qed.

(**)

Fixpoint nth_sqrt_mod_loop cnt n a p i :=
  match cnt with
  | 0 => None
  | S cnt' =>
      if i ^ n mod p =? a mod p then Some i
      else nth_sqrt_mod_loop cnt' n a p (S i)
  end.

Definition nth_sqrt_mod n a p := nth_sqrt_mod_loop p n a p 0.
Definition sqrt_mod a p := nth_sqrt_mod_loop p 2 a p 0.

Definition Legendre_symbol a p :=
  if p =? 2 then 1
  else if a mod p =? 0 then 0
  else
    match sqrt_mod a p with
    | Some _ => 1
    | None => p - 1
    end.

Theorem eq_sqrt_mod_loop_Some :
  ∀ cnt n a b p i,
  nth_sqrt_mod_loop cnt n a p i = Some b
  → i ≤ b < i + cnt ∧ b ^ n ≡ a mod p.
Proof.
intros * Hsm.
revert i Hsm.
induction cnt; intros; [ easy | ].
cbn - [ "*" ] in Hsm.
remember ((i ^ n) mod p =? a mod p) as e eqn:He.
symmetry in He.
destruct e; cycle 1. {
  apply IHcnt in Hsm.
  split; [ | easy ].
  rewrite Nat.add_succ_r, <- Nat.add_succ_l.
  split; [ flia Hsm | easy ].
}
injection Hsm; clear Hsm; intros; subst b.
apply Nat.eqb_eq in He.
split; [ flia | easy ].
Qed.

Theorem eq_sqrt_mod_Some :
  ∀ a b p,
  sqrt_mod a p = Some b
  → b < p ∧ b² ≡ a mod p.
Proof.
intros * Hsm.
now apply eq_sqrt_mod_loop_Some in Hsm.
Qed.

Theorem eq_sqrt_mod_loop_None :
  ∀ cnt n a i p,
  a ≢ 0 mod p
  → nth_sqrt_mod_loop cnt n a p i = None
  → ∀ b, i ≤ b < i + cnt → b ^ n ≢ a mod p.
Proof.
intros * Hap Hsm * Hib Hbb.
symmetry in Hbb.
revert i Hib Hsm.
induction cnt; intros; [ flia Hib | ].
cbn in Hsm.
remember ((i ^ n) mod p =? a mod p) as sip eqn:Hsip.
symmetry in Hsip.
destruct sip; [ easy | ].
destruct (Nat.eq_dec i b) as [Hib1| Hib1]; cycle 1. {
  apply IHcnt in Hsm; [ easy | ].
  split; [ | flia Hib ].
  flia Hib Hib1.
}
subst i.
clear Hib.
rewrite Hbb in Hsip.
now rewrite Nat.eqb_refl in Hsip.
Qed.

Theorem eq_sqrt_mod_None :
  ∀ a p,
  p ≠ 0
  → sqrt_mod a p = None
  → ∀ b, b² ≢ a mod p.
Proof.
intros * Hpz Hsm * Hbb.
rewrite Nat.pow_2_r in Hbb.
apply eq_sqrt_mod_loop_None with (b := b mod p) in Hsm. {
  rewrite Nat.pow_2_r in Hsm.
  rewrite Nat.Div0.mul_mod_idemp_l in Hsm.
  rewrite Nat.Div0.mul_mod_idemp_r in Hsm.
  easy.
} {
  intros H.
  rewrite Nat.Div0.mod_0_l in H.
  rewrite H in Hbb.
  progress unfold sqrt_mod in Hsm.
  destruct p; [ easy | ].
  cbn - [ "mod" ] in Hsm.
  remember (_ =? _) as x eqn:Hx.
  symmetry in Hx.
  destruct x; [ easy | ].
  rewrite H in Hx.
  apply Nat.eqb_neq in Hx.
  now rewrite Nat.Div0.mod_0_l in Hx.
}
split; [ easy | ].
now apply Nat.mod_upper_bound.
Qed.

Theorem sqrt_mod_loop_mod :
  ∀ cnt n a p i,
  nth_sqrt_mod_loop cnt n a p i = nth_sqrt_mod_loop cnt n (a mod p) p i.
Proof.
intros.
revert i.
induction cnt; intros; [ easy | cbn ].
rewrite Nat.Div0.mod_mod.
now rewrite IHcnt.
Qed.

Theorem sqrt_mod_mod : ∀ p a, sqrt_mod a p = sqrt_mod (a mod p) p.
Proof.
intros.
apply sqrt_mod_loop_mod.
Qed.

Theorem Euler_criterion : ∀ p,
  prime p
  → ∀ a, Legendre_symbol a p ≡ a ^ ((p - 1) / 2) mod p.
Proof.
intros * Hp *.
symmetry.
destruct (Nat.eq_dec p 2) as [Hp2| Hp2]; [ now subst p | ].
progress unfold Legendre_symbol.
generalize Hp2; intros H.
apply Nat.eqb_neq in H; rewrite H; clear H.
destruct (Nat.eq_dec (a mod p) 0) as [Haz| Haz]. {
  rewrite <- Nat_mod_pow_mod, Haz; cbn - [ "/" ].
  destruct p; [ easy | ].
  destruct p; [ easy | ].
  destruct p; [ easy | ].
  cbn - [ "/" "mod" ].
  rewrite Nat.pow_0_l; cycle 1. {
    intros H.
    apply Nat.div_small_iff in H; [ | easy ].
    flia H.
  }
  now rewrite Nat.Div0.mod_0_l.
}
rewrite <- Nat_mod_pow_mod.
generalize Haz; intros H.
apply Nat.eqb_neq in H; rewrite H; clear H.
rewrite sqrt_mod_mod.
remember (a mod p) as b eqn:Hb.
symmetry in Hb.
assert (Hap : b < p). {
  subst b; apply Nat.mod_upper_bound.
  now intros H; subst p.
}
clear a Hb; rename b into a.
remember (sqrt_mod a p) as sm eqn:Hsm.
symmetry in Hsm.
destruct sm as [b| ]. {
  apply eq_sqrt_mod_Some in Hsm.
  cbn in Hsm.
  rewrite Nat.mul_1_r in Hsm.
  destruct Hsm as (Hb, Hsm).
  rewrite <- Nat_mod_pow_mod.
  rewrite <- Hsm.
  rewrite Nat_mod_pow_mod.
  rewrite <- Nat.pow_2_r.
  rewrite <- Nat.pow_mul_r.
  rewrite <- (proj2 (Nat.Div0.div_exact _ _)). {
    rewrite Fermat_little; [ | easy | ]. {
      symmetry.
      apply Nat.mod_1_l.
      now apply prime_ge_2.
    }
    split; [ | easy ].
    destruct b; [ | now apply -> Nat.succ_le_mono ].
    rewrite Nat.mod_small in Hsm; [ | easy ].
    symmetry in Hsm.
    now rewrite Nat.mod_small in Hsm.
  }
  specialize (odd_prime _ Hp Hp2) as H1.
  specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H2.
  rewrite H1 in H2.
  rewrite H2, Nat.add_sub, Nat.mul_comm.
  apply Nat.Div0.mod_mul.
} {
  assert (Hpz : p ≠ 0) by flia Hap.
  specialize (eq_sqrt_mod_None a p Hpz Hsm) as H3.
  assert (Hzap : 0 < a < p) by flia Haz Hap.
  specialize (fact_pred_p_equiv p a Hp Hzap) as H1.
  assert (H : ∀ n, 1 ≤ n ≤ p - 1 → n² mod p ≠ a). {
    intros n Hn.
    rewrite <- (Nat.mod_small a p); [ | easy ].
    apply H3.
  }
  specialize (H1 H); clear H.
  rewrite <- H1.
  rewrite (Nat.mod_small (p - 1)); [ | flia Hap ].
  apply Wilson; [ | easy ].
  now apply prime_ge_2.
}
Qed.

(* Gauss Lemma *)

Definition nb_of_mult_gt_half a p :=
  List.length
    (List.filter (λ m, (p - 1) / 2 <? ((m * a) mod p))
       (List.seq 1 ((p - 1) / 2))).

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

Definition is_quadratic_residue a p := Legendre_symbol a p =? 1.

(*
Compute (let p := 29 in List.map (λ a, (sqrt_mod a p, a)) (List.seq 0 p)).

Compute (let n := 3 in map (λ p, (p, List.filter (λ a, match nth_sqrt_mod n a p with Some _ => true | None => false end) (List.seq 1 (p - 1)))) (List.seq 1 20)).

1,2,3,5,6,10,11,15,17

Compute (let p := 29 in List.filter (λ a, match sqrt_mod a p with Some _ => true | None => false end) (List.seq 1 (p - 1))).
Compute (let p := 29 in List.filter (λ a, (nb_of_mult_gt_half a p mod 2 =? 0)) (seq 1 (p - 1))).
Compute (let p := 29 in List.filter (λ a, is_quadratic_residue a p) (seq 1 p)).
*)

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

Theorem Legendre_symbol_mod_r :
  ∀ a p, Legendre_symbol a p = Legendre_symbol (a mod p) p.
Proof.
intros.
progress unfold Legendre_symbol.
rewrite Nat.Div0.mod_mod.
now rewrite sqrt_mod_mod.
Qed.

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

Theorem Nat_div_less_small : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a / b = n.
Proof.
intros * Hab.
assert (Hb : b ≠ 0). {
  now intros Hb; rewrite Hb, (Nat.mul_comm (n + 1)) in Hab.
}
replace a with (a - n * b + n * b) at 1 by now apply Nat.sub_add.
rewrite Nat.div_add; [ | easy ].
replace n with (0 + n) at 3 by easy; f_equal.
apply Nat.div_small.
apply Nat.add_lt_mono_r with (p := n * b).
rewrite Nat.add_comm in Hab; cbn in Hab.
now rewrite Nat.sub_add.
Qed.

Theorem Nat_eq_mul_2_div_mod_to_bool :
  ∀ a n,
  n ≠ 0
  → (2 * a / n) mod 2 = Nat.b2n ((n - 1) / 2 <? a mod n).
Proof.
intros * Hnz.
remember ((n - 1) / 2 <? a mod n) as b eqn:Hb; symmetry in Hb.
destruct b; cbn - [ "*" "mod" ]. {
  apply Nat.ltb_lt in Hb.
  specialize (Nat.div_mod a n Hnz) as H1.
  rewrite H1.
  rewrite Nat.mul_add_distr_l.
  rewrite (Nat.mul_comm n), Nat.mul_assoc.
  rewrite Nat.div_add_l; [ | easy ].
  rewrite Nat_mod_add_l_mul_l.
  apply Nat_eq_mod_1.
  split. {
    apply Nat.Lcm0.mod_divide.
    rewrite (Nat_div_less_small 1); [ now exists 0 | ].
    rewrite Nat.mul_1_l.
    cbn - [ "*" ].
    split. {
      apply Nat_div_lt_mul in Hb; [ | easy ].
      apply Nat.lt_sub_lt_add_l in Hb.
      now apply -> Nat.lt_succ_r in Hb.
    }
    apply Nat.mul_lt_mono_pos_l; [ easy | ].
    now apply Nat.mod_upper_bound.
  }
  split; [ | easy ].
  intros H2.
  apply Nat.div_small_iff in H2; [ | easy ].
  apply Nat.nle_gt in H2.
  apply H2; clear H2.
  apply Nat_div_lt_mul in Hb; [ | easy ].
  apply Nat.lt_sub_lt_add_l in Hb.
  now apply -> Nat.lt_succ_r in Hb.
} {
  apply Nat.ltb_ge in Hb.
  apply Nat.Lcm0.mod_divide.
  specialize (Nat.div_mod a n Hnz) as H1.
  rewrite H1.
  rewrite Nat.mul_add_distr_l.
  rewrite (Nat.mul_comm n), Nat.mul_assoc.
  rewrite Nat.div_add_l; [ | easy ].
  apply Nat.divide_add_r; [ now apply Nat.divide_mul_l | ].
  rewrite Nat.div_small; [ now exists 0 | ].
  apply (Nat.mul_le_mono_l _ _ 2) in Hb.
  eapply Nat.le_lt_trans; [ apply Hb | ].
  eapply Nat.le_lt_trans; [ apply Nat.Div0.mul_div_le | ].
  flia Hnz.
}
Qed.

Theorem fold_left_op_fun_from_d : ∀ {T A} d op a l (f : A → _)
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  List.fold_left (λ (c : T) i, op c (f i)) l a =
  op a (List.fold_left (λ (c : T) i, op c (f i)) l d).
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply op_d_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite op_d_l.
apply op_assoc.
Qed.

Theorem iter_list_cons : ∀ A B d op (a : B) la f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  Utils.iter_list (a :: la) (λ (c : A) i, op c (f i)) d =
  op (f a) (Utils.iter_list la (λ (c : A) i, op c (f i)) d).
Proof.
intros.
progress unfold Utils.iter_list; cbn.
rewrite op_d_l.
now apply (fold_left_op_fun_from_d d).
Qed.

(*
Theorem summation_list_cons : ∀ A (a : A) la f,
  ∑ (i ∈ a :: la), f i = f a + ∑ (i ∈ la), f i.
Proof.
intros.
apply iter_list_cons.
apply Nat.add_0_l.
apply Nat.add_0_r.
apply Nat.add_assoc.
Qed.

Theorem product_list_cons : ∀ A (a : A) la f,
  ∏ (i ∈ a :: la), f i = f a * ∏ (i ∈ la), f i.
Proof.
intros.
apply iter_list_cons.
apply Nat.mul_1_l.
apply Nat.mul_1_r.
apply Nat.mul_assoc.
Qed.
*)

Theorem Nat_pow_summation_r :
  ∀ a b e f, a ^ (∑ (i = b, e), f i) = ∏ (i = b, e), a ^ f i.
Proof.
intros.
progress unfold Utils.iter_seq.
remember (S e - b) as l eqn:Hl; clear Hl.
revert b.
induction l as [| c]; intros; [ easy | ].
cbn.
rewrite rngl_summation_list_cons.
rewrite rngl_product_list_cons.
rewrite Nat.pow_add_r.
rewrite nat_pow_of_rngl_power.
progress unfold rngl_mul.
cbn.
progress f_equal.
apply IHc.
Qed.

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

Theorem nat_leb_rngl_leb : ∀ a b, (a <=? b) = (a ≤? b)%L.
Proof. easy. Qed.

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

Theorem Eisenstein_lemma' :
  ∀ a p, prime p → coprimes a p →
  nb_of_mult_gt_half a p ≡ (∑ (k = 1, (p - 1) / 2), 2 * k * a / p) mod 2.
Proof.
intros * Hp Hap.
assert (Hpz : p ≠ 0) by now intros H; subst p.
progress unfold coprimes in Hap.
remember ((p - 1) / 2) as h eqn:Hh.
move h before p.
rewrite summation_mod_idemp.
erewrite rngl_summation_eq_compat; cycle 1. {
  intros i Hi.
  rewrite <- Nat.mul_assoc.
  now rewrite (Nat_eq_mul_2_div_mod_to_bool _ _ Hpz).
}
cbn - [ nb_of_mult_gt_half "<?" "/" "mod" ].
rewrite Hh.
rewrite eq_nb_of_mult_gt_half_summation.
erewrite rngl_summation_eq_compat; [ easy | ].
intros i Hi.
now rewrite <- nat_ltb_rngl_ltb.
Qed.

Theorem summation_to_twice_plus_1 :
  ∀ e f,
  ∑ (i = 1, e), f (2 * i) =
  ∑ (i = 1, 2 * e + 1), if i mod 2 =? 0 then f i else 0.
Proof.
intros.
induction e; cbn - [ "*" "mod" rngl_zero rngl_add ]. {
  rewrite rngl_summation_empty; [ | easy ].
  now rewrite rngl_summation_only_one.
}
rewrite rngl_summation_split_last; [ | now apply -> Nat.succ_le_mono ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat; cycle 1. {
  intros i Hi.
  now rewrite Nat_sub_succ_1.
}
cbn - [ "*" "mod" ].
rewrite IHe.
symmetry.
rewrite rngl_summation_split_last; cycle 1. {
  rewrite Nat.add_1_r.
  now apply -> Nat.succ_le_mono.
}
rewrite (rngl_summation_shift 1); cycle 1. {
  split; [ now apply -> Nat.succ_le_mono | ].
  rewrite Nat.add_1_r.
  now do 2 apply -> Nat.succ_le_mono.
}
rewrite Nat_sub_succ_1.
rewrite Nat.add_sub.
rewrite Nat_mod_add_l_mul_l.
rewrite Nat.mod_small; [ | now apply -> Nat.succ_lt_mono ].
cbn - [ "*" "mod" ].
rewrite Nat.add_0_r.
rewrite Nat.mul_succ_r.
rewrite rngl_summation_split_last; cycle 1. {
  rewrite Nat.add_comm; cbn.
  now apply -> Nat.succ_le_mono.
}
rewrite Nat.sub_0_r.
rewrite (rngl_summation_shift 1); cycle 1. {
  split; [ now apply -> Nat.succ_le_mono | ].
  rewrite Nat.add_comm; cbn.
  now do 2 apply -> Nat.succ_le_mono.
}
rewrite Nat_sub_succ_1.
rewrite <- Nat.add_sub_assoc; cycle 1. {
  now apply -> Nat.succ_le_mono.
}
rewrite Nat_sub_succ_1.
rewrite Nat_mod_add_l_mul_l.
rewrite Nat.Div0.mod_same.
cbn - [ "*" "mod" "/" "-" ].
f_equal; [ | now rewrite Nat.mul_succ_r ].
apply rngl_summation_eq_compat.
intros i Hi.
rewrite Nat.sub_0_r.
now rewrite Nat_sub_succ_1.
Qed.

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

Theorem Nat_add_sub_eq_l_mod :
  ∀ a b c d, b ≤ a → b + c ≡ a mod d → a - b ≡ c mod d.
Proof.
intros * Hba Hbca.
apply (Nat_add_cancel_r_mod _ _ b).
rewrite Nat.sub_add; [ | easy ].
now symmetry; rewrite Nat.add_comm.
Qed.

Theorem Nat_min_if_then_else :
  ∀ a b, min a b = if a <=? b then a else b.
Proof.
intros.
remember (a <=? b) as ab eqn:Hab; symmetry in Hab.
destruct ab. {
  apply Nat.leb_le in Hab.
  now apply Nat.min_l.
} {
  apply Nat.leb_gt, Nat.lt_le_incl in Hab.
  now apply Nat.min_r.
}
Qed.

Theorem Nat_leb_sub_r : ∀ a b c, (c ≤ b) → (a <=? b - c) = (a + c <=? b).
Proof.
intros * Hcb.
remember (_ <=? _) as x eqn:Hx; symmetry in Hx.
symmetry.
destruct x. {
  apply Nat.leb_le in Hx.
  apply Nat.leb_le.
  apply (Nat.add_le_mono_r _ _ c) in Hx.
  now rewrite Nat.sub_add in Hx.
} {
  apply Bool.not_true_iff_false in Hx.
  apply Bool.not_true_iff_false.
  intros H; apply Hx; clear Hx; rename H into Hx.
  apply Nat.leb_le in Hx.
  apply Nat.leb_le.
  now apply Nat.le_add_le_sub_r.
}
Qed.

Theorem Nat_leb_mul_l : ∀ a b c,
  a ≠ 0 → Nat.divide a c → (a * b <=? c) = (b <=? c / a).
Proof.
intros * Haz Hac.
remember (_ <=? _) as x eqn:Hx; symmetry in Hx.
symmetry.
destruct x. {
  apply Nat.leb_le in Hx.
  apply Nat.leb_le.
  apply (Nat.mul_le_mono_pos_l _ _ a). {
    now apply Nat.neq_0_lt_0.
  }
  rewrite <- Nat.Lcm0.divide_div_mul_exact; [ | easy ].
  now rewrite (Nat.mul_comm _ c), Nat.div_mul.
} {
  apply Bool.not_true_iff_false in Hx.
  apply Bool.not_true_iff_false.
  intros H; apply Hx; clear Hx; rename H into Hx.
  apply Nat.leb_le in Hx.
  apply Nat.leb_le.
  apply (Nat.mul_le_mono_pos_l _ _ a) in Hx; cycle 1. {
    now apply Nat.neq_0_lt_0.
  }
  rewrite <- Nat.Lcm0.divide_div_mul_exact in Hx; [ | easy ].
  now rewrite (Nat.mul_comm _ c), Nat.div_mul in Hx.
}
Qed.

Theorem Nat_leb_neq_ltb : ∀ a b, a ≠ b → (a <=? b) = (a <? b).
Proof.
intros * Hab.
remember (_ <? _) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Nat.ltb_lt in Hx.
  apply Nat.leb_le.
  now apply Nat.lt_le_incl.
} {
  apply Bool.not_true_iff_false in Hx.
  apply Bool.not_true_iff_false.
  intros H; apply Hx; clear Hx; rename H into Hx.
  apply Nat.leb_le in Hx.
  apply Nat.ltb_lt.
  now apply Nat_le_neq_lt.
}
Qed.

Theorem Nat_ltb_leb_pred: ∀ a b, b ≠ 0 → (a <? b) = (a <=? Nat.pred b).
Proof.
intros * Hbz.
remember (_ <=? _) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Nat.leb_le in Hx.
  apply Nat.ltb_lt.
  apply (Nat.le_lt_trans _ (Nat.pred b)); [ easy | ].
  now apply Nat.lt_pred_l.
} {
  apply Bool.not_true_iff_false in Hx.
  apply Bool.not_true_iff_false.
  intros H; apply Hx; clear Hx; rename H into Hx.
  apply Nat.ltb_lt in Hx.
  apply Nat.leb_le.
  now apply Nat.lt_le_pred.
}
Qed.

Theorem abs_eq_min : ∀ a b, Nat.Odd b → abs a b = min a (b - a).
Proof.
intros * Hb.
progress unfold abs.
rewrite Nat_min_if_then_else.
remember (a <=? _) as x eqn:Hx; symmetry in Hx.
remember (a <=? _) as y eqn:Hy in |-*; symmetry in Hy.
destruct x, y; [ easy | | | easy ]. {
  apply Nat.leb_le in Hx.
  apply Nat.leb_nle in Hy.
  exfalso; apply Hy; clear Hy.
  apply Nat.le_add_le_sub_l.
  apply (Nat.mul_le_mono_pos_r _ _ 2) in Hx; [ | easy ].
  rewrite <- Nat_mul_2_l, Nat.mul_comm.
  eapply Nat.le_trans; [ apply Hx | ].
  rewrite Nat.mul_comm.
  eapply Nat.le_trans.
  apply Nat.Div0.mul_div_le.
  apply Nat.le_sub_l.
} {
  apply Nat.leb_le in Hy.
  apply Nat.leb_gt in Hx.
  apply (Nat.add_le_mono_r _ _ a) in Hy.
  destruct (le_dec a b) as [Hab| Hab]. {
    rewrite Nat.sub_add in Hy; [ | easy ].
    rewrite <- Nat_mul_2_l, Nat.mul_comm in Hy.
    apply (Nat.mul_lt_mono_pos_l 2) in Hx; [ | easy ].
    rewrite <- Nat.Lcm0.divide_div_mul_exact in Hx; cycle 1. {
      destruct Hb as (m, Hm).
      rewrite Hm, Nat.add_sub.
      apply Nat.divide_factor_l.
    }
    rewrite Nat.mul_comm, Nat.div_mul in Hx; [ | easy ].
    apply Nat.lt_sub_lt_add_l in Hx.
    apply -> Nat.lt_succ_r in Hx.
    apply Nat.le_antisymm in Hx; [ | now rewrite Nat.mul_comm ].
    rewrite <- Hx.
    rewrite Nat_mul_2_l.
    apply Nat.add_sub.
  }
  apply Nat.nle_gt in Hab.
  rewrite (proj2 (Nat.sub_0_le b a)) in Hy; [ | now apply Nat.lt_le_incl ].
  cbn in Hy.
  apply Nat.le_add_le_sub_l in Hy.
  rewrite Nat.sub_diag in Hy.
  now apply Nat.le_0_r in Hy; subst a.
}
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

Theorem rngl_le_Nat_le : ∀ a b, (a ≤ b)%L ↔ (a ≤ b).
Proof.
intros.
apply Nat.leb_le.
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

Theorem Nat_even_mod_2 : ∀ x, Nat.even (x mod 2) = Nat.even x.
Proof.
intros.
remember (x mod 2) as x2 eqn:Hx2.
symmetry in Hx2.
symmetry.
destruct x2. {
  apply Nat.Div0.mod_divides in Hx2.
  destruct Hx2 as (c, Hx2); subst x.
  apply Nat.even_even.
}
destruct x2. {
  apply Nat_eq_mod_exists in Hx2.
  destruct Hx2 as (Hx2 & _).
  destruct Hx2 as (c, Hx2); subst x.
  rewrite Nat.mul_comm.
  apply Nat.even_odd.
}
specialize (Nat.mod_upper_bound x 2 (Nat.neq_succ_0 _))  as H1.
rewrite Hx2 in H1.
now do 2 apply Nat.succ_lt_mono in H1.
Qed.
