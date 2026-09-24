Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import Sorting.Permutation.
Import List.ListNotations.
Require Import Misc Primes.

Notation "a '²'" := (a ^ 2) (at level 1, format "a ²").

Notation "'∏' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c * g)%nat) 1%nat)
  (at level 35, i at level 0, b at level 60, e at level 60,
   right associativity,
   format "'[hv  ' ∏  ( i  =  b ,  e ) ,  '/' '[' g ']' ']'").
Notation "'∏' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, (c * g)%nat) 1%nat)
  (at level 35, i at level 0, l at level 60,
   right associativity,
   format "'[hv  ' ∏  ( i  ∈  l ) ,  '/' '[' g ']' ']'").

Theorem fold_iter_list : ∀ {A B} (f : A → B → A) l d,
  List.fold_left f l d = iter_list l f d.
Proof. easy. Qed.

Theorem fold_iter_seq : ∀ A b len f (d : A),
  iter_list (List.seq b len) f d =
    if b + len =? 0 then d
    else iter_seq b (b + len - 1) f d.
Proof.
intros.
progress unfold iter_seq.
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
  iter_list (List.seq (S b) (S len - 1)) f d =
    iter_seq (S b) (b + len) f d.
Proof.
intros.
rewrite fold_iter_seq; cbn.
now do 2 rewrite Nat.sub_0_r.
Qed.

Theorem fold_iter_seq_1 : ∀ A len f (d : A),
  iter_list (List.seq 1 len) f d = iter_seq 1 len f d.
Proof.
intros.
progress unfold iter_seq.
now rewrite Nat_sub_succ_1.
Qed.

Theorem fold_iter_seq_1_succ_sub : ∀ A len f (d : A),
  iter_list (List.seq 1 (S len - 1)) f d = iter_seq 1 len f d.
Proof. easy. Qed.

Theorem if_mul_negb :
  ∀ a (b : bool) c d e,
  (if b then a * (if negb b then c else d) else e) =
  (if b then a * d else e).
Proof. now intros; destruct b. Qed.

Theorem Nat_4_eq_2_mul_2 : 4 = 2 * 2.
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

Theorem Nat_eq_mod_exists : ∀ a b c, a mod b = c → ∃ k, a = k * b + c.
Proof.
intros * Habc.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  subst b.
  cbn in Habc; subst c.
  now exists 0.
}
exists (a / b).
rewrite Nat.mul_comm, <- Habc.
now apply Nat.div_mod.
Qed.

Theorem odd_prime_mod_4 : ∀ p, prime p → p ≠ 2 → p mod 4 = 1 ∨ p mod 4 = 3.
Proof.
intros * Hp Hp2.
remember (p mod 4) as p4 eqn:Hp4; symmetry in Hp4.
destruct p4. {
  apply Nat.Lcm0.mod_divide in Hp4.
  destruct Hp4 as (k, H); subst p.
  rewrite Nat_4_eq_2_mul_2, Nat.mul_assoc in Hp.
  apply prime_not_mul in Hp.
  destruct Hp as [Hp| ]; [ | easy ].
  now apply Nat.eq_mul_1 in Hp.
}
destruct p4; [ now left | right ].
destruct p4. {
  specialize (odd_prime p Hp Hp2) as H1.
  rewrite Nat_4_eq_2_mul_2 in Hp4.
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
progress unfold iter_list.
revert c.
induction l as [| a]; intros; cbn. {
  symmetry; apply Nat.mul_1_r.
}
rewrite IHl.
rename a into d.
remember (g d) as gd eqn:Hgd; symmetry in Hgd.
destruct gd; [ easy | cbn ].
rewrite Nat.add_0_r.
rewrite (List_fold_left_mul_fun_from_1 (c * f d)).
rewrite (List_fold_left_mul_fun_from_1 c).
rewrite (List_fold_left_mul_fun_from_1 (f d)).
do 3 rewrite <- Nat.mul_assoc.
f_equal.
rewrite Nat.mul_comm.
rewrite <- Nat.mul_assoc.
f_equal.
apply Nat.mul_comm.
Qed.

Theorem List_fold_left_mul_mul :
  ∀ A c l f (g : A → _),
  List.fold_left (λ a b, a * f b * g b) l c =
  List.fold_left (λ a b, a * f b) l c *
  ∏ (b ∈ l), g b.
Proof.
intros.
progress unfold iter_list.
revert c.
induction l as [| a]; intros; [ symmetry; apply Nat.mul_1_r | cbn ].
rewrite IHl.
rewrite Nat.add_0_r.
do 4 rewrite <- (List_fold_left_map  _ _ _ _ _ l).
do 2 rewrite <- List_fold_left_mul_assoc.
do 3 rewrite <- Nat.mul_assoc.
f_equal.
f_equal.
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
progress unfold iter_seq.
progress unfold iter_list.
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

(* Euler criterion *)

Theorem all_different_exist : ∀ f n,
  (∀ i, i < n → f i < n)
  → (∀ i j, i < j < n → f i ≠ f j)
  → ∀ a, a < n → ∃ x, f x = a.
Proof.
intros * Hn Hf * Han.
remember (List.seq 0 n) as l eqn:Hl.
set (g := λ i, if lt_dec i n then f i else i).
assert (Hperm : Permutation l (List.map g l)). {
  apply Permutation_sym.
  subst l.
  apply nat_bijection_Permutation. {
    intros i Hi; subst g; cbn.
    destruct (lt_dec i n) as [Hin| Hin]; [ | easy ].
    now apply Hn.
  } {
    intros i j Hfij; subst g; cbn in Hfij.
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
  prime p
  → 0 < a < p
  → ∀ b, 1 ≤ b < p
  → ∃! b', b' < p ∧ (b * b') mod p = a.
Proof.
intros * Hp (Ha, Hap) * Hb.
assert (Hpz : p ≠ 0) by flia Hb.
apply Nat.neq_0_lt_0 in Ha.
specialize (smaller_than_prime_all_different_multiples p Hp b Hb) as H1.
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
  destruct p; [ easy | flia ].
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
    apply Nat_mul_mod_cancel_l in Hxa. 2: {
      rewrite Nat.gcd_comm.
      now apply eq_gcd_prime_small_1.
    }
    rewrite Nat.Div0.mod_mod in Hxa.
    rewrite <- Hxa.
    now apply Nat.mod_small.
  } {
    apply Nat.nle_gt in Hbx.
    symmetry in Hxa.
    apply Nat_mul_mod_cancel_l in Hxa. 2: {
      rewrite Nat.gcd_comm.
      now apply eq_gcd_prime_small_1.
    }
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
  → ∃! b' : nat, b' < p ∧ (b * b') mod p = a ∧ b ≠ b'.
Proof.
intros * Hp (Haz, Hap) Hnres.
apply Nat.neq_0_lt_0 in Haz.
intros b Hbp.
assert (Hbb : ∀ b, 1 ≤ b < p → ∃! b', b' < p ∧ (b * b') mod p = a). {
  clear b Hbp.
  intros b Hb.
  apply congruence_inverse_has_unique_solution; [ easy | | easy ].
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
  (Hbb : ∀ b, 1 ≤ b < p → ∃! b', b' < p ∧ (b * b') mod p = a ∧ b ≠ b'). {
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
  → ∀ b, b * b ≢ a mod p.
Proof.
intros * Hpz Hsm * Hbb.
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
  → ∀ a, a ^ ((p - 1) / 2) ≡ Legendre_symbol a p mod p.
Proof.
intros * Hp *.
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
    rewrite Nat.pow_2_r.
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

Inspect 1.

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
progress unfold iter_seq.
progress unfold iter_list.
rewrite Nat_sub_succ_1.
rewrite (List_fold_left_mul_filter_filter _ _ _ _ g).
progress unfold iter_list.
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
progress unfold iter_seq.
progress unfold iter_list.
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
  rewrite (sign_abs ((b * a) mod p) p); cycle 1. {
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

Definition coprimes a b := Nat.gcd a b = 1.
Definition are_coprimes a b := Nat.gcd a b =? 1.

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
symmetry in H3.
rewrite <- Legendre_symbol_mod in H3; cycle 1. {
  destruct p; [ easy | ].
  destruct p; [ easy | ].
  now do 2 apply -> Nat.succ_le_mono.
}
rewrite H3, <- Hh.
assert (H4 : ∏ (i = 1, h), abs ((i * a) mod p) p ≡ fact h mod p). {
  specialize abs_all_different_multiples as H4.
  assert (H: 1 ≤ a < p) by easy.
  specialize (H4 p Hp a H); clear H.
  rewrite fact_eq_fold_left.
  progress unfold iter_seq.
  progress unfold iter_list.
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
      apply smaller_than_prime_all_different_multiples; [ easy | easy | ].
      split; [ easy | ].
      now apply Nat.mod_upper_bound.
    }
    destruct (lt_dec (S j mod p) (S i mod p)) as [Hlji| Hlji]. {
      rewrite <- (Nat.Div0.mul_mod_idemp_l (S i)) in Hij.
      rewrite <- (Nat.Div0.mul_mod_idemp_l (S j)) in Hij.
      symmetry in Hij.
      exfalso; revert Hij.
      apply smaller_than_prime_all_different_multiples; [ easy | easy | ].
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

Inspect 1.

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
  rewrite Nat_4_eq_2_mul_2 at 1.
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
  rewrite Nat_4_eq_2_mul_2.
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
  rewrite Nat_4_eq_2_mul_2 in Ha at 1.
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
  rewrite Nat_4_eq_2_mul_2 in H2.
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
    rewrite Nat_4_eq_2_mul_2.
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
  rewrite Nat_4_eq_2_mul_2 in H1.
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

Inspect 1.

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

Theorem Nat_eq_mul_2_div_mod_if_then_else :
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

Theorem List_eq_length_filter_summation :
  ∀ l f,
  List.length (List.filter f l) =
  ∑ (i = 1, List.length l), Nat.b2n (f (List.nth (i - 1) l 0)).
Proof.
intros.
induction l as [| a]; [ easy | ].
cbn - [ List.nth ].
rewrite summation_split_first; [ | now apply -> Nat.succ_le_mono ].
rewrite summation_succ_succ.
erewrite summation_eq_compat; cycle 1. {
  intros k Hk.
  rewrite Nat.sub_succ_l; [ | easy ].
  now cbn.
}
remember (f a) as fa eqn:Hfa; symmetry in Hfa.
now destruct fa; cbn; rewrite Hfa; cbn; [ f_equal | ].
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
apply summation_eq_compat.
intros k Hk.
rewrite List.seq_nth; cycle 1. {
  progress unfold "<".
  rewrite <- Nat.sub_succ_l; [ | easy ].
  now rewrite Nat_sub_succ_1.
}
now rewrite Nat.add_comm, Nat.sub_add.
Qed.

Theorem Eisenstein_lemma :
  ∀ a p, prime p → coprimes a p →
  nb_of_mult_gt_half a p ≡ (∑ (k = 1, (p - 1) / 2), 2 * k * a / p) mod 2.
Proof.
intros * Hp Hap.
assert (Hpz : p ≠ 0) by now intros H; subst p.
progress unfold coprimes in Hap.
remember ((p - 1) / 2) as h eqn:Hh.
move h before p.
rewrite summation_mod_idemp.
erewrite summation_eq_compat; cycle 1. {
  intros i Hi.
  rewrite <- Nat.mul_assoc.
  now rewrite (Nat_eq_mul_2_div_mod_if_then_else _ _ Hpz).
}
cbn - [ nb_of_mult_gt_half "<?" "/" "mod" ].
rewrite Hh.
now rewrite eq_nb_of_mult_gt_half_summation.
Qed.

Theorem summation_to_twice_plus_1 :
  ∀ e f,
  ∑ (i = 1, e), f (2 * i) =
  ∑ (i = 1, 2 * e + 1), if i mod 2 =? 0 then f i else 0.
Proof.
intros.
induction e; cbn - [ "*" "mod" ]. {
  rewrite summation_empty; [ | easy ].
  now rewrite summation_only_one.
}
rewrite summation_split_last; [ | now apply -> Nat.succ_le_mono ].
rewrite summation_succ_succ.
erewrite summation_eq_compat; cycle 1. {
  intros i Hi.
  now rewrite Nat_sub_succ_1.
}
cbn - [ "*" "mod" ].
rewrite IHe.
symmetry.
rewrite summation_split_last; cycle 1. {
  rewrite Nat.add_1_r.
  now apply -> Nat.succ_le_mono.
}
rewrite (summation_shift 1); cycle 1. {
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
rewrite summation_split_last; cycle 1. {
  rewrite Nat.add_comm; cbn.
  now apply -> Nat.succ_le_mono.
}
rewrite Nat.sub_0_r.
rewrite (summation_shift 1); cycle 1. {
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
rewrite Nat.Div0.mod_same, Nat.eqb_refl.
f_equal.
apply summation_eq_compat.
intros i Hi.
rewrite Nat.sub_0_r.
now rewrite Nat.add_comm, Nat.add_sub.
Qed.

(* to be completed
Theorem Eisenstein_lemma' :
  ∀ p q, prime p → prime q → p < q →
  nb_of_mult_gt_half q p ≡ (∑ (k = 1, (p - 1) / 2), k * q / p) mod 2.
Proof.
intros * Hp Hq Hpq.
(*
Compute (
  List.map (λ p,
      List.map (λ q,
(p, q,
Nat.eqb
       ((nb_of_mult_gt_half q p) mod 2)
       ((∑ (k = 1, (p - 1) / 2), k * q /p) mod 2)
)
      ) (List.filter (λ a, (Nat.ltb p a)) (List.filter is_prime (List.seq 2 20)))
  ) (List.filter is_prime (List.seq 2 20))
).
*)
assert (Hpz : p ≠ 0) by now intros H; subst p.
(**)
destruct (Nat.eq_dec p 2) as [Hp2| Hp2]. {
  subst p.
  now rewrite summation_empty.
}
assert
  (H1 : ∑ (k = 1, (p - 1) / 2), k * q =
     p * (∑ (i = 1, (p - 1) / 2), i * q / p) +
       ∑ (i = 1, (p - 1) / 2), (i * q) mod p). {
  erewrite summation_eq_compat; cycle 1. {
    intros k Hk.
    specialize (Nat.div_mod (k * q) p Hpz) as H1.
    now rewrite H1.
  }
  cbn - [ "/" "mod" ].
  rewrite summation_add.
  now rewrite <- mul_summation_distr_l.
}
rewrite <- mul_summation_distr_r, Nat.mul_comm in H1.
remember (∑ (k = _, _), _) as s eqn:Hs.
remember (∑ (k = _, _), _) as t eqn:Ht in H1.
move t  before s.
rewrite <- Ht.
remember (∑ (k = _, _), _) as r eqn:Hr in H1.
move r  before t.
symmetry in H1.
apply Nat.add_sub_eq_r in H1.
apply (f_equal (λ a, a mod 2)) in H1.
rewrite <- Nat.Div0.mul_mod_idemp_l in H1.
replace (p mod 2) with 1 in H1; cycle 1. {
  symmetry.
  apply (odd_prime _ Hp Hp2).
}
rewrite Nat.mul_1_l in H1.
rewrite eq_nb_of_mult_gt_half_summation.
remember ((p - 1) / 2) as h eqn:Hh.
(**)
rewrite <- H1, Hs, Hr.
Search ((_ - _) mod _).
Search ((_ + _) mod _).
Search ((_ mod _ + _) mod _).
Theorem Nat_sub_mod_idemp_l :
  ∀ a b n, b ≤ a → a mod n - b ≡ (a - b) mod n.
Proof.
intros * Hba.
clear Hba.
destruct (le_dec a b) as [Hab| Hab]. {
  replace (a - b) with 0 by flia Hab.
  replace (a mod n - b) with 0; cycle 1. {
    symmetry.
    apply Nat.sub_0_le.
    apply (Nat.le_trans _ a); [ | easy ].
    apply Nat.Div0.mod_le.
  }
  easy.
}
apply Nat.nle_gt in Hab.
remember (a - b) as c eqn:Hc.
replace a with (b + c) by flia Hc Hab.
rewrite <- Nat.Div0.add_mod_idemp_r.
(* bon, casse-couilles *)
...
  rewrite Nat.Div0.mod_0_l.
  Search (_ mod _ = 0).
...
replace a with (b + (a - b)) at 1 by flia Hba.
rewrite Nat
...
destruct (le_dec (a mod n) b) as [Hab| Hab]. {
  rewrite (proj2 (Nat.sub_0_le (a mod n) b)); [ | easy ].
  rewrite Nat_eq_mod_sub_0. {
    apply Nat.Div0.mod_0_l.
  }
...
rewrite (Nat.Div0.mod_eq (a - b) n).
rewrite (Nat.Div0.mod_eq a n).
do 2 rewrite <- Nat.sub_add_distr.
...
f_equal.

f_equal.

Search ((_ mod _ + _)).
Print Nat.Div0.add_mod_idemp_r.
Check Nat.Private_NDivProp.add_mod_idemp_r.
Print Nat.Private_NDivProp.add_mod_idemp_r.
Check Nat.Private_NDivProp.Private_NZDiv.add_mod_idemp_r.
Print Nat.Private_NDivProp.Private_NZDiv.add_mod_idemp_r.
Check Nat.Private_NDivProp.Private_NZDiv.add_mod_idemp_l.
Print Nat.Private_NDivProp.Private_NZDiv.add_mod_idemp_l.
Check Nat.mod_0_r.
Search (_ mod S _).
...
destruct (lt_dec b (a mod n)) as [Hba| Hba]. {
Search (_ - _).
...
  remember (a mod n - b) as c eqn:Hc.
Search (_ - _ = _ + _).
...
  replace b with (a mod n + b - a mod n) at 1 by flia Hba.

rewrite (Nat.Div0.mod_eq (a - b) n).
rewrite (Nat.Div0.mod_eq a n).
rewrite Nat_sub_sub_swap.
Search ((_ - _) mod _).

specialize (Nat.Div0.mod_eq a n) as H1.
...
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
specialize (Nat.div_mod a n Hnz) as H1.
Search (_ mod _ = _ - _).
...
rewrite <- Nat_sub_mod_idemp_l.
...
rewrite mul_summation_distr_l.
rewrite <- summation_sub; cycle 1. {
  intros k Hk.
  rewrite Nat.mul_comm.
  apply Nat.Div0.mod_le.
}
symmetry.
rewrite summation_mod_idemp.
f_equal.
(* c'est bon
Compute (List.map (λ p, List.map (λ q,
let h := (p - 1) / 2 in
(
Nat.eqb
  (∑ (i = 1, h), (q * i - (i * q) mod p) mod 2)
  (∑ (i = 1, h), Nat.b2n (h <? (i * q) mod p))
(*
  ((∑ (i = 1, h), Nat.b2n (h <? (i * q) mod p)) mod 2)
  ((∑ (i = 1, h), (q * i - (i * q) mod p)) mod 2)
*)
)
) (List.filter (Nat.ltb p) (List.filter is_prime (List.seq 3 70))))
(List.filter is_prime (List.seq 3 70))).
*)
...
rewrite Ht.
rewrite summation_mod_idemp; symmetry.
rewrite summation_mod_idemp; symmetry.
f_equal.
...
(* m'a l'air bon...
Compute (List.map (λ p, List.map (λ q,
let h := (p - 1) / 2 in
Nat.eqb
  (∑ (i = 1, h), Nat.b2n (h <? (i * q) mod p) mod 2)
  (∑ (i = 1, h), (i * q / p) mod 2)
) (List.filter (Nat.ltb p) (List.filter is_prime (List.seq 3 70))))
(List.filter is_prime (List.seq 3 70))).
*)
...
apply summation_eq_compat.
intros k Hk.
rewrite Hh.
(* pas bon
Compute (List.map (λ p, List.map (λ q,
  List.map (λ k,
(p, q, k,
Nat.eqb
  (Nat.b2n ((p - 1) / 2 <? (k * q) mod p) mod 2)
  ((k * q / p) mod 2)
)
) (List.seq 1 ((p - 1) / 2))
) (List.filter (Nat.ltb p) (List.filter is_prime (List.seq 3 30))))
(List.filter is_prime (List.seq 3 30))).
*)
...
remember (nb_of_mult_gt_half q p) as n eqn:Hn.
assert (s ≡ (r + n * p) mod 2). {
  rewrite Hs, Hr.
  rewrite Hn.
  rewrite eq_nb_of_mult_gt_half_summation.
  remember ((p - 1) / 2) as h eqn:Hh.
  symmetry.
  rewrite mul_summation_distr_r.
  rewrite <- summation_add.
  erewrite summation_eq_compat; cycle 1. {
    intros k Hk.
    progress unfold Nat.b2n.
    rewrite (Nat.mul_comm _ p), Nat_mul_if_distr_l.
    rewrite Nat.mul_1_r, Nat.mul_0_r.
    easy.
  }
  cbn - [ "mod" "<?" ].
...
rewrite List.length_seq.
erewrite (summation_eq_compat _ _ (λ _, if _ <? _ then _ else _)); cycle 1. {
  intros k Hk.
  rewrite List.seq_nth; [ | flia Hk ].
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  progress fold (Nat.b2n ((p - 1) / 2 <? (k * q) mod p)).
  easy.
}
cbn - [ "/" "mod" "<?"].
...
assert (Hzpq : 0 < p < q) by flia Hpq Hpz.
assert (Hcp : coprimes q p) by now apply eq_gcd_prime_small_1.
specialize (Gauss_lemma q p Hp Hcp _ eq_refl) as H2.
Search Legendre_symbol.
...
apply (Nat.mul_reg_r _ _ p Hpz).
remember (∑ (k = _, _), _) as x eqn:Hx.
specialize (Nat.Div0.mul_mod_idemp_l x p 2) as H1.
Search ((_ * _) = _ * _).
...
erewrite summation_eq_compat; cycle 1. {
  intros k Hk.
  specialize (Nat.div_mod (k * q) p Hpz) as H1.
  rewrite H1.
  rewrite Nat.mul_comm, Nat.div_add_l; [ | easy ].
...
remember ((p - 1) / 2) as h eqn:Hh.
move h before p.
rewrite summation_mod_idemp.
progress unfold iter_seq.
progress unfold iter_list.
rewrite Nat_sub_succ_1.
progress unfold nb_of_mult_gt_half.
rewrite <- Hh.
rewrite <- List.fold_left_S_0.
rewrite List_fold_left_filter.
(**)
erewrite List_fold_left_ext_in; cycle 1. {
  intros * Hb.
  replace (if _ <? _ then _ else _) with
    (c + Nat.b2n (h <? (b * q) mod p)); cycle 1. {
    remember (_ <? _) as x eqn:Hx; symmetry in Hx.
    rewrite Nat.add_comm.
    now destruct x.
  }
  easy.
}
(* ouais, chais pas... *)
...
erewrite List_fold_left_ext_in; [ easy | ].
cbn - [ "<?" "mod" ].
intros * Hb.
Search (if _ then _ else _).
remember (_ <? _) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Nat.ltb_lt in Hx.
  rewrite <- Nat.add_1_r; f_equal; symmetry.
  apply Nat_eq_mod_1.
  split. {
    apply Nat.Div0.mod_divides.
    clear c.
...
rewrite Nat.add_0_r.
now rewrite Nat.add_1_r.
...
rewrite Eisenstein_lemma; [ | easy | ].
specialize (summation_to_twice_plus_1 ((p - 1) / 2)) as H1.
specialize (H1 (λ a, (a * q / p))).
cbn - [ "*" "/" "mod" ] in H1.
rewrite H1; clear H1.
rewrite <- Nat.Lcm0.divide_div_mul_exact.
rewrite Nat.mul_comm.
rewrite Nat.div_mul; [ | easy ].
rewrite Nat.sub_add.
remember (∑ (k = _, _), _) as x in |-*; subst x.
symmetry.
Check summation_to_twice_plus_1.
Theorem glop : ∀ e f,
  ∑ (i = 1, e), f i = ∑ (i = 1, 2 * e + 1), (if i mod 2 =? 0 then f i else 0).
...

Theorem quadratic_reciprocity :
  ∀ p q, prime p → prime q → 2 < p < q →
  is_quadratic_residue p q = is_quadratic_residue q p ↔
    p mod 4 = 1 ∨ q mod 4 = 1.
Proof.
intros * Hp Hq Hpq.
split; intros H1. {
  rename H1 into Hx.
  remember (is_quadratic_residue q p) as b eqn:Hy; symmetry in Hy.
  move Hx after Hy.
  destruct b. {
    progress unfold is_quadratic_residue in Hx, Hy.
    apply Nat.eqb_eq in Hx, Hy.
    assert (Hzpq : 0 < p < q) by flia Hpq.
    assert (Hcp : coprimes q p) by now apply eq_gcd_prime_small_1.
    specialize (Gauss_lemma q p Hp Hcp _ eq_refl) as H1.
rewrite Hy in H1; symmetry in H1.
(**)
rewrite Nat_sub_1_pow_mod in H1; [ | flia Hpq ].
rewrite Eisenstein_lemma in H1; [ | easy | easy ].
(**)
assert (H : p ≠ 2) by flia Hpq.
specialize (odd_prime_mod_4 p Hp H) as Hp4; clear H.
assert (H : q ≠ 2) by flia Hpq.
specialize (odd_prime_mod_4 q Hq H) as Hq4; clear H.
destruct Hp4 as [Hp4| Hp4]; [ now left | right ].
destruct Hq4 as [Hq4| Hq4]; [ easy | exfalso ].
apply Nat_eq_mod_exists in Hp4, Hq4.
destruct Hp4 as (u, Hu).
destruct Hq4 as (v, Hv).
move v before u.
rewrite Nat.mul_comm in Hu, Hv.
(*
progress unfold nb_of_mult_gt_half in H1.
*)
remember ((p - 1) / 2) as p1 eqn:Hp1.
rewrite Hu in Hp1.
rewrite <- Nat.add_sub_assoc in Hp1; [ | now apply -> Nat.succ_le_mono ].
rewrite Nat_sub_succ_1 in Hp1.
rewrite Nat_4_eq_2_mul_2, <- Nat.mul_assoc in Hp1.
rewrite <- Nat_mul_add_1_distr_l, Nat.mul_comm in Hp1.
rewrite Nat.div_mul in Hp1; [ | easy ].
subst p1.
apply Nat_eq_pow_1 in H1.
destruct H1 as [H1| H1]. {
  apply Nat.add_sub_eq_nz in H1; [ subst p | easy ].
  destruct Hpq as (H, _).
  now apply Nat.lt_irrefl in H.
}
Search (_ mod 2).
progress unfold Legendre_symbol in Hx, Hy.
remember (q =? 2) as q2 eqn:Hq2; symmetry in Hq2.
destruct q2; [ clear Hx; apply Nat.eqb_eq in Hq2; flia Hq2 Hpq | ].
clear Hq2.
remember (p =? 2) as p2 eqn:Hp2; symmetry in Hp2.
destruct p2; [ clear Hy; apply Nat.eqb_eq in Hp2; flia Hp2 Hpq | ].
clear Hp2.
remember (p mod q =? 0) as pmq eqn:Hpmq; symmetry in Hpmq.
destruct pmq; [ easy | ].
apply Nat.eqb_neq in Hpmq.
remember (q mod p =? 0) as qmp eqn:Hqmp; symmetry in Hqmp.
destruct qmp; [ easy | ].
apply Nat.eqb_neq in Hqmp.
remember (sqrt_mod p q) as spq eqn:Hspq; symmetry in Hspq.
destruct spq as [a| ]; [ clear Hx | flia Hx Hpq ].
apply eq_sqrt_mod_Some in Hspq.
destruct Hspq as (Haq, Hapq).
remember (sqrt_mod q p) as sqp eqn:Hsqp; symmetry in Hsqp.
destruct sqp as [b| ]; [ clear Hy | flia Hy Hpq ].
apply eq_sqrt_mod_Some in Hsqp.
destruct Hsqp as (Hbp, Hbqp).
move b before a; move Hbqp before Hapq; move Hbp before Haq.
rewrite (Nat.mod_small p) in Hapq; [ | easy ].
...
apply Nat.Div0.mod_divides in H1.
destruct H1 as (c, Hc).
...
apply Nat_eq_pow_1 in H1.
...
specialize (List_fold_left_if_equiv_filter 1) as H2.
(*
rewrite <- (Nat.mod_1_l p) in H1 at 5; [ | flia Hu ].
*)
rewrite <- (Nat.mod_1_l p) in H1 at 6; [ | flia Hu ].
(**)
rewrite <- (Nat.mul_1_l (_ ^ _)) in H1.
...
rewrite <- H2 in H1.
rewrite Nat.mod_1_l in H1; [ | flia Hu ].
clear H2.
...
remember (_ ^ _) as a eqn:Ha.
symmetry in Ha.
destruct a; [ now rewrite Nat.Div0.mod_0_l in H1 | ].
apply Nat_eq_scuc_mod_1 in H1.
destruct a. {
Search (_ ^ _ = 1).
...
rewrite Nat_sub_1_pow_mod in H1; [ | flia Hpq ].
rewrite Eisenstein_lemma in H1; [ | easy | easy ].
assert (H : p ≠ 2) by flia Hpq.
specialize (odd_prime_mod_4 p Hp H) as Hp4; clear H.
assert (H : q ≠ 2) by flia Hpq.
specialize (odd_prime_mod_4 q Hq H) as Hq4; clear H.
destruct Hp4 as [Hp4| Hp4]; [ now left | right ].
destruct Hq4 as [Hq4| Hq4]; [ easy | exfalso ].
apply Nat_eq_mod_exists in Hp4, Hq4.
destruct Hp4 as (u, Hu).
destruct Hq4 as (v, Hv).
move v before u.
rewrite Nat.mul_comm in Hu, Hv.
Search (_ ^ _ = 1).
...
progress unfold Legendre_symbol in Hx.
remember (q =? 2) as q2 eqn:Hq2; symmetry in Hq2.
destruct q2; [ apply Nat.eqb_eq in Hq2; flia Hpq Hq2 | ].
clear Hq2.
remember (p mod q =? 0) as pqz eqn:Hpqz; symmetry in Hpqz.
destruct pqz; [ easy | ].
clear Hpqz.
remember (sqrt_mod p q) as spq eqn:Hspq; symmetry in Hspq.
destruct spq as [a| ]; [ clear Hx | flia Hx Hpq ].
apply eq_sqrt_mod_Some in Hspq.
destruct Hspq as (Haq, Hapq).
progress unfold Legendre_symbol in Hy.
remember (p =? 2) as p2 eqn:Hp2; symmetry in Hp2.
destruct p2; [ apply Nat.eqb_eq in Hp2; flia Hpq Hp2 | ].
clear Hp2.
remember (q mod p =? 0) as qpz eqn:Hqpz; symmetry in Hqpz.
destruct qpz; [ easy | ].
apply Nat.eqb_neq in Hqpz.
remember (sqrt_mod q p) as sqp eqn:Hsqp; symmetry in Hsqp.
destruct sqp as [b| ]; [ clear Hy | flia Hy Hpq ].
apply eq_sqrt_mod_Some in Hsqp.
destruct Hsqp as (Hbp, Hbqp).
move b before a; move Hbqp before Hapq; move Hbp before Haq.
...
rewrite <- (Nat.mod_small 3 4) in Hp4 at 2; [ | flia ].
rewrite <- (Nat.mod_small 3 4) in Hq4 at 2; [ | flia ].
apply Nat_eq_mod_sub_0 in Hp4, Hq4.
Search (_ mod _ = _ ↔ _).
...
    progress unfold Legendre_symbol in H1.
    progress unfold Legendre_symbol in Hx, Hy.
    remember (p =? 2) as p2 eqn:Hp2; symmetry in Hp2.
    destruct p2; [ apply Nat.eqb_eq in Hp2; flia Hpq Hp2 | ].
    remember (q =? 2) as q2 eqn:Hq2; symmetry in Hq2.
    destruct q2; [ apply Nat.eqb_eq in Hq2; flia Hpq Hq2 | ].
    clear Hp2 Hq2.
    remember (p mod q =? 0) as pqz eqn:Hpqz; symmetry in Hpqz.
    destruct pqz; [ easy | ].
    remember (q mod p =? 0) as qpz eqn:Hqpz; symmetry in Hqpz.
    destruct qpz; [ easy | ].
    move Hqpz before Hpqz.
    apply Nat.eqb_neq in Hpqz, Hqpz.
    rewrite Hx in H1.
    symmetry in H1.
    remember (sqrt_mod p q) as smpq eqn:Hsmpq; symmetry in Hsmpq.
    remember (sqrt_mod q p) as smqp eqn:Hsmqp; symmetry in Hsmqp.
    destruct smpq as [u| ]; [ clear Hx | flia Hx Hpq ].
    destruct smqp as [v| ]; [ clear Hy | flia Hy Hpq ].
    move u before q; move v before u.
    apply eq_sqrt_mod_Some in Hsmpq.
    apply eq_sqrt_mod_Some in Hsmqp.
    destruct Hsmpq as (Huq, Hu).
    destruct Hsmqp as (Hvp, Hv).
    move Hvp before Huq.
...

Theorem quadratic_reciprocity :
  ∀ p q, prime p → prime q → 2 < p → 2 < q → p ≠ q →
  is_quadratic_residue p q = is_quadratic_residue q p ↔
    p mod 4 = 1 ∨ q mod 4 = 1.
Proof.
intros * Hp Hq Hp2 Hq2 Hpq.
....
(*
Compute (List.map (λ p, List.map (λ q,
  (p, q, Bool.eqb (is_quadratic_residue p q) (is_quadratic_residue q p),
   orb (p mod 4 =? 1) (q mod 4 =? 1)))
  (List.filter (Nat.ltb p) (List.filter is_prime (List.seq 3 30))))
  (List.filter is_prime (List.seq 3 30))).
...
*)

(* attempt to define it with Legendre symbols but the problem is that
   my Legendre symbol is not "1 or -1" but "1 or p-1" *)
Theorem quadratic_reciprocity :
  ∀ p q, prime p → prime p →
  Legendre_symbol p q * Legendre_symbol q p =
  opp_1_pow (((p -1) / 2) * ((q - 1) / 2)).
*)
