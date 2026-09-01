Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import Sorting.Permutation.
Import List List.ListNotations.
Require Import Misc Primes.

(* Euler criterion *)

Theorem all_different_exist : ∀ f n,
  (∀ i, i < n → f i < n)
  → (∀ i j, i < j < n → f i ≠ f j)
  → ∀ a, a < n → ∃ x, f x = a.
Proof.
intros * Hn Hf * Han.
remember (seq 0 n) as l eqn:Hl.
set (g := λ i, if lt_dec i n then f i else i).
assert (Hperm : Permutation l (map g l)). {
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
  apply in_seq; flia Han.
}
specialize (H1 H); clear H.
subst g; cbn in H1.
apply in_map_iff in H1.
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
  → (∀ n, 1 ≤ n ≤ p - 1 → n ^ 2 mod p ≠ a)
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
  → (∀ n, 1 ≤ n ≤ p - 1 → n ^ 2 mod p ≠ a)
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
specialize (seq_NoDup (p - 1) 1) as Hnd.
remember (seq 1 (p - 1)) as l eqn:Hl.
assert
  (Hij : ∀ i, i ∈ l →
   ∃j, j ∈ l ∧ i ≠ j ∧ (i * j) mod p = a ∧
    ∀ k, k ∈ l → k ≠ i → (k * j) mod p ≠ a). {
  intros i Hi.
  specialize (Hbb i) as H1.
  assert (H : 1 ≤ i < p). {
    subst l.
    apply in_seq in Hi; flia Hi.
  }
  specialize (H1 H); clear H.
  destruct H1 as (j & (Hj1 & Hj2 & Hj3) & Hj4).
  exists j.
  split. {
    subst l; apply in_seq.
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
      apply in_seq in Hk.
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
        rewrite Hl in Hi; apply in_seq in Hi; flia Hi.
      }
      rewrite Nat.mod_small in Hj2. 2: {
        rewrite Hl in Hk; apply in_seq in Hk; flia Hk.
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
      rewrite Hl in Hk; apply in_seq in Hk.
      rewrite Nat.mod_small in Hj2; [ | flia Hk ].
      rewrite Nat.mod_small in Hj2; [ flia Hj2 Hik | ].
      rewrite Hl in Hi; apply in_seq in Hi; flia Hi.
    }
  }
}
clear Hbb Hnres.
replace (p - 1) with (length l). 2: {
  now subst l; rewrite length_seq.
}
clear Hl.
remember (length l) as len eqn:Hlen; symmetry in Hlen.
revert l Hnd Hij Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len. {
  apply length_zero_iff_nil in Hlen.
  now rewrite Hlen.
}
destruct l as [| b l]; [ easy | ].
specialize (Hij b (or_introl (eq_refl _))) as H1.
destruct H1 as (i2 & Hi2l & Hai2 & Hai2p & Hk).
destruct Hi2l as [Hi2l| Hi2l]; [ easy | ].
specialize (in_split i2 l Hi2l) as (l1 & l2 & Hll).
rewrite Hll.
cbn - [ "/" ]; rewrite Nat.add_0_r.
rewrite fold_left_app; cbn - [ "/" ].
rewrite fold_left_mul_from_1.
rewrite Nat.mul_shuffle0, Nat.mul_comm.
rewrite fold_left_mul_from_1.
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
  rewrite length_app in Hlen; cbn in Hlen.
  now rewrite Nat.add_comm in Hlen.
}
rewrite Nat.div_add; [ | easy ].
rewrite Nat.add_comm, Nat.pow_add_r, Nat.pow_1_r.
rewrite <- Nat.Div0.mul_mod_idemp_r.
rewrite <- (Nat.Div0.mul_mod_idemp_r _ (a ^ _)).
f_equal; f_equal.
rewrite Nat.mul_comm.
rewrite List_fold_left_mul_assoc, Nat.mul_1_l.
rewrite <- fold_left_app.
apply (IHlen (len - 1)); [ flia | | | ]. 3: {
  cbn in Hlen.
  apply Nat.succ_inj in Hlen.
  rewrite <- Hlen, Hll.
  do 2 rewrite length_app.
  cbn; flia.
} {
  apply NoDup_cons_iff in Hnd.
  destruct Hnd as (_, Hnd).
  rewrite Hll in Hnd.
  now apply NoDup_remove_1 in Hnd.
}
intros i Hi.
specialize (Hij i) as H1.
assert (H : i ∈ b :: l). {
  right; rewrite Hll.
  apply in_app_or in Hi.
  apply in_or_app.
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
      now rewrite Hll; right; apply in_or_app; right; left.
    }
    specialize (H1 H); clear H.
    assert (H : i2 ≠ i). {
      intros H; subst i2.
      move Hnd at bottom; move Hi at bottom.
      apply NoDup_cons_iff in Hnd.
      destruct Hnd as (_, Hnd).
      rewrite Hll in Hnd.
      now apply NoDup_remove_2 in Hnd.
    }
    specialize (H1 H).
    now rewrite Nat.mul_comm in H1.
  }
  rewrite Hll in Hjall.
  apply in_app_or in Hjall.
  apply in_or_app.
  destruct Hjall as [Hjall| Hjall]; [ now left | ].
  destruct Hjall as [Hjall| Hjall]; [ | now right ].
  subst j.
  destruct (Nat.eq_dec b i) as [Hbi| Hbi]. {
    subst i.
    move Hnd at bottom.
    apply NoDup_cons_iff in Hnd.
    destruct Hnd as (Hnd, _).
    exfalso; apply Hnd; clear Hnd.
    rewrite Hll.
    apply in_app_or in Hi.
    apply in_or_app.
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
apply in_app_or in Hkll.
apply in_or_app.
destruct Hkll as [Hkll| Hkll]; [ now left | now right; right ].
Qed.

(**)

Global Hint Resolve Nat.le_0_l : core.
Global Hint Resolve Nat.lt_0_succ : core.

Fixpoint sqrt_mod_loop cnt a p i :=
  match cnt with
  | 0 => None
  | S cnt' =>
      if i * i mod p =? a mod p then Some i
      else sqrt_mod_loop cnt' a p (S i)
  end.

Definition sqrt_mod a p := sqrt_mod_loop p a p 0.

Definition legendre_symbol a p :=
  if p =? 2 then 1
  else if a mod p =? 0 then 0
  else
    match sqrt_mod a p with
    | Some _ => 1
    | None => p - 1
    end.

Theorem eq_sqrt_mod_loop_Some :
  ∀ cnt a b p i,
  sqrt_mod_loop cnt a p i = Some b
  → i ≤ b < i + cnt ∧ b * b ≡ a mod p.
Proof.
intros * Hsm.
revert i Hsm.
induction cnt; intros; [ easy | ].
cbn - [ "*" ] in Hsm.
remember ((i * i) mod p =? a mod p) as e eqn:He.
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
  → b < p ∧ b * b ≡ a mod p.
Proof.
intros * Hsm.
now apply eq_sqrt_mod_loop_Some in Hsm.
Qed.

Theorem eq_sqrt_mod_loop_None :
  ∀ cnt a i p,
  a ≢ 0 mod p
  → sqrt_mod_loop cnt a p i = None
  → ∀ b, i ≤ b < i + cnt → b * b ≢ a mod p.
Proof.
intros * Hap Hsm * Hib Hbb.
symmetry in Hbb.
revert i Hib Hsm.
induction cnt; intros; [ flia Hib | ].
cbn in Hsm.
remember ((i * i) mod p =? a mod p) as sip eqn:Hsip.
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
  ∀ cnt a p i, sqrt_mod_loop cnt a p i = sqrt_mod_loop cnt (a mod p) p i.
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
  → ∀ a, a ^ ((p - 1) / 2) ≡ legendre_symbol a p mod p.
Proof.
intros * Hp *.
destruct (Nat.eq_dec p 2) as [Hp2| Hp2]; [ now subst p | ].
progress unfold legendre_symbol.
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
  assert (H : ∀ n, 1 ≤ n ≤ p - 1 → n ^ 2 mod p ≠ a). {
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
    (List.filter (λ m, (p - 1) / 2 <? ((m * a) mod p)) (seq 1 ((p - 1) / 2))).

Definition is_quadratic_residue a p := legendre_symbol a p =? 1.

(*
Compute (let p := 29 in List.filter (λ a, (nb_of_mult_gt_half a p mod 2 =? 0)) (seq 1 (p - 1))).
Compute (let p := 29 in List.filter (λ a, is_quadratic_residue a p) (seq 1 p)).
*)

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

Theorem List_fold_left_mul_filter_filter :
  ∀ A c l (f : A → _) g,
  fold_left (λ a b, a * f b) l c =
  fold_left (λ a b, a * f b) (filter g l) c *
  fold_left (λ a b, a * f b) (filter (λ a, negb (g a)) l) 1.
Proof.
intros.
revert c.
induction l as [| a]; intros; cbn. {
  symmetry; apply Nat.mul_1_r.
}
rewrite IHl.
rename a into d.
remember (g d) as gd eqn:Hgd; symmetry in Hgd.
destruct gd; [ easy | cbn ].
rewrite Nat.add_0_r.
rewrite (fold_left_mul_fun_from_1 (c * f d)).
rewrite (fold_left_mul_fun_from_1 c).
rewrite (fold_left_mul_fun_from_1 (f d)).
do 3 rewrite <- Nat.mul_assoc.
f_equal.
rewrite Nat.mul_comm.
rewrite <- Nat.mul_assoc.
f_equal.
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

(* to be completed
Theorem Gauss_lemma :
  ∀ a p n,
  n = nb_of_mult_gt_half a p
  → legendre_symbol a p = (p - 1) ^ n mod p.
Proof.
intros * Hn.
remember ((p - 1) / 2) as h eqn:Hh.
remember (List.fold_left (λ acc i, acc * (i * a)) (List.seq 1 h) 1) as z
  eqn:Hz.
assert (H1 : z = a ^ h * fact h). {
  subst z.
  erewrite List_fold_left_ext_in; cycle 1. {
    intros * Hb.
    now rewrite Nat.mul_assoc.
  }
  rewrite List_fold_left_mul_const_r.
  rewrite List.length_seq, Nat.mul_comm.
  f_equal; symmetry.
  apply fact_eq_fold_left.
}
assert
  (H2 :
     z ≡
       ((p - 1) ^ n *
        List.fold_left (λ acc i, acc * abs (i * a mod p) p) (List.seq 1 h) 1)
         mod p). {
  subst z.
  rewrite <- List_fold_left_map.
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
  rewrite List_fold_left_mul_filter_filter with (g := λ a, sign a p =? 1).
  do 2 rewrite List_fold_left_filter.
  erewrite List_fold_left_ext_in; cycle 1. {
    intros * Hb.
...
(* merde chiasse *)
    progress unfold sign.
    rewrite <- Hh.
    apply in_map_iff in Hb.
    destruct Hb as (x & Hx & Hxs).
    apply in_map in Hb.
    apply List.in_seq in Hb.
    rewrite <- Hh.
    destruct Hb as (H2, H3).
    apply <- Nat.succ_le_mono in H3.
    apply Nat.leb_le in H3.
    rewrite H3, Nat.eqb_refl.
    easy.
  }
  rewrite Nat.mul_comm.
  erewrite List_fold_left_ext_in; cycle 1. {
    intros * Hb.
    progress unfold sign.
    apply List.in_seq in Hb.
    rewrite <- Hh.
    destruct Hb as (H2, H3).
    apply <- Nat.succ_le_mono in H3.
    apply Nat.leb_le in H3.
    rewrite H3, Nat.eqb_refl.
    now cbn.
  }
(* n'importe n'awak *)
...
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
    rewrite (sign_abs ((b * a) mod p) p); cycle 1. {
      apply Nat.mod_upper_bound.
      intros H; subst p h.
      easy.
    }
    rewrite Nat.Div0.mul_mod_idemp_r.
    rewrite (Nat.mul_comm (sign _ _)).
    rewrite Nat.mul_assoc.
    easy.
  }
  remember (λ acc i, _) as g in |-*; subst g.
...
Theorem sign_mod : ∀ a n, 2 ≤ n → sign a n mod n = sign a n.
Proof.
intros * H2n.
progress unfold sign.
destruct (_ <=? _); [ now apply Nat.mod_1_l | ].
apply Nat.mod_small.
flia H2n.
Qed.

    rewrite <- Nat.Div0.mul_mod_idemp_l.


    rewrite <- (Nat.Div0.mul_mod_idemp_l (sign _ _)).
(*
  (c * ((sign ((b * a) mod p) p * abs ((b * a) mod p) p) mod p)) mod p = ?g c b
*)
    rewrite <- (Nat.Div0.mul_mod_idemp_l (sign _ _)).
rewrite sign_mod.
...
    rewrite Nat.Div0.mul_mod_idemp_r.
    rewrite Nat.mul_assoc.
    rewrite <- Nat.Div0.mul_mod_idemp_l.
...

    easy.
  }
  remember (λ acc i, _) as g in |-*; subst g.
...
*)
