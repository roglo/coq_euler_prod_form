From Stdlib Require Import Utf8 Arith.
From Stdlib Require Import Sorting.Permutation.
Import List List.ListNotations.
Require Import Misc Primes.

Definition euler_crit p :=
  filter (λ a, Nat_pow_mod a ((p - 1) / 2) p =? 1) (seq 0 p).

Definition quad_res p :=
  map (λ a, Nat_pow_mod a 2 p) (seq 1 (p - 1)).

Theorem euler_crit_iff : ∀ p a,
  a ∈ euler_crit p ↔ a < p ∧ a ^ ((p - 1) / 2) mod p = 1.
Proof.
intros.
split. {
  intros Hap.
  destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ now subst p | ].
  unfold euler_crit in Hap.
  apply filter_In in Hap.
  destruct Hap as (Ha, Hap).
  rewrite Nat_pow_mod_is_pow_mod in Hap; [ | easy ].
  apply in_seq in Ha.
  now apply Nat.eqb_eq in Hap.
} {
  intros (Hzap, Hap).
  destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ now subst p | ].
  unfold euler_crit.
  apply filter_In.
  rewrite Nat_pow_mod_is_pow_mod; [ | easy ].
  split; [ apply in_seq; flia Hzap | now apply Nat.eqb_eq ].
}
Qed.

Theorem quad_res_iff : ∀ p a,
  a ∈ quad_res p ↔ ∃ q, 1 ≤ q < p ∧ q ^ 2 mod p = a.
Proof.
intros.
split. {
  intros Hap.
  destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ now subst p | ].
  unfold quad_res in Hap.
  apply in_map_iff in Hap.
  destruct Hap as (b & Hpa & Hb).
  rewrite Nat_pow_mod_is_pow_mod in Hpa; [ | easy ].
  apply in_seq in Hb.
  replace (1 + (p - 1)) with p in Hb by flia Hpz.
  now exists b.
} {
  intros (q & Hqp & Hq).
  destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ now subst p | ].
  unfold quad_res.
  apply in_map_iff.
  exists (q mod p).
  rewrite Nat_pow_mod_is_pow_mod; [ | easy ].
  rewrite Nat_mod_pow_mod.
  split; [ easy | ].
  apply in_seq.
  replace (1 + (p - 1)) with p  by flia Hpz.
  split; [ now rewrite Nat.mod_small | ].
  now apply Nat.mod_upper_bound.
}
Qed.

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

Theorem euler_criterion_quadratic_residue_iff : ∀ p a,
  prime p
  → p ≠ 2
  → a ≠ 0
  → a ∈ euler_crit p ↔ a ∈ quad_res p.
Proof.
intros * Hp Hp2 Haz.
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ now subst p | ].
split; intros Hap. 2: {
  apply quad_res_iff in Hap.
  apply euler_crit_iff.
  destruct Hap as (q & Hqp & Hqpa).
  rewrite <- Hqpa.
  split; [ now apply Nat.mod_upper_bound | ].
  rewrite Nat_mod_pow_mod.
  rewrite <- Nat.pow_mul_r.
  rewrite <- (proj2 (Nat.Div0.div_exact _ _)). 2: {
    specialize (odd_prime p Hp Hp2) as H1.
    specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H2.
    now rewrite H2, H1, Nat.add_sub, Nat.mul_comm, Nat.Div0.mod_mul.
  }
  now apply fermat_little.
} {
  apply euler_crit_iff in Hap.
  apply quad_res_iff.
  destruct Hap as (Ha, Hap).
  apply (not_forall_in_interv_imp_exist 1 (p - 1)). {
    intros n.
    apply Decidable.dec_and. {
      apply Decidable.dec_and; [ apply dec_le | apply dec_lt ].
    } {
      apply Nat.eq_decidable.
    }
  } {
    destruct p; [ easy | cbn ].
    destruct p; [ | flia ].
    flia Haz Ha.
  }
  intros H.
  assert (Hnres : ∀ n, 1 ≤ n ≤ p - 1 → n ^ 2 mod p ≠ a). {
    intros n Hn.
    specialize (H n Hn).
    intros H1; apply H.
    split; [ flia Hn | easy ].
  }
  clear H.
  (* https://proofwiki.org/wiki/Euler%27s_Criterion *)
  (* The congruence 𝑏𝑥≡𝑎(mod𝑝) has (modulo 𝑝) a unique solution 𝑏′ by Solution
     of Linear Congruence. *)
  assert (Hbb : ∀ b, 1 ≤ b < p → ∃! b', b' < p ∧ (b * b') mod p = a). {
    intros b Hb.
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
      specialize (H4 H H1 a Ha); clear H.
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
  }
  (* https://proofwiki.org/wiki/Euler%27s_Criterion *)
  (* Note that 𝑏′≢𝑏, because otherwise we would have 𝑏2≡𝑎(mod𝑝) and 𝑎 would be
     a quadratic residue of 𝑝. *)
  assert
    (H : ∀ b, 1 ≤ b < p → ∃! b', b' < p ∧ (b * b') mod p = a ∧ b ≠ b'). {
    intros b Hbp.
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
  }
  clear Hbb; rename H into Hbb.
  (* https://proofwiki.org/wiki/Euler%27s_Criterion *)
  (* It follows that the residue classes {1,2,…,𝑝−1} modulo 𝑝 fall into
     (𝑝−1)/2 pairs 𝑏,𝑏′ such that 𝑏𝑏′≡𝑎(mod𝑝). *)
  assert (H : fact (p - 1) mod p = a ^ ((p - 1) / 2) mod p). {
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
    clear Hap.
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
  }
  specialize (proj1 (Wilson p (prime_ge_2 p Hp)) Hp) as HW.
  rewrite Hap, HW in H.
  flia Hp2 H.
}
Qed.
