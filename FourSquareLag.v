(* Lagrange's four-square theorem *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Misc Primes FourSquareEuler.

Tactic Notation "transparent" "assert" "(" ident(H) ":" lconstr(type) ")" :=
  unshelve (refine (let H := (_ : type) in _)).

Lemma le_half_prime_square_diff : ∀ p a a',
   prime p
   → p mod 2 = 1
   → a ≤ (p - 1) / 2
   → a' ≤ (p - 1) / 2
   → a' < a
   → a ^ 2 ≢  a' ^ 2 mod p.
Proof.
intros * Hp Hp2 Ha Ha' Haa.
intros H1.
apply Nat_eq_mod_sub_0 in H1.
rewrite Nat_sqr_sub_sqr, Nat.mul_comm in H1.
apply Nat.mod_divide in H1; [ | now intros H2; subst p ].
specialize (Nat.gauss _ _ _ H1) as H2.
apply (Nat.mul_le_mono_l _ _ 2) in Ha.
apply (Nat.mul_le_mono_l _ _ 2) in Ha'.
rewrite <- Nat.divide_div_mul_exact in Ha; [ | easy | ]. 2: {
  specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H3.
  rewrite Hp2 in H3.
  rewrite H3, Nat.add_sub.
  apply Nat.divide_factor_l.
}
rewrite (Nat.mul_comm _ (p - 1)), Nat.div_mul in Ha; [ | easy ].
rewrite <- Nat.divide_div_mul_exact in Ha'; [ | easy | ]. 2: {
  specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H3.
  rewrite Hp2 in H3.
  rewrite H3, Nat.add_sub.
  apply Nat.divide_factor_l.
}
rewrite (Nat.mul_comm _ (p - 1)), Nat.div_mul in Ha'; [ | easy ].
assert (H : Nat.gcd p (a - a') = 1). {
  apply eq_gcd_prime_small_1; [ easy | ].
  split; [ flia Haa | ].
  flia Ha Ha' Haa.
}
specialize (H2 H); clear H.
destruct H2 as (k, Hk).
destruct k. {
  apply Nat.eq_add_0 in Hk.
  now destruct Hk; subst a a'.
}
cbn in Hk.
apply (f_equal (Nat.mul 2)) in Hk.
do 2 rewrite Nat.mul_add_distr_l in Hk.
specialize (prime_ge_2 _ Hp) as Hpge2.
flia Ha Ha' Hk Hpge2.
Qed.

Lemma le_half_prime_succ_square_diff : ∀ p b b',
  prime p
  → p mod 2 = 1
  → b ≤ (p - 1) / 2
  → b' ≤ (p - 1) / 2
  → b < b'
  → b' ^ 2 + 1 ≢ (b ^ 2 + 1) mod p.
Proof.
intros * Hp Hp2 Hb Hb' Hbb' Hb1.
assert (Hpz : p ≠ 0) by now intros H; subst p.
apply Nat_eq_mod_sub_0 in Hb1.
replace (b' ^ 2 + 1 - (b ^ 2 + 1)) with (b' ^ 2 - b ^ 2) in Hb1 by flia.
rewrite Nat_sqr_sub_sqr, Nat.mul_comm in Hb1.
apply Nat.mod_divide in Hb1; [ | easy ].
specialize (Nat.gauss _ _ _ Hb1) as H2.
apply (Nat.mul_le_mono_l _ _ 2) in Hb.
apply (Nat.mul_le_mono_l _ _ 2) in Hb'.
rewrite <- Nat.divide_div_mul_exact in Hb; [ | easy | ]. 2: {
  specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H3.
  rewrite Hp2 in H3.
  rewrite H3, Nat.add_sub.
  apply Nat.divide_factor_l.
}
rewrite (Nat.mul_comm _ (p - 1)), Nat.div_mul in Hb; [ | easy ].
rewrite <- Nat.divide_div_mul_exact in Hb'; [ | easy | ]. 2: {
  specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H3.
  rewrite Hp2 in H3.
  rewrite H3, Nat.add_sub.
  apply Nat.divide_factor_l.
}
rewrite (Nat.mul_comm _ (p - 1)), Nat.div_mul in Hb'; [ | easy ].
assert (H : Nat.gcd p (b' - b) = 1). {
  apply eq_gcd_prime_small_1; [ easy | ].
  split; [ flia Hbb' | ].
  flia Hb Hb' Hbb'.
}
specialize (H2 H); clear H.
destruct H2 as (k, Hk).
destruct k. {
  apply Nat.eq_add_0 in Hk.
  now destruct Hk; subst b b'.
}
cbn in Hk.
apply (f_equal (Nat.mul 2)) in Hk.
do 2 rewrite Nat.mul_add_distr_l in Hk.
specialize (prime_ge_2 _ Hp) as Hpge2.
flia Hb Hb' Hk Hpge2.
Qed.

(* pigeonhole *)

Fixpoint find_dup (la : list (nat * nat)) :=
  match la with
  | [] => None
  | (n, a) :: la' =>
      match find (λ nb, snd nb =? a) la' with
      | None => find_dup la'
      | Some (n', _) => Some (n, n')
      end
  end.

Definition pigeonhole_fun a (f : nat → nat) :=
  match find_dup (List.map (λ n, (n, f n)) (seq 0 a)) with
  | Some (n, n') => (n, n')
  | None => (0, 0)
  end.

Theorem find_dup_some : ∀ x x' la,
  find_dup la = Some (x, x')
  → ∃ y la1 la2 la3,
     la = la1 ++ (x, y) :: la2 ++ (x', y) :: la3.
Proof.
intros * Hfd.
induction la as [| a]; [ easy | ].
cbn in Hfd.
destruct a as (n, a).
remember (find (λ nb, snd nb =? a) la) as r eqn:Hr.
symmetry in Hr.
destruct r as [(n', b)| ]. {
  injection Hfd; clear Hfd; intros; subst n n'.
  exists b, []; cbn.
  apply find_some in Hr; cbn in Hr.
  destruct Hr as (Hx'la, Hba).
  apply Nat.eqb_eq in Hba; subst b.
  apply in_split in Hx'la.
  destruct Hx'la as (l1 & l2 & Hll).
  exists l1, l2.
  now rewrite Hll.
} {
  specialize (IHla Hfd).
  destruct IHla as (y & la1 & la2 & la3 & Hll).
  now exists y, ((n, a) :: la1), la2, la3; rewrite Hll.
}
Qed.

Theorem find_dup_none : ∀ la,
  find_dup la = None → NoDup (map snd la).
Proof.
intros * Hnd.
induction la as [| a]; [ constructor | cbn ].
constructor. {
  cbn in Hnd.
  destruct a as (n, a).
  remember (find _ _) as b eqn:Hb; symmetry in Hb.
  destruct b; [ now destruct p | ].
  specialize (find_none _ _ Hb) as H1; cbn in H1; cbn.
  intros Ha.
  specialize (IHla Hnd).
  clear - IHla H1 Ha.
  induction la as [ | b]; [ easy | ].
  cbn in Ha.
  cbn in IHla.
  destruct Ha as [Ha| Ha]. {
    subst a.
    specialize (H1 b (or_introl eq_refl)).
    now apply Nat.eqb_neq in H1.
  } {
    apply NoDup_cons_iff in IHla.
    destruct IHla as (Hn, Hnd).
    specialize (IHla0 Hnd).
    apply IHla0; [ | easy ].
    intros x Hx.
    now apply H1; right.
  }
} {
  apply IHla.
  cbn in Hnd.
  destruct a as (n, a).
  remember (find _ _) as b eqn:Hb; symmetry in Hb.
  destruct b; [ now destruct p | easy ].
}
Qed.

Theorem pigeonhole : ∀ a b f x x',
  b < a
  → (∀ x, x < a → f x < b)
  → pigeonhole_fun a f = (x, x')
  → x < a ∧ x' < a ∧ x ≠ x' ∧ f x = f x'.
Proof.
intros * Hba Hf Hpf.
unfold pigeonhole_fun in Hpf.
remember (find_dup _) as fd eqn:Hfd.
symmetry in Hfd.
destruct fd as [(n, n') |]. {
  injection Hpf; clear Hpf; intros; subst n n'.
  specialize (find_dup_some _ _ _ Hfd) as (y & la1 & la2 & la3 & Hll).
  assert (Hxy : (x, y) ∈ map (λ n, (n, f n)) (seq 0 a)). {
    rewrite Hll.
    apply in_app_iff.
    now right; left.
  }
  apply in_map_iff in Hxy.
  destruct Hxy as (z & Hxy & Hz).
  injection Hxy; clear Hxy; intros; subst z y.
  assert (Hxy : (x', f x) ∈ map (λ n, (n, f n)) (seq 0 a)). {
    rewrite Hll.
    apply in_app_iff.
    right; right.
    apply in_app_iff.
    now right; left.
  }
  apply in_map_iff in Hxy.
  destruct Hxy as (z & Hxy & Hz').
  injection Hxy; clear Hxy; intros Hff H1; subst z.
  apply in_seq in Hz.
  apply in_seq in Hz'.
  split; [ easy | ].
  split; [ easy | ].
  split; [ | easy ].
  clear - Hll.
  assert (H : NoDup (map (λ n, (n, f n)) (seq 0 a))). {
    apply FinFun.Injective_map_NoDup; [ | apply seq_NoDup ].
    intros b c Hbc.
    now injection Hbc.
  }
  rewrite Hll in H.
  apply NoDup_remove_2 in H.
  intros Hxx; apply H; subst x'.
  apply in_app_iff; right.
  now apply in_app_iff; right; left.
} {
  apply find_dup_none in Hfd.
  rewrite map_map in Hfd.
  cbn in Hfd.
  exfalso; clear x x' Hpf.
  revert a f Hba Hf Hfd.
  induction b; intros; [ now specialize (Hf _ Hba) | ].
  destruct a; [ flia Hba | ].
  apply Nat.succ_lt_mono in Hba.
  remember (filter (λ i, f i =? b) (seq 0 (S a))) as la eqn:Hla.
  symmetry in Hla.
  destruct la as [| x1]. {
    assert (H : ∀ x, x < a → f x < b). {
      intros x Hx.
      destruct (Nat.eq_dec (f x) b) as [Hfxb| Hfxb]. {
        specialize (List_filter_nil _ _ Hla x) as H1.
        assert (H : x ∈ seq 0 (S a)). {
          apply in_seq.
          flia Hx.
        }
        specialize (H1 H); clear H; cbn in H1.
        now apply Nat.eqb_neq in H1.
      }
      assert (H : x < S a) by flia Hx.
      specialize (Hf x H); clear H.
      flia Hf Hfxb.
    }
    specialize (IHb a f Hba H); clear H.
    rewrite <- Nat.add_1_r in Hfd.
    rewrite seq_app in Hfd; cbn in Hfd.
    rewrite map_app in Hfd; cbn in Hfd.
    specialize (NoDup_remove_1 _ _ _ Hfd) as H1.
    now rewrite app_nil_r in H1.
  }
  destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
    subst b.
    destruct a; [ flia Hba | ].
    specialize (Hf a) as H1.
    assert (H : a < S (S a)) by flia.
    specialize (H1 H); clear H.
    specialize (Hf (S a) (Nat.lt_succ_diag_r _)) as H2.
    apply Nat.lt_1_r in H1.
    apply Nat.lt_1_r in H2.
    do 2 rewrite <- Nat.add_1_r in Hfd.
    do 2 rewrite seq_app in Hfd; cbn in Hfd.
    rewrite <- app_assoc in Hfd.
    do 2 rewrite map_app in Hfd.
    cbn in Hfd.
    apply NoDup_remove_2 in Hfd.
    apply Hfd.
    apply in_app_iff; right.
    now rewrite H1, Nat.add_1_r, H2; left.
  }
  destruct la as [| x2]. {
    specialize (IHb a (λ i, if lt_dec i x1 then f i else f (i + 1)) Hba).
    cbn in IHb.
    assert (H : ∀ x, x < a → (if lt_dec x x1 then f x else f (x + 1)) < b). {
      intros x Hx.
      destruct (lt_dec x x1) as [Hxx| Hxx]. {
        assert (Hxb : f x ≠ b). {
          intros Hxb.
          assert (H : x ∈ filter (λ i, f i =? b) (seq 0 (S a))). {
            apply filter_In.
            split; [ apply in_seq; cbn; flia Hx | ].
            now apply Nat.eqb_eq.
          }
          rewrite Hla in H.
          destruct H as [H| H]; [ flia Hxx H| easy ].
        }
      specialize (Hf x).
        assert (H : x < S a) by flia Hx.
        specialize (Hf H); clear H.
        flia Hf Hxb.
      }
      apply Nat.nlt_ge in Hxx.
      specialize (Hf (x + 1)).
      assert (H : x + 1 < S a) by flia Hx.
      specialize (Hf H); clear H.
      assert (Hxb : f (x + 1) ≠ b). {
        intros Hxb.
        assert (H : x + 1 ∈ filter (λ i, f i =? b) (seq 0 (S a))). {
          apply filter_In.
          split; [ apply in_seq; cbn; flia Hx | ].
          now apply Nat.eqb_eq.
        }
        rewrite Hla in H.
        destruct H as [H| H]; [ flia Hxx H| easy ].
      }
      flia Hf Hxb.
    }
    specialize (IHb H); clear H.
    apply IHb; clear - Hfd.
    specialize (proj1 (NoDup_map_iff 0 _ _) Hfd) as H1.
    apply (NoDup_map_iff 0).
    intros x x' Hx Hx' Hxx.
    rewrite seq_length in Hx, Hx', H1.
    rewrite seq_nth in Hxx; [ | easy ].
    rewrite seq_nth in Hxx; [ cbn | easy ].
    cbn in Hxx.
    destruct (lt_dec x x1) as [Hxx1| Hxx1]. {
      destruct (lt_dec x' x1) as [Hx'x1| Hx'x1]. {
        apply H1; [ flia Hx | flia Hx' | ].
        rewrite seq_nth; [ | flia Hx ].
        rewrite seq_nth; [ easy | flia Hx' ].
      } {
        apply Nat.nlt_ge in Hx'x1.
        assert (H : x = x' + 1). {
          apply H1; [ flia Hx | flia Hx' | ].
          rewrite seq_nth; [ | flia Hx ].
          rewrite seq_nth; [ easy | flia Hx' ].
        }
        flia Hxx1 Hx'x1 H.
      }
    }
    apply Nat.nlt_ge in Hxx1.
    destruct (lt_dec x' x1) as [Hx'x1| Hx'x1]. {
      assert (H : x + 1 = x'). {
        apply H1; [ flia Hx | flia Hx' | ].
        rewrite seq_nth; [ | flia Hx ].
        rewrite seq_nth; [ easy | flia Hx' ].
      }
      flia Hxx1 Hx'x1 H.
    } {
      apply Nat.nlt_ge in Hx'x1.
      apply (Nat.add_cancel_r _ _ 1).
      apply H1; [ flia Hx | flia Hx' | ].
      rewrite seq_nth; [ | flia Hx ].
      rewrite seq_nth; [ easy | flia Hx' ].
    }
  }
  assert (Hx1 : x1 ∈ x1 :: x2 :: la) by now left.
  assert (Hx2 : x2 ∈ x1 :: x2 :: la) by now right; left.
  rewrite <- Hla in Hx1.
  rewrite <- Hla in Hx2.
  apply filter_In in Hx1.
  apply filter_In in Hx2.
  destruct Hx1 as (Hx1, Hfx1).
  destruct Hx2 as (Hx2, Hfx2).
  apply Nat.eqb_eq in Hfx1.
  apply Nat.eqb_eq in Hfx2.
  assert (H : x1 ≠ x2). {
    intros H; subst x2.
    clear - Hla.
    specialize (seq_NoDup (S a) 0) as H1.
    specialize (NoDup_filter (λ i, f i =? b) _ H1) as H2.
    rewrite Hla in H2.
    apply NoDup_cons_iff in H2.
    destruct H2 as (H2, _); apply H2.
    now left.
  }
  clear - Hfd Hx1 Hx2 H Hfx1 Hfx2.
  remember (seq 0 (S a)) as l; clear a Heql.
  apply H; clear H.
  specialize (proj1 (NoDup_map_iff 0 l (λ x, f x)) Hfd) as H1.
  cbn in H1.
  apply (In_nth _ _ 0) in Hx1.
  apply (In_nth _ _ 0) in Hx2.
  destruct Hx1 as (n1 & Hn1 & Hx1).
  destruct Hx2 as (n2 & Hn2 & Hx2).
  specialize (H1 _ _ Hn1 Hn2) as H2.
  rewrite Hx1, Hx2, Hfx1, Hfx2 in H2.
  rewrite <- Hx1, <- Hx2.
  f_equal.
  now apply H2.
}
Qed.

Theorem Nat_eq_mod_divide_sum : ∀ n a b,
  n ≠ 0
  → a ≡ (n - b mod n) mod n
  → Nat.divide n (a + b).
Proof.
intros * Hnz Hab.
destruct (le_dec n (a + b mod n)) as [Hpx| Hpx]. {
  apply Nat_eq_mod_sub_0 in Hab.
  rewrite Nat_sub_sub_assoc in Hab. 2: {
    split; [ | easy ].
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite <- (Nat.mod_add _ 1) in Hab; [ | easy ].
  rewrite Nat.mul_1_l in Hab.
  rewrite Nat.sub_add in Hab; [ | easy ].
  rewrite Nat.add_mod_idemp_r in Hab; [ | easy ].
  now apply Nat.mod_divide in Hab.
} {
  apply Nat.nle_gt in Hpx.
  symmetry in Hab.
  apply Nat_eq_mod_sub_0 in Hab.
  rewrite Nat_sub_sub_swap, <- Nat.sub_add_distr in Hab.
  remember (a + b mod n) as v eqn:Hv.
  move Hab at bottom.
  destruct (Nat.eq_dec v 0) as [Hvz| Hvz]. 2: {
    destruct v; [ easy | ].
    rewrite Nat.mod_small in Hab; [ | flia Hpx ].
    flia Hpx Hab.
  }
  move Hvz at top; subst v.
  symmetry in Hv.
  apply Nat.eq_add_0 in Hv.
  destruct Hv as (Hxz, Hx'uz).
  subst a; cbn.
  now apply Nat.mod_divide in Hx'uz.
}
Qed.

Lemma odd_prime_sum_two_squares_plus_one_lt : ∀ x x' p (u := (p - 1) / 2) k,
  prime p
  → p mod 2 = 1
  → x' < p + 1
  → x ≤ u
  → u < x'
  → x ^ 2 + (x' - (u + 1)) ^ 2 + 1 = k * p
  → k < p.
Proof.
intros * Hp Hp2 Hx'p Hxu Hx'u Hk.
assert (Hpz : p ≠ 0) by now (intros H1; subst p).
  apply (Nat.mul_lt_mono_pos_r p); [ flia Hpz | ].
  rewrite <- Hk.
  apply (le_lt_trans _ (u ^ 2 + u ^ 2 + 1)). {
    apply Nat.add_le_mono_r.
    apply Nat.add_le_mono; [ now apply Nat.pow_le_mono_l | ].
    apply Nat.pow_le_mono_l.
    apply (Nat.add_le_mono_r _ _ (u + 1)).
    rewrite Nat.sub_add; [ | flia Hx'u ].
    rewrite Nat.add_assoc.
    replace (u + u) with (2 * u) by flia.
    unfold u.
    rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
      apply Nat.mod_divide; [ easy | ].
      specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H2.
      rewrite Hp2 in H2.
      rewrite H2, Nat.add_sub, Nat.mul_comm.
      now apply Nat.mod_mul.
    }
    rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
    flia Hx'p.
  } {
    specialize (prime_ge_2 p Hp) as H2p.
    specialize (Nat.div_mod (p - 1) 2 (Nat.neq_succ_0 _)) as H1.
    assert (H : (p - 1) mod 2 = 0). {
      specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H.
      rewrite H, Hp2, Nat.add_sub, Nat.mul_comm.
      now apply Nat.mod_mul.
    }
    rewrite H, Nat.add_0_r in H1; clear H.
    assert (H : p = 2 * u + 1). {
      unfold u.
      rewrite <- H1.
      rewrite Nat.sub_add; [ easy | flia H2p ].
    }
    rewrite H.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
    rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
    replace (u ^ 2 + u ^ 2) with (2 * u ^ 2) by flia.
    rewrite Nat.pow_2_r.
    rewrite Nat.add_assoc.
    apply Nat.add_lt_mono_r.
    rewrite Nat.mul_shuffle0.
    do 2 rewrite Nat.mul_assoc.
    enough (Hu : 0 < u) by flia Hu.
    unfold u.
    apply (Nat.mul_lt_mono_pos_r 2); [ flia | ].
    rewrite Nat.mul_0_l.
    rewrite Nat.mul_comm, <- H1.
    flia H2p.
  }
Qed.

Definition resolve_a2_b2_1 p :=
  let u := (p - 1) / 2 in
  let f i :=
    if le_dec i u then (i ^ 2) mod p
    else (p - ((i - (u + 1)) ^ 2 + 1) mod p) mod p
  in
  let (x, x') := pigeonhole_fun (p + 1) f in
  let (a, b) :=
    if le_dec x u then (x, x' - (u + 1))
    else (x', x - (u + 1))
  in
  (a, b, (a ^ 2 + b ^ 2 + 1) / p).

Definition check_resolve_a2_b2_1 p :=
  let '(a, b, n) := resolve_a2_b2_1 p in
  (p, n, a, b).

Compute (map check_resolve_a2_b2_1 (Primes.firstn_primes' 20)).

Lemma odd_prime_divides_sum_two_squares_plus_one : ∀ p a b n,
  prime p
  → p mod 2 = 1
  → resolve_a2_b2_1 p = (a, b, n)
  → 0 < n < p ∧ a ^ 2 + b ^ 2 + 1 = n * p.
Proof.
intros p aa bb n Hp Hp2 Hr.
assert
  (Ha :
   ∀ a a',
   a ≤ (p - 1) / 2
   → a' ≤ (p - 1) / 2
   → a ≠ a'
   → a ^ 2 ≢ a' ^ 2 mod p). {
  intros * Ha Ha' Haa.
  destruct (lt_dec a' a) as [Haa'| Haa']. {
    now apply le_half_prime_square_diff.
  } {
    assert (H : a < a') by flia Haa Haa'.
    intros H1.
    symmetry in H1.
    revert H1.
    now apply le_half_prime_square_diff.
  }
}
assert
  (Hb :
   ∀ b b',
   b ≤ (p - 1) / 2
   → b' ≤ (p - 1) / 2
   → b ≠ b'
   → (p - (b ^ 2 + 1) mod p) ≢ (p - (b' ^ 2 + 1) mod p) mod p). {
  intros * Hb Hb' Hbb H.
  assert (Hpz : p ≠ 0) by now (intros H1; subst p).
  remember ((b ^ 2 + 1) mod p) as b1 eqn:Hb1.
  remember ((b' ^ 2 + 1) mod p) as b'1 eqn:Hb'1.
  destruct (lt_dec b1 b'1) as [Hbb'| Hbb']. {
    apply Nat_eq_mod_sub_0 in H.
    replace (p - b1 - (p - b'1)) with (b'1 - b1) in H. 2: {
      specialize (Nat.mod_upper_bound (b' ^ 2 + 1) p Hpz) as H1.
      rewrite <- Hb'1 in H1.
      flia Hbb' H1.
    }
    apply Nat.mod_divide in H; [ | easy ].
    destruct H as (k, Hk).
    destruct k; [ flia Hk Hbb' | ].
    apply Nat.add_sub_eq_nz in Hk. 2: {
      now apply Nat.neq_mul_0.
    }
    specialize (Nat.mod_upper_bound (b' ^ 2 + 1) p Hpz) as H1.
    rewrite <- Hb'1, <- Hk in H1.
    flia H1.
  }
  destruct (lt_dec b'1 b1) as [Hbb'1| Hbb'1]. {
    symmetry in H.
    apply Nat_eq_mod_sub_0 in H.
    replace (p - b'1 - (p - b1)) with (b1 - b'1) in H. 2: {
      specialize (Nat.mod_upper_bound (b ^ 2 + 1) p Hpz) as H1.
      rewrite <- Hb1 in H1.
      flia Hbb' H1.
    }
    apply Nat.mod_divide in H; [ | easy ].
    destruct H as (k, Hk).
    destruct k; [ flia Hk Hbb'1 | ].
    apply Nat.add_sub_eq_nz in Hk. 2: {
      now apply Nat.neq_mul_0.
    }
    specialize (Nat.mod_upper_bound (b ^ 2 + 1) p Hpz) as H1.
    rewrite <- Hb1, <- Hk in H1.
    flia H1.
  }
  replace b'1 with b1 in * by flia Hbb' Hbb'1.
  clear Hbb' Hbb'1 H.
  rewrite Hb'1 in Hb1.
  destruct (lt_dec b b') as [Hbb'| Hbb']. {
    revert Hb1.
    now apply le_half_prime_succ_square_diff.
  } {
    symmetry in Hb1.
    revert Hb1.
    apply le_half_prime_succ_square_diff; try easy.
    apply Nat.nlt_ge in Hbb'.
    flia Hbb Hbb'.
  }
}
(* pigeonhole *)
unfold resolve_a2_b2_1 in Hr.
assert (Hpz : p ≠ 0) by now (intros H1; subst p).
set (u := (p - 1) / 2) in *.
set
  (f i :=
     if le_dec i u then (i ^ 2) mod p
     else (p - ((i - (u + 1)) ^ 2 + 1) mod p) mod p) in Hr.
remember (pigeonhole_fun (p + 1) f) as xx eqn:Hxx.
symmetry in Hxx.
destruct xx as (x, x').
specialize (pigeonhole (p + 1) p f x x') as H1.
assert (H : p < p + 1) by flia.
specialize (H1 H); clear H.
assert (H : ∀ x, x < p + 1 → f x < p). {
  intros x1 Hx.
  unfold f; cbn - [ "/" ].
  destruct (le_dec x1 u); now apply Nat.mod_upper_bound.
}
specialize (H1 H Hxx); clear H.
destruct H1 as (Hxp & Hx'p & Hxx' & Hfxx).
unfold f in Hfxx.
destruct (le_dec x u) as [Hxu| Hxu]. {
  injection Hr; clear Hr; intros Hn Hbb Haa.
  rewrite Haa, Hbb in Hn.
  do 2 rewrite Nat.mul_1_r, <- Nat.pow_2_r in Hn.
  destruct (le_dec x' u) as [Hx'u| Hx'u]. {
    now specialize (Ha x x' Hxu Hx'u Hxx') as H1.
  }
  apply Nat.nle_gt in Hx'u.
  specialize (Nat_eq_mod_divide_sum p _ _ Hpz Hfxx) as H1.
  rewrite Nat.add_assoc in H1.
  destruct H1 as (k, Hk).
  rewrite Haa, Hbb in Hk.
  rewrite Hk, Nat.div_mul in Hn; [ | easy ].
  subst k.
  split; [ | easy ].
  rewrite <- Haa, <- Hbb in Hk.
  split. {
    destruct n; [ | flia ].
    now rewrite Nat.add_1_r in Hk.
  }
  now apply (odd_prime_sum_two_squares_plus_one_lt x x').
}
apply Nat.nle_gt in Hxu.
destruct (le_dec x' u) as [Hx'u| Hx'u]. {
  injection Hr; clear Hr; intros Hn Hbb Haa.
  rewrite Haa, Hbb in Hn.
  do 2 rewrite Nat.mul_1_r, <- Nat.pow_2_r in Hn.
  symmetry in Hfxx.
  specialize (Nat_eq_mod_divide_sum p _ _ Hpz Hfxx) as H1.
  rewrite Nat.add_assoc in H1.
  destruct H1 as (k, Hk).
  rewrite Haa, Hbb in Hk.
  rewrite Hk, Nat.div_mul in Hn; [ | easy ].
  subst k.
  split; [ | easy ].
  rewrite <- Haa, <- Hbb in Hk.
  split. {
    destruct n; [ | flia ].
    now rewrite Nat.add_1_r in Hk.
  }
  now apply (odd_prime_sum_two_squares_plus_one_lt x' x).
}
apply Nat.nle_gt in Hx'u.
specialize (Hb (x - (u + 1)) (x' - (u + 1))) as H1.
exfalso; apply H1; [ | | | easy ]. {
  apply (Nat.add_le_mono_r _ _ (u + 1)).
  rewrite Nat.sub_add; [ | flia Hxu ].
  replace (u + (u + 1)) with (2 * u + 1) by flia.
  unfold u.
  rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
    apply Nat.mod_divide; [ easy | ].
    specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H2.
    rewrite Hp2 in H2.
    rewrite H2, Nat.add_sub, Nat.mul_comm.
    now apply Nat.mod_mul.
  }
  rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
  flia Hxp.
} {
  apply (Nat.add_le_mono_r _ _ (u + 1)).
  rewrite Nat.sub_add; [ | flia Hx'u ].
  replace (u + (u + 1)) with (2 * u + 1) by flia.
  unfold u.
  rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
    apply Nat.mod_divide; [ easy | ].
    specialize (Nat.div_mod p 2 (Nat.neq_succ_0 _)) as H2.
    rewrite Hp2 in H2.
    rewrite H2, Nat.add_sub, Nat.mul_comm.
    now apply Nat.mod_mul.
  }
  rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
  flia Hx'p.
} {
  intros H; apply Hxx'.
  apply (Nat.add_cancel_r _ _ (u + 1)) in H.
  rewrite Nat.sub_add in H; [ | flia Hxu ].
  rewrite Nat.sub_add in H; [ | flia Hx'u ].
  easy.
}
Qed.

Check Euler_s_four_square_identity_v2.

Definition four_square_sol p :=
  { mx &
    let '(m, (x1, x2, x3, x4)) := mx in
    m ≠ 0 ∧
    x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 = m * p }.

Theorem four_square_multiple : ∀ p,
  prime p
  → four_square_sol p.
Proof.
intros p Hp.
destruct (Nat.eq_dec p 2) as [Hp2| Hpn2]. {
  subst p.
  now exists (1, (1, 1, 0, 0)).
}
specialize (odd_prime p Hp Hpn2) as Hp2.
remember (resolve_a2_b2_1 p) as abn eqn:Hres.
symmetry in Hres.
destruct abn as ((a, b), n).
specialize (odd_prime_divides_sum_two_squares_plus_one p a b n Hp Hp2) as H1.
specialize (H1 Hres).
destruct H1 as (Hnp, Hsum).
exists (n, (a, b, 1, 0)).
rewrite Nat.pow_1_l, Nat.add_0_r.
split; [ flia Hnp | easy ].
Qed.

Definition best_four_square_sol p :=
  { mx : four_square_sol p &
    ∀ nx : four_square_sol p, fst (projT1 mx) ≤ fst (projT1 nx) }.

Theorem glop : ∀ p (mx : best_four_square_sol p),
  prime p
  → p mod 2 = 1
  → fst (projT1 (projT1 mx)) = 1.
Proof.
intros * Hp Hp2.
assert (Hpz : p ≠ 0) by now (intros H; subst p).
destruct mx as (m, Hmx); cbn.
destruct m as (m, Hm); cbn.
cbn in Hmx.
destruct m as (m, (((x1, x2), x3), x4)).
cbn in Hmx; cbn.
destruct Hm as (Hmz, Hm).
specialize (Nat.div_mod x1 m Hmz) as Hx1.
specialize (Nat.div_mod x2 m Hmz) as Hx2.
specialize (Nat.div_mod x3 m Hmz) as Hx3.
specialize (Nat.div_mod x4 m Hmz) as Hx4.
set (v := m / 2).
set (f x := (if le_dec (x mod m) v then x mod m else m - x mod m) ^ 2).
set (sqr_y1 := f x1).
set (sqr_y2 := f x2).
set (sqr_y3 := f x3).
set (sqr_y4 := f x4).
assert (Hx : ∀ x, f x ≤ v ^ 2). {
  intros; unfold f.
  destruct (le_dec (x mod m) v) as [Hx1v| Hx1v]. {
    now apply Nat.pow_le_mono_l.
  } {
    apply Nat.nle_gt in Hx1v.
    apply Nat.pow_le_mono_l.
    apply (Nat.add_le_mono_r _ _ (x mod m)).
    rewrite Nat.sub_add. 2: {
      now apply Nat.lt_le_incl, Nat.mod_upper_bound.
    }
    transitivity (v + (v + 1)). 2: {
      apply Nat.add_le_mono_l.
      now rewrite Nat.add_1_r.
    }
    replace (v + (v + 1)) with (2 * v + 1) by flia.
    unfold v.
    specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
    rewrite H1 at 1.
    apply Nat.add_le_mono_l.
    apply lt_n_Sm_le.
    now apply Nat.mod_upper_bound.
  }
}
assert (Hy1 : sqr_y1 ≤ v ^ 2) by apply Hx.
assert (Hy2 : sqr_y2 ≤ v ^ 2) by apply Hx.
assert (Hy3 : sqr_y3 ≤ v ^ 2) by apply Hx.
assert (Hy4 : sqr_y4 ≤ v ^ 2) by apply Hx.
assert (Hym : (sqr_y1 + sqr_y2 + sqr_y3 + sqr_y4) mod m = 0). {
  assert (Hxy2 : ∀ x, x ^ 2 ≡ f x mod m). {
    intros x.
    unfold f.
    destruct (le_dec (x mod m) v) as [Hxv| Hxv]. {
      now rewrite Nat_mod_pow_mod.
    } {
      rewrite Nat_sqr_sub. 2: {
        now apply Nat.lt_le_incl, Nat.mod_upper_bound.
      }
      symmetry.
      rewrite <- (Nat.mod_add _ (2 * (x mod m))); [ | easy ].
      rewrite Nat.mul_shuffle0.
      rewrite Nat.sub_add. 2: {
        remember (x mod m) as y.
        replace m with (y + (m - y)). 2: {
          rewrite Nat.add_comm, Nat.sub_add; [ easy | ].
          rewrite Heqy.
          now apply Nat.lt_le_incl, Nat.mod_upper_bound.
        }
        rewrite Nat_sqr_add.
        rewrite Nat.mul_add_distr_l.
        rewrite <- Nat.mul_assoc, <- Nat.pow_2_r.
        flia.
      }
      rewrite <- Nat.add_mod_idemp_l; [ | easy ].
      rewrite <- Nat_mod_pow_mod.
      rewrite Nat.mod_same; [ | easy ].
      rewrite Nat.pow_0_l; [ | easy ].
      rewrite Nat.mod_0_l; [ | easy ].
      rewrite Nat.add_0_l.
      now rewrite Nat_mod_pow_mod.
    }
  }
  unfold sqr_y1, sqr_y2, sqr_y3, sqr_y4.
  rewrite Nat.add_mod; [ | easy ].
  rewrite (Nat.add_mod (_ + _)); [ | easy ].
  rewrite Nat.add_mod_idemp_l; [ | easy ].
  rewrite (Nat.add_mod (f x1)); [ | easy ].
  rewrite <- Nat.add_assoc.
  rewrite Nat.add_mod_idemp_l; [ | easy ].
  rewrite Nat.add_assoc.
  do 4 rewrite <- Hxy2.
  rewrite Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.add_comm, Nat.add_assoc.
  rewrite Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.add_comm.
  do 2 rewrite Nat.add_assoc.
  rewrite Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.add_comm, Nat.add_assoc.
  rewrite Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.add_comm.
  do 2 rewrite Nat.add_assoc.
  rewrite Hm.
  rewrite Nat.mul_comm.
  now apply Nat.mod_mul.
}
apply Nat.mod_divide in Hym; [ | easy ].
destruct Hym as (r, Hr).
assert (Hrm : r ≤ m). {
  apply (Nat.mul_le_mono_pos_r _ _ m); [ flia Hmz | ].
  rewrite <- Hr.
  transitivity (v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2). {
    apply Nat.add_le_mono; [ | easy ].
    apply Nat.add_le_mono; [ | easy ].
    now apply Nat.add_le_mono.
  }
  unfold v.
  specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
  replace (_ + _ + _ + _) with (4 * (m / 2) ^ 2) by flia.
  rewrite <- Nat.pow_2_r.
  rewrite H1 at 2.
  rewrite Nat_sqr_add.
  rewrite Nat.pow_mul_l.
  replace (2 ^ 2) with 4 by easy.
  flia.
}
assert (Hmn : m < p). {
  remember (resolve_a2_b2_1 p) as abn eqn:Habn.
  symmetry in Habn.
  destruct abn as ((a, b), n).
  specialize (odd_prime_divides_sum_two_squares_plus_one p a b n) as H1.
  specialize (H1 Hp Hp2 Habn).
  destruct H1 as (Hnp, Habnp).
  assert (Hnz : n ≠ 0) by flia Hnp.
  transparent assert (H1 : four_square_sol p). {
    unfold four_square_sol.
    exists (n, (a, b, 1, 0)).
    split; [ easy | ].
    rewrite Nat.pow_1_l, Nat.pow_0_l; [ | easy ].
    now rewrite Nat.add_0_r.
  }
  specialize (Hmx H1) as H2.
  cbn in H2.
  flia Hnp H2.
}
destruct (Nat.eq_dec r m) as [Hrme| Hrme]. {
  subst r; clear Hrm.
  assert (Hme : m mod 2 = 0). {
    enough (H : m mod 2 ≠ 1). {
      specialize (Nat.mod_upper_bound m 2 (Nat.neq_succ_0 _)) as H1.
      flia H H1.
    }
    intros Hm21.
    specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
    rewrite Hm21 in H1.
    assert (sqr_y1 + sqr_y2 + sqr_y3 + sqr_y4 < m * m). {
      apply (le_lt_trans _ (4 * ((m - 1) / 2) ^ 2)). {
        rewrite H1, Nat.add_sub.
        rewrite (Nat.mul_comm 2), Nat.div_mul; [ | easy ].
        fold v.
        transitivity (v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2). {
          flia Hy1 Hy2 Hy3 Hy4.
        }
        flia.
      } {
        rewrite H1 at 1.
        rewrite Nat.add_sub.
        rewrite (Nat.mul_comm 2), Nat.div_mul; [ | easy ].
        rewrite Nat.pow_2_r.
        replace 4 with (2 * 2) by flia.
        rewrite Nat.mul_shuffle0.
        rewrite Nat.mul_assoc.
        rewrite <- Nat.mul_assoc.
        apply Nat.mul_lt_mono; flia H1.
      }
    }
    flia Hr H.
  }
  (* each sqr_yi must be equal to v², i.e. (m/2)²
     therefore xi mod m = m / 2,
     then Σ xi² = mp = Σ (mqi+m/2)² = Σ (m²qi²+(m/2)²+2mqim/2)
     = m²Σ qi² + m² + Σ m²qi = m² (Σ qi² + 1 + Σ qi) = mp
     → impossible since m < p *)
  assert
    (Hy :
     sqr_y1 = v ^ 2 ∧ sqr_y2 = v ^ 2 ∧ sqr_y3 = v ^ 2 ∧ sqr_y4 = v ^ 2). {
    enough
      (Hy :
       ¬ (sqr_y1 ≠ v ^ 2) ∧ ¬ (sqr_y2 ≠ v ^ 2) ∧
       ¬ (sqr_y3 ≠ v ^ 2) ∧ ¬ (sqr_y4 ≠ v ^ 2)). {
      destruct Hy as (H1 & H2 & H3 & H4).
      apply Nat.eq_dne in H1.
      apply Nat.eq_dne in H2.
      apply Nat.eq_dne in H3.
      apply Nat.eq_dne in H4.
      easy.
    }
    assert (Hvvmm : v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2 ≤ m * m). {
      unfold v.
      specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
      rewrite Hme, Nat.add_0_r in H1.
      rewrite H1 at 5 6.
      rewrite Nat.pow_2_r.
      flia.
    }
    rewrite <- and_assoc.
    split. {
      apply Decidable.not_or.
      intros [Hss| Hss]. {
        assert (Hs1 : sqr_y1 < v ^ 2) by flia Hy1 Hss.
        assert (H : sqr_y1 + sqr_y2 + sqr_y3 + sqr_y4 < m * m). {
          apply (Nat.lt_le_trans _ (v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2)). {
            flia Hs1 Hy2 Hy3 Hy4.
          }
          easy.
        }
        flia Hr H.
      } {
        assert (Hs1 : sqr_y2 < v ^ 2) by flia Hy2 Hss.
        assert (H : sqr_y1 + sqr_y2 + sqr_y3 + sqr_y4 < m * m). {
          apply (Nat.lt_le_trans _ (v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2)). {
            flia Hy1 Hs1 Hy3 Hy4.
          }
          easy.
        }
        flia Hr H.
      }
    } {
      apply Decidable.not_or.
      intros [Hss| Hss]. {
        assert (Hs1 : sqr_y3 < v ^ 2) by flia Hy3 Hss.
        assert (H : sqr_y1 + sqr_y2 + sqr_y3 + sqr_y4 < m * m). {
          apply (Nat.lt_le_trans _ (v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2)). {
            flia Hy1 Hy2 Hs1 Hy4.
          }
          easy.
        }
        flia Hr H.
      } {
        assert (Hs1 : sqr_y4 < v ^ 2) by flia Hy4 Hss.
        assert (H : sqr_y1 + sqr_y2 + sqr_y3 + sqr_y4 < m * m). {
          apply (Nat.lt_le_trans _ (v ^ 2 + v ^ 2 + v ^ 2 + v ^ 2)). {
            flia Hy1 Hy2 Hy3 Hs1.
          }
          easy.
        }
        flia Hr H.
      }
    }
  }
  (* therefore xi mod m = m / 2 *)
  destruct Hy as (Hsy1 & Hsy2 & Hsy3 & Hsy4).
  clear Hy1 Hy2 Hy3 Hy4.
  unfold f in sqr_y1, sqr_y2, sqr_y3, sqr_y4.
  assert (Hsy : ∀ x, m / 2 < x mod m → m - x mod m = m / 2 → False). {
    clear - Hmz Hme.
    intros * Hxv Hsy.
    apply Nat.add_sub_eq_nz in Hsy. 2: {
      intros Hv.
      specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
      now rewrite Hv, Hme in H1.
    }
    assert (Hxm2 : x mod m = m / 2). {
      replace (m / 2) with (m - m / 2). {
        rewrite <- Hsy at 2.
        now rewrite Nat.add_sub.
      } {
        specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
        rewrite Hme, Nat.add_0_r in H1.
        flia H1.
      }
    }
    flia Hxv Hxm2.
  }
  destruct (le_dec (x1 mod m) v) as [Hx1v| Hx1v]. 2: {
    apply Nat.nle_gt in Hx1v.
    apply Nat.pow_inj_l in Hsy1; [ | easy ].
    subst sqr_y1 v.
    now exfalso; apply (Hsy x1).
  }
  destruct (le_dec (x2 mod m) v) as [Hx2v| Hx2v]. 2: {
    apply Nat.nle_gt in Hx2v.
    apply Nat.pow_inj_l in Hsy2; [ | easy ].
    subst sqr_y2 v.
    now exfalso; apply (Hsy x2).
  }
  destruct (le_dec (x3 mod m) v) as [Hx3v| Hx3v]. 2: {
    apply Nat.nle_gt in Hx3v.
    apply Nat.pow_inj_l in Hsy3; [ | easy ].
    subst sqr_y3 v.
    now exfalso; apply (Hsy x3).
  }
  destruct (le_dec (x4 mod m) v) as [Hx4v| Hx4v]. 2: {
    apply Nat.nle_gt in Hx4v.
    apply Nat.pow_inj_l in Hsy4; [ | easy ].
    subst sqr_y4 v.
    now exfalso; apply (Hsy x4).
  }
  move Hx2v before Hx1v.
  move Hx3v before Hx2v.
  move Hx4v before Hx3v.
  clear Hsy.
  unfold sqr_y1 in Hsy1.
  unfold sqr_y2 in Hsy2.
  unfold sqr_y3 in Hsy3.
  unfold sqr_y4 in Hsy4.
  apply Nat.pow_inj_l in Hsy1; [ | easy ].
  apply Nat.pow_inj_l in Hsy2; [ | easy ].
  apply Nat.pow_inj_l in Hsy3; [ | easy ].
  apply Nat.pow_inj_l in Hsy4; [ | easy ].
  clear Hx1v Hx2v Hx3v Hx4v.
  rewrite Hsy1 in Hx1.
  rewrite Hsy2 in Hx2.
  rewrite Hsy3 in Hx3.
  rewrite Hsy4 in Hx4.
  (* then Σ xi² = mp = Σ (mqi+m/2)² = Σ (m²qi²+(m/2)²+2mqim/2)
     = m²Σ qi² + m² + Σ m²qi = m² (Σ qi² + 1 + Σ qi) = mp *)
  move Hm at bottom.
  rewrite Hx1, Hx2, Hx3, Hx4 in Hm.
  do 4 rewrite Nat_sqr_add in Hm.
  remember (x1 / m) as q1 eqn:Hq1.
  remember (x2 / m) as q2 eqn:Hq2.
  remember (x3 / m) as q3 eqn:Hq3.
  remember (x4 / m) as q4 eqn:Hq4.
  move q4 before q1; move q3 before q1; move q2 before q1.
  move Hq4 before Hq1; move Hq3 before Hq1; move Hq2 before Hq1.
  unfold v in Hm.
  setoid_rewrite (Nat.mul_shuffle0 2) in Hm.
  rewrite <- (Nat.divide_div_mul_exact m) in Hm; [ | easy | ]. 2: {
    now apply Nat.mod_divide in Hme.
  }
  rewrite (Nat.mul_comm 2) in Hm.
  rewrite Nat.div_mul in Hm; [ | easy ].
  ring_simplify in Hm.
  do 7 rewrite <- Nat.add_assoc in Hm.
  rewrite Nat.add_comm in Hm.
  do 6 rewrite Nat.add_assoc in Hm.
  replace (4 * (m / 2) ^ 2) with (m ^ 2) in Hm. 2: {
    specialize (Nat.div_mod m 2 (Nat.neq_succ_0 _)) as H1.
    rewrite Hme, Nat.add_0_r in H1.
    replace 4 with (2 ^ 2) by easy.
    rewrite <- Nat.pow_mul_l.
    now rewrite <- H1.
  }
  rewrite <- Nat.pow_2_r in Hm.
  do 4 rewrite Nat.pow_mul_l in Hm.
  replace (m ^ 2) with (m ^ 2 * 1) in Hm at 1 by flia.
  do 8 rewrite <- Nat.mul_add_distr_l in Hm.
  rewrite Nat.pow_2_r, <- Nat.mul_assoc in Hm.
  apply Nat.mul_cancel_l in Hm; [ | easy ].
  destruct (Nat.eq_dec (q1 + q2 + q3 + q4) 0) as [Hqz| Hqz]. {
    apply Nat.eq_add_0 in Hqz.
    destruct Hqz as (Hqz, H); move H at top; subst q4.
    apply Nat.eq_add_0 in Hqz.
    destruct Hqz as (Hqz, H); move H at top; subst q3.
    apply Nat.eq_add_0 in Hqz.
    destruct Hqz as (Hqz, H); move H at top; subst q2.
    move Hqz at top; subst q1.
    cbn in Hm.
    rewrite Nat.mul_1_r in Hm.
    flia Hmn Hm.
  }
  move Hp at bottom.
  rewrite <- Hm in Hp.
  apply prime_not_mul in Hp.
  destruct Hp as [Hp| Hp]; [ easy | ].
  flia Hp Hqz.
}
destruct (Nat.eq_dec r 0) as [Hrz| Hrz]. {
  subst r.
  clear Hy1 Hy2 Hy3 Hy4 Hrm.
  apply Nat.neq_sym in Hrme.
  apply Nat.eq_add_0 in Hr.
  destruct Hr as (Hr, Hr4).
  apply Nat.eq_add_0 in Hr.
  destruct Hr as (Hr, Hr3).
  apply Nat.eq_add_0 in Hr.
  destruct Hr as (Hr1, Hr2).
  unfold sqr_y1, f in Hr1.
  unfold sqr_y2, f in Hr2.
  unfold sqr_y3, f in Hr3.
  unfold sqr_y4, f in Hr4.
  destruct (le_dec (x1 mod m) v) as [Hx1v| Hx1v]. 2: {
    apply Nat.pow_eq_0 in Hr1; [ | easy ].
    specialize (Nat.mod_upper_bound x1 m Hrme) as H1.
    flia Hr1 H1.
  }
  destruct (le_dec (x2 mod m) v) as [Hx2v| Hx2v]. 2: {
    apply Nat.pow_eq_0 in Hr2; [ | easy ].
    specialize (Nat.mod_upper_bound x2 m Hrme) as H2.
    flia Hr2 H2.
  }
  destruct (le_dec (x3 mod m) v) as [Hx3v| Hx3v]. 2: {
    apply Nat.pow_eq_0 in Hr3; [ | easy ].
    specialize (Nat.mod_upper_bound x3 m Hrme) as H3.
    flia Hr3 H3.
  }
  destruct (le_dec (x4 mod m) v) as [Hx4v| Hx4v]. 2: {
    apply Nat.pow_eq_0 in Hr4; [ | easy ].
    specialize (Nat.mod_upper_bound x4 m Hrme) as H4.
    flia Hr4 H4.
  }
  apply Nat.pow_eq_0 in Hr1; [ | easy ].
  apply Nat.pow_eq_0 in Hr2; [ | easy ].
  apply Nat.pow_eq_0 in Hr3; [ | easy ].
  apply Nat.pow_eq_0 in Hr4; [ | easy ].
  clear Hx1v Hx2v Hx3v Hx4v.
  move Hm at bottom.
  rewrite Hx1, Hr1, Nat.add_0_r in Hm.
  rewrite Hx2, Hr2, Nat.add_0_r in Hm.
  rewrite Hx3, Hr3, Nat.add_0_r in Hm.
  rewrite Hx4, Hr4, Nat.add_0_r in Hm.
  do 4 rewrite Nat.pow_mul_l in Hm.
  do 3 rewrite <- Nat.mul_add_distr_l in Hm.
  rewrite Nat.pow_2_r, <- Nat.mul_assoc in Hm.
  apply Nat.mul_cancel_l in Hm; [ | easy ].
  rewrite <- Hm in Hp.
  move Hp at bottom.
  apply prime_not_mul in Hp.
  destruct Hp as [Hp| Hp]; [ easy | ].
  rewrite Hp, Nat.mul_1_r in Hm.
  flia Hmn Hm.
}
(*
specialize (Euler_s_four_square_identity_v2 x1 x2 x3 x4) as H1.
*)
Require Import ZArith.
specialize (Z_Euler_s_four_square_identity_v2) as H1.
unfold Z_diff in H1.
set (zx1 := Z.of_nat x1).
set (zx2 := Z.of_nat x2).
set (zx3 := Z.of_nat x3).
set (zx4 := Z.of_nat x4).
set
  (g x :=
     if le_dec (x mod m) v then Z.of_nat (x mod m)
     else (Z.of_nat (x mod m) - Z.of_nat m)%Z).
set (zy1 := g x1).
set (zy2 := g x2).
set (zy3 := g x3).
set (zy4 := g x4).
specialize (H1 zx1 zx2 zx3 zx4 zy1 zy2 zy3 zy4).
replace (zx1 ^ 2 + zx2 ^ 2 + zx3 ^ 2 + zx4 ^ 2)%Z with (Z.of_nat (m * p))
  in H1. 2: {
  unfold zx1, zx2, zx3, zx4.
  do 4 rewrite Z.pow_2_r.
  do 4 rewrite <- Nat2Z.inj_mul.
  do 3 rewrite <- Nat2Z.inj_add.
  do 4 rewrite <- Nat.pow_2_r.
  now rewrite Hm.
}
assert (Hgf : ∀ x, (g x ^ 2 = Z.of_nat (f x))%Z). {
  intros x.
  unfold g, f.
  destruct (le_dec (x mod m) v) as [Hxv| Hxv]. {
    rewrite Z.pow_2_r, Nat.pow_2_r.
    now rewrite Nat2Z.inj_mul.
  } {
    apply Nat.nle_gt in Hxv.
    rewrite Z.pow_2_r, Nat.pow_2_r.
    rewrite Nat2Z.inj_mul.
    rewrite Nat2Z.inj_sub. 2: {
      now apply Nat.lt_le_incl, Nat.mod_upper_bound.
    }
    rewrite <- Z.opp_involutive.
    rewrite <- Z.mul_opp_l.
    rewrite Z.opp_sub_distr.
    rewrite Z.add_comm.
    rewrite <- Z.mul_opp_r.
    rewrite Z.opp_sub_distr.
    rewrite (Z.add_comm (- Z.of_nat m)%Z).
    easy.
  }
}
replace (zy1 ^ 2 + zy2 ^ 2 + zy3 ^ 2 + zy4 ^ 2)%Z with (Z.of_nat (r * m))
  in H1. 2: {
  unfold zy1, zy2, zy3, zy4.
  do 4 rewrite Hgf.
  do 3 rewrite <- Nat2Z.inj_add.
  fold sqr_y1 sqr_y2 sqr_y3 sqr_y4.
  now rewrite Hr.
}
rewrite <- Nat2Z.inj_mul in H1.
set (z1 := (zx1 * zy1 + zx2 * zy2 + zx3 * zy3 + zx4 * zy4)%Z) in H1.
assert (Hz1 : (z1 mod Z.of_nat m = 0)%Z). {
  assert
    (Hz :
       (Z.of_nat
          (x1 * (x1 mod m) + x2 * (x2 mod m) +
           x3 * (x3 mod m) + x4 * (x4 mod m)) mod Z.of_nat m)%Z = 0%Z). {
    rewrite <- mod_Zmod; [ | easy ].
    replace 0%Z with (Z.of_nat 0) by easy.
    f_equal.
    rewrite <- Nat.add_mod_idemp_r; [ | easy ].
    rewrite Nat.mul_mod_idemp_r; [ | easy ].
    rewrite Nat.add_mod_idemp_r; [ | easy ].
    rewrite Nat.add_comm.
    do 2 rewrite Nat.add_assoc.
    rewrite <- Nat.add_mod_idemp_r; [ | easy ].
    rewrite Nat.mul_mod_idemp_r; [ | easy ].
    rewrite Nat.add_mod_idemp_r; [ | easy ].
    rewrite Nat.add_comm.
    do 2 rewrite Nat.add_assoc.
    rewrite <- Nat.add_mod_idemp_r; [ | easy ].
    rewrite Nat.mul_mod_idemp_r; [ | easy ].
    rewrite Nat.add_mod_idemp_r; [ | easy ].
    rewrite Nat.add_comm.
    do 2 rewrite Nat.add_assoc.
    rewrite <- Nat.add_mod_idemp_r; [ | easy ].
    rewrite Nat.mul_mod_idemp_r; [ | easy ].
    rewrite Nat.add_mod_idemp_r; [ | easy ].
    rewrite Nat.add_comm.
    do 2 rewrite Nat.add_assoc.
    do 4 rewrite <- Nat.pow_2_r.
    rewrite Hm, Nat.mul_comm.
    now apply Nat.mod_mul.
  }
  unfold z1.
  unfold zx1, zx2, zx3, zx4.
  unfold zy1, zy2, zy3, zy4, g.
  destruct (le_dec (x1 mod m) v) as [Hx1v| Hx1v]. {
    destruct (le_dec (x2 mod m) v) as [Hx2v| Hx2v]. {
      destruct (le_dec (x3 mod m) v) as [Hx3v| Hx3v]. {
        destruct (le_dec (x4 mod m) v) as [Hx4v| Hx4v]. {
          do 4 rewrite <- Nat2Z.inj_mul.
          now do 3 rewrite <- Nat2Z.inj_add.
        } {
          rewrite Z.mul_sub_distr_l.
          rewrite Z.add_sub_assoc.
          do 5 rewrite <- Nat2Z.inj_mul.
          do 3 rewrite <- Nat2Z.inj_add.
          rewrite Nat2Z.inj_mul.
          unfold Z.sub.
          rewrite <- Z.mul_opp_l.
          rewrite Z.mod_add; [ easy | ].
          intros H.
          replace 0%Z with (Z.of_nat 0) in H by easy.
          now apply Nat2Z.inj_iff in H.
        }
      }
...
specialize (H1 y1 y2 y3 y4); symmetry in H1.
rewrite Hm, Hr in H1.
set (z1 := x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4) in H1.
set (z2 := diff (x1 * y2 + x4 * y3) (x2 * y1 + x3 * y4)) in H1.
set (z3 := diff (x1 * y3 + x2 * y4) (x3 * y1 + x4 * y2)) in H1.
set (z4 := diff (x1 * y4 + x3 * y2) (x2 * y3 + x4 * y1)) in H1.
assert (Hz1 : z1 mod m = 0). {
  unfold z1.
  unfold y1, y2, y3, y4, f.
  destruct (le_dec (x1 mod m) v) as [Hx1v| Hx1v]. {
    do 2 rewrite <- Nat.add_assoc.
    rewrite <- Nat.add_mod_idemp_l; [ | easy ].
    rewrite Nat.mul_mod_idemp_r; [ | easy ].
    rewrite Nat.add_mod_idemp_l; [ | easy ].
    destruct (le_dec (x2 mod m) v) as [Hx2v| Hx2v]. {
      rewrite Nat.add_comm.
      do 2 rewrite <- Nat.add_assoc.
      rewrite <- Nat.add_mod_idemp_l; [ | easy ].
      rewrite Nat.mul_mod_idemp_r; [ | easy ].
      rewrite Nat.add_mod_idemp_l; [ | easy ].
      destruct (le_dec (x3 mod m) v) as [Hx3v| Hx3v]. {
        rewrite Nat.add_comm.
        do 2 rewrite <- Nat.add_assoc.
        rewrite <- Nat.add_mod_idemp_l; [ | easy ].
        rewrite Nat.mul_mod_idemp_r; [ | easy ].
        rewrite Nat.add_mod_idemp_l; [ | easy ].
        destruct (le_dec (x4 mod m) v) as [Hx4v| Hx4v]. {
          rewrite Nat.add_comm.
          do 2 rewrite <- Nat.add_assoc.
          rewrite <- Nat.add_mod_idemp_l; [ | easy ].
          rewrite Nat.mul_mod_idemp_r; [ | easy ].
          rewrite Nat.add_mod_idemp_l; [ | easy ].
          rewrite Nat.add_comm.
          rewrite Nat.add_assoc.
          do 4 rewrite <- Nat.pow_2_r.
          rewrite Hm, Nat.mul_comm.
          now apply Nat.mod_mul.
        } {
          rewrite Nat.mul_sub_distr_l.
          rewrite Nat.add_comm.
          rewrite <- Nat.add_assoc.
          rewrite Nat.add_comm.
          rewrite Nat.add_sub_assoc. 2: {
            apply Nat.mul_le_mono_l, Nat.lt_le_incl.
            now apply Nat.mod_upper_bound.
          }
          apply Nat_eq_mod_sub_0.
          rewrite Nat.mod_add; [ | easy ].
          rewrite Nat.mul_mod_idemp_r; [ | easy ].
          do 4 rewrite <- Nat.pow_2_r.
          replace (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) with (m * p - x4 ^ 2) by flia Hm.
...
Theorem Nat_add_mod_cancel_l : ∀ a b c m,
  (a + b) ≡ (a + c) mod m ↔ b ≡ c mod m.
Admitted.
apply (Nat_add_mod_cancel_l (x1 ^ 2)).
do 2 rewrite Nat.add_assoc.
rewrite Hm.
Search ((_ * _) mod _).
rewrite Nat.mul_comm, Nat.mod_mul; [ | easy ].
symmetry.
replace (x1 ^ 2 + x1 ^ 2) with (2 * x1 ^ 2) by flia.
rewrite Hx1.
rewrite Nat_sqr_add.
do 2 rewrite Nat.mul_add_distr_l.
rewrite Nat.pow_mul_l.
rewrite Nat.pow_2_r.
rewrite Nat.mul_comm.
do 2 rewrite <- Nat.mul_assoc.
rewrite <- Nat.add_assoc.
rewrite Nat_mod_add_l_mul_l; [ | easy ].
do 3 rewrite (Nat.mul_comm 2).
do 3 rewrite <- Nat.mul_assoc.
rewrite Nat_mod_add_r_mul_l; [ | easy ].
rewrite <- Nat.mul_mod_idemp_l; [ | easy ].
rewrite Nat_mod_pow_mod.
rewrite Nat.mul_mod_idemp_l; [ | easy ].
rewrite Nat.mul_comm.
(* I don't see why *)
...
