Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith(* Init.Nat*).
Import List ListNotations.

Require Import RingLike.Core.
Require Import RingLike.IterMul.
Require Import RingLike.Nat_algebra.

Require Import Misc Primes.

Fixpoint list_regroup {A} (eq : A → A → bool) (la : list A) :=
  match la with
  | a :: la =>
      match list_regroup eq la with
      | (b, n) :: lb =>
          if eq a b then (b, S n) :: lb else (a, 1) :: (b, n) :: lb
      | [] =>
          [(a, 1)]
      end
  | [] => []
  end.

Definition prime_decomp_with_power n := list_regroup Nat.eqb (prime_decomp n).

Theorem list_regroup_nil_iff {A} eq : ∀ (la : list A),
  list_regroup eq la = [] ↔ la = [].
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn.
split; [ | easy ].
intros H1; exfalso.
remember (list_regroup eq la) as lb eqn:Hlb.
symmetry in Hlb.
destruct lb as [| (b, n)]; [ easy | ].
now destruct (eq a b).
Qed.

Theorem prime_decomp_prod_all : ∀ n, n ≠ 0 → ∏ (p ∈ prime_decomp n), p = n.
Proof.
intros * Hnz.
specialize (prime_decomp_prod n Hnz) as H1.
progress unfold Utils.iter_list.
replace rngl_mul with Nat.mul by easy.
replace rngl_one with 1 by easy.
easy.
Qed.

(* to be completed
Theorem Fermat_two_squares_any :
  ∀ n,
  (∀ p k, (p, k) ∈ prime_decomp_with_power n → p mod 4 ≠ 3 ∨ Nat.Even k)
  ↔ ∃ a b, n = a² + b².
Proof.
intros.
split. {
  intros Hp.
  induction n as (n, IHn) using lt_wf_rec.
  remember (prime_decomp_with_power n) as pdp eqn:Hpdp.
  symmetry in Hpdp.
(*
  progress unfold prime_decomp_with_power in Hpdp.
  remember (prime_decomp n) as pd eqn:Hpd.
  symmetry in Hpd.
Print list_regroup.
...
*)
  revert n Hpdp IHn.
  induction pdp as [| (p, k)]; intros. {
    progress unfold prime_decomp_with_power in Hpdp.
    apply list_regroup_nil_iff in Hpdp.
    apply prime_decomp_nil_iff in Hpdp.
    destruct Hpdp; subst n; [ now exists 0, 0 | ].
    now exists 0, 1.
  }
  assert (H : ∀ p k, (p, k) ∈ pdp → p mod 4 ≠ 3 ∨ Nat.Even k). {
    now intros; apply Hp; right.
  }
  specialize (IHpdp H); clear H.
Check prime_decomp_prod_all.
Theorem prime_decomp_with_power_prod_all :
  ∀ n, n ≠ 0 → ∏ (pk ∈ prime_decomp_with_power n), fst pk ^ snd pk = n.
Proof.
intros * Hnz.
Admitted.
  set (m := ∏ (pk ∈ pdp), fst pk ^ snd pk).
  specialize (IHpdp m).
  assert (H : prime_decomp_with_power m = pdp). {
    progress unfold m.
progress unfold prime_decomp_with_power.
Search prime_decomp.
...
prime_decomp_prod_all: ∀ n : nat, n ≠ 0 → ∏ (p ∈ prime_decomp n), p = n
    rewrite prime_decomp_prod_all.
...

Theorem Fermat_two_squares :
  ∀ p, prime p → p mod 4 = 1 → ∃! a b, (p = a² + b²).

*)
