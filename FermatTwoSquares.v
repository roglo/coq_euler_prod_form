Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith(* Init.Nat*).
Import List.ListNotations.

Require Import RingLike.Core.
Require Import RingLike.IterMul.
Require Import RingLike.Nat_algebra.

Require Import Misc Primes.

Check List.fold_left.

Definition list_regroup {A} (eq : A → A → bool) (la : list A) :=
  List.fold_right
    (λ a lb,
       match lb with
       | (b, k) :: lb' =>
           if eq a b then (b, S k) :: lb' else (a, 1) :: (b, k) :: lb'
       | [] =>
           [(a, 1)]
       end)
    [] la.

(*
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
*)

Definition list_expand {A} (la : list (A * nat)) :=
  List.flat_map (λ pk, List.repeat (fst pk) (snd pk)) la.

Definition prime_decomp_with_power n := list_regroup Nat.eqb (prime_decomp n).

Theorem fold_list_regroup {A} (eq : A → A → bool) :
  ∀ (la : list A),
  List.fold_right
    (λ (a : A) (lb : list (A * nat)),
       match lb with
       | [] => [(a, 1)]
       | (b, k) :: lb' => if eq a b then (b, S k) :: lb' else (a, 1) :: (b, k) :: lb'
       end)
    [] la =
  list_regroup eq la.
Proof. easy. Qed.

Theorem list_regroup_nil_iff {A} eq : ∀ (la : list A),
  list_regroup eq la = [] ↔ la = [].
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn.
split; [ | easy ].
rewrite fold_list_regroup.
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

Theorem fold_list_expand {A} :
  ∀ (la : list (A * _)),
  List.flat_map (λ pk, List.repeat (fst pk) (snd pk)) la = list_expand la.
Proof. easy. Qed.

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
  set (m := ∏ (pk ∈ pdp), fst pk ^ snd pk).
  specialize (IHpdp H m); clear H.
  assert (H : prime_decomp_with_power m = pdp). {
    progress unfold m.
    progress unfold prime_decomp_with_power.
Print list_expand.
Theorem glop  : ∀ la n pk,
  prime_decomp_with_power n = pk :: la
  → list_regroup Nat.eqb (list_expand la) = la.
Proof.
intros * Hpd.
revert n pk Hpd.
induction la as [| (p, k)]; intros; [ easy | ].
cbn.
progress unfold list_expand in IHla.
Theorem list_regroup_app {A} (eq : A → _) :
  ∀ la lb,
  list_regroup eq (la ++ lb) =
    list_regroup eq (list_expand (list_regroup eq la ++ list_regroup eq lb)).
Proof.
intros.
progress unfold list_expand.
rewrite List.flat_map_app.
revert lb.
induction la as [| a]; intros; cbn. {
  do 2 rewrite fold_list_regroup.
  symmetry.
  remember (list_regroup eq lb) as lc eqn:Hlc.
  symmetry in Hlc.
  destruct lc as [| (p, k)]; [ easy | ].
  cbn.
  rewrite fold_list_regroup.
  rewrite fold_list_expand.
  rewrite <- Hlc.
  revert p k lc Hlc.
  induction lb as [| q]; intros; [ easy | cbn ].
  rewrite fold_list_regroup.
  cbn in Hlc.
  rewrite fold_list_regroup in Hlc.
  rewrite Hlc.
  rewrite IHlb. {
    remember (list_regroup eq lb) as lgb eqn:Hlgb.
    symmetry in Hlgb.
    destruct lgb as [| (b, k')]. {
      injection Hlc; clear Hlc; intros; subst q k lc.
(* ouah, fait chier *)
...
  revert p k lc Hlc.
  induction lb as [| p]; intros; [ easy | cbn ].
  cbn in Hlc.
  remember (list_regroup eq lb) as gb eqn:Hgb.
  symmetry in Hgb.
  destruct gb as [| (p', k')]. {
    now injection Hlc; clear Hlc; intros; subst p k lc.
  }
  remember (eq p p') as pp eqn:Hpp; symmetry in Hpp.
  destruct pp. {
    injection Hlc; clear Hlc; intros; subst lc p0 k.
...
    apply IHlb.
...
  specialize (IHlb 
  rewrite IHlb; [ easy | ].
...
... ...
rewrite <- (glop Nat.eqb).
f_equal.
...
Theorem glop {A} eq : ∀ (la : list A), list_expand (list_regroup eq la) = la.
...
Check prime_decomp_prod_all.
Theorem prime_decomp_with_power_prod_all :
  ∀ n, n ≠ 0 → ∏ (pk ∈ prime_decomp_with_power n), fst pk ^ snd pk = n.
Proof.
intros * Hnz.
...
    specialize (prime_decomp_with_power_prod_all m) as H1.
...
Search prime_decomp.
Inspect 2.
Search list_regroup.
...
prime_decomp_prod_all: ∀ n : nat, n ≠ 0 → ∏ (p ∈ prime_decomp n), p = n
    rewrite prime_decomp_prod_all.
...

Theorem Fermat_two_squares :
  ∀ p, prime p → p mod 4 = 1 → ∃! a b, (p = a² + b²).

*)
