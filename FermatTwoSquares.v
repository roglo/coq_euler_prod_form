Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith(* Init.Nat*) SetoidList.
Import List.ListNotations.

Require Import RingLike.Core.
Require Import RingLike.IterMul.
Require Import RingLike.IterAnd.
Require Import RingLike.Nat_algebra.

Require Import Misc Primes.

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

Definition List_Forall_bool {A} (f : A → bool) l := ⋀ (x ∈ l), f x.

Definition two_squ_resolvable pd :=
  ⋀ (pk ∈ pd),
    let '(p, k) := pk in
    negb (Nat.eqb (p mod 4) 3) || Nat.even k.

Fixpoint resolve_2sq_loop it (n : nat) :=
  match it with
  | 0 => None
  | S it' =>
      let pd := prime_decomp_with_power n in
      List.fold_left
        (λ kkk pk,
           let r := resolve_2sq_loop_for_prime it' pk in
           Some 1)
        pd None
  end
with resolve_2sq_loop_for_prime it (pk : nat * nat) :=
  match it with
  | 0 => None
  | S it' =>
      let '(p, k) := pk in
      if (negb (Nat.eqb (p mod 4) 3) || Nat.even k)%bool then
        let i := 2 in (* to be completed *)
        (* i²+1 ≡ 0 (mod p) *)
        (* i²+1 = k * p *)
        let k := (i² + 1) / p in
        match resolve_2sq_loop it' k with
        | Some pd => Some i (* to be completed *)
        | None => None
        end
      else
        None
  end.

(* to be completed
Compute (List.map (λ n, (n, resolve_2sq_loop n n)) (List.seq 1 100)).

Theorem prime_decomp_spec :
  ∀ n pd, n ≠ 0 →
  prime_decomp n = pd ↔ Sorted le pd ∧ Forall prime pd ∧ ∏ (p ∈ pd), p = n.
Proof.
intros * Hnz.
(*
assert (hhhhhhh : ∀ (p q : nat) pd, p ∈ pd → p ∈ q :: pd).
now intros; right.
Show Proof.
*)
split. {
  intros Hpd.
  rewrite <- Hpd.
  split; [ apply Sorted_prime_decomp | ].
  split. {
    apply Forall_forall.
    apply in_prime_decomp_is_prime.
  }
  now apply prime_decomp_prod_all.
}
intros (Hs & Hpd & Hp).
revert n Hnz Hp.
induction pd as [| p]; intros. {
  rewrite rngl_product_list_empty in Hp; [ | easy ].
  now subst n.
}
rewrite rngl_product_list_cons in Hp.
generalize Hs; intros H.
apply Sorted_inv in H.
destruct H as (H & _).
specialize (IHpd H); clear H.
generalize Hpd; intros H.
apply Forall_cons_iff in H.
destruct H as (_ & H).
specialize (IHpd H); clear H.
specialize (IHpd (∏ (p ∈  pd), p)).
assert (H : ∏ (p ∈ pd), p ≠ 0). {
  intros H.
  replace 0 with 0%L in H by easy.
  apply rngl_product_list_integral in H; [ | easy | easy | easy ].
  destruct H as (q & Hq & H); subst q.
  specialize (proj1 (Forall_forall prime (p :: pd)) Hpd) as H1.
  now specialize (H1 0%L (or_intror Hq)).
}
specialize (IHpd H eq_refl); clear H.
rewrite <- Hp.
clear n Hnz Hp.
remember (∏ (i ∈ _), _) as x in IHpd; subst x. (* renaming *)
rewrite <- IHpd at 2.
clear IHpd.
(**)
apply Sorted_inv in Hs.
destruct Hs as (Hs, Hr).
apply Forall_cons_iff in Hpd.
destruct Hpd as (Hp, Hpd).
Theorem glop :
  ∀ p pd,
  HdRel le p pd
  → prime p
  → Sorted le pd
  → Forall prime pd
  → prime_decomp (p * ∏ (i ∈ pd), i)%L = p :: prime_decomp (∏ (i ∈ pd), i).
Proof.
intros * Hr Hp Hs Hpd.
revert p Hr Hp.
induction pd as [| q]; intros. {
  rewrite rngl_product_list_empty; [ | easy ].
  rewrite Nat.mul_1_r.
  replace 1%L with 1 by easy; cbn.
  now apply prime_decomp_of_prime.
}
rewrite rngl_product_list_cons.
rewrite Nat.mul_assoc.
(* faudrait un théorème avec un "n" général, au lieu de "p". Ce "n"
   serait le produit de nombres premiers inférieurs à ceux de "pd" *)
...

Theorem prime_decomp_with_power_prod_all :
  ∀ n, n ≠ 0 → ∏ (pk ∈ prime_decomp_with_power n), fst pk ^ snd pk = n.
Proof.
intros * Hnz.
specialize (prime_decomp_prod_all n Hnz) as H1.
progress unfold prime_decomp_with_power.
remember (prime_decomp n) as pd eqn:Hp; symmetry in Hp.
revert n Hnz Hp H1.
induction pd as [| p]; intros; [ easy | ].
cbn.
rewrite fold_list_regroup.
remember (list_regroup Nat.eqb pd) as g eqn:Hg.
symmetry in Hg.
destruct g as [| (a, k)]. {
  apply list_regroup_nil_iff in Hg; subst pd.
  rewrite rngl_product_list_only_one in H1.
  rewrite rngl_product_list_only_one; cbn.
  now rewrite Nat.mul_1_r.
}
rewrite rngl_product_list_cons in H1.
specialize (IHpd (∏ (i ∈ pd), i)).
assert (H : ∏ (i ∈ pd), i ≠ 0). {
  clear - Hp.
  revert n Hp.
  induction pd as [| q]; intros. {
    now rewrite rngl_product_list_empty.
  }
  rewrite rngl_product_list_cons.
  apply Nat.neq_mul_0.
  split. {
    intros H; subst q.
    specialize (in_prime_decomp_is_prime n 0) as H1.
    rewrite Hp in H1.
    cbn in H1.
    progress unfold prime in H1.
    cbn in H1.
    apply Bool.diff_false_true.
    apply H1.
    now right; left.
  }
  apply (IHpd (p * ∏ (i ∈ pd), i)).
Search (prime_decomp (_ * _)).
About prime_decomp_mul.
...
  rewrite primt_decomp_mul
... ...
specialize (IHpd H); clear H.
...
remember (p =? a) as pa eqn:Hpa; symmetry in Hpa.
destruct pa. {
  apply Nat.eqb_eq in Hpa; subst a.
  rewrite rngl_product_list_cons.
  cbn - [ rngl_power ].
...

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
Theorem glop : ∀ la n,
  prime_decomp_with_power n = la
  → list_regroup Nat.eqb (list_expand la) = la.
Proof.
intros * Hn.
revert n Hn.
induction la as [| (p, k)]; intros; [ easy | cbn ].
rewrite fold_list_expand.
rewrite fold_list_regroup.
Inspect 6.
Search prime_decomp_with_power.
...
specialize (IHla (prime_decomp_with_power n)).
...
Theorem glop : ∀ la n pk,
  prime_decomp_with_power n = pk :: la
  → list_regroup Nat.eqb (list_expand la) = la.
Proof.
intros * Hpd.
...
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
