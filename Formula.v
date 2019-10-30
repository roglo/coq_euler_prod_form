(* Euler Product Formula *)
(* https://en.wikipedia.org/wiki/Proof_of_the_Euler_product_formula_for_the_Riemann_zeta_function *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz Setoid Morphisms.
Require Import Sorting.Permutation SetoidList.
Import List List.ListNotations.
Require Import Misc Primes.

(* ζ(s) = Σ (n ∈ ℕ* ) 1/n^s = Π (p ∈ Primes) 1/(1-1/p^s) *)

(* Here ζ is not applied to ℂ as usual, but to any field, whose
   type is defined below; most of the theorems has a field f
   as implicit first parameter.
     And we have never to evaluate a value ζ(s) for a given s,
   so the ζ function is just defined by the coefficients of
   its terms. See type ln_series below. *)

Class field :=
  { f_type : Set;
    f_zero : f_type;
    f_one : f_type;
    f_add : f_type → f_type → f_type;
    f_mul : f_type → f_type → f_type;
    f_opp : f_type → f_type;
    f_inv : f_type → f_type;
    f_add_comm : ∀ x y, f_add x y = f_add y x;
    f_add_assoc : ∀ x y z, f_add x (f_add y z) = f_add (f_add x y) z;
    f_add_0_l : ∀ x, f_add f_zero x = x;
    f_add_opp_diag_l : ∀ x, f_add (f_opp x) x = f_zero;
    f_mul_comm : ∀ x y, f_mul x y = f_mul y x;
    f_mul_assoc : ∀ x y z, f_mul x (f_mul y z) = f_mul (f_mul x y) z;
    f_mul_1_l : ∀ x, f_mul f_one x = x;
    f_mul_inv_diag_l : ∀ x, x ≠ f_zero → f_mul (f_inv x) x = f_one;
    f_mul_add_distr_l : ∀ x y z,
      f_mul x (f_add y z) = f_add (f_mul x y) (f_mul x z);
    f_charact_ne_2 : f_add f_one f_one ≠ f_zero }.

Declare Scope field_scope.
Delimit Scope field_scope with F.

Definition f_sub {F : field} x y := f_add x (f_opp y).

Notation "- x" := (f_opp x) : field_scope.
Notation "x + y" := (f_add x y) : field_scope.
Notation "x - y" := (f_sub x y) : field_scope.
Notation "x * y" := (f_mul x y) : field_scope.
Notation "0" := (f_zero) : field_scope.
Notation "1" := (f_one) : field_scope.

Theorem f_add_0_r {F : field} : ∀ x, (x + 0)%F = x.
Proof.
intros.
rewrite f_add_comm.
apply f_add_0_l.
Qed.

Theorem f_opp_0 {F : field} : (- 0)%F = 0%F.
Proof.
rewrite <- (f_add_0_r (- 0)%F).
apply f_add_opp_diag_l.
Qed.

Theorem f_add_opp_diag_r {F : field} : ∀ x, (x + - x = 0)%F.
Proof.
intros.
rewrite f_add_comm.
apply f_add_opp_diag_l.
Qed.

Theorem f_add_sub {F : field} : ∀ x y, (x + y - y)%F = x.
Proof.
intros.
unfold f_sub.
rewrite <- f_add_assoc.
rewrite f_add_opp_diag_r.
now rewrite f_add_0_r.
Qed.

Theorem f_add_move_r {F : field} : ∀ x y z, (x + y)%F = z ↔ x = (z - y)%F.
Proof.
intros.
split.
-intros H.
 rewrite <- H.
 now rewrite f_add_sub.
-intros H.
 rewrite H.
 unfold f_sub.
 rewrite <- f_add_assoc.
 rewrite f_add_opp_diag_l.
 now rewrite f_add_0_r.
Qed.

Theorem f_add_move_0_r {F : field} : ∀ x y, (x + y = 0)%F ↔ x = (- y)%F.
Proof.
intros.
split.
-intros H.
 apply f_add_move_r in H.
 unfold f_sub in H.
 now rewrite f_add_0_l in H.
-intros H.
 apply f_add_move_r.
 unfold f_sub.
 now rewrite f_add_0_l.
Qed.

Theorem f_add_add_swap {F : field} : ∀ x y z, (x + y + z = x + z + y)%F.
Proof.
intros.
do 2 rewrite <- f_add_assoc.
apply f_equal, f_add_comm.
Qed.

Theorem f_mul_add_distr_r {F : field} : ∀ x y z,
  ((x + y) * z)%F = (x * z + y * z)%F.
Proof.
intros.
rewrite f_mul_comm, f_mul_add_distr_l.
now do 2 rewrite (f_mul_comm z).
Qed.

Theorem f_mul_0_l {F : field} : ∀ x, (0 * x = 0)%F.
Proof.
intros.
assert (H : (0 * x + x = x)%F). {
  transitivity ((0 * x + f_one * x)%F).
  -now rewrite f_mul_1_l.
  -rewrite <- f_mul_add_distr_r.
   now rewrite f_add_0_l, f_mul_1_l.
}
apply f_add_move_r in H.
unfold f_sub in H.
now rewrite f_add_opp_diag_r in H.
Qed.

Theorem f_mul_0_r {F : field} : ∀ x, (x * 0 = 0)%F.
Proof.
intros.
rewrite f_mul_comm.
apply f_mul_0_l.
Qed.

Theorem f_eq_mul_0_l {F : field} : ∀ x y,
  (x * y = 0)%F → y ≠ 0%F → x = 0%F.
Proof.
intros * Hxy Hy.
rewrite f_mul_comm in Hxy.
apply (f_equal (f_mul (f_inv y))) in Hxy.
rewrite f_mul_0_r, f_mul_assoc in Hxy.
rewrite f_mul_inv_diag_l in Hxy; [ | easy ].
now rewrite f_mul_1_l in Hxy.
Qed.

Theorem f_mul_opp_l {F : field} : ∀ x y, (- x * y = - (x * y))%F.
Proof.
intros.
apply f_add_move_0_r.
rewrite <- f_mul_add_distr_r.
rewrite f_add_opp_diag_l.
apply f_mul_0_l.
Qed.

Theorem f_mul_opp_r {F : field} : ∀ x y, (x * - y = - (x * y))%F.
Proof.
intros.
now rewrite f_mul_comm, f_mul_opp_l, f_mul_comm.
Qed.

Theorem f_mul_1_r {F : field} : ∀ x, (x * f_one)%F = x.
Proof.
intros.
rewrite f_mul_comm.
apply f_mul_1_l.
Qed.

Theorem f_eq_opp_eq_0 {F : field} : ∀ x, x = (- x)%F → x = 0%F.
Proof.
intros * Hx.
apply f_add_move_0_r in Hx.
replace x with (x * 1)%F in Hx by now rewrite f_mul_1_r.
rewrite <- f_mul_add_distr_l in Hx.
apply f_eq_mul_0_l in Hx; [ easy | ].
apply f_charact_ne_2.
Qed.

(* Euler product formula *)

(*
Riemann zeta function is
   ζ(s) = 1 + 1/2^s + 1/3^s + 1/4^s + 1/5^s + ...

Euler product formula is the fact that
                    1
   ζ(s) = -----------------------------------------------
          (1-1/2^s) (1-1/3^s) (1-1/5^s) ... (1-1/p^s) ...

where the product in the denominator applies on all prime numbers
and only them.

The proof is the following.

We first prove that
   ζ(s) (1-1/2^s) = 1 + 1/3^s + 1/5^s + 1/7^s + ...

i.e. all terms but the multiples of 2
i.e. all odd numbers

(this is easy to verify on a paper)

Then we continue by proving
   ζ(s) (1-1/2^s) (1-1/3^s) =
       1 + 1/5^s + 1/7^s + 1/11^s + ... + 1/23^s + 1/25^s + ...

i.e. all terms but the multiples of 2 and 3

Then we do it for the number 5 in the second term (1/5^s) of the series.

This number in the second term is always the next prime number, like in the
Sieve of Eratosthenes.

Up to prime number p, we have, using commutativity
  ζ(s) (1-1/2^s) (1-1/3^s) ... (1-1/p^s) = 1 + 1/q^s + ...

where q is the prime number after p and the rest holds terms whose
number is greater than q and not divisible by the primes between
2 and p.

When p tends towards infinity, the term to the right is just 1
and we get Euler's formula.

    ---

Implementation.

ζ(s) and all the expressions above are actually of the form
    a₁ + a₂/2^s + a₃/3^s + a₄/4^s + ...

We can represent them by the sequence
    (a_n) = (a₁, a₂, a₃, ...)

For example, ζ is (1, 1, 1, 1, ...)
and (1-1/3^s) is (1, 0, -1, 0, 0, 0, ...)

We call them "series with logarithm powers" because they can be
written
    a₁ + a₂ x^ln(2) + a₃ x^ln(3) + a₄ x^ln(4) + a₅ x^ln(5) + ...

with x = e^(-s). Easy to verify.

Note that we do not consider the parameters s or x. The fact that
they are supposed to be complex number is irrelevant in this proof.
We just consider they belong to a field (type "field" defined
above).
*)

(* Definition of the type of such a series; a value s of this
   type is a function ls : nat → field representing the series
       ls(1) + ls(2)/2^s + ls(3)/3^s + ls(4)/4^s + ...
   or the equivalent form with x at a logarithm power
       ls(1) + ls(2).x^ln(2) + ls(3).x^ln(3) + ls(4).x^ln(4)+...
   where x = e^(-s)
 *)

Class ln_series {F : field} :=
  { ls : nat → f_type }.

(* Definition of the type of a polynomial: this is just
   a finite series; it can be represented by a list *)

Class ln_polyn {F : field} :=
  { lp : list f_type }.

(* Syntactic scopes, allowing to use operations on series and
   polynomials with usual mathematical forms. For example we can
   write e.g.
        (s1 * s2 + s3)%LS
   instead of the less readable
        ls_add (ls_mul s1 s2) s3
*)

Declare Scope ls_scope.
Delimit Scope ls_scope with LS.

Declare Scope lp_scope.
Delimit Scope lp_scope with LP.

Arguments ls {_} _%LS _%nat.
Arguments lp {_}.

(* Equality between series; since these series start with 1, the
   comparison is only on natural indices different from 0 *)

Definition ls_eq {F : field} s1 s2 := ∀ n, n ≠ 0 → ls s1 n = ls s2 n.
Arguments ls_eq _ s1%LS s2%LS.

(* which is an equivalence relation *)

Theorem ls_eq_refl {F : field} : reflexive _ ls_eq.
Proof. easy. Qed.

Theorem ls_eq_sym {F : field} : symmetric _ ls_eq.
Proof.
intros x y Hxy i Hi.
now symmetry; apply Hxy.
Qed.

Theorem ls_eq_trans {F : field} : transitive _ ls_eq.
Proof.
intros x y z Hxy Hyz i Hi.
now eapply eq_trans; [ apply Hxy | apply Hyz ].
Qed.

Add Parametric Relation {F : field} : (ln_series) ls_eq
 reflexivity proved by ls_eq_refl
 symmetry proved by ls_eq_sym
 transitivity proved by ls_eq_trans
 as ls_eq_rel.

(* The unit series: 1 + 0/2^s + 0/3^s + 0/4^s + ... *)

Definition ls_one {F : field} :=
  {| ls n := match n with 1 => f_one | _ => 0%F end |}.

(* Notation for accessing a series coefficient at index i *)

Notation "r ~{ i }" := (ls r i) (at level 1, format "r ~{ i }").
Notation "x '∈' l" := (List.In x l) (at level 60).

(* adding, opposing, subtracting polynomials *)

Definition lp_add {F : field} p q :=
  {| lp :=
       List.map (prod_curry f_add) (List_combine_all (lp p) (lp q) 0%F) |}.
Definition lp_opp {F : field} p := {| lp := List.map f_opp (lp p) |}.
Definition lp_sub {F : field} p q := lp_add p (lp_opp q).

Notation "x - y" := (lp_sub x y) : lp_scope.

(* At last, the famous ζ function: all its coefficients are 1 *)

Definition ζ {F : field} := {| ls _ := f_one |}.

(* Series where the indices, which are multiple of some n, are 0
      1 + ls(2)/2^s + ls(3)/3^s + ... + ls(n-1)/(n-1)^s + 0/n^s +
      ... + ls(ni-1)/(ni-1)^s + 0/ni^s + ls(ni+1)/(ni+1)^s + ...
   This special series allows to cumulate the multiplications of
   terms of the form (1-1/p^s); when doing (1-1/p^s).ζ, the result
   is ζ without all terms multiple of p *)

Definition series_but_mul_of {F : field} n s :=
  {| ls i :=
       match i mod n with
       | 0 => 0%F
       | _ => ls s i
       end |}.

(* list of divisors of a natural number *)

Definition divisors_but_firstn_and_lastn d n :=
  List.filter (λ a, n mod a =? 0) (List.seq d (S n - d)).

Definition divisors := divisors_but_firstn_and_lastn 1.

(* product of series is like the convolution product but
   limited to divisors; indeed the coefficient of the term
   in x^ln(n), resulting of the multiplication of two series
   u and v, is the sum:
      u_1.v_n + ... u_d.v_{n/d} + ... u_n.v_1
   where d covers all the divisors of n *)

Definition log_prod_term {F : field} u v n i :=
  (u i * v (n / i))%F.

Definition log_prod_list {F : field} u v n :=
  List.map (log_prod_term u v n) (divisors n).

Definition log_prod {F : field} u v n :=
  List.fold_left f_add (log_prod_list u v n) 0%F.

(* Σ (i = 1, ∞) s1_i x^ln(i) * Σ (i = 1, ∞) s2_i x^ln(i) *)
Definition ls_mul {F : field} s1 s2 :=
  {| ls := log_prod (ls s1) (ls s2) |}.

(* polynomial seen as a series *)

Definition ls_of_pol {F : field} p :=
  {| ls n :=
       match n with
       | 0 => 0%F
       | S n' => List.nth n' (lp p) 0%F end |}.

Definition ls_pol_mul_r {F : field} s p :=
  ls_mul s (ls_of_pol p).

Arguments ls_of_pol _ p%LP.
Arguments ls_pol_mul_r _ s%LS p%LP.

Notation "x = y" := (ls_eq x y) : ls_scope.
Notation "x * y" := (ls_mul x y) : ls_scope.
Notation "s *' p" := (ls_pol_mul_r s p) (at level 41, left associativity) :
   ls_scope.

Theorem in_divisors : ∀ n,
  n ≠ 0 → ∀ d, d ∈ divisors n → n mod d = 0 ∧ d ≠ 0.
Proof.
intros * Hn *.
unfold divisors, divisors_but_firstn_and_lastn.
intros Hd.
apply filter_In in Hd.
destruct Hd as (Hd, Hnd).
split; [ now apply Nat.eqb_eq | ].
apply in_seq in Hd; flia Hd.
Qed.

Theorem in_divisors_iff : ∀ n,
  n ≠ 0 → ∀ d, d ∈ divisors n ↔ n mod d = 0 ∧ d ≠ 0.
Proof.
intros * Hn *.
unfold divisors, divisors_but_firstn_and_lastn.
split; [ now apply in_divisors | ].
intros (Hnd, Hd).
apply filter_In.
split; [ | now apply Nat.eqb_eq ].
apply in_seq.
split; [ flia Hd | ].
apply Nat.mod_divides in Hnd; [ | easy ].
destruct Hnd as (c, Hc).
rewrite Nat.mul_comm in Hc; rewrite Hc.
destruct c; [ easy | ].
cbn; flia.
Qed.

(* allows to rewrite H1, H2 with
      H1 : s1 = s3
      H2 : s2 = s4
   in expression
      (s1 * s2)%F
   changing it into
      (s3 * s4)%F *)
Instance ls_mul_morph {F : field} :
  Proper (ls_eq ==> ls_eq ==> ls_eq) ls_mul.
Proof.
intros s1 s2 Hs12 s'1 s'2 Hs'12 n Hn.
cbn - [ log_prod ].
unfold log_prod, log_prod_list; f_equal.
specialize (in_divisors n Hn) as Hd.
remember (divisors n) as l eqn:Hl; clear Hl.
induction l as [| a l]; [ easy | cbn ].
rewrite IHl; [ | now intros d Hdl; apply Hd; right ].
f_equal.
unfold log_prod_term.
specialize (Hd a (or_introl eq_refl)) as Ha.
destruct Ha as (Hna, Ha).
rewrite Hs12; [ | easy ].
rewrite Hs'12; [ easy | ].
apply Nat.mod_divides in Hna; [ | easy ].
destruct Hna as (c, Hc).
rewrite Hc, Nat.mul_comm, Nat.div_mul; [ | easy ].
now intros H; rewrite Hc, H, Nat.mul_0_r in Hn.
Qed.

Theorem fold_left_map_log_prod_term {F : field} : ∀ u i x l,
  (∀ j, j ∈ l → 2 ≤ j)
  → fold_left f_add (map (log_prod_term (ls ls_one) u (S i)) l) x = x.
Proof.
intros * Hin.
revert i.
induction l as [| a l]; intros; [ easy | ].
cbn - [ ls_one ].
unfold log_prod_term at 2.
replace ls_one~{a} with 0%F. 2: {
  cbn.
  destruct a; [ easy | ].
  destruct a; [ exfalso | now destruct a ].
  specialize (Hin 1 (or_introl eq_refl)); flia Hin.
}
rewrite f_mul_0_l, f_add_0_r.
apply IHl.
intros j Hj.
now apply Hin; right.
Qed.

Theorem ls_mul_1_l {F : field} : ∀ r, (ls_one * r = r)%LS.
Proof.
intros * i Hi.
destruct i; [ easy | clear Hi ].
cbn - [ ls_one ].
unfold log_prod_term at 2.
replace ls_one~{1} with f_one by easy.
rewrite f_add_0_l, f_mul_1_l, Nat.div_1_r.
cbn - [ ls_one ].
apply fold_left_map_log_prod_term.
intros j Hj.
assert (H : ∀ s i f, 2 ≤ s → j ∈ filter f (seq s i) → 2 ≤ j). {
  clear; intros * Hs Hj.
  revert s j Hs Hj.
  induction i; intros; [ easy | ].
  cbn - [ "mod" ] in Hj.
  remember (f s) as m eqn:Hm; symmetry in Hm.
  destruct m. {
    cbn in Hj.
    destruct Hj as [Hj| Hj]; [ now subst s | ].
    apply (IHi (S s)); [ flia Hs | easy ].
  }
  apply (IHi (S s)); [ flia Hs | easy ].
}
eapply (H 2 i); [ easy | ].
apply Hj.
Qed.

Theorem eq_first_divisor_1 : ∀ n, n ≠ 0 → List.hd 0 (divisors n) = 1.
Proof.
intros.
now destruct n.
Qed.

Theorem eq_last_divisor : ∀ n, n ≠ 0 → List.last (divisors n) 0 = n.
Proof.
intros n Hn.
remember (divisors n) as l eqn:Hl.
symmetry in Hl.
unfold divisors, divisors_but_firstn_and_lastn in Hl.
rewrite Nat_sub_succ_1 in Hl.
specialize (List_last_seq 1 n Hn) as H1.
replace (1 + n - 1) with n in H1 by flia.
specialize (proj2 (filter_In (λ a, n mod a =? 0) n (seq 1 n))) as H2.
rewrite Hl in H2.
rewrite Nat.mod_same in H2; [ | easy ].
cbn in H2.
assert (H3 : n ∈ seq 1 n). {
  rewrite <- H1 at 1.
  apply List_last_In.
  now destruct n.
}
assert (H : n ∈ seq 1 n ∧ true = true) by easy.
specialize (H2 H); clear H.
assert (H : seq 1 n ≠ []); [ now intros H; rewrite H in H3 | ].
specialize (app_removelast_last 0 H) as H4; clear H.
rewrite H1 in H4.
assert (H : seq 1 n ≠ []); [ now intros H; rewrite H in H3 | ].
rewrite H4, filter_app in Hl; cbn in Hl.
rewrite Nat.mod_same in Hl; [ | easy ].
cbn in Hl; rewrite <- Hl.
apply List_last_app.
Qed.

Theorem divisors_are_sorted : ∀ n, Sorted.Sorted lt (divisors n).
Proof.
intros.
unfold divisors, divisors_but_firstn_and_lastn.
rewrite Nat_sub_succ_1.
specialize (SetoidList.filter_sort eq_equivalence Nat.lt_strorder) as H2.
specialize (H2 Nat.lt_wd).
specialize (H2 (λ a, n mod a =? 0) (seq 1 n)).
now specialize (H2 (Sorted_Sorted_seq _ _)).
Qed.

Theorem fold_f_add_assoc {F : field} : ∀ a b l,
  fold_left f_add l (a + b)%F = (fold_left f_add l a + b)%F.
Proof.
intros.
revert a.
induction l as [| c l]; intros; [ easy | cbn ].
rewrite <- IHl; f_equal.
apply f_add_add_swap.
Qed.

Theorem divisor_inv : ∀ n d, d ∈ divisors n → n / d ∈ divisors n.
Proof.
intros * Hd.
apply List.filter_In in Hd.
apply List.filter_In.
destruct Hd as (Hd, Hm).
apply List.in_seq in Hd.
apply Nat.eqb_eq in Hm.
rewrite Nat_mod_0_mod_div; [ | flia Hd | easy ].
split; [ | easy ].
apply Nat.mod_divides in Hm; [ | flia Hd ].
destruct Hm as (m, Hm).
rewrite Hm at 1.
apply List.in_seq.
rewrite Nat.mul_comm, Nat.div_mul; [ | flia Hd ].
split.
+apply (Nat.mul_lt_mono_pos_l d); [ flia Hd | ].
 flia Hm Hd.
+rewrite Hm.
 destruct d; [ flia Hd | cbn; flia ].
Qed.

Theorem sorted_equiv_nat_lists : ∀ l l',
  Sorted.Sorted lt l
  → Sorted.Sorted lt l'
  → (∀ a, a ∈ l ↔ a ∈ l')
  → l = l'.
Proof.
intros * Hl Hl' Hll.
revert l' Hl' Hll.
induction l as [| a l]; intros. {
  destruct l' as [| a' l']; [ easy | ].
  now specialize (proj2 (Hll a') (or_introl eq_refl)) as H1.
}
destruct l' as [| a' l']. {
  now specialize (proj1 (Hll a) (or_introl eq_refl)) as H1.
}
assert (Hltt : Relations_1.Transitive lt). {
  intros x y z Hxy Hyz.
  now transitivity y.
}
assert (Haa : a = a'). {
  specialize (proj1 (Hll a) (or_introl eq_refl)) as H1.
  destruct H1 as [H1| H1]; [ easy | ].
  specialize (proj2 (Hll a') (or_introl eq_refl)) as H2.
  destruct H2 as [H2| H2]; [ easy | ].
  apply Sorted.Sorted_StronglySorted in Hl; [ | easy ].
  apply Sorted.Sorted_StronglySorted in Hl'; [ | easy ].
  inversion Hl; subst.
  inversion Hl'; subst.
  specialize (proj1 (Forall_forall (lt a) l) H4) as H7.
  specialize (proj1 (Forall_forall (lt a') l') H6) as H8.
  specialize (H7 _ H2).
  specialize (H8 _ H1).
  flia H7 H8.
}
subst a; f_equal.
apply IHl.
-now apply Sorted.Sorted_inv in Hl.
-now apply Sorted.Sorted_inv in Hl'.
-intros a; split; intros Ha.
 +specialize (proj1 (Hll _) (or_intror Ha)) as H1.
  destruct H1 as [H1| H1]; [ | easy ].
  subst a'.
  apply Sorted.Sorted_StronglySorted in Hl; [ | easy ].
  inversion Hl; subst.
  specialize (proj1 (Forall_forall (lt a) l) H2) as H3.
  specialize (H3 _ Ha); flia H3.
 +specialize (proj2 (Hll _) (or_intror Ha)) as H1.
  destruct H1 as [H1| H1]; [ | easy ].
  subst a'.
  apply Sorted.Sorted_StronglySorted in Hl'; [ | easy ].
  inversion Hl'; subst.
  specialize (proj1 (Forall_forall (lt a) l') H2) as H3.
  specialize (H3 _ Ha); flia H3.
Qed.

Theorem sorted_gt_lt_rev : ∀ l, Sorted.Sorted gt l → Sorted.Sorted lt (rev l).
Proof.
intros l Hl.
induction l as [| a l]; [ constructor | cbn ].
apply (SetoidList.SortA_app eq_equivalence).
-now apply IHl; inversion Hl.
-now constructor.
-intros x y Hx Hy.
 apply SetoidList.InA_alt in Hy.
 destruct Hy as (z & Haz & Hza); subst z.
 destruct Hza; [ subst a | easy ].
 apply SetoidList.InA_rev in Hx.
 rewrite List.rev_involutive in Hx.
 apply SetoidList.InA_alt in Hx.
 destruct Hx as (z & Haz & Hza); subst z.
 apply Sorted.Sorted_inv in Hl.
 destruct Hl as (Hl, Hyl).
 clear IHl.
 induction Hyl; [ easy | ].
 destruct Hza as [Hx| Hx]; [ now subst x | ].
 transitivity b; [ clear H | easy ].
 assert (Hgtt : Relations_1.Transitive gt). {
   unfold gt.
   clear; intros x y z Hxy Hyz.
   now transitivity y.
 }
 apply Sorted.Sorted_StronglySorted in Hl; [ | easy ].
 inversion Hl; subst.
 specialize (proj1 (Forall_forall (gt b) l) H2) as H3.
 now apply H3.
Qed.

Theorem map_inv_divisors : ∀ n,
  divisors n = List.rev (List.map (λ i, n / i) (divisors n)).
Proof.
intros.
specialize (divisors_are_sorted n) as H1.
assert (H2 : Sorted.Sorted lt (rev (map (λ i : nat, n / i) (divisors n)))). {
  apply sorted_gt_lt_rev.
  destruct n; [ constructor | ].
  specialize (in_divisors (S n) (Nat.neq_succ_0 _)) as H2.
  remember (divisors (S n)) as l eqn:Hl; symmetry in Hl.
  clear Hl.
  induction l as [| a l]; [ constructor | ].
  cbn; constructor.
  -apply IHl; [ now inversion H1 | ].
   now intros d; intros Hd; apply H2; right.
  -clear IHl.
   revert a H1 H2.
   induction l as [| b l]; intros; [ constructor | ].
   cbn; constructor; unfold gt.
   apply Sorted.Sorted_inv in H1.
   destruct H1 as (_, H1).
   apply Sorted.HdRel_inv in H1.
   assert (Ha : a ≠ 0). {
     intros H; subst a.
     now specialize (H2 0 (or_introl eq_refl)) as H3.
   }
   assert (Hb : b ≠ 0). {
     intros H; subst b.
     now specialize (H2 0 (or_intror (or_introl eq_refl))) as H3.
   }
   specialize (Nat.div_mod (S n) a Ha) as H3.
   specialize (Nat.div_mod (S n) b Hb) as H4.
   specialize (H2 a (or_introl eq_refl)) as H.
   rewrite (proj1 H), Nat.add_0_r in H3; clear H.
   specialize (H2 b (or_intror (or_introl eq_refl))) as H.
   rewrite (proj1 H), Nat.add_0_r in H4; clear H.
   apply (Nat.mul_lt_mono_pos_l b); [ flia Hb | ].
   rewrite <- H4.
   apply (Nat.mul_lt_mono_pos_l a); [ flia Ha | ].
   rewrite (Nat.mul_comm _ (_ * _)), Nat.mul_shuffle0.
   rewrite <- Nat.mul_assoc, <- H3.
   apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
}
apply sorted_equiv_nat_lists; [ easy | easy | ].
intros a.
split; intros Ha.
-apply List.in_rev; rewrite List.rev_involutive.
 destruct (zerop n) as [Hn| Hn]; [ now subst n | ].
 apply Nat.neq_0_lt_0 in Hn.
 specialize (in_divisors n Hn a Ha) as (Hna, Haz).
 apply List.in_map_iff.
 exists (n / a).
 split; [ | now apply divisor_inv ].
 apply Nat_mod_0_div_div; [ | easy ].
 split; [ flia Haz | ].
 apply Nat.mod_divides in Hna; [ | easy ].
 destruct Hna as (c, Hc); subst n.
 destruct c; [ now rewrite Nat.mul_comm in Hn | ].
 rewrite Nat.mul_comm; cbn; flia.
-apply List.in_rev in Ha.
 destruct (zerop n) as [Hn| Hn]; [ now subst n | ].
 apply Nat.neq_0_lt_0 in Hn.
 apply in_divisors_iff; [ easy | ].
 apply List.in_map_iff in Ha.
 destruct Ha as (b & Hnb & Hb).
 subst a.
 apply in_divisors; [ easy | ].
 now apply divisor_inv.
Qed.

Theorem f_mul_fold_add_distr_l {F : field} : ∀ a b l,
  (a * fold_left f_add l b)%F =
  (fold_left f_add (map (f_mul a) l) (a * b)%F).
Proof.
intros.
revert a b.
induction l as [| c l]; intros; [ easy | cbn ].
rewrite <- f_mul_add_distr_l.
apply IHl.
Qed.

Theorem f_mul_fold_add_distr_r {F : field} : ∀ a b l,
  (fold_left f_add l a * b)%F =
  (fold_left f_add (map (f_mul b) l) (a * b)%F).
Proof.
intros.
revert a b.
induction l as [| c l]; intros; [ easy | cbn ].
rewrite (f_mul_comm b).
rewrite <- f_mul_add_distr_r.
apply IHl.
Qed.

Theorem map_f_mul_fold_add_distr_l {F : field} : ∀ (a : nat → f_type) b f l,
  map (λ i, (a i * fold_left f_add (f i) b)%F) l =
  map (λ i, fold_left f_add (map (f_mul (a i)) (f i)) (a i * b)%F) l.
Proof.
intros a b.
induction l as [| c l]; [ easy | cbn ].
rewrite f_mul_fold_add_distr_l; f_equal.
apply IHl.
Qed.

Theorem map_f_mul_fold_add_distr_r {F : field} : ∀ a (b : nat → f_type) f l,
  map (λ i, (fold_left f_add (f i) a * b i)%F) l =
  map (λ i, fold_left f_add (map (f_mul (b i)) (f i)) (a * b i)%F) l.
Proof.
intros a b.
induction l as [| c l]; [ easy | cbn ].
rewrite f_mul_fold_add_distr_r; f_equal.
apply IHl.
Qed.

Theorem fold_add_add {F : field} : ∀ a a' l l',
  (fold_left f_add l a + fold_left f_add l' a')%F =
  fold_left f_add (l ++ l') (a + a')%F.
Proof.
intros.
revert a.
induction l as [| b l]; intros; cbn. {
  rewrite f_add_comm, (f_add_comm _ a').
  symmetry; apply fold_f_add_assoc.
}
rewrite IHl.
now rewrite f_add_add_swap.
Qed.

Theorem fold_add_map_fold_add {F : field} : ∀ (f : nat → _) a b l,
  List.fold_left f_add (List.map (λ i, List.fold_left f_add (f i) (a i)) l)
    b =
  List.fold_left f_add (List.flat_map (λ i, a i :: f i) l)
    b.
Proof.
intros.
induction l as [| c l]; [ easy | cbn ].
rewrite fold_f_add_assoc.
rewrite fold_f_add_assoc.
rewrite IHl, f_add_comm.
rewrite fold_add_add.
rewrite (f_add_comm _ b).
now rewrite fold_f_add_assoc.
Qed.

Theorem map_mul_triplet {F : field} : ∀ u v w (f g h : nat → nat → nat) k l a,
  fold_left f_add
    (flat_map
       (λ d, map (λ d', (u (f d d') * v (g d d') * w (h d d')))%F (k d)) l)
    a =
  fold_left f_add
    (map (λ t, let '(i, j, k) := t in (u i * v j * w k)%F)
      (flat_map
         (λ d, map (λ d', (f d d', g d d', h d d')) (k d)) l))
    a.
Proof.
intros.
revert a.
induction l as [| b l]; intros; [ easy | cbn ].
rewrite map_app.
do 2 rewrite fold_left_app.
rewrite IHl; f_equal; clear.
remember (k b) as l eqn:Hl; clear Hl.
revert a b.
induction l as [| c l]; intros; [ easy | cbn ].
apply IHl.
Qed.

Definition xyz_zxy '((x, y, z) : (nat * nat * nat)) := (z, x, y).

Theorem mul_assoc_indices_eq : ∀ n,
  flat_map (λ d, map (λ d', (d, d', n / d / d')) (divisors (n / d))) (divisors n) =
  map xyz_zxy (flat_map (λ d, map (λ d', (d', d / d', n / d)) (divisors d)) (rev (divisors n))).
Proof.
intros.
destruct (zerop n) as [Hn| Hn]; [ now rewrite Hn | ].
apply Nat.neq_0_lt_0 in Hn.
do 2 rewrite flat_map_concat_map.
rewrite map_rev.
rewrite (map_inv_divisors n) at 2.
rewrite <- map_rev.
rewrite rev_involutive.
rewrite map_map.
rewrite concat_map.
rewrite map_map.
f_equal.
specialize (in_divisors n Hn) as Hin.
remember (divisors n) as l eqn:Hl; clear Hl.
induction l as [| a l]; [ easy | ].
cbn - [ divisors ].
rewrite IHl. 2: {
  intros * Hd.
  now apply Hin; right.
}
f_equal.
rewrite Nat_mod_0_div_div; cycle 1. {
  specialize (Hin a (or_introl eq_refl)) as (H1, H2).
  split; [ flia H2 | ].
  apply Nat.mod_divides in H1; [ | easy ].
  destruct H1 as (c, Hc); rewrite Hc.
  destruct c; [ now rewrite Hc, Nat.mul_comm in Hn | ].
  rewrite Nat.mul_comm; cbn; flia.
} {
  apply (Hin a (or_introl eq_refl)).
}
now rewrite map_map.
Qed.

Definition compare_trip '(i1, j1, k1) '(i2, j2, k2) :=
  match Nat.compare i1 i2 with
  | Eq =>
      match Nat.compare j1 j2 with
      | Eq => Nat.compare k1 k2
      | c => c
      end
  | c => c
  end.
Definition lt_triplet t1 t2 := compare_trip t1 t2 = Lt.

Theorem StrictOrder_lt_triplet : StrictOrder lt_triplet.
Proof.
constructor.
-intros ((i, j), k) H.
 unfold lt_triplet, compare_trip in H.
 now do 3 rewrite Nat.compare_refl in H.
-unfold lt_triplet, compare_trip.
 intros ((a1, a2), a3) ((b1, b2), b3) ((c1, c2), c3) Hab Hbc.
 remember (a1 ?= b1) as ab1 eqn:Hab1; symmetry in Hab1.
 remember (a1 ?= c1) as ac1 eqn:Hac1; symmetry in Hac1.
 remember (b1 ?= c1) as bc1 eqn:Hbc1; symmetry in Hbc1.
 remember (a2 ?= b2) as ab2 eqn:Hab2; symmetry in Hab2.
 remember (b2 ?= c2) as bc2 eqn:Hbc2; symmetry in Hbc2.
 remember (a2 ?= c2) as ac2 eqn:Hac2; symmetry in Hac2.
 move ac2 before ab1; move bc2 before ab1; move ab2 before ab1.
 move bc1 before ab1; move ac1 before ab1.
 destruct ab1; [ | | easy ].
 +apply Nat.compare_eq_iff in Hab1; subst b1.
  destruct ab2; [ | | easy ].
  *apply Nat.compare_eq_iff in Hab2; subst b2.
   apply Nat.compare_lt_iff in Hab.
   destruct bc1; [ | | easy ].
  --apply Nat.compare_eq_iff in Hbc1; subst c1.
    rewrite <- Hac1, Nat.compare_refl.
    destruct bc2; [ | | easy ].
   ++apply Nat.compare_eq_iff in Hbc2; subst c2.
     apply Nat.compare_lt_iff in Hbc.
     rewrite <- Hac2, Nat.compare_refl.
     apply Nat.compare_lt_iff.
     now transitivity b3.
   ++apply Nat.compare_lt_iff in Hbc2.
     destruct ac2; [ | easy | ].
    **apply Nat.compare_eq_iff in Hac2; subst c2.
      flia Hbc2.
    **apply Nat.compare_gt_iff in Hac2.
      flia Hbc2 Hac2.
  --apply Nat.compare_lt_iff in Hbc1.
    destruct ac1; [ | easy | ].
   **apply Nat.compare_eq_iff in Hac1; flia Hbc1 Hac1.
   **apply Nat.compare_gt_iff in Hac1; flia Hbc1 Hac1.
  *destruct bc1; [ | | easy ].
  --apply Nat.compare_eq_iff in Hbc1; subst c1.
    destruct bc2; [ | | easy ].
   ++apply Nat.compare_eq_iff in Hbc2; subst c2.
     rewrite <- Hac2, Hab2.
     destruct ac1; [ easy | easy | ].
     now rewrite Nat.compare_refl in Hac1.
   ++apply Nat.compare_lt_iff in Hab2.
     apply Nat.compare_lt_iff in Hbc2.
     destruct ac1; [ | easy | ].
    **destruct ac2; [ | easy | ].
    ---apply Nat.compare_eq_iff in Hac2; subst c2.
       flia Hab2 Hbc2.
    ---apply Nat.compare_gt_iff in Hac2.
       flia Hab2 Hbc2 Hac2.
    **now rewrite Nat.compare_refl in Hac1.
  --now rewrite <- Hac1, Hbc1.
 +destruct ac1; [ | easy | ].
  *apply Nat.compare_eq_iff in Hac1; subst c1.
   destruct ac2; [ | easy | ].
  --apply Nat.compare_eq_iff in Hac2; subst c2.
    destruct bc1; [ | | easy ].
   ++apply Nat.compare_eq_iff in Hbc1; subst b1.
     now rewrite Nat.compare_refl in Hab1.
   ++apply Nat.compare_lt_iff in Hab1.
     apply Nat.compare_lt_iff in Hbc1.
     flia Hab1 Hbc1.
  --destruct bc1; [ | | easy ].
   ++apply Nat.compare_eq_iff in Hbc1; subst b1.
     now rewrite Nat.compare_refl in Hab1.
   ++apply Nat.compare_lt_iff in Hab1.
     apply Nat.compare_lt_iff in Hbc1.
     flia Hab1 Hbc1.
  *destruct bc1; [ | | easy ].
  --apply Nat.compare_eq_iff in Hbc1; subst c1.
    now rewrite Hac1 in Hab1.
  --apply Nat.compare_lt_iff in Hab1.
    apply Nat.compare_lt_iff in Hbc1.
    apply Nat.compare_gt_iff in Hac1.
    flia Hab1 Hbc1 Hac1.
Qed.

Theorem Permutation_f_sum_add {F : field} {A} : ∀ (l1 l2 : list A) f a,
  Permutation l1 l2
  → fold_left f_add (map f l1) a =
     fold_left f_add (map f l2) a.
Proof.
intros * Hperm.
induction Hperm using Permutation_ind; [ easy | | | ]. {
  cbn; do 2 rewrite fold_f_add_assoc.
  now rewrite IHHperm.
} {
  now cbn; rewrite f_add_add_swap.
}
etransitivity; [ apply IHHperm1 | apply IHHperm2 ].
Qed.

(* The product of series is associative; first, lemmas *)

Theorem fold_add_flat_prod_assoc {F : field} : ∀ n u v w,
  n ≠ 0
  → fold_left f_add
       (flat_map (λ d, map (f_mul (u d)) (log_prod_list v w (n / d)))
          (divisors n))
       0%F =
     fold_left f_add
       (flat_map (λ d, map (f_mul (w (n / d))) (log_prod_list u v d))
          (divisors n))
       0%F.
Proof.
intros * Hn.
do 2 rewrite flat_map_concat_map.
unfold log_prod_list.
do 2 rewrite List_map_map_map.
unfold log_prod_term.
assert (H : ∀ f l,
  map (λ d, map (λ d', (u d * (v d' * w (n / d / d')))%F) (f d)) l =
  map (λ d, map (λ d', (u d * v d' * w (n / d / d'))%F) (f d)) l). {
  intros.
  induction l as [| a l]; [ easy | cbn ].
  rewrite IHl; f_equal; clear.
  induction (f a) as [| b l]; [ easy | cbn ].
  rewrite IHl; f_equal.
  apply f_mul_assoc.
}
rewrite H; clear H.
assert (H : ∀ f l,
  map (λ d, map (λ d', (w (n / d) * (u d' * v (d / d')))%F) (f d)) l =
  map (λ d, map (λ d', (u d' * v (d / d') * w (n / d))%F) (f d)) l). {
  intros.
  induction l as [| a l]; [ easy | cbn ].
  rewrite IHl; f_equal; clear.
  induction (f a) as [| b l]; [ easy | cbn ].
  rewrite IHl; f_equal.
  apply f_mul_comm.
}
rewrite H; clear H.
do 2 rewrite <- flat_map_concat_map.
do 2 rewrite map_mul_triplet.
remember (
  flat_map (λ d, map (λ d', (d, d', n / d / d')) (divisors (n / d)))
    (divisors n))
  as l1 eqn:Hl1.
remember (
  flat_map (λ d, map (λ d', (d', d / d', n / d)) (divisors d))
    (divisors n))
  as l2 eqn:Hl2.
move l2 before l1.
assert (H1 : ∀ d1 d2 d3, d1 * d2 * d3 = n ↔ (d1, d2, d3) ∈ l1). {
  split; intros Huvw.
  -intros.
   assert (Hd1 : d1 ≠ 0) by now intros H; rewrite <- Huvw, H in Hn.
   assert (Hd2 : d2 ≠ 0). {
     now intros H; rewrite <- Huvw, H, Nat.mul_0_r in Hn.
   }
   assert (Hd3 : d3 ≠ 0). {
     now intros H; rewrite <- Huvw, H, Nat.mul_comm in Hn.
   }
   subst l1.
   apply in_flat_map.
   exists d1.
   split. {
     apply in_divisors_iff; [ easy | ].
     split; [ | easy ].
     rewrite <- Huvw.
     apply Nat.mod_divides; [ easy | ].
     exists (d2 * d3).
     symmetry; apply Nat.mul_assoc.
   }
   apply List.in_map_iff.
   exists d2.
   rewrite <- Huvw.
   rewrite <- Nat.mul_assoc, Nat.mul_comm.
   rewrite Nat.div_mul; [ | easy ].
   rewrite Nat.mul_comm.
   rewrite Nat.div_mul; [ | easy ].
   split; [ easy | ].
   apply in_divisors_iff; [ now apply Nat.neq_mul_0 | ].
   split; [ | easy ].
   apply Nat.mod_divides; [ easy | ].
   exists d3; apply Nat.mul_comm.
  -subst l1.
   apply List.in_flat_map in Huvw.
   destruct Huvw as (d & Hd & Hdi).
   apply List.in_map_iff in Hdi.
   destruct Hdi as (d' & Hd' & Hdd).
   apply in_divisors in Hd; [ | easy ].
   destruct Hd as (Hnd, Hd).
   injection Hd'; clear Hd'; intros Hw Hv Hu.
   subst d1 d2 d3.
   apply Nat.mod_divides in Hnd; [ | easy ].
   destruct Hnd as (d1, Hd1).
   rewrite Hd1, Nat.mul_comm, Nat.div_mul in Hdd; [ | easy ].
   rewrite Hd1, (Nat.mul_comm _ d1), Nat.div_mul; [ | easy ].
   assert (Hd1z : d1 ≠ 0) by now intros H; rewrite H in Hdd.
   apply in_divisors in Hdd; [ | easy ].
   destruct Hdd as (Hdd, Hd'z).
   apply Nat.mod_divides in Hdd; [ | easy ].
   destruct Hdd as (d'', Hdd).
   rewrite <- Nat.mul_assoc, Nat.mul_comm; f_equal.
   rewrite Hdd at 1.
   now rewrite (Nat.mul_comm _ d''), Nat.div_mul.
}
assert (H2 : ∀ d1 d2 d3, d1 * d2 * d3 = n ↔ (d1, d2, d3) ∈ l2). {
  intros.
  split; intros Hddd.
  -assert (Hd1 : d1 ≠ 0) by now intros H; rewrite <- Hddd, H in Hn.
   assert (Hd2 : d2 ≠ 0). {
     now intros H; rewrite <- Hddd, H, Nat.mul_0_r in Hn.
   }
   assert (Hd3 : d3 ≠ 0). {
     now intros H; rewrite <- Hddd, H, Nat.mul_comm in Hn.
   }
   subst l2.
   apply in_flat_map.
   exists (d1 * d2).
   split. {
     apply in_divisors_iff; [ easy | ].
     split; [ | now apply Nat.neq_mul_0 ].
     rewrite <- Hddd.
     apply Nat.mod_divides; [ now apply Nat.neq_mul_0 | ].
     now exists d3.
   }
   apply List.in_map_iff.
   exists d1.
   rewrite <- Hddd.
   rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
   rewrite Nat.mul_comm, Nat.div_mul; [ | now apply Nat.neq_mul_0 ].
   split; [ easy | ].
   apply in_divisors_iff; [ now apply Nat.neq_mul_0 | ].
   split; [ | easy ].
   apply Nat.mod_divides; [ easy | ].
   exists d2; apply Nat.mul_comm.
  -subst l2.
   apply List.in_flat_map in Hddd.
   destruct Hddd as (d & Hd & Hdi).
   apply List.in_map_iff in Hdi.
   destruct Hdi as (d' & Hd' & Hdd).
   apply in_divisors in Hd; [ | easy ].
   destruct Hd as (Hnd, Hd).
   injection Hd'; clear Hd'; intros Hd3 Hd2 Hd1.
   subst d1 d2 d3.
   apply Nat.mod_divides in Hnd; [ | easy ].
   destruct Hnd as (d1, Hd1).
   rewrite Hd1, (Nat.mul_comm d), Nat.div_mul; [ | easy ].
   rewrite Nat.mul_comm; f_equal.
   apply in_divisors in Hdd; [ | easy ].
   destruct Hdd as (Hdd, Hd').
   apply Nat.mod_divides in Hdd; [ | easy ].
   destruct Hdd as (d'', Hdd).
   rewrite Hdd at 1.
   now rewrite (Nat.mul_comm _ d''), Nat.div_mul.
}
assert (Hl1s : Sorted.Sorted lt_triplet l1). {
  clear - Hn Hl1.
  specialize (in_divisors n Hn) as Hin.
  specialize (divisors_are_sorted n) as Hs.
  remember (divisors n) as l eqn:Hl; clear Hl.
  subst l1.
  induction l as [| a l]; [ now cbn | ].
  cbn - [ divisors ].
  apply (SetoidList.SortA_app eq_equivalence).
  -specialize (Hin a (or_introl eq_refl)); clear IHl.
   destruct Hin as (Hna, Ha).
   apply Nat.mod_divides in Hna; [ | easy ].
   destruct Hna as (b, Hb).
   rewrite Hb, Nat.mul_comm, Nat.div_mul; [ | easy ].
   subst n.
   assert (Hb : b ≠ 0) by now intros H; rewrite H, Nat.mul_comm in Hn.
   clear Hn l Hs; rename b into n; rename Hb into Hn.
   specialize (in_divisors n Hn) as Hin.
   specialize (divisors_are_sorted n) as Hs.
   remember (divisors n) as l eqn:Hl; clear Hl.
   induction l as [| b l]; cbn; [ easy | ].
   constructor.
   +apply IHl; [ now intros d Hd; apply Hin; right | now inversion Hs ].
   +clear IHl.
    destruct l as [| c l]; cbn; [ easy | ].
    constructor.
    unfold lt_triplet, compare_trip.
    rewrite Nat.compare_refl.
    remember (b ?= c) as bb eqn:Hbb; symmetry in Hbb.
    destruct bb; [ | easy | ].
    *apply Nat.compare_eq in Hbb; subst b.
     inversion Hs; subst.
     inversion H2; flia H0.
    *apply Nat.compare_gt_iff in Hbb.
     inversion Hs; subst.
     inversion H2; flia H0 Hbb.
  -apply IHl; [ now intros d Hd; apply Hin; right | now inversion Hs ].
  -intros t1 t2 Hsl Hitt.
   assert (Hjk1 : ∃ j1 k1, t1 = (a, j1, k1)). {
     clear - Hsl.
     remember (divisors (n / a)) as l eqn:Hl; symmetry in Hl; clear Hl.
     induction l as [| b l]; [ now apply SetoidList.InA_nil in Hsl | ].
     cbn in Hsl.
     apply SetoidList.InA_cons in Hsl.
     destruct Hsl as [Hsl| Hsl]. {
       now rewrite Hsl; exists b, (n / a / b).
     }
     now apply IHl.
   }
   destruct Hjk1 as (j1 & k1 & Ht1); rewrite Ht1.
   assert (Hjk2 : ∃ i2 j2 k2, a < i2 ∧ t2 = (i2, j2, k2)). {
     clear - Hs Hitt.
     revert a Hs.
     induction l as [| b l]; intros. {
       now apply SetoidList.InA_nil in Hitt.
     }
     cbn - [ divisors ] in Hitt.
     apply SetoidList.InA_app in Hitt.
     destruct Hitt as [Hitt| Hitt]. {
       clear - Hitt Hs.
       assert (H2 : ∃ j2 k2, t2 = (b, j2, k2)). {
         clear - Hitt.
         induction (divisors (n / b)) as [| a l]. {
           now apply SetoidList.InA_nil in Hitt.
         }
         cbn in Hitt.
         apply SetoidList.InA_cons in Hitt.
         destruct Hitt as [Hitt| Hitt]. {
           now rewrite Hitt; exists a, (n / b / a).
         }
         now apply IHl.
       }
       destruct H2 as (j2 & k2 & H2).
       rewrite H2.
       exists b, j2, k2.
       split; [ | easy ].
       apply Sorted.Sorted_inv in Hs.
       destruct Hs as (Hs, Hr2).
       now apply Sorted.HdRel_inv in Hr2.
     }
     apply IHl; [ easy | ].
     apply Sorted.Sorted_inv in Hs.
     destruct Hs as (Hs, Hr).
     apply Sorted.Sorted_inv in Hs.
     destruct Hs as (Hs, Hr2).
     constructor; [ easy | ].
     apply Sorted.HdRel_inv in Hr.
     eapply (SetoidList.InfA_ltA Nat.lt_strorder); [ apply Hr | easy ].
   }
   destruct Hjk2 as (i2 & j2 & k2 & Hai2 & Ht2).
   rewrite Ht2.
   unfold lt_triplet; cbn.
   remember (a ?= i2) as ai eqn:Hai; symmetry in Hai.
   destruct ai; [ | easy | ].
   +apply Nat.compare_eq_iff in Hai; flia Hai Hai2.
   +apply Nat.compare_gt_iff in Hai; flia Hai Hai2.
}
assert (Hll : length l1 = length l2). {
  rewrite mul_assoc_indices_eq in Hl1.
  subst l1 l2.
  rewrite map_length.
  do 2 rewrite List_flat_map_length.
  do 2 rewrite map_rev.
  rewrite map_map.
  remember (map _ (divisors n)) as l eqn:Hl; clear.
  remember 0 as a; clear Heqa.
  revert a.
  induction l as [| b l]; intros; [ easy | cbn ].
  rewrite fold_right_app; cbn.
  rewrite IHl; clear.
  revert a b.
  induction l as [| c l]; intros; [ easy | cbn ].
  rewrite IHl; ring.
}
assert (H3 : ∀ t, t ∈ l1 ↔ t ∈ l2). {
  intros ((d1, d2), d3); split; intros Ht.
  -now apply H2, H1.
  -now apply H1, H2.
}
assert (Hnd1 : NoDup l1). {
  clear - Hl1s.
  induction l1 as [| a1 l1]; [ constructor | ].
  apply Sorted.Sorted_inv in Hl1s.
  destruct Hl1s as (Hs, Hr).
  constructor; [ | now apply IHl1 ].
  intros Ha.
  clear IHl1.
  revert a1 Hr Ha.
  induction l1 as [| a2 l1]; intros; [ easy | ].
  apply Sorted.HdRel_inv in Hr.
  destruct Ha as [Ha| Ha]. {
    subst a1; revert Hr.
    apply StrictOrder_lt_triplet.
  }
  apply Sorted.Sorted_inv in Hs.
  eapply IHl1; [ easy | | apply Ha ].
  eapply SetoidList.InfA_ltA; [ | apply Hr | easy ].
  apply StrictOrder_lt_triplet.
}
assert (Hnd2 : NoDup l2). {
  rewrite mul_assoc_indices_eq in Hl1.
  remember (λ d : nat, map (λ d' : nat, (d', d / d', n / d)) (divisors d))
    as f eqn:Hf.
  rewrite Hl1 in Hnd1.
  rewrite Hl2.
  apply NoDup_map_inv in Hnd1.
  rewrite flat_map_concat_map in Hnd1.
  rewrite map_rev in Hnd1.
  rewrite flat_map_concat_map.
  remember (map f (divisors n)) as l eqn:Hl.
  now apply NoDup_concat_rev.
}
assert (HP : Permutation l1 l2). {
  now apply NoDup_Permutation.
}
now apply Permutation_f_sum_add.
Qed.

Theorem log_prod_assoc {F : field} : ∀ u v w i,
  i ≠ 0
  → log_prod u (log_prod v w) i = log_prod (log_prod u v) w i.
Proof.
intros * Hi.
unfold log_prod at 1 3.
unfold log_prod_list, log_prod_term.
unfold log_prod.
rewrite map_f_mul_fold_add_distr_l.
rewrite fold_add_map_fold_add.
rewrite map_f_mul_fold_add_distr_r.
rewrite fold_add_map_fold_add.
assert
  (H : ∀ (u : nat → _) f l,
   flat_map (λ i, (u i * 0)%F :: f i) l =
   flat_map (λ i, 0%F :: f i) l). {
  clear; intros.
  induction l as [| a l]; [ easy | cbn ].
  now rewrite f_mul_0_r, IHl.
}
rewrite H; clear H.
assert
  (H : ∀ (u : nat → _) f l,
   flat_map (λ i, (0 * u i)%F :: f i) l =
   flat_map (λ i, 0%F :: f i) l). {
  clear; intros.
  induction l as [| a l]; [ easy | cbn ].
  now rewrite f_mul_0_l, IHl.
}
rewrite H; clear H.
assert
  (H : ∀ (f : nat → _) l l',
   fold_left f_add (flat_map (λ i, 0%F :: f i) l) l' =
   fold_left f_add (flat_map f l) l'). {
  clear; intros.
  revert l'.
  induction l as [| a l]; intros; [ easy | cbn ].
  rewrite f_add_0_r.
  do 2 rewrite fold_left_app.
  apply IHl.
}
do 2 rewrite H.
clear H.
now apply fold_add_flat_prod_assoc.
Qed.

(* Associativity of product of series *)

Theorem ls_mul_assoc {F : field} : ∀ x y z,
  (x * (y * z) = (x * y) * z)%LS.
Proof.
intros * i Hi.
now cbn; apply log_prod_assoc.
Qed.

(* Polynomial 1-1/n^s ≍ 1-x^ln(n) *)

Definition pol_pow {F : field} n :=
  {| lp := List.repeat 0%F (n - 1) ++ [f_one] |}.

(*
Here, we prove that
   ζ(s) (1 - 1/2^s)
is equal to
   ζ(s) without terms whose rank is divisible by 2
   (only odd ones are remaining)

But actually, our theorem is more general.
We prove, for any m and r, that
   r(s) (1 - 1/m^s)

where r is a series having the following property
   ∀ i, r(s)_{i} = r(s)_{n*i}
(the i-th coefficient of the series is equal to its (n*i)-th coefficient,
which is true for ζ since all its coefficients are 1)

is equal to a series r with all coefficients, whose rank is
a multiple of m, are removed.

The resulting series ζ(s) (1-1/m^s) has this property for all n
such as gcd(m,n)=1, allowing us at the next theorems to restart
with that series and another prime number. We can then iterate
for all prime numbers.

Note that we can then apply that whatever order of prime numbers
and even not prime numbers if we want, providing their gcd two by
two is 1.
*)

Theorem series_times_pol_1_sub_pow {F : field} : ∀ s m,
  2 ≤ m
  → (∀ i, i ≠ 0 → ls s i = ls s (m * i))
  → (s *' (pol_pow 1 - pol_pow m) = series_but_mul_of m s)%LS.
Proof.
intros * Hm Hs n Hn.
cbn - [ ls_of_pol log_prod ].
remember (n mod m) as p eqn:Hp; symmetry in Hp.
unfold log_prod, log_prod_list.
remember (log_prod_term (ls s) (ls (ls_of_pol (pol_pow 1 - pol_pow m))) n)
  as t eqn:Ht.
assert (Htn : t n = s~{n}). {
  rewrite Ht; unfold log_prod_term.
  rewrite Nat.div_same; [ | easy ].
  replace ((ls_of_pol _)~{1}) with f_one. 2: {
    symmetry; cbn.
    destruct m; [ flia Hm | cbn ].
    rewrite Nat.sub_0_r.
    destruct m; [ flia Hm | clear; cbn ].
    now destruct m; cbn; rewrite f_opp_0, f_add_0_r.
  }
  apply f_mul_1_r.
}
destruct p. {
  apply Nat.mod_divides in Hp; [ | flia Hm ].
  destruct Hp as (p, Hp).
  assert (Hpz : p ≠ 0). {
    now intros H; rewrite H, Nat.mul_0_r in Hp.
  }
  move p before n; move Hpz before Hn.
  assert (Htm : t p = (- s~{n})%F). {
    assert (H : t p = (- s~{p})%F). {
      rewrite Ht; unfold log_prod_term.
      rewrite Hp, Nat.div_mul; [ | easy ].
      replace ((ls_of_pol _)~{m}) with (- f_one)%F. 2: {
        symmetry; cbn.
        destruct m; [ flia Hm | cbn ].
        rewrite Nat.sub_0_r.
        destruct m; [ flia Hm | clear; cbn ].
        induction m; [ cbn; apply f_add_0_l | cbn ].
        destruct m; cbn in IHm; cbn; [ easy | apply IHm ].
      }
      now rewrite f_mul_opp_r, f_mul_1_r.
    }
    rewrite Hs in H; [ | easy ].
    now rewrite <- Hp in H.
  }
  assert (Hto : ∀ d, d ∈ divisors n → d ≠ n → d ≠ p → t d = 0%F). {
    intros d Hdn Hd1 Hdm.
    rewrite Ht; unfold log_prod_term.
    remember (n / d) as nd eqn:Hnd; symmetry in Hnd.
    assert (Hd : d ≠ 0). {
      intros H; rewrite H in Hdn.
      now apply in_divisors in Hdn.
    }
    move d before p; move Hd before Hn.
    assert (Hdnd : n = d * nd). {
      rewrite <- Hnd.
      apply Nat.div_exact; [ easy | ].
      now apply in_divisors in Hdn.
    }
    clear Hnd.
    assert (Hd1n : nd ≠ 1). {
      now intros H; rewrite H, Nat.mul_1_r in Hdnd; symmetry in Hdnd.
    }
    replace ((ls_of_pol (pol_pow 1 - pol_pow m))~{nd}) with 0%F. 2: {
      symmetry; cbn.
      destruct nd; [ easy | ].
      destruct m; intros. {
        cbn - [ "/" ]; rewrite f_add_opp_diag_r.
        now destruct nd.
      }
      rewrite Nat_sub_succ_1.
      assert (Hndm : nd ≠ m). {
        intros H; rewrite Hdnd, H, Nat.mul_comm in Hp.
        now apply Nat.mul_cancel_l in Hp.
      }
      destruct m. {
        destruct nd; [ easy | now destruct nd ].
      }
      destruct nd; [ easy | cbn ].
      destruct m. {
        destruct nd; [ | now destruct nd ].
        rewrite Hdnd, Nat.mul_comm in Hp.
        now apply Nat.mul_cancel_l in Hp.
      }
      cbn; rewrite f_opp_0, f_add_0_l.
      destruct nd; [ easy | ].
      clear - Hndm.
      revert nd Hndm.
      induction m; intros. {
        destruct nd; [ easy | now destruct nd ].
      }
      cbn; rewrite f_opp_0, f_add_0_l.
      destruct nd; [ easy | ].
      apply -> Nat.succ_inj_wd_neg in Hndm.
      now apply IHm.
    }
    apply f_mul_0_r.
  }
(**)
  assert (Hpd : p ∈ divisors n). {
    apply in_divisors_iff; [ easy | ].
    now rewrite Hp, Nat.mod_mul.
  }
  specialize (In_nth _ _ 0 Hpd) as (k & Hkd & Hkn).
  specialize (nth_split _ 0 Hkd) as (l1 & l2 & Hll & Hl1).
  rewrite Hkn in Hll.
  assert (Hdn : divisors n ≠ []). {
    intros H; rewrite H in Hll; now destruct l1.
  }
  specialize (app_removelast_last 0 Hdn) as H1.
  rewrite eq_last_divisor in H1; [ | easy ].
  rewrite Hll in H1 at 2.
  rewrite H1, map_app, fold_left_app; cbn.
  destruct l2 as [| a l2]. {
    rewrite removelast_app; [ | easy ].
    rewrite removelast_app in H1; [ | easy ].
    cbn; rewrite app_nil_r.
    rewrite app_nil_r in H1.
    assert (H : p = n). {
      rewrite Hll in H1.
      now apply app_inj_tail in H1.
    }
    rewrite H, Htn in Htm; move Htm at bottom.
    apply f_eq_opp_eq_0 in Htm.
    rewrite Htn, Htm, f_add_0_r.
...
  assert (Hmz : m ≠ 0) by now intros H; rewrite H in Hp.
  assert (Hmd : m ∈ divisors n). {
    apply in_divisors_iff; [ easy | ].
    now rewrite Hp, Nat.mul_comm, Nat.mod_mul.
  }
  specialize (In_nth _ _ 0 Hmd) as (k & Hkd & Hkn).
  specialize (nth_split _ 0 Hkd) as (l1 & l2 & Hll & Hl1).
  rewrite Hkn in Hll.
  rewrite Hll, map_app; cbn.
  specialize (eq_first_divisor_1 n Hn) as H1.
  remember (divisors n) as l.
  destruct l1 as [| a l1]. {
    cbn in Hl1; subst k.
    destruct l as [| a l]; [ easy | ].
    cbn in Hkn, H1.
    rewrite <- Hkn, H1 in Hm; flia Hm.
  }
  rewrite Hll in H1; cbn in H1; subst a.
  cbn; rewrite f_add_0_l, Ht1, Htn.
  rewrite fold_left_app; cbn.
  rewrite fold_f_add_assoc.
  assert (H1 : ∀ a, fold_left f_add (map t l1) a = a). {
    assert (Hdl : ∀ d, d ∈ l1 → t d = 0). {
      intros d Hd.
      specialize (divisors_are_sorted n) as Hds.
      rewrite <- Heql, Hll in Hds; cbn in Hds.
      apply Hto. {
        intros H; subst d.
        assert (H : 1 ∈ (l1 ++ m :: l2)). {
          now apply in_or_app; left.
        }
        replace (1 :: l1 ++ m :: l2) with ([] ++ 1 :: l1 ++ m :: l2)
          in Hds by easy.
        now apply Sorted_Sorted_lt_app_not_in_r in Hds.
      }
      intros H; subst d.
      assert (H : m ∈ (1 :: l1)) by now right.
      rewrite app_comm_cons in Hds.
      revert H.
      now apply Sorted_Sorted_lt_app_not_in_l in Hds.
    }
    intros a; clear - Hdl.
    revert a.
    induction l1 as [| b l]; intros; [ easy | ].
    cbn; rewrite Hdl; [ | now left ].
    rewrite f_add_0_r.
    apply IHl; intros c Hc.
    now apply Hdl; right.
  }
  rewrite H1.
  assert (H2 : ∀ a, fold_left f_add (map t l2) a = a). {
    assert (Hdl : ∀ d, d ∈ l2 → t d = 0). {
      intros d Hd.
      clear Hs.
      specialize (divisors_are_sorted n) as Hs.
      rewrite <- Heql, Hll in Hs; cbn in Hs.
      apply Hto. {
        intros H; subst d.
        apply Sorted.Sorted_StronglySorted in Hs; [ | apply Nat.lt_strorder ].
        apply Sorted.StronglySorted_inv in Hs.
        destruct Hs as (Hds, Hall).
        specialize (proj1 (Forall_forall _ _) Hall 1) as H2.
        assert (H : 1 ∈ (l1 ++ m :: l2)). {
          now apply in_or_app; right; right.
        }
        specialize (H2 H); flia H2.
      }
      intros H; subst d.
      apply Sorted.Sorted_inv in Hs.
      destruct Hs as (Hs, Hr).
      now apply Sorted_Sorted_lt_app_not_in_r in Hs.
    }
    intros a; clear - Hdl.
    revert a.
    induction l2 as [| b l]; intros; [ easy | ].
    cbn; rewrite Hdl; [ | now left ].
    rewrite f_add_0_r.
    apply IHl; intros c Hc.
    now apply Hdl; right.
  }
  rewrite H2.
  apply f_add_opp_diag_r.
}
assert (Hto : ∀ d, d ∈ divisors n → d ≠ 1 → t d = 0). {
  intros d Hd Hd1.
  rewrite Ht; unfold log_prod_term.
  replace ((ls_of_pol (pol_pow 1 - pol_pow m))~{d}) with 0. 2: {
    symmetry.
    clear - Hn Hp Hd Hd1.
    assert (Hdm : d ≠ m). {
      intros H; subst d.
      apply in_divisors in Hd; [ | easy ].
      now rewrite Hp in Hd.
    }
    clear - Hd1 Hdm; cbn.
    destruct d; [ easy | ].
    destruct m. {
      cbn.
      cbn; rewrite f_add_opp_diag_r.
      destruct d; [ easy | now destruct d ].
    }
    apply -> Nat.succ_inj_wd_neg in Hd1.
    apply -> Nat.succ_inj_wd_neg in Hdm.
    rewrite Nat_sub_succ_1.
    revert d Hd1 Hdm.
    induction m; intros. {
      cbn; rewrite f_add_opp_diag_r.
      destruct d; [ easy | now destruct d ].
    }
    cbn.
    destruct d; [ easy | clear Hd1 ].
    apply -> Nat.succ_inj_wd_neg in Hdm.
    destruct d. {
      destruct m; [ easy | ].
      now cbn; rewrite f_add_opp_diag_r.
    }
    specialize (IHm (S d) (Nat.neq_succ_0 _) Hdm) as H1.
    destruct m. {
      cbn.
      destruct d; [ easy | now destruct d ].
    }
    cbn in H1; cbn.
    destruct m. {
      cbn.
      destruct d; [ easy | ].
      destruct d; [ easy | now destruct d ].
    }
    cbn in H1.
    destruct d. {
      now cbn; rewrite f_add_opp_diag_r.
    }
    cbn; apply H1.
  }
  apply f_mul_0_l.
}
remember (divisors n) as l eqn:Hl; symmetry in Hl.
destruct l as [| a l]; [ now destruct n | ].
specialize (eq_first_divisor_1 n Hn) as H1.
rewrite Hl in H1; cbn in H1; subst a.
cbn; rewrite f_add_0_l, <- Ht1.
assert (H1 : ∀ a, fold_left f_add (map t l) a = a). {
  intros a.
  specialize (divisors_are_sorted n) as Hds.
  rewrite Hl in Hds; clear Hl.
  apply Sorted.Sorted_StronglySorted in Hds; [ | apply Nat.lt_strorder ].
  apply Sorted.StronglySorted_inv in Hds.
  destruct Hds as (Hds, Hall).
  revert a.
  induction l as [| b l]; intros; cbn; [ easy | ].
  rewrite f_add_comm, fold_f_add_assoc.
  rewrite IHl; cycle 1. {
    intros d Hd Hd1.
    apply Hto; [ | easy ].
    destruct Hd as [Hd| Hd]; [ now subst d | ].
    now right; right.
  } {
    now apply Sorted.StronglySorted_inv in Hds.
  } {
    now apply Forall_inv_tail in Hall.
  }
  rewrite Hto; cycle 1; [ now right; left | | ]. {
    intros H; subst b.
    apply Forall_inv in Hall; flia Hall.
  }
  apply f_add_0_l.
}
apply H1.
Qed.

(*
Here, we try to prove that
   (1 - 1/2^s) (1 - 1/3^s) (1 - 1/5^s) ... (1 - 1/p^s) ζ(s)
is equal to
   ζ(s) without terms whose rank is divisible by 2, 3, 5, ... or p
i.e.
   1 + 1/q^s + ... where q is the next prime after p

But actually, our theorem is a little more general:

1/ we do not do it for 2, 3, 5 ... p but for any list of natural numbers
   (n1, n2, n3, ... nm) such that gcd(ni,nj) = 1 for i≠j, what is true
   in particular for a list of prime numbers.

2/ It is not the ζ function but any series r with logarithm powers such that
       ∀ i, r_{i} = r_{n*i}
   for any n in (n1, n2, n3 ... nm)
   what is true for ζ function since ∀ i ζ_{i}=1.
*)

Notation "'Π' ( a ∈ l ) , e" := (List.fold_right (λ a c, (e .* c)%LS) ls_one l)
  (at level 36, a at level 0, l at level 60, e at level 36) : ls_scope.

Theorem list_of_pow_1_sub_pol_times_series {F : field} : ∀ l r,
  (∀ a, List.In a l → 2 ≤ a)
  → (∀ a, a ∈ l → ∀ i, i ≠ 0 → r~{i} = r~{a*i})
  → (∀ na nb, na ≠ nb → Nat.gcd (List.nth na l 1) (List.nth nb l 1) = 1)
  → (Π (a ∈ l), (pol_pow 1 - pol_pow a) * r =
     fold_right series_but_mul_of r l)%LS.
Proof.
intros * Hge2 Hai Hgcd.
induction l as [| a1 l]. {
  intros i Hi.
  cbn - [ ".*" ls_mul ls_one ].
  now apply ls_mul_1_l.
}
cbn.
remember (Π (a ∈ l), (pol_pow 1 - pol_pow a))%LS as p eqn:Hp.
unfold ".*".
rewrite <- ls_mul_assoc.
rewrite IHl; cycle 1. {
  now intros a Ha; apply Hge2; right.
} {
  intros a Ha i Hi; apply Hai; [ now right | easy ].
} {
  intros na nb Hnn.
  apply (Hgcd (S na) (S nb)).
  now intros H; apply Hnn; apply Nat.succ_inj in H.
}
apply pol_1_sub_pow_times_series; [ now apply Hge2; left | ].
intros i Hi.
specialize (Hai a1 (or_introl eq_refl)) as Ha1i.
clear - Hi Ha1i Hgcd.
induction l as [| a l]; [ now apply Ha1i | cbn ].
remember (i mod a) as m eqn:Hm; symmetry in Hm.
destruct m. {
  destruct a; [ easy | ].
  apply Nat.mod_divides in Hm; [ | easy ].
  destruct Hm as (m, Hm).
  rewrite Hm, Nat.mul_comm, <- Nat.mul_assoc, Nat.mul_comm.
  now rewrite Nat.mod_mul.
}
remember ((a1 * i) mod a) as n eqn:Hn; symmetry in Hn.
destruct n. {
  destruct a; [ easy | ].
  apply Nat.mod_divide in Hn; [ | easy ].
  specialize (Nat.gauss (S a) a1 i Hn) as H1.
  enough (H : Nat.gcd (S a) a1 = 1). {
    specialize (H1 H); clear H.
    apply Nat.mod_divide in H1; [ | easy ].
    now rewrite Hm in H1.
  }
  specialize (Hgcd 0 1 (Nat.neq_0_succ _)) as H2.
  now cbn in H2; rewrite Nat.gcd_comm in H2.
}
apply IHl; intros na nb Hnab; cbn.
destruct na. {
  destruct nb; [ easy | ].
  now apply (Hgcd 0 (S (S nb))).
}
destruct nb; [ now apply (Hgcd (S (S na)) 0) | ].
apply (Hgcd (S (S na)) (S (S nb))).
now apply Nat.succ_inj_wd_neg.
Qed.

Corollary list_of_1_sub_pow_primes_times_ζ {F : field} : ∀ l,
  (∀ p, p ∈ l → is_prime p = true)
  → NoDup l
  → (Π (p ∈ l), (pol_pow 1 - pol_pow p) * ζ =
     fold_right series_but_mul_of ζ l)%LS.
Proof.
intros * Hp Hnd.
apply list_of_pow_1_sub_pol_times_series; [ | easy | ]. {
  intros p Hpl.
  specialize (Hp _ Hpl) as H1.
  destruct p; [ easy | ].
  destruct p; [ easy | ].
  do 2 apply -> Nat.succ_le_mono.
  apply Nat.le_0_l.
} {
  intros * Hnab.
  destruct (lt_dec na (length l)) as [Hna| Hna]. {
    specialize (Hp _ (nth_In l 1 Hna)) as H1.
    destruct (lt_dec nb (length l)) as [Hnb| Hnb]. {
      specialize (Hp _ (nth_In l 1 Hnb)) as H2.
      move H1 before H2.
      assert (Hne : nth na l 1 ≠ nth nb l 1). {
        intros He.
        apply Hnab.
        apply (proj1 (NoDup_nth l 1) Hnd na nb Hna Hnb He).
      }
      now apply eq_primes_gcd_1.
    }
    apply Nat.nlt_ge in Hnb.
    rewrite (nth_overflow _ _ Hnb).
    apply Nat.gcd_1_r.
  }
  apply Nat.nlt_ge in Hna.
  rewrite (nth_overflow _ _ Hna).
  apply Nat.gcd_1_r.
}
Qed.

...

Definition infinite_fold_left {A B} (f : A → B → A) (l : nat → list B) a :=
  λ i, fold_left f (l i) a.

Locate "Π".

Notation "s *' p" := (ls_mul s (ls_of_pol p))
   (at level 42, left associativity, p at level 1) : ls_scope.

Check fold_left.

Inspect 7.

(*
Definition infinite_lp_prod {F : field} (f : nat → nat) :=
  fold_left (λ a b, (a *' (pol_pow 1 - pol_pow (f b)))%LS).

Check infinite_lp_prod.
*)

(* To be moved to Primes.v when done *)

Fixpoint primes_upto_aux n cnt :=
  match cnt with
  | 0 => []
  | S c =>
      if is_prime n then n :: primes_upto_aux (n + 1) c
      else primes_upto_aux (n + 1) c
  end.

Definition primes_upto := primes_upto_aux 1.

Compute (primes_upto 17).

Fixpoint prime_after_aux cnt n :=
  if is_prime n then n
  else
    match cnt with
    | 0 => 0 (* should never happen, thanks to Chebychev *)
    | S c => prime_after_aux c (n + 1)
    end.

Definition prime_after n := prime_after_aux (n + 1) (n + 1).

Compute (prime_after 2).

Fixpoint nth_prime_aux cnt n :=
  let p := prime_after n in
  match cnt with
  | 0 => p
  | S c => nth_prime_aux c p
  end.

Definition nth_prime n := nth_prime_aux (n - 1) 0.

Compute (nth_prime 3).

(* slow but simple *)

Definition firstn_primes n := map nth_prime (seq 1 n).

(* fast but complicated *)

Fixpoint firstn_primes_loop n p :=
  match n with
  | 0 => []
  | S n' =>
      let p' := prime_after p in
      p' :: firstn_primes_loop n' p'
  end.

Definition firstn_primes' n := firstn_primes_loop n 0.

Time Compute (let n := 60 in firstn_primes n).
Time Compute (let n := 60 in firstn_primes' n).

(*
Time Compute (firstn_primes 100).
Time Compute (firstn_primes' 100).
*)

...

(* Bertrand's postulate proven by Chebychev *)

Theorem prime_after_never_answers_0 : ∀ n, prime_after n ≠ 0.
Proof.
...

Theorem prime_after_is_prime : ∀ n, is_prime (prime_after n).
Proof.
...

Theorem no_primes_between_a_prime_and_the_following_one :
  ∀ p, is_prime p
  → ∀ q, p < q < prime_after p → is_prime q = false.
Proof.
...

Theorem ζ_Euler_product_eq : ...
