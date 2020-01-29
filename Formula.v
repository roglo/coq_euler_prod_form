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
      f_mul x (f_add y z) = f_add (f_mul x y) (f_mul x z) }.

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

Theorem f_mul_mul_swap {F : field} : ∀ x y z, (x * y * z = x * z * y)%F.
Proof.
intros.
do 2 rewrite <- f_mul_assoc.
apply f_equal, f_mul_comm.
Qed.

Theorem f_opp_involutive {F : field} : ∀ x, (- - x)%F = x.
Proof.
intros.
symmetry.
apply f_add_move_0_r.
apply f_add_opp_diag_r.
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
  transitivity ((0 * x + 1 * x)%F).
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

Theorem f_mul_1_r {F : field} : ∀ x, (x * 1)%F = x.
Proof.
intros.
rewrite f_mul_comm.
apply f_mul_1_l.
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
  {| ls n := match n with 1 => 1%F | _ => 0%F end |}.

(* Notation for accessing a series coefficient at index i *)

Notation "r ~{ i }" := (ls r i) (at level 1, format "r ~{ i }").

(* adding, opposing, subtracting polynomials *)

Definition lp_add {F : field} p q :=
  {| lp :=
       List.map (prod_curry f_add) (List_combine_all (lp p) (lp q) 0%F) |}.
Definition lp_opp {F : field} p := {| lp := List.map f_opp (lp p) |}.
Definition lp_sub {F : field} p q := lp_add p (lp_opp q).

Notation "x - y" := (lp_sub x y) : lp_scope.
Notation "1" := (ls_one) : ls_scope.

(* At last, the famous ζ function: all its coefficients are 1 *)

Definition ζ {F : field} := {| ls _ := 1%F |}.

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

Definition divisors n := List.filter (λ a, n mod a =? 0) (List.seq 1 n).

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
unfold divisors.
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
unfold divisors.
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

(* allows to rewrite H1, H2 with
      H1 : s1 = s3
      H2 : s2 = s4
   in expression
      (s1 * s2)%LS
   changing it into
      (s3 * s4)%LS *)
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

Theorem divisors_are_sorted : ∀ n, Sorted.Sorted lt (divisors n).
Proof.
intros.
unfold divisors.
specialize (SetoidList.filter_sort eq_equivalence Nat.lt_strorder) as H2.
specialize (H2 Nat.lt_wd).
specialize (H2 (λ a, n mod a =? 0) (seq 1 n)).
now specialize (H2 (Sorted_Sorted_seq _ _)).
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

(* Commutativity of product of series *)

Theorem fold_f_add_assoc {F : field} : ∀ a b l,
  fold_left f_add l (a + b)%F = (fold_left f_add l a + b)%F.
Proof.
intros.
revert a.
induction l as [| c l]; intros; [ easy | cbn ].
rewrite <- IHl; f_equal.
apply f_add_add_swap.
Qed.

Theorem fold_f_mul_assoc {F : field} : ∀ a b l,
  fold_left f_mul l (a * b)%F = (fold_left f_mul l a * b)%F.
Proof.
intros.
revert a.
induction l as [| c l]; intros; [ easy | cbn ].
rewrite <- IHl; f_equal.
apply f_mul_mul_swap.
Qed.

Theorem fold_log_prod_add_on_rev {F : field} : ∀ u v n l,
  n ≠ 0
  → (∀ d, d ∈ l → n mod d = 0 ∧ d ≠ 0)
  → fold_left f_add (map (log_prod_term u v n) l) f_zero =
     fold_left f_add (map (log_prod_term v u n) (rev (map (λ i, n / i) l)))
       f_zero.
Proof.
intros * Hn Hd.
induction l as [| a l]; intros; [ easy | cbn ].
rewrite f_add_0_l.
rewrite List.map_app.
rewrite List.fold_left_app; cbn.
specialize (Hd a (or_introl eq_refl)) as H1.
destruct H1 as (H1, H2).
rewrite <- IHl.
-unfold log_prod_term at 2 4.
 rewrite Nat_mod_0_div_div; [ | | easy ]; cycle 1. {
   split; [ flia H2 | ].
   apply Nat.mod_divides in H1; [ | easy ].
   destruct H1 as (c, Hc).
   destruct c; [ now rewrite Nat.mul_comm in Hc | ].
   rewrite Hc, Nat.mul_comm; cbn; flia.
 }
 rewrite (f_mul_comm (v (n / a))).
 now rewrite <- fold_f_add_assoc, f_add_0_l.
-intros d Hdl.
 now apply Hd; right.
Qed.

Theorem fold_log_prod_comm {F : field} : ∀ u v i,
  fold_left f_add (log_prod_list u v i) f_zero =
  fold_left f_add (log_prod_list v u i) f_zero.
Proof.
intros u v n.
unfold log_prod_list.
rewrite map_inv_divisors at 2.
remember (divisors n) as l eqn:Hl; symmetry in Hl.
destruct (zerop n) as [Hn| Hn]; [ now subst n; cbn in Hl; subst l | ].
apply Nat.neq_0_lt_0 in Hn.
specialize (in_divisors n Hn) as Hd; rewrite Hl in Hd.
now apply fold_log_prod_add_on_rev.
Qed.

Theorem ls_mul_comm {F : field} : ∀ x y,
  (x * y = y * x)%LS.
Proof.
intros * i Hi.
cbn - [ log_prod ].
apply fold_log_prod_comm.
Qed.

(* *)

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

(* The product of series is associative; first, lemmas *)

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

Definition xyz_zxy '((x, y, z) : (nat * nat * nat)) := (z, x, y).

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
now apply log_prod_assoc.
Qed.

Theorem ls_mul_mul_swap {F : field} : ∀ x y z,
  (x * y * z = x * z * y)%LS.
Proof.
intros.
rewrite ls_mul_comm.
rewrite (ls_mul_comm _ y).
rewrite ls_mul_assoc.
rewrite (ls_mul_comm _ x).
apply ls_mul_assoc.
Qed.

(* *)

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
replace ls_one~{1} with 1%F by easy.
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

Theorem ls_mul_1_r {F : field} : ∀ r, (r * 1 = r)%LS.
Proof.
intros.
now rewrite ls_mul_comm, ls_mul_1_l.
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
unfold divisors in Hl.
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

Theorem NoDup_divisors : ∀ n, NoDup (divisors n).
Proof.
intros.
specialize (divisors_are_sorted n) as Hs.
apply Sorted.Sorted_StronglySorted in Hs; [ | apply Nat.lt_strorder ].
remember (divisors n) as l eqn:Hl; clear Hl.
induction Hs; [ constructor | ].
constructor; [ | easy ].
intros Ha.
clear - H Ha.
specialize (proj1 (Forall_forall (lt a) l) H a Ha) as H1.
flia H1.
Qed.

(* Polynomial 1-1/n^s ≍ 1-x^ln(n) *)

Definition pol_pow {F : field} n :=
  {| lp := List.repeat 0%F (n - 1) ++ [1%F] |}.

(* *)

Notation "1" := (pol_pow 1) : lp_scope.

Theorem fold_ls_mul_assoc {F : field} {A} : ∀ l b c (f : A → _),
  (fold_left (λ c a, c * f a) l (b * c) =
   fold_left (λ c a, c * f a) l b * c)%LS.
Proof.
intros.
revert b c.
induction l as [| d l]; intros; [ easy | cbn ].
do 3 rewrite IHl.
apply ls_mul_mul_swap.
Qed.

Theorem eq_pol_1_sub_pow_0 {F : field} : ∀ m n d,
  d ∈ divisors n
  → d ≠ 1
  → d ≠ m
  → (ls_of_pol (pol_pow 1 - pol_pow m))~{d} = 0%F.
Proof.
intros * Hd Hd1 Hdm.
destruct (Nat.eq_dec n 0) as [Hn| Hn]; [ now subst n | ].
apply in_divisors in Hd; [ | easy ].
destruct Hd as (Hnd, Hd).
cbn.
destruct d; [ easy | ].
destruct m. {
  cbn; rewrite f_add_opp_diag_r.
  destruct d; [ easy | now destruct d ].
}
rewrite Nat_sub_succ_1.
apply -> Nat.succ_inj_wd_neg in Hdm.
destruct m. {
  destruct d; [ easy | now destruct d ].
}
destruct d; [ easy | cbn ].
destruct m. {
  destruct d; [ easy | now destruct d ].
}
cbn; rewrite f_opp_0, f_add_0_l.
destruct d; [ easy | ].
clear - Hdm.
do 2 apply -> Nat.succ_inj_wd_neg in Hdm.
revert d Hdm.
induction m; intros. {
  destruct d; [ easy | now destruct d ].
}
cbn; rewrite f_opp_0, f_add_0_l.
destruct d; [ easy | ].
apply -> Nat.succ_inj_wd_neg in Hdm.
now apply IHm.
Qed.

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
  replace ((ls_of_pol _)~{1}) with 1%F. 2: {
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
      replace ((ls_of_pol _)~{m}) with (- 1%F)%F. 2: {
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
      symmetry.
      assert (Hndm : nd ≠ m). {
        intros H; rewrite Hdnd, H, Nat.mul_comm in Hp.
        apply Nat.mul_cancel_l in Hp; [ easy | ].
        now intros H1; rewrite H, H1, Nat.mul_0_r in Hdnd.
      }
      assert (Hndd : nd ∈ divisors n). {
        specialize (divisor_inv n _ Hdn) as H1.
        rewrite Hdnd in H1 at 1.
        rewrite Nat.mul_comm, Nat.div_mul in H1; [ easy | ].
        now intros H; rewrite H in Hdnd.
      }
      now apply (eq_pol_1_sub_pow_0 _ n).
    }
    apply f_mul_0_r.
  }
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
  rewrite removelast_app; [ | easy ].
  rewrite map_app.
  rewrite fold_left_app.
  assert (H2 : ∀ a, fold_left f_add (map t l1) a = a). {
    assert (H2 : ∀ d, d ∈ l1 → t d = 0%F). {
      intros d Hd.
      assert (H2 : d ≠ n). {
        intros H2; move H2 at top; subst d.
        specialize (divisors_are_sorted n) as H2.
        rewrite H1 in H2.
        apply Sorted.Sorted_StronglySorted in H2. 2: {
          apply Nat.lt_strorder.
        }
        clear - Hd H2.
        induction l1 as [| a l1]; [ easy | ].
        destruct Hd as [Hd| Hd]. {
          subst a.
          cbn in H2.
          remember (l1 ++ p :: l2) as l eqn:Hl; symmetry in Hl.
          destruct l as [| a l]; [ now destruct l1 | ].
          remember (removelast (a :: l)) as l3 eqn:Hl3.
          clear - H2.
          cbn in H2.
          apply StronglySorted_inv in H2.
          destruct H2 as (_, H1).
          induction l3 as [| a l]. {
            cbn in H1.
            apply Forall_inv in H1; flia H1.
          }
          cbn in H1.
          apply Forall_inv_tail in H1.
          now apply IHl.
        }
        cbn in H2.
        remember (l1 ++ p :: l2) as l eqn:Hl; symmetry in Hl.
        destruct l as [| a1 l]; [ now destruct l1 | ].
        remember (removelast (a1 :: l)) as l3 eqn:Hl3.
        cbn in H2.
        apply StronglySorted_inv in H2.
        now apply IHl1.
      }
      apply Hto; [ | easy | ]. 2: {
        intros H; move H at top; subst d.
        specialize (divisors_are_sorted n) as H3.
        rewrite Hll in H3.
        clear - Hd H3.
        apply Sorted.Sorted_StronglySorted in H3. 2: {
          apply Nat.lt_strorder.
        }
        induction l1 as [| a l]; [ easy | ].
        cbn in H3.
        destruct Hd as [Hp| Hp]. {
          subst a.
          apply StronglySorted_inv in H3.
          destruct H3 as (_, H3).
          clear - H3.
          induction l as [| a l]. {
            cbn in H3; apply Forall_inv in H3; flia H3.
          }
          cbn in H3.
          apply Forall_inv_tail in H3.
          now apply IHl.
        }
        apply StronglySorted_inv in H3.
        now apply IHl.
      }
      rewrite Hll.
      now apply in_or_app; left.
    }
    intros a.
    clear - H2.
    induction l1 as [| b l]; [ easy | ].
    cbn; rewrite fold_f_add_assoc.
    rewrite H2; [ | now left ].
    rewrite f_add_0_r.
    apply IHl.
    intros d Hd.
    now apply H2; right.
  }
  rewrite <- fold_f_add_assoc.
  rewrite (f_add_comm _ (t n)), H2.
  rewrite f_add_0_r.
  destruct l2 as [| a l2]. {
    rewrite Hll in H1; cbn in H1.
    rewrite removelast_app in H1; [ | easy ].
    cbn in H1; cbn.
    rewrite app_nil_r in H1.
    apply app_inj_tail in H1.
    destruct H1 as (_, H1); move H1 at top; subst p.
    destruct m; [ flia Hm | ].
    destruct m; [ flia Hm | ].
    cbn in Hp; flia Hn Hp.
  }
  remember (a :: l2) as l; cbn; subst l.
  rewrite map_cons.
  cbn - [ removelast ].
  rewrite Htn, Htm.
  rewrite f_add_opp_diag_r.
  assert (H3 : ∀ d, d ∈ removelast (a :: l2) → t d = 0%F). {
    intros d Hd.
    apply Hto.
    -rewrite Hll.
     apply in_or_app; right; right.
     remember (a :: l2) as l.
     clear - Hd.
     (* lemma to do *)
     destruct l as [| a l]; [ easy | ].
     revert a Hd.
     induction l as [| b l]; intros; [ easy | ].
     destruct Hd as [Hd| Hd]; [ now subst d; left | ].
     now right; apply IHl.
    -intros H; move H at top; subst d.
     assert (Hnr : n ∈ removelast (l1 ++ p :: a :: l2)). {
       rewrite removelast_app; [ | easy ].
       apply in_or_app; right.
       remember (a :: l2) as l; cbn; subst l.
       now right.
     }
     remember (removelast (l1 ++ p :: a :: l2)) as l eqn:Hl.
     clear - H1 Hnr.
     specialize (NoDup_divisors n) as H2.
     rewrite H1 in H2; clear H1.
     induction l as [| a l]; [ easy | ].
     destruct Hnr as [Hnr| Hrn]. {
       subst a; cbn in H2.
       apply NoDup_cons_iff in H2.
       destruct H2 as (H, _); apply H.
       now apply in_or_app; right; left.
     }
     cbn in H2.
     apply NoDup_cons_iff in H2.
     now apply IHl.
    -intros H; move H at top; subst d.
     move Hpd at bottom.
     specialize (NoDup_divisors n) as Hnd.
     rewrite Hll in Hpd, Hnd.
     remember (a :: l2) as l3 eqn:Hl3.
     clear - Hpd Hd Hnd.
     assert (Hp : p ∈ l3). {
       clear - Hd.
       destruct l3 as [| a l]; [ easy | ].
       revert a Hd.
       induction l as [| b l]; intros; [ easy | ].
       remember (b :: l) as l1; cbn in Hd; subst l1.
       destruct Hd as [Hd| Hd]; [ now subst a; left | ].
       now right; apply IHl.
     }
     clear Hd.
     apply NoDup_remove_2 in Hnd; apply Hnd; clear Hnd.
     now apply in_or_app; right.
  }
  remember (removelast (a :: l2)) as l eqn:Hl.
  clear - H3.
  assert (Ha : ∀ a, fold_left f_add (map t l) a = a). {
    induction l as [| b l]; intros; [ easy | cbn ].
    rewrite fold_f_add_assoc.
    rewrite H3; [ | now left ].
    rewrite f_add_0_r; apply IHl.
    now intros d Hd; apply H3; right.
  }
  apply Ha.
}
assert (Hto : ∀ d, d ∈ divisors n → d ≠ n → t d = 0%F). {
  intros d Hd Hd1.
  rewrite Ht; unfold log_prod_term.
  replace ((ls_of_pol (pol_pow 1 - pol_pow m))~{n / d}) with 0%F. 2: {
    symmetry.
    assert (Hn1 : n / d ≠ 1). {
      intros H.
      apply in_divisors in Hd; [ | easy ].
      destruct Hd as (Hnd, Hd).
      apply Nat.mod_divides in Hnd; [ | easy ].
      destruct Hnd as (c, Hc).
      rewrite Hc, Nat.mul_comm, Nat.div_mul in H; [ | easy ].
      rewrite H, Nat.mul_1_r in Hc.
      now symmetry in Hc.
    }
    assert (Hdm : n / d ≠ m). {
      intros H; subst m.
      specialize (divisor_inv n d Hd) as Hnd.
      apply in_divisors in Hnd; [ | easy ].
      now rewrite Hp in Hnd.
    }
    apply divisor_inv in Hd.
    now apply (eq_pol_1_sub_pow_0 _ n).
  }
  apply f_mul_0_r.
}
assert (Hnd : n ∈ divisors n). {
  apply in_divisors_iff; [ easy | ].
  now rewrite Nat.mod_same.
}
specialize (NoDup_divisors n) as Hndd.
remember (divisors n) as l eqn:Hl; symmetry in Hl.
clear - Hnd Hto Htn Hndd.
induction l as [| a l]; [ easy | cbn ].
rewrite fold_f_add_assoc.
destruct Hnd as [Hnd| Hnd]. {
  subst a.
  replace (fold_left _ _ _) with 0%F. 2: {
    symmetry.
    clear - Hto Hndd.
    induction l as [| a l]; [ easy | cbn ].
    rewrite fold_f_add_assoc.
    apply NoDup_cons_iff in Hndd.
    rewrite Hto; [ | now right; left | ]. 2: {
      intros H; apply (proj1 Hndd); rewrite H.
      now left.
    }
    rewrite f_add_0_r.
    apply IHl. {
      intros d Hd Hdn.
      apply Hto; [ | easy ].
      destruct Hd as [Hd| Hd]; [ now left | now right; right ].
    }
    destruct Hndd as (Hna, Hndd).
    apply NoDup_cons_iff in Hndd.
    apply NoDup_cons_iff.
    split; [ | easy ].
    intros H; apply Hna.
    now right.
  }
  now rewrite Htn, f_add_0_l.
}
apply NoDup_cons_iff in Hndd.
rewrite Hto; [ | now left | now intros H; subst a ].
rewrite f_add_0_r.
apply IHl; [ | easy | easy ].
intros d Hd Hdn.
apply Hto; [ now right | easy ].
Qed.

(*
Here, we try to prove that
   ζ(s) (1 - 1/2^s) (1 - 1/3^s) (1 - 1/5^s) ... (1 - 1/p^s)
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

Notation "'Π' ( a ∈ l ) , p" :=
  (List.fold_left (λ c a, (c * ls_of_pol p%LP)%LS) l ls_one)
  (at level 36, a at level 0, l at level 60, p at level 36) : ls_scope.

Theorem list_of_pow_1_sub_pol_times_series {F : field} : ∀ l r,
  (∀ a, List.In a l → 2 ≤ a)
  → (∀ a, a ∈ l → ∀ i, i ≠ 0 → r~{i} = r~{a*i})
  → (∀ na nb, na ≠ nb → Nat.gcd (List.nth na l 1) (List.nth nb l 1) = 1)
  → (r * Π (a ∈ l), (pol_pow 1 - pol_pow a) =
     fold_right series_but_mul_of r l)%LS.
Proof.
intros * Hge2 Hai Hgcd.
induction l as [| a1 l]. {
  intros i Hi.
  cbn - [ ls_mul ].
  now rewrite ls_mul_1_r.
}
cbn.
rewrite fold_ls_mul_assoc.
rewrite ls_mul_assoc.
rewrite IHl; cycle 1. {
  now intros a Ha; apply Hge2; right.
} {
  intros a Ha i Hi; apply Hai; [ now right | easy ].
} {
  intros na nb Hnn.
  apply (Hgcd (S na) (S nb)).
  now intros H; apply Hnn; apply Nat.succ_inj in H.
}
apply series_times_pol_1_sub_pow; [ now apply Hge2; left | ].
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
  (∀ p, p ∈ l → prime p)
  → NoDup l
  → (ζ * Π (p ∈ l), (pol_pow 1 - pol_pow p) =
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

(* *)

Definition primes_upto n := filter is_prime (seq 1 n).

(*
Compute (primes_upto 17).
*)

Theorem primes_upto_are_primes : ∀ k p,
  p ∈ primes_upto k
  → prime p.
Proof.
intros * Hp.
now apply filter_In in Hp.
Qed.

Theorem NoDup_primes_upto : ∀ k, NoDup (primes_upto k).
Proof.
intros.
unfold primes_upto.
apply NoDup_filter.
apply seq_NoDup.
Qed.

Theorem gcd_primes_upto : ∀ k na nb,
  na ≠ nb
  → Nat.gcd (nth na (primes_upto k) 1) (nth nb (primes_upto k) 1) = 1.
Proof.
intros * Hnab.
remember (nth na (primes_upto k) 1) as pa eqn:Hpa.
remember (nth nb (primes_upto k) 1) as pb eqn:Hpb.
move pb before pa.
destruct (le_dec (length (primes_upto k)) na) as [Hka| Hka]. {
  rewrite Hpa, nth_overflow; [ | easy ].
  apply Nat.gcd_1_l.
}
destruct (le_dec (length (primes_upto k)) nb) as [Hkb| Hkb]. {
  rewrite Hpb, nth_overflow; [ | easy ].
  apply Nat.gcd_1_r.
}
apply Nat.nle_gt in Hka.
apply Nat.nle_gt in Hkb.
apply eq_primes_gcd_1. {
  apply (primes_upto_are_primes k).
  now rewrite Hpa; apply nth_In.
} {
  apply (primes_upto_are_primes k).
  now rewrite Hpb; apply nth_In.
}
intros H; apply Hnab; clear Hnab.
subst pa pb.
apply (proj1 (NoDup_nth (primes_upto k) 1)); [ | easy | easy | easy ].
apply NoDup_primes_upto.
Qed.

(* formula for all primes up to a given value *)

Theorem list_of_1_sub_pow_primes_upto_times {F : field} : ∀ r k,
  (∀ a, a ∈ primes_upto k → ∀ i, i ≠ 0 → r~{i} = r~{a*i})
  → (r * Π (p ∈ primes_upto k), (1 - pol_pow p) =
     fold_right series_but_mul_of r (primes_upto k))%LS.
Proof.
intros * Hri.
apply list_of_pow_1_sub_pol_times_series; [ | easy | ]. {
  intros p Hpl.
  apply primes_upto_are_primes in Hpl.
  destruct p; [ easy | ].
  destruct p; [ easy | flia ].
} {
  intros * Hnab.
  now apply gcd_primes_upto.
}
Qed.

Theorem series_but_mul_primes_upto {F : field} : ∀ n i r, 1 < i < n →
  (fold_right series_but_mul_of r (primes_upto n))~{i} = 0%F.
Proof.
intros * (H1i, Hin).
specialize (exist_prime_divisor i H1i) as H1.
destruct H1 as (d & Hd & Hdi).
assert (Hdn : d ∈ primes_upto n). {
  apply filter_In.
  split; [ | easy ].
  apply in_seq.
  assert (Hdz : d ≠ 0); [ now intros H; rewrite H in Hd | ].
  apply Nat.mod_divide in Hdi; [ | easy ].
  apply Nat.mod_divides in Hdi; [ | easy ].
  destruct Hdi as (c, Hc).
  split. {
    destruct d; [ rewrite Hc in H1i; cbn in H1i; flia H1i | flia ].
  }
  apply (le_lt_trans _ i); [ | flia Hin ].
  rewrite Hc.
  destruct c; [ rewrite Hc, Nat.mul_0_r in H1i; flia H1i | ].
  rewrite Nat.mul_succ_r; flia.
}
assert (Hdz : d ≠ 0); [ now intros H; rewrite H in Hd | ].
apply Nat.mod_divide in Hdi; [ | easy ].
apply Nat.mod_divides in Hdi; [ | easy ].
destruct Hdi as (c, Hc).
subst i.
remember (primes_upto n) as l.
clear n Hin Heql.
induction l as [| a l]; [ easy | ].
destruct Hdn as [Hdn| Hdn]. {
  subst a; cbn.
  now rewrite Nat.mul_comm, Nat.mod_mul.
}
cbn.
destruct ((d * c) mod a); [ easy | ].
now apply IHl.
Qed.

Theorem times_product_on_primes_close_to {F : field} : ∀ r s n,
  (∀ a, a ∈ primes_upto n → ∀ i, i ≠ 0 → r~{i} = r~{a*i})
  → s = (r * Π (p ∈ primes_upto n), (1 - pol_pow p))%LS
  → s~{1} = r~{1} ∧ ∀ i, 1 < i < n → s~{i} = 0%F.
Proof.
intros * Hrp Hs; subst s.
split. 2: {
  intros * (H1i, Hin).
  rewrite list_of_1_sub_pow_primes_upto_times; [ | easy | flia H1i ].
  now apply series_but_mul_primes_upto.
}
cbn.
rewrite f_add_0_l.
unfold log_prod_term.
rewrite Nat.div_1_r.
specialize (gcd_primes_upto n) as Hgcd.
assert (Hil : ∀ a, a ∈ primes_upto n → 2 ≤ a). {
  intros * Ha.
  apply filter_In in Ha.
  destruct a; [ easy | ].
  destruct a; [ easy | flia ].
}
remember (primes_upto n) as l eqn:Hl; symmetry in Hl.
replace ((Π (p ∈ l), (1 - pol_pow p))~{1})%F with 1%F. 2: {
  symmetry.
  clear Hl.
  induction l as [| p l]; [ easy | cbn ].
  rewrite fold_ls_mul_assoc; [ | easy ].
  cbn - [ ls_of_pol ].
  rewrite f_add_0_l.
  unfold log_prod_term.
  rewrite Nat.div_1_r.
  rewrite IHl; cycle 1. {
    intros a Ha i Hi.
    apply Hrp; [ now right | easy ].
  } {
    intros * Hnab.
    apply (Hgcd (S na) (S nb) (proj2 (Nat.succ_inj_wd_neg na nb) Hnab)).
  } {
    intros a Ha.
    now apply Hil; right.
  }
  rewrite f_mul_1_l.
  destruct p; cbn. {
    specialize (Hil 0 (or_introl eq_refl)).
    flia Hil.
  }
  rewrite Nat.sub_0_r.
  destruct p. {
    specialize (Hil 1 (or_introl eq_refl)).
    flia Hil.
  }
  cbn; clear.
  now destruct p; cbn; rewrite f_opp_0, f_add_0_r.
}
apply f_mul_1_r.
Qed.

Corollary ζ_times_product_on_primes_close_to_1 {F : field} : ∀ s n,
  s = (ζ * Π (p ∈ primes_upto n), (1 - pol_pow p))%LS
  → s~{1} = 1%F ∧ (∀ i, 1 < i < n → s~{i} = 0%F).
Proof.
intros * Hs.
replace 1%F with ζ~{1} by easy.
now apply times_product_on_primes_close_to.
Qed.

(*
Definition lim_tow_inf_eq {F : field} (f : nat → ln_series) (s : ln_series) :=
  ∀ i, i ≠ 0 → ∃ n, ∀ m, m > n → (f m)~{i} = s~{i}.

Notation "'lim' ( n '→' '∞' ) x = y" := (lim_tow_inf_eq (λ n, x%LS) y%LS)
  (at level 70, n at level 1, x at level 50).

Theorem lim_ζ_times_product_on_primes {F : field} :
  lim (n → ∞) ζ * Π (p ∈ primes_upto n), (1 - pol_pow p) = 1.
Proof.
intros i Hi.
exists i.
intros m Hmi.
specialize (ζ_times_product_on_primes_close_to_1 _ m (eq_refl _)) as H1.
destruct H1 as (H1, H2).
destruct (Nat.eq_dec i 1) as [H1i| H1i]; [ now subst i | ].
replace (1~{i}) with 0%F by now destruct i; [ | destruct i ].
apply H2.
split; [ | easy ].
destruct i; [ easy | ].
destruct i; [ easy | ].
apply -> Nat.succ_lt_mono.
apply Nat.lt_0_succ.
Qed.
*)

Definition limit_sequence_equal {A} (f : nat → nat → A) (v : nat → A) :=
  ∀ i, { n & ∀ m, n ≤ m → f m i = v i }.

Notation "'gen_lim' ( n → ∞ ) x = y" := (limit_sequence_equal (λ n, x) y)
  (at level 70, n at level 1, x at level 50).

Definition ls1 {F : field} s i := s~{i+1}.

Notation "'lim' ( n → ∞ ) x = y" :=
  (gen_lim (n → ∞) ls1 x%LS = ls1 y%LS)
  (at level 70, n at level 1, x at level 50).

Theorem lim_ζ_times_product_on_primes {F : field} :
  lim (n → ∞) ζ * Π (p ∈ primes_upto n), (1 - pol_pow p) = 1.
Proof.
intros i.
exists (i + 2).
intros m Hmi.
specialize (ζ_times_product_on_primes_close_to_1 _ m (eq_refl _)) as H1.
destruct H1 as (H1, H2).
unfold ls1.
destruct (Nat.eq_dec i 0) as [Hzi| Hzi]; [ now subst i | ].
replace (1~{i+1}) with 0%F by now destruct i; [ | destruct i ].
apply H2.
split; [ | flia Hmi ].
destruct i; [ easy | ].
rewrite Nat.add_1_r.
apply -> Nat.succ_lt_mono.
apply Nat.lt_0_succ.
Qed.

Check @lim_ζ_times_product_on_primes.

(*
Theorem ζ_Euler_product_eq : ...
*)

Require Import Totient QuadRes.

Theorem prime_φ : ∀ p, prime p → φ p = p - 1.
Proof.
intros * Hp.
unfold φ.
unfold coprimes.
rewrite (filter_ext_in _ (λ d, true)). 2: {
  intros a Ha.
  apply Nat.eqb_eq.
  apply in_seq in Ha.
  rewrite Nat.add_comm, Nat.sub_add in Ha. 2: {
    destruct p; [ easy | flia ].
  }
  now apply eq_gcd_prime_small_1.
}
clear Hp.
destruct p; [ easy | ].
rewrite Nat.sub_succ, Nat.sub_0_r.
induction p; [ easy | ].
rewrite <- (Nat.add_1_r p).
rewrite seq_app.
rewrite filter_app.
now rewrite app_length, IHp.
Qed.

Theorem prime_pow_φ : ∀ p, prime p →
  ∀ k, k ≠ 0 → φ (p ^ k) = p ^ (k - 1) * φ p.
Proof.
intros * Hp * Hk.
rewrite (prime_φ p); [ | easy ].
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ now subst p | ].
unfold φ.
unfold coprimes.
(**)
rewrite (filter_ext_in _ (λ d, negb (d mod p =? 0))). 2: {
  intros a Ha.
  apply in_seq in Ha.
  rewrite Nat.add_comm, Nat.sub_add in Ha. 2: {
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  remember (a mod p) as r eqn:Hr; symmetry in Hr.
  destruct r. {
    apply Nat.eqb_neq.
    apply Nat.mod_divides in Hr; [ | easy ].
    destruct Hr as (d, Hd).
    rewrite Hd.
    destruct k; [ easy | cbn ].
    rewrite Nat.gcd_mul_mono_l.
    intros H.
    apply Nat.eq_mul_1 in H.
    destruct H as (H, _).
    now subst p.
  } {
    apply Nat.eqb_eq.
    assert (Hg : Nat.gcd p a = 1). {
      rewrite <- Nat.gcd_mod; [ | easy ].
      rewrite Nat.gcd_comm.
      apply eq_gcd_prime_small_1; [ easy | ].
      split; [ rewrite Hr; flia | ].
      now apply Nat.mod_upper_bound.
    }
    clear - Hg.
    induction k; [ easy | ].
    now apply Nat_gcd_1_mul_l.
  }
}
clear Hp.
replace k with (k - 1 + 1) at 1 by flia Hk.
rewrite Nat.pow_add_r, Nat.pow_1_r.
remember (p ^ (k - 1)) as a eqn:Ha.
clear k Hk Ha Hpz.
induction a; [ easy | ].
cbn.
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]. {
  subst p; cbn.
  now rewrite Nat.mul_0_r.
}
destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
  subst a; cbn.
  do 2 rewrite Nat.add_0_r.
  rewrite (filter_ext_in _ (λ d, true)). 2: {
    intros a Ha.
    apply in_seq in Ha.
    rewrite Nat.mod_small; [ | flia Ha ].
    destruct a; [ flia Ha | easy ].
  }
  clear.
  destruct p; [ easy | ].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  induction p; [ easy | ].
  rewrite <- (Nat.add_1_r p).
  rewrite seq_app, filter_app, app_length.
  now rewrite IHp.
}
rewrite <- Nat.add_sub_assoc. 2: {
  apply Nat.neq_0_lt_0.
  now apply Nat.neq_mul_0.
}
rewrite Nat.add_comm.
rewrite seq_app, filter_app, app_length.
rewrite IHa, Nat.add_comm; f_equal.
rewrite Nat.add_comm, Nat.sub_add. 2: {
  apply Nat.neq_0_lt_0.
  now apply Nat.neq_mul_0.
}
replace p with (1 + (p - 1)) at 2 by flia Hpz.
rewrite seq_app, filter_app, app_length.
cbn.
rewrite Nat.mod_mul; [ | easy ]; cbn.
rewrite (filter_ext_in _ (λ d, true)). 2: {
  intros b Hb.
  remember (b mod p) as c eqn:Hc; symmetry in Hc.
  destruct c; [ | easy ].
  apply Nat.mod_divide in Hc; [ | easy ].
  destruct Hc as (c, Hc).
  subst b.
  apply in_seq in Hb.
  destruct Hb as (Hb1, Hb2).
  clear - Hb1 Hb2; exfalso.
  revert p a Hb1 Hb2.
  induction c; intros; [ flia Hb1 | ].
  cbn in Hb1, Hb2.
  destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
    subst a.
    cbn in Hb1, Hb2.
    destruct p; [ flia Hb1 | ].
    rewrite Nat.sub_succ, Nat.sub_0_r in Hb2.
    flia Hb2.
  }
  destruct (Nat.eq_dec p 0) as [Hpz| Hpz]. {
    subst p; flia Hb1.
  }
  specialize (IHc p (a - 1)) as H1.
  assert (H : (a - 1) * p + 1 ≤ c * p). {
    rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
    rewrite <- Nat.add_sub_swap. 2: {
      destruct a; [ easy | ].
      cbn; flia.
    }
    flia Hb1 Haz Hpz.
  }
  specialize (H1 H); clear H.
  apply H1.
  apply (Nat.add_lt_mono_l _ _ p).
  eapply lt_le_trans; [ apply Hb2 | ].
  ring_simplify.
  do 2 apply Nat.add_le_mono_r.
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
  rewrite Nat.sub_add. 2: {
    destruct a; [ easy | rewrite Nat.mul_succ_r; flia ].
  }
  now rewrite Nat.mul_comm.
}
clear.
remember (a * p + 1) as b; clear a Heqb.
destruct p; [ easy | ].
rewrite Nat.sub_succ, Nat.sub_0_r.
revert b.
induction p; intros; [ easy | ].
rewrite <- Nat.add_1_r.
rewrite seq_app, filter_app, app_length.
now rewrite IHp.
Qed.

Theorem divide_add_div_le : ∀ m p q,
  2 ≤ p
  → 2 ≤ q
  → Nat.divide p m
  → Nat.divide q m
  → m / p + m / q ≤ m.
Proof.
intros * H2p H2q Hpm Hqm.
destruct Hpm as (kp, Hkp).
destruct Hqm as (kq, Hkq).
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ flia Hpz H2p | ].
destruct (Nat.eq_dec q 0) as [Hqz| Hqz]; [ flia Hqz H2q | ].
rewrite Hkq at 2.
rewrite Nat.div_mul; [ | easy ].
rewrite Hkp at 1.
rewrite Nat.div_mul; [ | easy ].
apply (Nat.mul_le_mono_pos_r _ _ (p * q)). {
  destruct p; [ easy | ].
  destruct q; [ easy | cbn; flia ].
}
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_assoc, <- Hkp.
rewrite Nat.mul_assoc, Nat.mul_shuffle0, <- Hkq.
rewrite <- Nat.mul_add_distr_l.
apply Nat.mul_le_mono_l.
rewrite Nat.add_comm.
apply Nat.add_le_mul. {
  destruct p; [ easy | ].
  destruct p; [ easy | flia ].
} {
  destruct q; [ easy | ].
  destruct q; [ easy | flia ].
}
Qed.

Theorem length_filter_mod_seq : ∀ a b,
  a mod b ≠ 0
  → length (filter (λ d, negb (d mod b =? 0)) (seq a b)) = b - 1.
Proof.
intros a b Hab1.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
specialize (Nat.div_mod a b Hbz) as H1.
remember (a / b) as q eqn:Hq.
remember (a mod b) as r eqn:Hr.
move q after r; move Hq after Hr.
replace b with (b - r + r) at 1. 2: {
  apply Nat.sub_add.
  now rewrite Hr; apply Nat.lt_le_incl, Nat.mod_upper_bound.
}
rewrite seq_app, filter_app, app_length.
rewrite List_filter_all_true. 2: {
  intros c Hc.
  apply Bool.negb_true_iff, Nat.eqb_neq.
  apply in_seq in Hc.
  intros Hcon.
  specialize (Nat.div_mod c b Hbz) as H2.
  rewrite Hcon, Nat.add_0_r in H2.
  remember (c / b) as s eqn:Hs.
  subst a c.
  clear Hcon.
  destruct Hc as (Hc1, Hc2).
  rewrite Nat.add_sub_assoc in Hc2. 2: {
    rewrite Hr.
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Nat.add_sub_swap in Hc2; [ | flia ].
  rewrite Nat.add_sub in Hc2.
  replace b with (b * 1) in Hc2 at 3 by flia.
  rewrite <- Nat.mul_add_distr_l in Hc2.
  apply Nat.mul_lt_mono_pos_l in Hc2; [ | flia Hbz ].
  rewrite Nat.add_1_r in Hc2.
  apply Nat.succ_le_mono in Hc2.
  apply Nat.nlt_ge in Hc1.
  apply Hc1; clear Hc1.
  apply (le_lt_trans _ (b * q)); [ | flia Hab1 ].
  now apply Nat.mul_le_mono_l.
}
rewrite seq_length.
replace r with (1 + (r - 1)) at 3 by flia Hab1.
rewrite seq_app, filter_app, app_length; cbn.
rewrite H1 at 1.
rewrite Nat.add_sub_assoc. 2: {
  rewrite Hr.
  now apply Nat.lt_le_incl, Nat.mod_upper_bound.
}
rewrite Nat.add_sub_swap; [ | flia ].
rewrite Nat.add_sub.
rewrite Nat_mod_add_l_mul_l; [ | easy ].
rewrite Nat.mod_same; [ cbn | easy ].
rewrite List_filter_all_true. 2: {
  intros c Hc.
  apply Bool.negb_true_iff, Nat.eqb_neq.
  apply in_seq in Hc.
  intros Hcon.
  specialize (Nat.div_mod c b Hbz) as H2.
  rewrite Hcon, Nat.add_0_r in H2.
  remember (c / b) as s eqn:Hs.
  subst a c.
  clear Hcon.
  destruct Hc as (Hc1, Hc2).
  rewrite Nat.add_sub_assoc in Hc2. 2: {
    rewrite Hr.
    rewrite Nat_mod_add_l_mul_l; [ | easy ].
    rewrite Nat.mod_small; [ flia Hab1 | ].
    rewrite Hr.
    now apply Nat.mod_upper_bound.
  }
  rewrite Nat.add_sub_swap in Hc2; [ | flia ].
  rewrite Nat.add_sub in Hc2.
  rewrite Nat.add_sub_assoc in Hc2. 2: {
    rewrite Hr.
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Nat.sub_add in Hc2; [ | flia ].
  rewrite Nat.add_sub_assoc in Hc1. 2: {
    rewrite Hr.
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Nat.add_sub_swap in Hc1; [ | flia ].
  rewrite Nat.add_sub in Hc1.
  rewrite Nat.add_shuffle0 in Hc2.
  apply Nat.nlt_ge in Hc1; apply Hc1; clear Hc1.
  rewrite Nat.add_1_r.
  apply -> Nat.succ_le_mono.
  replace b with (b * 1) at 3 by flia.
  rewrite <- Nat.mul_add_distr_l.
  apply Nat.mul_le_mono_l.
  replace b with (b * 1) in Hc2 at 3 by flia.
  rewrite <- Nat.mul_add_distr_l in Hc2.
  apply Nat.nlt_ge; intros Hc1.
  replace s with ((q + 1) + S (s - (q + 2))) in Hc2 by flia Hc1.
  rewrite Nat.mul_add_distr_l in Hc2.
  apply Nat.add_lt_mono_l in Hc2.
  apply Nat.nle_gt in Hc2; apply Hc2; clear Hc2.
  rewrite Nat.mul_comm; cbn.
  transitivity b; [ | flia Hc1 ].
  rewrite Hr.
  now apply Nat.lt_le_incl, Nat.mod_upper_bound.
}
rewrite seq_length.
rewrite Nat.add_sub_assoc; [ | flia Hab1 ].
rewrite Nat.sub_add; [ easy | ].
rewrite Hr.
now apply Nat.lt_le_incl, Nat.mod_upper_bound.
Qed.

Theorem gcd_1_div_mul_exact : ∀ m p q kp kq,
  q ≠ 0
  → Nat.gcd p q = 1
  → m = kp * p
  → m = kq * q
  → kp = q * (kp / q).
Proof.
intros * Hqz Hg Hkp Hkq.
rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
  apply (Nat.gauss _ p). {
    rewrite Nat.mul_comm, <- Hkp, Hkq.
    now exists kq.
  } {
    now rewrite Nat.gcd_comm.
  }
}
now rewrite Nat.mul_comm, Nat.div_mul.
Qed.

Theorem Nat_gcd_1_mul_divide : ∀ m p q,
  Nat.gcd p q = 1
  → Nat.divide p m
  → Nat.divide q m
  → Nat.divide (p * q) m.
Proof.
intros * Hg Hpm Hqm.
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
  subst m; cbn.
  now exists 0.
}
assert (Hpz : p ≠ 0). {
  destruct Hpm as (k, Hk).
  now intros H; rewrite H, Nat.mul_0_r in Hk.
}
assert (Hqz : q ≠ 0). {
  destruct Hqm as (k, Hk).
  now intros H; rewrite H, Nat.mul_0_r in Hk.
}
destruct Hpm as (kp, Hkp).
destruct Hqm as (kq, Hkq).
exists (kp * kq / m).
rewrite Nat.mul_comm.
rewrite Hkp at 2.
rewrite Nat.div_mul_cancel_l; [ | easy | ]. 2: {
  intros H; subst kp.
  rewrite Hkp in Hkq; cbn in Hkq.
  symmetry in Hkq.
  apply Nat.eq_mul_0 in Hkq.
  destruct Hkq as [H| H]; [ | now subst q ].
  now subst kq.
}
rewrite (Nat.mul_comm p), <- Nat.mul_assoc.
rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
  exists (kq / p).
  rewrite Nat.mul_comm.
  rewrite Nat.gcd_comm in Hg.
  now apply (gcd_1_div_mul_exact m q p kq kp).
}
rewrite (Nat.mul_comm p).
rewrite Nat.div_mul; [ | easy ].
now rewrite Nat.mul_comm.
Qed.

Definition prime_divisors n :=
  filter (λ d, (is_prime d && (n mod d =? 0))%bool) (seq 1 n).

Theorem prime_divisors_decomp : ∀ n a,
  a ∈ prime_divisors n ↔ a ∈ prime_decomp n.
Proof.
intros.
split; intros Ha. {
  apply filter_In in Ha.
  destruct Ha as (Ha, H).
  apply Bool.andb_true_iff in H.
  destruct H as (Hpa, Hna).
  apply Nat.eqb_eq in Hna.
  apply in_seq in Ha.
  apply Nat.mod_divide in Hna; [ | flia Ha ].
  apply prime_decomp_in_iff.
  split; [ | split ]; [ flia Ha | easy | easy ].
} {
  apply filter_In.
  apply prime_decomp_in_iff in Ha.
  destruct Ha as (Hnz & Ha & Han).
  split. {
    apply in_seq.
    split. {
      transitivity 2; [ flia | ].
      now apply prime_ge_2.
    } {
      destruct Han as (k, Hk); subst n.
      destruct k; [ easy | flia ].
    }
  }
  apply Bool.andb_true_iff.
  split; [ easy | ].
  apply Nat.eqb_eq.
  apply Nat.mod_divide in Han; [ easy | ].
  now intros H1; subst a.
}
Qed.

Theorem prime_divisors_nil_iff: ∀ n, prime_divisors n = [] ↔ n = 0 ∨ n = 1.
Proof.
intros.
split; intros Hn. {
  apply prime_decomp_nil_iff.
  remember (prime_decomp n) as l eqn:Hl; symmetry in Hl.
  destruct l as [| a l]; [ easy | ].
  specialize (proj2 (prime_divisors_decomp n a)) as H1.
  rewrite Hl, Hn in H1.
  now exfalso; apply H1; left.
} {
  now destruct Hn; subst n.
}
Qed.

(* primitive roots *)

Fixpoint prim_root_cycle_loop n g gr it :=
  match it with
  | 0 => []
  | S it' =>
      let gr' := (g * gr) mod n in
      if gr' =? g then [gr]
      else gr :: prim_root_cycle_loop n g gr' it'
  end.

Definition prim_root_cycle n g := prim_root_cycle_loop n g g (n - 1).

Definition is_prim_root n g := length (prim_root_cycle n g) =? n - 1.

Definition prim_roots n := filter (is_prim_root n) (seq 1 (n - 1)).

Fixpoint in_list_nat n l :=
  match l with
  | [] => false
  | a :: l => if n =? a then true else in_list_nat n l
  end.

Definition is_quad_res p n := in_list_nat n (quad_res p).

(* Euler's theorem *)

Theorem different_coprimes_all_different_multiples : ∀ n a,
  a ∈ coprimes n
  → ∀ i j,
  i ∈ coprimes n
  → j ∈ coprimes n
  → i ≠ j
  → (i * a) mod n ≠ (j * a) mod n.
Proof.
(* like smaller_than_prime_all_different_multiples but more general *)
intros * Ha * Hi Hj Hij.
intros Haa; symmetry in Haa.
apply in_coprimes_iff in Ha.
apply in_coprimes_iff in Hi.
apply in_coprimes_iff in Hj.
destruct Ha as (Ha, Hna).
destruct Hi as (Hi, Hni).
destruct Hj as (Hj, Hnj).
assert
  (H : ∀ i j, i ∈ seq 1 (n - 1) → j ∈ seq 1 (n - 1) → i < j →
   (j * a) mod n ≠ (i * a) mod n). {
  clear i j Hi Hj Hni Hnj Hij Haa.
  intros * Hi Hj Hilj Haa.
  apply in_seq in Hi.
  apply in_seq in Hj.
  apply Nat_mul_mod_cancel_r in Haa; [ | now rewrite Nat.gcd_comm ].
  rewrite Nat.mod_small in Haa; [ | flia Hj ].
  rewrite Nat.mod_small in Haa; [ | flia Hi ].
  flia Hilj Haa.
}
destruct (lt_dec i j) as [Hilj| Hjli]. {
  now revert Haa; apply H.
} {
  symmetry in Haa.
  assert (Hilj : j < i) by flia Hij Hjli.
  now revert Haa; apply H.
}
Qed.

Theorem coprimes_mul_in_coprimes : ∀ n i j,
  i ∈ coprimes n → j ∈ coprimes n → (i * j) mod n ∈ coprimes n.
Proof.
intros * Hi Hj.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
apply in_coprimes_iff in Hi.
apply in_coprimes_iff in Hj.
destruct Hi as (Hi, Hgi).
destruct Hj as (Hj, Hgj).
apply in_seq in Hi.
apply in_seq in Hj.
apply in_coprimes_iff.
split. {
  apply in_seq.
  split. {
    remember ((i * j) mod n) as a eqn:Ha; symmetry in Ha.
    destruct a; [ | flia ].
    apply Nat.mod_divide in Ha; [ | easy ].
    apply Nat.gauss in Ha; [ | easy ].
    destruct Ha as (k, Hk).
    replace n with (1 * n) in Hgj by flia.
    subst j.
    rewrite Nat.gcd_mul_mono_r in Hgj.
    apply Nat.eq_mul_1 in Hgj.
    destruct Hgj as (H1k, Hn); subst n.
    flia Hi.
  } {
    rewrite Nat.add_comm, Nat.sub_add; [ | flia Hnz ].
    now apply Nat.mod_upper_bound.
  }
} {
  rewrite Nat.gcd_comm, Nat.gcd_mod; [ | easy ].
  now apply Nat_gcd_1_mul_r.
}
Qed.

Theorem NoDup_coprimes : ∀ n, NoDup (coprimes n).
Proof.
intros.
unfold coprimes.
apply NoDup_filter, seq_NoDup.
Qed.

Theorem fold_φ : ∀ n, length (coprimes n) = φ n.
Proof. easy. Qed.

Theorem gcd_prod_coprimes : ∀ n,
  Nat.gcd n (fold_left Nat.mul (coprimes n) 1) = 1.
Proof.
intros.
assert (H : ∀ a, a ∈ coprimes n → Nat.gcd n a = 1). {
  intros * H.
  now apply in_coprimes_iff in H.
}
remember (coprimes n) as l eqn:Hl; symmetry in Hl; clear Hl.
induction l as [| a l]; intros; [ apply Nat.gcd_1_r | ].
cbn; rewrite Nat.add_0_r.
rewrite fold_left_mul_from_1.
apply Nat_gcd_1_mul_r; [ now apply H; left | ].
apply IHl.
intros b Hb.
now apply H; right.
Qed.

Theorem euler_fermat_little : ∀ n a,
  n ≠ 0 → a ≠ 0 → Nat.gcd a n = 1 → a ^ φ n ≡ 1 mod n.
Proof.
intros * Hnz Haz Hg.
(* https://wstein.org/edu/2007/spring/ent/ent-html/node19.html#sec:flittle *)
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]; [ now subst n | ].
assert (Ha : a mod n ∈ coprimes n). {
  apply in_coprimes_iff.
  rewrite Nat.gcd_comm, Nat.gcd_mod; [ | easy ].
  rewrite Nat.gcd_comm.
  split; [ | easy ].
  apply in_seq.
  rewrite Nat.add_comm, Nat.sub_add; [ | flia Hnz ].
  split. {
    remember (a mod n) as b eqn:Hb; symmetry in Hb.
    destruct b; [ | flia ].
    apply Nat.mod_divides in Hb; [ | easy ].
    replace n with (n * 1) in Hg by flia.
    destruct Hb as (k, Hk); subst a.
    rewrite Nat.gcd_mul_mono_l in Hg.
    now apply Nat.eq_mul_1 in Hg.
  } {
    now apply Nat.mod_upper_bound.
  }
}
rewrite <- Nat_mod_pow_mod.
assert
  (H1 : ∀ i j, i ∈ coprimes n → j ∈ coprimes n
   → i ≠ j → (i * a) mod n ≠ (j * a) mod n). {
  intros * Hi Hj Hij.
  rewrite <- (Nat.mul_mod_idemp_r i); [ | easy ].
  rewrite <- (Nat.mul_mod_idemp_r j); [ | easy ].
  now apply different_coprimes_all_different_multiples.
}
assert (Hcc : ∀ i, i ∈ coprimes n → (i * a) mod n ∈ coprimes n). {
  intros i Hi.
  rewrite <- Nat.mul_mod_idemp_r; [ | easy ].
  now apply coprimes_mul_in_coprimes.
}
assert
  (Hperm :
     Permutation (map (λ i, (i * a) mod n) (coprimes n)) (coprimes n)). {
  apply NoDup_Permutation_bis; [ | apply NoDup_coprimes | | ]; cycle 1. {
    now rewrite map_length.
  } {
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    rewrite <- Hji.
    rewrite <- Nat.mul_mod_idemp_r; [ | easy ].
    now apply coprimes_mul_in_coprimes.
  } {
    apply NoDup_map_iff with (d := 0).
    intros * Hi Hj Hnth.
    destruct (Nat.eq_dec i j) as [Heij| Heij]; [ easy | exfalso ].
    revert Hnth.
    apply H1; [ now apply nth_In | now apply nth_In | ].
    specialize (NoDup_coprimes n) as H2.
    remember (coprimes n) as l.
    clear - Hi Hj Heij H2.
    revert i j Hi Hj Heij.
    induction l as [| a l]; intros; [ easy | ].
    apply NoDup_cons_iff in H2.
    destruct H2 as (Ha, Hnd).
    intros H; cbn in H.
    destruct i. {
      destruct j; [ easy | ].
      subst a; apply Ha.
      cbn in Hj.
      apply Nat.succ_lt_mono in Hj.
      now apply nth_In.
    }
    destruct j. {
      subst a; apply Ha.
      cbn in Hi.
      apply Nat.succ_lt_mono in Hi.
      now apply nth_In.
    }
    cbn in Hi, Hj.
    apply Nat.succ_lt_mono in Hi.
    apply Nat.succ_lt_mono in Hj.
    apply -> Nat.succ_inj_wd_neg in Heij.
    revert H.
    now apply IHl.
  }
}
remember (λ i : nat, (i * a) mod n) as f eqn:Hf.
remember (fold_left Nat.mul (map f (coprimes n)) 1) as x eqn:Hx.
remember (fold_left Nat.mul (coprimes n) 1) as y eqn:Hy.
assert (Hx1 : x mod n = y mod n). {
  subst x y.
  erewrite Permutation_fold_mul; [ easy | apply Hperm ].
}
assert (Hx2 : x mod n = (y * a ^ φ n) mod n). {
  subst x y; rewrite Hf.
  rewrite <- (map_map (λ i, i * a) (λ j, j mod n)).
  rewrite fold_left_mul_map_mod.
  now rewrite fold_left_mul_map_mul.
}
rewrite Hx2 in Hx1.
(**)
replace y with (y * 1) in Hx1 at 2 by flia.
apply Nat_mul_mod_cancel_l in Hx1. 2: {
  rewrite Hy, Nat.gcd_comm.
  apply gcd_prod_coprimes.
}
now rewrite Nat_mod_pow_mod.
Qed.

(* where can I put this theorem above? not in Primes.v since Prime does
   not know Totient; not in Totient.v since Totient does not know Primes.
   In a third .v file, perhaps? In that file, I could also all fermat's
   little theorem as a corollary. *)

Corollary fermat_little_again : ∀ p,
  prime p → ∀ a, 1 ≤ a < p → a ^ (p - 1) mod p = 1.
Proof.
intros * Hp * Hap.
rewrite <- prime_φ; [ | easy ].
replace 1 with (1 mod p). 2: {
  apply Nat.mod_1_l.
  now apply prime_ge_2.
}
apply euler_fermat_little; [ now intros H; subst p | flia Hap | ].
rewrite Nat.gcd_comm.
now apply eq_gcd_prime_small_1.
Qed.

(* proof of corollary above simpler than fermat_little, isn't it? *)

About prime_φ. (* ← to include in that .v file I was talking about above *)

Theorem φ_interv : ∀ n, 2 ≤ n → 1 ≤ φ n < n.
Proof.
intros * H2n.
unfold φ.
unfold coprimes.
split. {
  destruct n; [ easy | ].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  destruct n; [ flia H2n | ].
  remember (S (S n)) as ssn.
  cbn; rewrite Nat.gcd_1_r; cbn; flia.
} {
  rewrite List_length_filter_negb; [ | apply seq_NoDup ].
  rewrite seq_length.
  flia H2n.
}
Qed.

(* multiplicative order modulo *)

Fixpoint ord_mod_aux it n a i :=
  match it with
  | 0 => 0
  | S it' =>
      if Nat.eq_dec (Nat_pow_mod a i n) 1 then i
      else ord_mod_aux it' n a (i + 1)
  end.

Definition ord_mod n a := ord_mod_aux n n a 1.

Theorem List_seq_eq_nil : ∀ a b, seq a b = [] → b = 0.
Proof.
intros * Hs.
now destruct b.
Qed.

Lemma ord_mod_aux_prop : ∀ it n a i,
  n + 1 ≤ it + i
  → (∀ j, 1 ≤ j < i → (a ^ j) mod n ≠ 1)
  → 2 ≤ n
  → Nat.gcd a n = 1
  → a ^ ord_mod_aux it n a i mod n = 1 ∧
     ∀ m, 0 < m < ord_mod_aux it n a i → (a ^ m) mod n ≠ 1.
Proof.
intros * Hnit Hj H2n Hg.
assert (Hnz : n ≠ 0) by flia H2n.
destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
  subst a.
  rewrite Nat.gcd_0_l in Hg; flia H2n Hg.
}
revert i Hnit Hj.
induction it; intros. {
  cbn; cbn in Hnit.
  specialize (euler_fermat_little n a Hnz Haz Hg) as H1.
  rewrite (Nat.mod_small 1) in H1; [ | easy ].
  specialize (Hj (φ n)) as H2.
  assert (H : 1 ≤ φ n < i). {
    specialize (φ_interv n H2n) as H3.
    split; [ easy | ].
    transitivity n; [ easy | flia Hnit ].
  }
  now specialize (H2 H).
}
cbn.
rewrite Nat_pow_mod_is_pow_mod; [ | easy ].
destruct (Nat.eq_dec (a ^ i mod n) 1) as [Ha1| Ha1]. {
  split; [ easy | ].
  intros m Hm.
  now apply Hj.
}
apply IHit; [ flia Hnit | ].
intros k Hk.
destruct (Nat.eq_dec k i) as [Hki| Hki]; [ now subst k | ].
apply Hj; flia Hk Hki.
Qed.

Theorem ord_mod_prop : ∀ n a,
  2 ≤ n
  → Nat.gcd a n = 1
  → (a ^ ord_mod n a) mod n = 1 ∧
     ∀ m, 0 < m < ord_mod n a → (a ^ m) mod n ≠ 1.
Proof.
intros * H2n Hg.
apply ord_mod_aux_prop; [ easy | | easy | easy ].
intros j Hj.
flia Hj.
Qed.

Theorem ord_mod_1_r : ∀ n, 2 ≤ n → ord_mod n 1 = 1.
Proof.
intros * H2n.
destruct n; [ easy | ].
cbn - [ Nat_pow_mod ].
rewrite Nat_pow_mod_is_pow_mod; [ | easy ].
rewrite Nat.pow_1_r.
rewrite Nat.mod_1_l; [ easy | flia H2n ].
Qed.

Lemma eq_ord_mod_aux_0 : ∀ it n a i,
  n ≠ 0
  → i ≠ 0
  → ord_mod_aux it n a i = 0
  → ∀ j, i ≤ j < i + it → a ^ j mod n ≠ 1.
Proof.
intros * Hnz Hiz Ho * Hj.
revert i Hiz Ho Hj.
induction it; intros; [ flia Hj | ].
cbn in Ho.
rewrite Nat_pow_mod_is_pow_mod in Ho; [ | easy ].
destruct (Nat.eq_dec (a ^ i mod n) 1) as [Hai| Hai]; [ easy | ].
destruct (Nat.eq_dec i j) as [Hij| Hij]; [ now subst i | ].
apply (IHit (i + 1)); [ flia | easy | ].
split; [ flia Hj Hij | flia Hj ].
Qed.

Theorem ord_mod_neq_0 : ∀ n a, 2 ≤ n → Nat.gcd a n = 1 → ord_mod n a ≠ 0.
Proof.
intros * H2n Hg Ho.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
  subst a.
  rewrite Nat.gcd_0_l in Hg.
  flia Hg H2n.
}
unfold ord_mod in Ho.
specialize (eq_ord_mod_aux_0 n n a 1 Hnz (Nat.neq_succ_0 _) Ho) as H1.
specialize (euler_fermat_little n a Hnz Haz Hg) as H2.
rewrite (Nat.mod_small 1) in H2; [ | easy ].
revert H2; apply H1.
specialize (φ_interv n H2n) as H2.
flia H2.
Qed.

Theorem ord_mod_divisor : ∀ n a b,
  Nat.gcd a n = 1
  → a ^ b mod n = 1
  → Nat.divide (ord_mod n a) b.
Proof.
intros * Hg Habn.
destruct (lt_dec n 2) as [H2n| H2n]. {
  destruct n; [ easy | ].
  destruct n; [ easy | flia H2n ].
}
apply Nat.nlt_ge in H2n.
specialize (ord_mod_prop n a H2n Hg) as H1.
destruct H1 as (Han, Ham).
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  now subst b; exists 0.
}
destruct (lt_dec b (ord_mod n a)) as [Hbo| Hbo]. {
  apply Nat.neq_0_lt_0 in Hbz.
  now specialize (Ham b (conj Hbz Hbo)) as H1.
}
apply Nat.nlt_ge in Hbo.
destruct (Nat.eq_dec (ord_mod n a) 0) as [Hoz| Hoz]. {
  now apply ord_mod_neq_0 in Hoz.
}
specialize (Nat.div_mod b (ord_mod n a) Hoz) as H1.
destruct (Nat.eq_dec (b mod ord_mod n a) 0) as [Hmz| Hmz]. {
  rewrite Hmz, Nat.add_0_r in H1.
  exists (b / ord_mod n a).
  now rewrite Nat.mul_comm.
}
exfalso; apply Hmz; clear Hmz.
assert (H2 : a ^ (b mod ord_mod n a) ≡ 1 mod n). {
  rewrite H1 in Habn.
  rewrite Nat.pow_add_r in Habn.
  rewrite Nat.pow_mul_r in Habn.
  rewrite <- Nat.mul_mod_idemp_l in Habn; [ | flia H2n ].
  rewrite <- Nat_mod_pow_mod in Habn.
  rewrite Han in Habn.
  rewrite Nat.pow_1_l in Habn.
  rewrite Nat.mod_1_l in Habn; [ | easy ].
  rewrite Nat.mul_1_l in Habn.
  now rewrite <- (Nat.mod_1_l n) in Habn.
}
rewrite Nat.mod_1_l in H2; [ | easy ].
specialize (Ham (b mod ord_mod n a)) as H3.
remember (ord_mod n a) as x eqn:Hx.
remember (b mod x) as r eqn:Hr.
destruct (Nat.eq_dec r 0) as [Hrz| Hzr]; [ easy | exfalso ].
assert (H : 0 < r < x). {
  split; [ flia Hzr | ].
  rewrite Hr.
  now apply Nat.mod_upper_bound.
}
now specialize (H3 H).
Qed.

(* https://wstein.org/edu/2007/spring/ent/ent-html/node29.html *)

Theorem ord_mod_mul_divide : ∀ n a b r s,
  Nat.gcd a n = 1
  → Nat.gcd b n = 1
  → Nat.gcd r s = 1
  → ord_mod n a = r
  → ord_mod n b = s
  → Nat.divide (ord_mod n (a * b)) (r * s).
Proof.
intros * Han Hbn Hg Hoa Hob.
destruct (lt_dec n 2) as [H2n| H2n]. {
  destruct n. {
    cbn in Hoa, Hob; cbn.
    now subst r s.
  }
  destruct n; [ | flia H2n ].
  cbn in Hoa, Hob.
  now subst r s.
}
apply Nat.nlt_ge in H2n.
destruct (lt_dec a 2) as [H2a| H2a]. {
  destruct a. {
    rewrite Nat.gcd_0_l in Han; flia Han H2n.
  }
  destruct a; [ | flia H2a ].
  rewrite ord_mod_1_r in Hoa; [ | easy ].
  subst r.
  do 2 rewrite Nat.mul_1_l.
  now rewrite Hob.
}
apply Nat.nlt_ge in H2a.
destruct (lt_dec b 2) as [H2b| H2b]. {
  destruct b. {
    rewrite Nat.gcd_0_l in Hbn; flia Hbn H2n.
  }
  destruct b; [ | flia H2b ].
  rewrite ord_mod_1_r in Hob; [ | easy ].
  subst s.
  do 2 rewrite Nat.mul_1_r.
  now rewrite Hoa.
}
apply Nat.nlt_ge in H2b.
assert (H2 : (a * b) ^ (r * s) = a ^ (r * s) * b ^ (r * s)). {
  apply Nat.pow_mul_l.
}
specialize (ord_mod_prop n a H2n Han) as Har.
rewrite Hoa in Har.
destruct Har as (Har, Harn).
specialize (ord_mod_prop n b H2n Hbn) as Hbs.
rewrite Hob in Hbs.
destruct Hbs as (Hbs, Hbsn).
apply (f_equal (λ x, x mod n)) in H2.
rewrite (Nat.pow_mul_r a) in H2.
rewrite (Nat.mul_comm r s) in H2.
rewrite (Nat.pow_mul_r b) in H2.
rewrite Nat.mul_mod in H2; [ | flia H2n ].
rewrite <- (Nat_mod_pow_mod (a ^ r)) in H2.
rewrite <- (Nat_mod_pow_mod (b ^ s)) in H2.
rewrite Har, Hbs in H2.
do 2 rewrite Nat.pow_1_l in H2.
rewrite (Nat.mod_small 1) in H2; [ | easy ].
rewrite Nat.mul_1_l in H2.
rewrite (Nat.mod_small 1) in H2; [ | easy ].
rewrite (Nat.mul_comm s r) in H2.
move H2 at bottom.
apply ord_mod_divisor; [ | easy ].
now apply Nat_gcd_1_mul_l.
Qed.

Theorem order_multiplicative : ∀ n a b r s,
  Nat.gcd a n = 1
  → Nat.gcd b n = 1
  → ord_mod n a = r
  → ord_mod n b = s
  → Nat.gcd r s = 1
  → ord_mod n (a * b) = r * s.
Proof.
intros * Han Hbn Hoa Hob Hg.
destruct (lt_dec n 2) as [H2n| H2n]. {
  destruct n. {
    cbn in Hoa; cbn.
    now subst r.
  }
  destruct n; [ | flia H2n ].
  cbn in Hoa; cbn.
  now subst r.
}
apply Nat.nlt_ge in H2n.
specialize (ord_mod_mul_divide n a b r s Han Hbn Hg Hoa Hob) as H1.
(* https://wstein.org/edu/2007/spring/ent/ent-html/node29.html *)
remember (ord_mod n (a * b)) as d eqn:Hd.
specialize (Nat.divide_mul_split d r s) as H2.
assert (Habn : Nat.gcd (a * b) n = 1) by now apply Nat_gcd_1_mul_l.
assert (H : d ≠ 0). {
  rewrite Hd.
  now apply ord_mod_neq_0.
}
specialize (H2 H H1); clear H.
destruct H2 as (r1 & s1 & Hrs & Hr & Hs).
specialize (ord_mod_prop n a H2n Han) as (Hao & Ham).
rewrite Hoa in Hao, Ham.
specialize (ord_mod_prop n b H2n Hbn) as (Hbo & Hbm).
rewrite Hob in Hbo, Hbm.
specialize (ord_mod_prop n (a * b) H2n Habn) as (Habo & Habm).
rewrite <- Hd in Habo, Habm.
rewrite Hrs in Habo.
assert (Hrr : r1 = r). {
  apply (f_equal (λ x, x ^ (s / s1))) in Habo.
  rewrite Nat.pow_1_l in Habo.
  apply (f_equal (λ x, x mod n)) in Habo.
  rewrite Nat_mod_pow_mod in Habo.
  rewrite Nat.mod_1_l in Habo; [ | easy ].
  rewrite <- Nat.pow_mul_r in Habo.
  rewrite <- Nat.mul_assoc in Habo.
  assert (Hs1z : s1 ≠ 0). {
    intros H; subst s1.
    destruct Hs as (k, Hk).
    rewrite Nat.mul_0_r in Hk.
    rewrite Hk in Hob.
    now apply ord_mod_neq_0 in Hob.
  }
  rewrite <- Nat.divide_div_mul_exact in Habo; [ | easy | easy ].
  rewrite (Nat.mul_comm s1), Nat.div_mul in Habo; [ | easy ].
  rewrite (Nat.mul_comm r1) in Habo.
  rewrite Nat.pow_mul_r in Habo.
  rewrite Nat.pow_mul_l in Habo.
  rewrite <- Nat_mod_pow_mod in Habo.
  rewrite <- Nat.mul_mod_idemp_r in Habo; [ | flia H2n ].
  rewrite Hbo, Nat.mul_1_r in Habo.
  rewrite Nat_mod_pow_mod in Habo.
  rewrite <- Nat.pow_mul_r in Habo.
  assert (H2 : Nat.divide r (s * r1)). {
    rewrite <- Hoa.
    now apply ord_mod_divisor.
  }
  apply Nat.gauss in H2; [ | easy ].
  move Hr at bottom.
  now apply Nat.divide_antisym.
}
assert (Hss : s1 = s). {
  clear Hrr.
  apply (f_equal (λ x, x ^ (r / r1))) in Habo.
  rewrite Nat.pow_1_l in Habo.
  apply (f_equal (λ x, x mod n)) in Habo.
  rewrite Nat_mod_pow_mod in Habo.
  rewrite Nat.mod_1_l in Habo; [ | easy ].
  rewrite <- Nat.pow_mul_r in Habo.
  rewrite Nat.mul_shuffle0 in Habo.
  assert (Hr1z : r1 ≠ 0). {
    intros H; subst r1.
    destruct Hr as (k, Hk).
    rewrite Nat.mul_0_r in Hk.
    rewrite Hk in Hoa.
    now apply ord_mod_neq_0 in Hoa.
  }
  rewrite <- Nat.divide_div_mul_exact in Habo; [ | easy | easy ].
  rewrite (Nat.mul_comm r1), Nat.div_mul in Habo; [ | easy ].
  rewrite Nat.pow_mul_r in Habo.
  rewrite Nat.pow_mul_l in Habo.
  rewrite <- Nat_mod_pow_mod in Habo.
  rewrite <- Nat.mul_mod_idemp_l in Habo; [ | flia H2n ].
  rewrite Hao, Nat.mul_1_l in Habo.
  rewrite Nat_mod_pow_mod in Habo.
  rewrite <- Nat.pow_mul_r in Habo.
  assert (H2 : Nat.divide s (r * s1)). {
    rewrite <- Hob.
    now apply ord_mod_divisor.
  }
  apply Nat.gauss in H2; [ | now rewrite Nat.gcd_comm ].
  move Hs at bottom.
  now apply Nat.divide_antisym.
}
now subst r1 s1.
Qed.

Fixpoint list_with_occ l :=
  match l with
  | [] => []
  | x :: l' =>
      match list_with_occ l' with
      | [] => [(x, 1)]
      | (y, c) :: l' =>
          if Nat.eq_dec x y then (x, c + 1) :: l'
          else (x, 1) :: (y, c) :: l'
      end
  end.

Definition prime_decomp_pow p := list_with_occ (prime_decomp p).

(* roots of equation x^n ≡ 1 mod p *)
Definition roots_pow_sub_1_mod n p :=
  filter (λ x, Nat_pow_mod x n p =? 1) (seq 1 (p - 1)).

Compute (let '(n, p) := (2, 13) in roots_pow_sub_1_mod n p).
Compute (let '(n, p) := (4, 13) in roots_pow_sub_1_mod n p).
Compute (let '(n, p) := (3, 13) in roots_pow_sub_1_mod n p).

Theorem Couteau : ∀ a b n, Nat.gcd a n = 1 → a ^ (b mod φ n) ≡ a ^ b mod n.
Proof.
intros * Hg.
destruct (lt_dec n 2) as [H2n| H2n]. {
  destruct n; [ easy | ].
  destruct n; [ easy | flia H2n ].
}
apply Nat.nlt_ge in H2n.
destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
  subst a; cbn in Hg; flia Hg H2n.
}
specialize (Nat.div_mod b (φ n)) as H1.
assert (H : φ n ≠ 0). {
  specialize (φ_interv n H2n) as H2.
  flia H2.
}
specialize (H1 H); clear H.
apply (f_equal (λ x, a ^ x mod n)) in H1.
rewrite Nat.pow_add_r in H1.
rewrite Nat.pow_mul_r in H1.
rewrite <- Nat.mul_mod_idemp_l in H1; [ | flia H2n ].
rewrite <- (Nat_mod_pow_mod (a ^ φ n)) in H1.
rewrite euler_fermat_little in H1; [ | flia H2n | easy | easy ].
rewrite Nat.mod_1_l in H1; [ | easy ].
rewrite Nat.pow_1_l in H1.
rewrite Nat.mod_1_l in H1; [ | easy ].
now rewrite Nat.mul_1_l in H1.
Qed.

(*
Theorem root_bound : ∀ f n a sta len,
  f = (λ n a x, Σ (i = 0, n), a i * x ^ i)
  → a n ≠ 0
  → length (filter (λ x, f n a x =? 0) (seq sta len)) ≤ n.
Proof.
intros * Hf Han.
revert a sta len Han.
induction n; intros. {
  rewrite List_filter_all_false; [ easy | ].
  intros x Hx.
  apply Nat.eqb_neq.
  rewrite Hf; cbn.
  now rewrite Nat.mul_1_r.
}
(* https://wstein.org/edu/2007/spring/ent/ent-html/node28.html#prop:atmost *)
remember (length (filter (λ x, f (S n) a x =? 0) (seq sta len))) as m eqn:Hm.
symmetry in Hm.
destruct m; [ flia | ].
assert (H : ∃ α, f (S n) a α = 0). {
  clear - Hm.
  revert sta m Hm.
  induction len; intros; [ easy | ].
  cbn in Hm.
  remember (f (S n) a sta) as f1 eqn:Hf1; symmetry in Hf1.
  destruct f1; [ now exists sta | ].
  cbn in Hm.
  apply (IHlen (S sta) m).
  apply Hm.
}
destruct H as (α, Hα).
apply -> Nat.succ_le_mono.
assert (H1 : ∀ x, f (S n) a x = f (S n) a x - f (S n) a α). {
  intros x.
  now rewrite Hα, Nat.sub_0_r.
}
assert (H2 : ∀ x, f (S n) a x = Σ (i = 0, S n), a i * x ^ i - Σ (i = 0, S n), a i * α ^ i). {
  intros.
  specialize (H1 x).
  rewrite Hf in H1.
  now rewrite Hf.
}
clear H1; rename H2 into H1.
assert
  (H2 : ∀ x, α ≤ x → f (S n) a x = Σ (i = 1, S n), a i * (x ^ i - α ^ i)). {
  intros * Hαx.
  specialize (H1 x).
  rewrite <- summation_sub in H1. 2: {
    intros i Hi.
    apply Nat.mul_le_mono_l.
    now apply Nat.pow_le_mono_l.
  }
  rewrite H1.
  rewrite summation_split_first; [ | flia ].
  do 2 rewrite Nat.pow_0_r.
  rewrite Nat.sub_diag, Nat.add_0_l.
  apply summation_eq_compat.
  intros i Hi.
  symmetry; apply Nat.mul_sub_distr_l.
}
assert
  (H3 : ∀ x,
   α ≤ x →
   f (S n) a x =
     (x - α) *
     Σ (i = 0, n), a (i + 1) * Σ (j = 0, i), x ^ (i - j) * α ^ j). {
  intros x Hx.
  rewrite mul_summation_distr_l.
  rewrite H2; [ | easy ].
  rewrite summation_shift.
  apply summation_eq_compat.
  intros i Hi.
  replace (S i) with (i + 1) by flia.
  rewrite (Nat.mul_comm (x - α)).
  rewrite <- Nat.mul_assoc; f_equal.
  rewrite Nat_pow_sub_pow; [ | flia Hi | easy ].
  rewrite Nat.add_sub.
  rewrite Nat.mul_comm; f_equal.
  cbn.
  rewrite Nat.sub_0_r, Nat.add_sub, Nat.mul_1_r.
  rewrite (Nat.add_comm i 1).
  rewrite seq_app.
  rewrite fold_left_app.
  cbn - [ "-" ].
  rewrite Nat.sub_0_r, Nat.mul_1_r.
  clear.
  remember (seq 1 i) as l; remember (x ^ i) as a.
  clear.
  revert a; induction l as [| b l]; intros; [ easy | ].
  cbn - [ "-" ].
  rewrite IHl; f_equal; f_equal; f_equal; f_equal.
  flia.
}
(* mouais... cette hypothèse α ≤ x craint. En fait, faudrait
   bosser dans ℤ ; c'est chiant parce que, jusqu'ici, ℕ me
   suffisait ; déjà que j'essaie d'éviter d'entrer dans les
   considérations des polynômes (supposant d'y mettre toute
   la machinerie...) *)
...
*)

Theorem glop : ∀ p d,
  prime p
  → Nat.divide d (p - 1)
  → length (roots_pow_sub_1_mod d p) = d.
Proof.
intros * Hp Hdp.
destruct Hdp as (e, He).
unfold roots_pow_sub_1_mod.
rewrite (filter_ext _ (λ x, x ^ d mod p =? 1)). 2: {
  intros x.
  rewrite Nat_pow_mod_is_pow_mod; [ easy | ].
  now intros H; subst p.
}
assert (Hp1 :
  length (filter (λ x, x ^ (p - 1) mod p =? 1) (seq 1 (p - 1))) = p - 1). {
  rewrite List_filter_all_true; [ apply seq_length | ].
  intros a Ha.
  apply in_seq in Ha.
  apply Nat.eqb_eq.
  apply fermat_little; [ easy | flia Ha ].
}
(* https://wstein.org/edu/2007/spring/ent/ent-html/node28.html#prop:dsols *)
destruct (lt_dec e 2) as [H2e| H2e]. {
  destruct e. {
    specialize (prime_ge_2 p Hp) as H.
    flia He H.
  }
  destruct e; [ | flia H2e ].
  now rewrite Nat.mul_1_l in He; rewrite <- He.
}
apply Nat.nlt_ge in H2e.
set (g x := Σ (i = 1, e), x ^ (d * (e - i))).
assert (Hd : ∀ x, x ^ (p - 1) - 1 = (x ^ d - 1) * g x). {
  intros.
  destruct (Nat.eq_dec x 0) as [Hxz| Hxz]. {
    subst x.
    rewrite Nat.pow_0_l. 2: {
      specialize (prime_ge_2 _ Hp) as H1.
      flia H1.
    }
    rewrite Nat.pow_0_l; [ easy | ].
    intros H; subst d.
    rewrite Nat.mul_0_r in He.
    specialize (prime_ge_2 _ Hp) as H1.
    flia He H1.
  }
  unfold g.
  rewrite He, Nat.mul_comm.
  rewrite Nat.pow_mul_r.
  replace 1 with (1 ^ e) at 1 2 by apply Nat.pow_1_l.
  rewrite Nat_pow_sub_pow; [ | flia H2e | ]. 2: {
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  rewrite Nat.pow_1_l.
  f_equal.
  replace e with (S (e - 1)) at 2 by flia H2e.
  rewrite summation_shift.
  apply summation_eq_compat.
  intros i Hi.
  rewrite Nat.pow_1_l, Nat.mul_1_r.
  rewrite <- Nat.pow_mul_r.
  f_equal; flia.
}
(* generalization on Euler's theorem? *)
Compute (φ 4).
Compute (roots_pow_sub_1_mod 2 4).
Compute (φ 6).
Compute (roots_pow_sub_1_mod 2 6).
Compute (roots_pow_sub_1_mod 1 6).
Compute (φ 8).
Compute (roots_pow_sub_1_mod 4 8).
Compute (roots_pow_sub_1_mod 2 8). (* no: 4 *)
Compute (φ 9).
Compute (roots_pow_sub_1_mod 6 9).
Compute (roots_pow_sub_1_mod 3 9).
Compute (roots_pow_sub_1_mod 2 9).
Compute (φ 10).
Compute (roots_pow_sub_1_mod 4 10).
Compute (roots_pow_sub_1_mod 2 10).
Compute (φ 12).
Compute (roots_pow_sub_1_mod 4 12).
Compute (roots_pow_sub_1_mod 2 12). (* no: 4 *)
Compute (φ 14).
Compute (roots_pow_sub_1_mod 6 14).
Compute (roots_pow_sub_1_mod 3 14).
Compute (roots_pow_sub_1_mod 2 14).
Compute (φ 15).
Compute (roots_pow_sub_1_mod 8 15).
Compute (roots_pow_sub_1_mod 4 15). (* no: 8 *)
Compute (roots_pow_sub_1_mod 2 15). (* no: 4 *)
Compute (φ 16).
Compute (roots_pow_sub_1_mod 8 16).
Compute (roots_pow_sub_1_mod 4 16). (* no: 8 *)
Compute (roots_pow_sub_1_mod 2 16). (* no: 4 *)
Compute (φ 18).
Compute (roots_pow_sub_1_mod 6 18).
Compute (roots_pow_sub_1_mod 3 18).
Compute (roots_pow_sub_1_mod 2 18).
Compute (φ 20).
Compute (roots_pow_sub_1_mod 8 20).
Compute (roots_pow_sub_1_mod 4 20). (* no: 8 *)
Compute (roots_pow_sub_1_mod 2 20). (* no: 4 *)
Compute (φ 21).
Compute (roots_pow_sub_1_mod 12 21).
Compute (roots_pow_sub_1_mod 6 21). (* no: 12 *)
Compute (roots_pow_sub_1_mod 4 21).
Compute (roots_pow_sub_1_mod 3 21).
Compute (roots_pow_sub_1_mod 2 21). (* no: 4 *)
Compute (roots_pow_sub_1_mod 1 21).
Compute (φ 22).
Compute (roots_pow_sub_1_mod 10 22).
Compute (roots_pow_sub_1_mod 5 22).
Compute (roots_pow_sub_1_mod 2 22).
Compute (φ 24).
Compute (roots_pow_sub_1_mod 8 24).
Compute (roots_pow_sub_1_mod 4 24). (* no: 8 *)
Compute (roots_pow_sub_1_mod 2 24). (* no: 8; four times! *)
Compute (φ 25).
Compute (length (roots_pow_sub_1_mod 20 25)).
Compute (length (roots_pow_sub_1_mod 10 25)).
Compute (length (roots_pow_sub_1_mod 5 25)).
Compute (length (roots_pow_sub_1_mod 4 25)).
Compute (length (roots_pow_sub_1_mod 2 25)).
Compute (φ 26).
Compute (length (roots_pow_sub_1_mod 12 26)).
Compute (length (roots_pow_sub_1_mod 6 26)).
Compute (length (roots_pow_sub_1_mod 4 26)).
Compute (length (roots_pow_sub_1_mod 3 26)).
Compute (length (roots_pow_sub_1_mod 2 26)).
Compute (φ 27).
Compute (length (roots_pow_sub_1_mod 18 27)).
Compute (length (roots_pow_sub_1_mod 9 27)).
Compute (length (roots_pow_sub_1_mod 6 27)).
Compute (length (roots_pow_sub_1_mod 3 27)).
Compute (length (roots_pow_sub_1_mod 2 27)).
Compute (φ 28).
Compute (length (roots_pow_sub_1_mod 12 28)).
Compute (length (roots_pow_sub_1_mod 6 28)). (* no: 12 *)
Compute (length (roots_pow_sub_1_mod 4 28)).
Compute (length (roots_pow_sub_1_mod 3 28)).
Compute (length (roots_pow_sub_1_mod 2 28)). (* no: 4 *)
Compute (φ 30).
Compute (roots_pow_sub_1_mod 8 30).
Compute (roots_pow_sub_1_mod 4 30). (* no: 8 *)
Compute (roots_pow_sub_1_mod 2 30). (* no: 4 *)
Compute (roots_pow_sub_1_mod 1 30).
Compute (let n := 28 in map (λ d, (d, length (roots_pow_sub_1_mod d n)))(divisors (φ n))).
Compute (let n := 30 in map (λ d, (d, length (roots_pow_sub_1_mod d n)))(divisors (φ n))).
Compute (let n := 39 in map (λ d, (d, length (roots_pow_sub_1_mod d n)))(divisors (φ n))).
...
assert (Hx : length (filter (λ x, x ^ d mod p =? 1) (seq 1 (p - 1))) ≤ d). {
...
Check root_bound.
... before root_bound: to be removed:
  rewrite He.
  destruct (Nat.eq_dec d 0) as [Hdz| Hdz]. {
    subst d; cbn.
    rewrite List_filter_all_true. 2: {
      intros a Ha.
      apply Nat.eqb_eq.
      now apply Nat.mod_small, prime_ge_2.
    }
    now rewrite Nat.mul_0_r.
  }
  assert (Hep : e ≤ p - 1). {
    rewrite He.
    destruct d; [ easy | flia ].
  }
  clear - Hp Hdz Hep.
  revert e Hep.
  induction d; intros; [ easy | clear Hdz ].
  rewrite Nat.mul_succ_r.
  cbn.
  destruct d. {
    rewrite Nat.mul_0_r, Nat.add_0_l.
    destruct (Nat.eq_dec e 0) as [Hez| Hez]. {
      subst e; cbn; flia.
    }
    replace e with (1 + (e - 1)) by flia Hez.
    rewrite seq_app; cbn.
    rewrite Nat.mod_1_l; [ | now apply prime_ge_2 ].
    cbn.
    rewrite List_filter_all_false; [ cbn; flia | ].
    intros a Ha.
    rewrite Nat.mul_1_r.
    apply Nat.eqb_neq.
    apply in_seq in Ha.
    rewrite Nat.mod_small; [ flia Ha | flia Ha Hep ].
  }
...
assert (Hg : length (filter (λ x, g x =? 0) (seq 1 (p - 1))) ≤ d * (e - 1)). {
...

Definition prim_roots' p :=
  let l := prime_decomp_pow (p - 1) in
  let l'' :=
    map
      (λ '(d, q),
       let l1 := roots_pow_sub_1_mod (d ^ q) p in
       let l2 := roots_pow_sub_1_mod (d ^ (q - 1)) p in
       fold_left (λ l x2, remove Nat.eq_dec x2 l) l2 l1)
    l
  in
  fold_left (λ l1 l2, map (λ '(x, y), x * y mod p) (list_prod l1 l2))
     l'' [1].

Compute (let p := 31 in (sort Nat.leb (prim_roots' p), (prim_roots p))).
Compute (let p := 31 in combine (sort Nat.leb (prim_roots' p)) (prim_roots p)).

Theorem eq_list_with_occ_nil : ∀ l, list_with_occ l = [] → l = [].
Proof.
intros * Hl.
destruct l as [| a l]; [ easy | exfalso ].
cbn in Hl.
destruct (list_with_occ l); [ easy | ].
destruct p.
now destruct (Nat.eq_dec a n).
Qed.

Lemma map_mul_1_l_mod : ∀ p l,
  (∀ x, x ∈ l → x < p)
  → map (λ x, (1 * x) mod p) l = l.
Proof.
intros * Hlt.
induction l as [| a l]; [ easy | ].
cbn - [ Nat.mul ].
rewrite Nat.mul_1_l.
f_equal. {
  apply Nat.mod_small.
  now apply Hlt; left.
}
apply IHl.
intros x Hx.
now apply Hlt; right.
Qed.

Theorem List_in_remove {A} : ∀ eq_dec x y (l : list A),
  y ∈ remove eq_dec x l → y ∈ l.
Proof.
intros * Hy.
induction l as [| z l]; [ easy | ].
cbn in Hy; cbn.
destruct (eq_dec x z) as [Hxz| Hxz]. {
  now right; subst z; apply IHl.
} {
  destruct Hy as [Hy| Hy]; [ now left | ].
  now right; apply IHl.
}
Qed.

Theorem prim_roots'_are_prim_roots :
  ∀ p a, a ∈ prim_roots' p ↔
  (∀ i, 1 ≤ i ≤ p - 1 → ∃ j, a ^ j ≡ i mod p).
Proof.
intros.
split. {
  intros Hap * Hip.
  unfold prim_roots' in Hap.
  remember (prime_decomp_pow (p - 1)) as l eqn:Hl; symmetry in Hl.
  remember
    (fold_left (λ l1 l2, map (λ '(x, y), (x * y) mod p) (list_prod l1 l2))
       (map
          (λ '(d, q),
           fold_left (λ (l : list nat) (x2 : nat), remove Nat.eq_dec x2 l)
           (roots_pow_sub_1_mod (d ^ (q - 1)) p)
           (roots_pow_sub_1_mod (d ^ q) p)) l)) as f eqn:Hf.
...
  induction l as [| x l]. {
    cbn in Hap.
    destruct Hap as [Hap| Hap]; [ | easy ].
    unfold prime_decomp_pow in Hl.
    apply eq_list_with_occ_nil in Hl.
    apply prime_decomp_nil_iff in Hl.
    destruct Hl as [Hp| Hp]; [ flia Hp Hip | ].
    replace i with 1 by flia Hp Hip; subst a.
    exists 1.
    now rewrite Nat.pow_1_r.
  }
  cbn in Hap.
  rewrite app_nil_r in Hap.
  destruct x as (d, q).
  rewrite (map_map _ (λ '(x, y), (x * y) mod p)) in Hap.
  rewrite map_mul_1_l_mod in Hap. 2: {
    intros x Hx.
    remember (roots_pow_sub_1_mod (d ^ q) p) as l1 eqn:Hl1.
    remember (roots_pow_sub_1_mod (d ^ (q - 1)) p) as l2 eqn:Hl2.
    assert (H : ∀ x, x ∈ l1 → x < p). {
      intros y Hy.
      rewrite Hl1 in Hy.
      unfold roots_pow_sub_1_mod in Hy.
      apply filter_In in Hy.
      destruct Hy as (Hy, _).
      apply in_seq in Hy.
      flia Hy.
    }
    clear - Hx H.
    revert l1 Hx H.
    induction l2 as [| a l2]; intros; cbn in Hx; [ now apply H | ].
    eapply IHl2; [ apply Hx | ].
    intros y Hy.
    apply List_in_remove in Hy.
    apply H, Hy.
  }
  apply IHl; [ ... | ].
  clear IHl.
...

Theorem glop : ∀ p, prime p → ∃ a, is_prim_root p a = true.
Proof.
intros * Hp.
unfold is_prim_root.
enough (H : ∃ a, length (prim_root_cycle p a) = p - 1). {
  destruct H as (a, H); exists a.
  now apply Nat.eqb_eq in H.
}
remember (prime_divisors (p - 1)) as pd eqn:Hpd.
(* https://wstein.org/edu/2007/spring/ent/ent-html/node29.html *)
Compute (prim_roots 13, quad_res 13).
Compute (map (prim_root_cycle 13) [1; 5; 8; 12]).
Compute (map (prim_root_cycle 13) [1; 3; 9]).
Compute (map (λ x, x mod 13) [15; 45; 24; 72]).
Compute (map (prim_root_cycle 13) [2; 6; 11; 7]).
Compute (prime_decomp 12).
About prime_decomp.
...

Theorem glop : ∀ p, prime p → ∃ a, a ^ ((p - 1) / 2) mod p = p - 1.
Proof.
intros * Hp.
destruct (Nat.eq_dec p 2) as [Hp2| Hp2]; [ now exists 1; subst p | ].
assert (H2p : 2 ≤ p) by now apply prime_ge_2.
assert (H3p : 3 ≤ p) by flia Hp2 H2p.
clear Hp2 H2p.
...
remember (prime_divisors (p - 1)) as pd eqn:Hpd.
(* https://wstein.org/edu/2007/spring/ent/ent-html/node29.html *)
...
(* a must be a quadratic nonresidue of p *)
(* https://en.wikipedia.org/wiki/Euler%27s_criterion *)
...
intros * Hp.
destruct (Nat.eq_dec p 2) as [Hp2| Hp2]; [ now exists 1; subst p | ].
assert (H2p : 2 ≤ p) by now apply prime_ge_2.
assert (H3p : 3 ≤ p) by flia Hp2 H2p.
clear Hp2 H2p.
specialize (pow_prime_sub_1_div_2 p Hp) as H1.
apply (not_forall_in_interv_imp_exist 1 (p - 1)); [ | flia H3p | ]. {
  intros; apply Nat.eq_decidable.
}
intros H2.
assert (Hap1 : ∀ a, 1 ≤ a ≤ p - 1 → a ^ ((p - 1) / 2) mod p = 1). {
  intros a Ha.
  specialize (H2 a Ha).
  assert (H : 1 ≤ a < p) by flia Ha.
  now destruct (H1 a H).
}
clear H1 H2.
Compute (let p := 3 in map (λ n, Nat_pow_mod n ((p - 1)/2) p) (seq 1 (p - 1))).
...
specialize (not_all_div_2_mod_add_1_eq_1 (p - 1)) as H1.
assert (H : 2 ≤ p - 1) by flia H3p.
specialize (H1 H); clear H.
rewrite Nat.sub_add in H1; [ easy | flia H3p ].
Qed.
