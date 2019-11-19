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
  (∀ p, p ∈ l → is_prime p = true)
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
  → is_prime p = true.
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
specialize (prime_divisor i H1i) as H1.
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

Check @ζ_times_product_on_primes_close_to_1.

(* below to be moved to Primes.v when working *)

Theorem lt_prime_sqr_not_1 : ∀ p,
  is_prime p = true → ∀ a, 2 ≤ a ≤ p - 2 → a ^ 2 mod p ≠ 1.
Proof.
intros * Hp * Hap Ha.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
replace 1 with (1 mod p) in Ha at 2. 2: {
  apply Nat.mod_1_l; flia Hap.
}
apply Nat_eq_mod_sub_0 in Ha. 2: {
  destruct a; [ easy | ].
  cbn; apply -> Nat.succ_le_mono.
  apply Nat.le_0_l.
}
rewrite Nat_sqr_sub_1 in Ha.
apply Nat.mod_divide in Ha; [ | easy ].
specialize (Nat.gauss _ _ _ Ha) as H1.
assert (H : Nat.gcd p (a + 1) = 1). {
  apply eq_gcd_prime_small_1; [ easy | flia Hap ].
}
specialize (H1 H); clear H.
destruct H1 as (c, Hc).
destruct c; [ flia Hc Hap | ].
cbn in Hc; flia Hc Hap.
Qed.

Theorem lt_prime_pow_sub_2_not_1 : ∀ p,
  is_prime p = true → ∀ a : nat, 2 ≤ a ≤ p - 2 → a ^ (p - 2) mod p ≠ 1.
Proof.
intros * Hp * Hap Ha.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
replace 1 with (1 mod p) in Ha at 2. 2: {
  apply Nat.mod_1_l; flia Hap.
}
apply Nat_eq_mod_sub_0 in Ha. 2: {
  apply Nat.neq_0_lt_0.
  apply Nat.pow_nonzero; flia Hap.
}
specialize (fermat_little p Hp a) as H1.
assert (H : 1 ≤ a < p) by flia Hap.
specialize (H1 H); clear H.
replace (p - 1) with (S (p - 2)) in H1 by flia Hap.
cbn in H1.
rewrite <- (Nat.sub_add 1 (a ^ (p - 2))) in H1 at 1. 2: {
  apply Nat.neq_0_lt_0.
  apply Nat.pow_nonzero; flia Hap.
}
rewrite Nat.mul_add_distr_l, Nat.mul_1_r in H1.
rewrite <- Nat.add_mod_idemp_l in H1; [ | easy ].
rewrite <- Nat.mul_mod_idemp_r in H1; [ | easy ].
rewrite Ha, Nat.mul_0_r in H1.
rewrite Nat.mod_0_l in H1; [ | easy ].
rewrite Nat.add_0_l in H1.
rewrite Nat.mod_small in H1; [ flia Hap H1 | flia Hap ].
Qed.

(* if 2≤a≤p-2 then a ≠ a⁻¹ [mod p]; we know that a⁻¹=a^(p-2) by
   Fermat's little theorem *)

Theorem lt_prime_inv_is_diff : ∀ p,
  is_prime p = true → ∀ a, 2 ≤ a ≤ p - 2 → a ^ (p - 2) mod p ≠ a mod p.
Proof.
intros * Hp * Hap Ha.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
apply Nat_eq_mod_sub_0 in Ha. 2: {
  rewrite <- (Nat.pow_1_r a) at 1.
  apply Nat.pow_le_mono_r; flia Hap.
}
rewrite <- (Nat.mul_1_r a) in Ha at 2.
replace (p - 2) with (S (p - 3)) in Ha by flia Hap.
rewrite Nat.pow_succ_r in Ha; [ | flia Hap ].
rewrite <- Nat.mul_sub_distr_l in Ha.
apply Nat.mod_divide in Ha; [ | easy ].
specialize (Nat.gauss _ _ _ Ha) as H1.
assert (H : Nat.gcd p a = 1). {
  apply eq_gcd_prime_small_1; [ easy | flia Hap ].
}
specialize (H1 H); clear H.
specialize (fermat_little _ Hp a) as H2.
assert (H : 1 ≤ a < p) by flia Hap.
specialize (H2 H); clear H.
destruct H1 as (c, Hc).
apply Nat.add_sub_eq_nz in Hc. 2: {
  intros H; apply Nat.eq_mul_0 in H.
  destruct H as [H| H]; [ | easy ].
  subst c; rewrite Nat.mul_0_l in Hc.
  apply Nat.sub_0_le in Hc.
  apply Nat.nlt_ge in Hc; apply Hc; clear Hc.
  destruct p; [ easy | ].
  destruct p; [ easy | ].
  destruct p; [ flia Hap | ].
  destruct p; [ flia Hap | ].
  do 3 rewrite Nat.sub_succ.
  rewrite Nat.sub_0_r; cbn.
  unfold "<".
  replace 2 with (2 * 1) by easy.
  apply Nat.mul_le_mono; [ easy | ].
  apply Nat.neq_0_lt_0.
  apply Nat.pow_nonzero; flia Hap.
}
apply (f_equal (Nat.mul (a ^ 2))) in Hc.
rewrite <- Nat.pow_add_r in Hc.
replace (2 + (p - 3)) with (p - 1) in Hc by flia Hap.
rewrite <- Hc in H2.
rewrite Nat.mul_add_distr_l, Nat.mul_1_r in H2.
rewrite Nat.mul_assoc in H2.
rewrite Nat.mod_add in H2; [ | easy ].
revert H2.
now apply lt_prime_sqr_not_1.
Qed.

(* (a ^ b) mod c for testing, without computing a ^ b but
   using mod along the way *)

Fixpoint Nat_pow_mod_loop a b c :=
  match b with
  | 0 => 1 mod c
  | S b' => (a * Nat_pow_mod_loop a b' c) mod c
  end.

Definition Nat_pow_mod a b c := Nat_pow_mod_loop a b c.

(* but they are the same (if c ≠ 0) *)

Theorem Nat_pow_mod_is_pow_mod : ∀ a b c,
  c ≠ 0 → Nat_pow_mod a b c = (a ^ b) mod c.
Proof.
intros * Hcz.
revert a.
induction b; intros; [ easy | ].
cbn; rewrite IHb.
now rewrite Nat.mul_mod_idemp_r.
Qed.

(* inverse modulo (true when n is prime) *)

Definition inv_mod i n := Nat_pow_mod i (n - 2) n.

Theorem mul_inv_diag_l_mod : ∀ p,
  is_prime p = true → ∀i, 1 ≤ i ≤ p - 1 → (inv_mod i p * i) mod p = 1.
Proof.
intros * Hp * Hip.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
unfold inv_mod.
rewrite Nat_pow_mod_is_pow_mod; [ | easy ].
rewrite Nat.mul_mod_idemp_l; [ | easy ].
replace i with (i ^ 1) at 2 by now rewrite Nat.pow_1_r.
rewrite <- Nat.pow_add_r.
replace (p - 2 + 1) with (p - 1) by flia Hip.
apply fermat_little; [ easy | flia Hip ].
Qed.

Theorem mul_inv_diag_r_mod : ∀ p,
  is_prime p = true → ∀ i, 1 ≤ i ≤ p - 1 → (i * inv_mod i p) mod p = 1.
Proof. now intros; rewrite Nat.mul_comm; apply mul_inv_diag_l_mod. Qed.

Theorem inv_mod_neq : ∀ p,
  is_prime p = true → ∀ i, 2 ≤ i ≤ p - 2 → inv_mod i p ≠ i.
Proof.
intros * Hp * Hip Hcon.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
unfold inv_mod in Hcon.
rewrite Nat_pow_mod_is_pow_mod in Hcon; [ | now intros H; subst p ].
specialize (fermat_little_1 p Hp i) as H1.
rewrite (Nat.mod_small i) in H1; [ | flia Hip ].
rewrite <- Hcon in H1 at 2.
apply Nat_eq_mod_sub_0 in H1; [ | apply Nat.pow_le_mono_r; flia Hip ].
replace p with (p - 2 + 2) in H1 at 1 by flia Hip.
rewrite <- (Nat.mul_1_r (_ ^ (p - 2))) in H1.
rewrite Nat.pow_add_r in H1.
rewrite <- Nat.mul_sub_distr_l in H1.
rewrite <- Nat.mul_mod_idemp_l in H1; [ | easy ].
rewrite Hcon in H1.
apply Nat.mod_divide in H1; [ | easy ].
specialize (Nat.gauss _ _ _ H1) as H2.
assert (H : Nat.gcd p i = 1). {
  apply eq_gcd_prime_small_1; [ easy | flia Hip ].
}
specialize (H2 H); clear H.
rewrite Nat_sqr_sub_1 in H2.
specialize (Nat.gauss _ _ _ H2) as H3.
assert (H : Nat.gcd p (i + 1) = 1). {
  apply eq_gcd_prime_small_1; [ easy | flia Hip ].
}
specialize (H3 H); clear H.
apply Nat.divide_pos_le in H3; [ flia Hip H3 | flia Hip ].
Qed.

Theorem pow_mod_prime_ne_0 : ∀ i n p,
  is_prime p = true
  → 1 ≤ i < p
  → i ^ n mod p ≠ 0.
Proof.
intros * Hp Hip Hinp.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
apply Nat.mod_divide in Hinp; [ | easy ].
induction n. {
  cbn in Hinp.
  destruct Hinp as (c, Hc).
  symmetry in Hc.
  apply Nat.eq_mul_1 in Hc.
  now rewrite (proj2 Hc) in Hp.
}
cbn in Hinp.
specialize (Nat.gauss _ _ _ Hinp) as H1.
assert (H : Nat.gcd p i = 1) by now apply eq_gcd_prime_small_1.
specialize (H1 H); clear H.
apply IHn, H1.
Qed.

Theorem inv_mod_interv : ∀ p, is_prime p = true →
  ∀ i, 2 ≤ i ≤ p - 2 → 2 ≤ inv_mod i p ≤ p - 2.
Proof.
intros * Hp * Hip.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
unfold inv_mod.
rewrite Nat_pow_mod_is_pow_mod; [ | now intros H; subst p ].
split. {
  apply Nat.nlt_ge; intros Hi.
  remember (i ^ (p - 2) mod p) as j eqn:Hj; symmetry in Hj.
  destruct j. {
    revert Hj.
    apply pow_mod_prime_ne_0; [ easy | flia Hip ].
  }
  destruct j; [ clear Hi | flia Hi ].
  specialize (fermat_little p Hp i) as H1.
  assert (H : 1 ≤ i < p) by flia Hip.
  specialize (H1 H); clear H.
  replace (p - 1) with (S (p - 2)) in H1 by flia Hip.
  cbn in H1.
  rewrite <- Nat.mul_mod_idemp_r in H1; [ | easy ].
  rewrite Hj, Nat.mul_1_r in H1.
  rewrite Nat.mod_small in H1; [ flia Hip H1 | flia Hip ].
} {
  apply Nat.nlt_ge; intros Hi.
  remember (i ^ (p - 2) mod p) as j eqn:Hj; symmetry in Hj.
  replace j with (p - 1) in Hj. 2: {
    specialize (Nat.mod_upper_bound (i ^ (p - 2)) p Hpz) as H1.
    rewrite Hj in H1; flia Hi H1.
  }
  clear j Hi.
  specialize (fermat_little p Hp i) as H1.
  assert (H : 1 ≤ i < p) by flia Hip.
  specialize (H1 H); clear H.
  replace (p - 1) with (S (p - 2)) in H1 by flia Hip.
  cbn in H1.
  rewrite <- Nat.mul_mod_idemp_r in H1; [ | easy ].
  rewrite Hj in H1.
  replace 1 with (1 mod p) in H1 at 2; [ | rewrite Nat.mod_small; flia Hip ].
  apply Nat_eq_mod_sub_0 in H1. 2: {
    destruct i; [ flia Hip | ].
    destruct p; [ flia Hip | ].
    destruct p; [ flia Hip | ].
    cbn; remember (i * S p); flia.
  }
  apply Nat.mod_divide in H1; [ | easy ].
  destruct H1 as (c, Hc).
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in Hc.
  rewrite <- Nat.sub_add_distr in Hc.
  assert (H : Nat.divide p (i + 1)). {
    exists (i - c).
    rewrite Nat.mul_sub_distr_r, <- Hc.
    rewrite Nat_sub_sub_distr. 2: {
      split; [ | easy ].
      destruct p; [ easy | ].
      rewrite Nat.mul_succ_r.
      destruct i; [ easy | ].
      destruct p; [ easy | ].
      cbn; remember (i * S p); flia.
    }
    now rewrite Nat.sub_diag, Nat.add_0_l.
  }
  clear Hc; rename H into Hc.
  apply Nat.divide_pos_le in Hc; [ | flia ].
  flia Hip Hc.
}
Qed.

Theorem inv_mod_prime_involutive : ∀ p,
  is_prime p = true
  → ∀ i, 2 ≤ i ≤ p - 2
  → inv_mod (inv_mod i p) p = i.
Proof.
intros * Hp * Hip.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
unfold inv_mod.
rewrite Nat_pow_mod_is_pow_mod; [ | now intros H; subst p ].
rewrite Nat_pow_mod_is_pow_mod; [ | now intros H; subst p ].
rewrite Nat_mod_pow_mod.
rewrite <- Nat.pow_mul_r.
rewrite Nat.mul_sub_distr_r.
do 2 rewrite Nat.mul_sub_distr_l.
rewrite Nat_sub_sub_distr. 2: {
  split; [ flia Hip | ].
  rewrite <- Nat.mul_sub_distr_l.
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_l.
  flia Hip.
}
rewrite (Nat.mul_comm 2).
rewrite <- Nat.sub_add_distr.
rewrite <- Nat.mul_add_distr_l.
replace (2 + 2) with 4 by easy.
replace (2 * 2) with 4 by easy.
rewrite <- Nat.mul_sub_distr_l.
rewrite Nat.pow_add_r.
rewrite Nat.pow_mul_r.
rewrite <- Nat.mul_mod_idemp_l; [ | easy ].
rewrite <- Nat_mod_pow_mod.
rewrite fermat_little_1; [ | easy ].
rewrite Nat_mod_pow_mod.
rewrite Nat.mul_mod_idemp_l; [ | easy ].
rewrite <- Nat.pow_add_r.
rewrite Nat.sub_add; [ | flia Hip ].
rewrite fermat_little_1; [ | easy ].
apply Nat.mod_small; flia Hip.
Qed.

(* from a prime number p, group together values "a" between 2 and
   p-2 with their inverse modulo p, which is "a^(p-2)" according
   to Fermat's little theorem; return a list where these pairs
   are concatened. E.g. with_inv_pair 11 returns
        [2; 6; 3; 4; 5; 9; 7; 8]
   with 2*6≡1, 3*4≡1, 5*9≡1, 7*8≡1 [mod 11].
   This list is a permutation of the sequence of numbers from 2
   to p-2 (to be proven). So, the product of all elements of this
   list is at the same time 1 and 2*3*4..*(n-2) [mod p] *)

Fixpoint with_inv_pair_loop p i :=
  match i with
  | 0 | 1 => []
  | S i' => i :: inv_mod i p :: with_inv_pair_loop p i'
  end.

Definition with_inv_pair p := nodup Nat.eq_dec (with_inv_pair_loop p (p - 2)).

Compute (with_inv_pair 11).

Theorem length_with_inv_pair_loop : ∀ p i,
  length (with_inv_pair_loop p i) = 2 * i - 2.
Proof.
intros.
revert p.
induction i; intros; [ easy | ].
cbn - [ "/" ].
destruct i; [ easy | ].
cbn - [ with_inv_pair_loop ].
rewrite IHi; flia.
Qed.

Theorem seq_succ_r : ∀ a b, seq a (S b) = seq a b ++ [a + b].
Proof.
intros.
revert a.
induction b; intros; [ now cbn; rewrite Nat.add_0_r | ].
remember (S b) as sb; cbn; subst sb.
now rewrite IHb, Nat.add_succ_comm.
Qed.

(* all values between 2 and p-2 have an inverse modulo p, which is not
   themselves *)

(* more than automorphism, actually;
   extra properties: f(i)≠i, i*f(i)≡1 *)
Theorem inv_mod_autom : ∀ p (P := λ i, 2 ≤ i ≤ p - 2), is_prime p = true →
  (∀ i, P i → P (inv_mod i p)) ∧
  (∀ i j, P i → P j → inv_mod i p = inv_mod j p → i = j) ∧
  (∀ j, P j → ∃ i, P i ∧ inv_mod i p = j) ∧
  (∀ i, P i → inv_mod i p ≠ i) ∧
  (∀ i, P i → (i * inv_mod i p) mod p = 1) ∧
  (∀ i, P i → (inv_mod i p * i) mod p = 1).
Proof.
intros * Hp.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
split; [ now apply inv_mod_interv | ].
split. {
  unfold P; intros * HPi HPj Hijp.
  apply (f_equal (λ i, inv_mod i p)) in Hijp.
  rewrite inv_mod_prime_involutive in Hijp; [ | easy | easy ].
  now rewrite inv_mod_prime_involutive in Hijp.
}
split. {
  intros * HPj.
  exists (inv_mod j p).
  rewrite inv_mod_prime_involutive; [ | easy | easy ].
  split; [ | easy ].
  now apply inv_mod_interv.
}
split; [ now apply inv_mod_neq | ].
split. {
  intros * H; apply mul_inv_diag_r_mod; [ easy | ].
  unfold P in H; flia H.
} {
  intros * H; apply mul_inv_diag_l_mod; [ easy | ].
  unfold P in H; flia H.
}
Qed.

...

Theorem eq_fold_left_mul_seq_2_prime_sub_3_1 : ∀ p,
  is_prime p = true
  → 3 ≤ p
  → fold_left Nat.mul (seq 2 (p - 3)) 1 mod p = 1.
Proof.
intros * Hp H3p.
Search inv_mod.
...
intros * Hp H3p.
remember (seq 2 (p - 3)) as l eqn:Hl.
assert
  (Hij : ∀ i, i ∈ l →
   ∃ j, j ∈ l ∧ (i * j) mod p = 1 ∧ i ≠ j). {
  intros i Hi.
  exists (inv_mod i p).
  subst l.
  apply in_seq in Hi.
  split. {
    apply in_seq.
    specialize (inv_mod_interv p Hp i) as H1.
    assert (H : 2 ≤ i ≤ p - 2) by flia Hi.
    specialize (H1 H); flia H1.
  }
  split. {
    apply mul_inv_diag_r_mod; [ easy | flia Hi ].
  }
  apply not_eq_sym.
  apply inv_mod_neq; [ easy | flia Hi ].
}
destruct l as [| a l]. {
  cbn; rewrite Nat.mod_1_l; flia H3p.
}
cbn; rewrite Nat.add_0_r.
assert (Ha2: a = 2). {
  remember (p - 3) as len eqn:Hlen.
  destruct len; [ easy | ].
  cbn in Hl.
  now injection Hl; intros.
}
subst a.
specialize (Hij 2 (or_introl (eq_refl _))) as H1.
destruct H1 as (i2 & Hi2 & H2i2 & H2i).
destruct Hi2 as [Hi2| Hi2]; [ easy | ].
specialize (in_split i2 l Hi2) as (l1 & l2 & Hll).
rewrite Hll.
rewrite fold_left_app; cbn.
rewrite fold_left_mul_from_1.
rewrite Nat.mul_shuffle0, Nat.mul_comm.
rewrite fold_left_mul_from_1.
do 2 rewrite Nat.mul_assoc.
remember (i2 * 2) as x.
rewrite <- Nat.mul_assoc; subst x.
rewrite <- Nat.mul_mod_idemp_l; [ | flia H3p ].
rewrite (Nat.mul_comm i2).
rewrite H2i2, Nat.mul_1_l.
rewrite Nat.mul_comm.
rewrite List_fold_left_mul_assoc, Nat.mul_1_l.
rewrite <- fold_left_app.
...

(* *)

Theorem Wilson : ∀ n, is_prime n = true ↔ fact (n - 1) mod n = n - 1.
Proof.
intros.
split.
-intros Hn.
 destruct (lt_dec n 3) as [H3n| H3n]. {
   specialize (prime_ge_2 n Hn) as H2n.
   now replace n with 2 by flia H2n H3n.
 }
 apply Nat.nlt_ge in H3n.
 replace (n - 1) with (S (n - 2)) at 1 by flia H3n.
 rewrite Nat_fact_succ.
 replace (S (n - 2)) with (n - 1) by flia H3n.
 rewrite <- Nat.mul_mod_idemp_r; [ | flia H3n ].
 enough (H : fact (n - 2) mod n = 1). {
   rewrite H, Nat.mul_1_r.
   apply Nat.mod_small; flia H3n.
 }
 rewrite fact_eq_fold_left.
 enough (H : fold_left Nat.mul (seq 2 (n - 3)) 1 mod n = 1). {
   replace (seq 1 (n - 2)) with (1 :: seq 2 (n - 3)). 2: {
     clear - H3n.
     destruct n; [ flia H3n | ].
     destruct n; [ flia H3n | ].
     destruct n; [ flia H3n | ].
     now cbn; rewrite Nat.sub_0_r.
   }
   easy.
 }
 (* now we must prove that the multiplication can be done by
    associating pairs of (a, b) in interval [2, n-2] such that
    a * b ≡ 1 (mod n). We not by Fermat's little theorem that
    a * a^(n-2) indeed equals 1 mod n. So b=a^(n-2) mod n. All
    these pairs are supposed to cover [2, n-2] *)
 remember (seq 2 (n - 3)) as l eqn:Hl.
subst l.
...
 remember (with_inv_pair n) as l' eqn:Hl'.
 move l' before l.
 assert (Hperm : Permutation l l'). {
   assert (length l = length l'). {
     rewrite Hl, Hl'.
     rewrite seq_length.
     unfold with_inv_pair.
     (* even comparison of lengths is not easy to proof *)
...

Theorem ζ_Euler_product_eq : ...
