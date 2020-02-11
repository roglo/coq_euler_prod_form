(* Rpolynomial.v *)

(* polynomials on a ring *)

(* obsolete: I use Rpolynomial2.v now *)

...

Set Nested Proofs Allowed.
Require Import Utf8 Arith Setoid Morphisms Psatz.
Import List List.ListNotations.
Require Import Misc Ring2.

Notation "'Σ' ( i = b , e ) , g" :=
  (fold_left (λ c i, (c + g)%Rng) (seq b (S e - b)) 0%Rng)
  (at level 45, i at level 0, b at level 60, e at level 60) : ring_scope.

Section Lap.

Context {A : Type}.
Context {rng : ring A}.

(* lap : list as polynomial, i.e. the only field of the record in the
   definition of polynomial after *)

Inductive lap_eq : list A → list A → Prop :=
  | lap_eq_nil_nil : lap_eq [] []
  | lap_eq_nil_cons : ∀ b bl, (b = 0)%Rng → lap_eq bl [] → lap_eq [] (b :: bl)
  | lap_eq_cons_nil : ∀ a al, (a = 0)%Rng → lap_eq al [] → lap_eq (a :: al) []
  | lap_eq_cons_cons : ∀ a b al bl,
      (a = b)%Rng → lap_eq al bl → lap_eq (a :: al) (b :: bl).

Definition lap_zero := ([] : list A).
Definition lap_one := [1%Rng].

Fixpoint lap_add al1 al2 :=
  match al1 with
  | [] => al2
  | a1 :: bl1 =>
      match al2 with
      | [] => al1
      | a2 :: bl2 => (a1 + a2)%Rng :: lap_add bl1 bl2
      end
  end.

Definition lap_convol_mul_term la lb i :=
  (Σ (j = 0, i), List.nth j la 0 * List.nth (i - j)%nat lb 0)%Rng.

Theorem lap_eq_nil_cons_inv : ∀ x l,
  lap_eq [] (x :: l)
  → (x = 0)%Rng ∧ lap_eq l [].
Proof.
intros x l H.
now inversion H.
Qed.

Theorem lap_eq_cons_nil_inv : ∀ x l,
  lap_eq (x :: l) []
  → (x = 0)%Rng ∧ lap_eq l [].
Proof.
intros x l H.
now inversion H.
Qed.

Theorem lap_eq_cons_cons_inv : ∀ a b la lb,
  lap_eq (a :: la) (b :: lb)
  → (a = b)%Rng ∧ lap_eq la lb.
Proof.
intros * H.
now inversion H.
Qed.

Theorem lap_eq_iff : ∀ la lb,
  lap_eq la lb ↔ ∀ i, (nth i la 0 = nth i lb 0)%Rng.
Proof.
intros.
split; intros Hll. {
  intros i.
  revert i lb Hll.
  induction la as [| a la]; intros. {
    cbn.
    destruct lb as [| b lb]; [ easy | cbn ].
    apply lap_eq_nil_cons_inv in Hll.
    destruct i; [ easy | ].
    destruct Hll as (_, Hll); symmetry.
    clear - Hll.
    revert i.
    induction lb as [| b lb]; intros; [ now destruct i | cbn ].
    apply lap_eq_cons_nil_inv in Hll.
    destruct i; [ easy | ].
    now apply IHlb.
  } {
    cbn.
    destruct lb as [| b lb]. {
      apply lap_eq_cons_nil_inv in Hll.
      destruct i; [ easy | cbn ].
      destruct Hll as (_, Hll).
      clear - Hll.
      revert i.
      induction la as [| a la]; intros; [ now destruct i | cbn ].
      apply lap_eq_cons_nil_inv in Hll.
      destruct i; [ easy | ].
      now apply IHla.
    } {
      apply lap_eq_cons_cons_inv in Hll.
      destruct i; [ easy | cbn ].
      now apply IHla.
    }
  }
} {
  revert lb Hll.
  induction la as [| a la]; intros. {
    induction lb as [| b lb]; constructor. {
      now specialize (Hll 0).
    } {
      assert (H : (∀ i : nat, (nth i [] 0 = nth i lb 0)%Rng)). {
        intros i; specialize (Hll (S i)).
        now destruct i.
      }
      specialize (IHlb H); clear - IHlb.
      rename IHlb into Hb.
      induction lb as [| b lb]; [ easy | ].
      apply lap_eq_nil_cons_inv in Hb.
      now constructor.
    }
  } {
    destruct lb as [| b lb]. {
      constructor; [ now specialize (Hll 0) | ].
      apply IHla.
      intros i; cbn.
      specialize (Hll (S i)); cbn in Hll.
      now destruct i.
    } {
      constructor; [ now specialize (Hll 0) | ].
      apply IHla; intros i.
      now specialize (Hll (S i)).
    }
  }
}
Qed.

End Lap.

Theorem lap_eq_refl {A} {rng : ring A} : reflexive _ lap_eq.
Proof.
intros la.
now induction la; constructor.
Qed.

Theorem lap_eq_sym {A} {rng : ring A} : symmetric _ lap_eq.
Proof.
intros la lb Hll.
specialize (proj1 (lap_eq_iff _ _) Hll) as H1.
clear Hll.
apply lap_eq_iff.
intros i; symmetry.
apply H1.
Qed.

Theorem lap_eq_trans {A} {rng : ring A} : transitive _ lap_eq.
Proof.
intros la lb lc H12 H23.
specialize (proj1 (lap_eq_iff _ _) H12) as H1.
specialize (proj1 (lap_eq_iff _ _) H23) as H2.
apply lap_eq_iff.
intros i.
etransitivity; [ apply H1 | apply H2 ].
Qed.

Add Parametric Relation {A} {rng : ring A} : _ lap_eq
 reflexivity proved by lap_eq_refl
 symmetry proved by lap_eq_sym
 transitivity proved by lap_eq_trans
 as lap_eq_rel.

(* polynomials *)

Section Polynomials.

Context {A : Type}.
Context {rng : ring A}.

Record polynomial := mkpol { al : list A }.

Definition pol_zero := mkpol [].
Definition pol_one := mkpol [1%Rng].

Definition pol_eq p1 p2 := lap_eq (al p1) (al p2).

Definition pol_add p1 p2 := mkpol (lap_add (al p1) (al p2)).

Definition pol_opp p := mkpol (map (λ a, (- a)%Rng) (al p)).
Definition pol_sub p1 p2 := pol_add p1 (pol_opp p2).

Definition pol_mul p1 p2 :=
  mkpol
    (map
       (lap_convol_mul_term (al p1) (al p2))
       (seq 0 (length (al p1) + length (al p2) - 1))).

Definition xpow i := mkpol (repeat 0%Rng i ++ [1%Rng]).

End Polynomials.

Declare Scope pol_scope.
Delimit Scope pol_scope with pol.
Bind Scope pol_scope with polynomial.
Notation "0" := pol_zero : pol_scope.
Notation "1" := pol_one : pol_scope.
Notation "- a" := (pol_opp a) : pol_scope.
Notation "a + b" := (pol_add a b) : pol_scope.
Notation "a - b" := (pol_sub a b) : pol_scope.
Notation "a * b" := (pol_mul a b) : pol_scope.
Notation "a = b" := (pol_eq a b) : pol_scope.
Notation "'ⓧ' ^ a" := (xpow a) (at level 30, format "'ⓧ' ^ a") : pol_scope.
Notation "'ⓧ'" := (xpow 1) (at level 30, format "'ⓧ'") : pol_scope.

Notation "'Σ' ( i = b , e ) , g" :=
  (fold_left (λ c i, (c + g)%pol) (seq b (S e - b)) 0%pol) : pol_scope.

Theorem pol_eq_refl {A} {rng : ring A} : reflexive _ pol_eq.
Proof.
intros (la).
unfold pol_eq; cbn.
now induction la; constructor.
Qed.

Theorem pol_eq_sym {A} {rng : ring A} : symmetric _ pol_eq.
Proof.
intros (la) (lb) Hll.
specialize (proj1 (lap_eq_iff _ _) Hll) as H1.
clear Hll.
apply lap_eq_iff.
intros i; symmetry.
apply H1.
Qed.

Theorem pol_eq_trans {A} {rng : ring A} : transitive _ pol_eq.
Proof.
intros (la) (lb) (lc) H12 H23.
specialize (proj1 (lap_eq_iff _ _) H12) as H1.
specialize (proj1 (lap_eq_iff _ _) H23) as H2.
apply lap_eq_iff.
intros i.
etransitivity; [ apply H1 | apply H2 ].
Qed.

Add Parametric Relation {A} {rng : ring A} : _ pol_eq
 reflexivity proved by pol_eq_refl
 symmetry proved by pol_eq_sym
 transitivity proved by pol_eq_trans
 as pol_eq_rel.

Theorem fold_left_rng_add_fun_from_0 {A} {rng : ring A} : ∀ a l (f : nat → _),
  (fold_left (λ c i, c + f i) l a =
   a + fold_left (λ c i, c + f i) l 0)%Rng.
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply rng_add_0_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite rng_add_0_l.
apply rng_add_assoc.
Qed.

Theorem all_0_rng_summation_0 {A} {rng : ring A} : ∀ b e f,
  (∀ i, b ≤ i ≤ e → (f i = 0)%Rng)
  → (Σ (i = b, e), f i = 0)%Rng.
Proof.
intros * Hz.
remember (S e - b) as n eqn:Hn.
revert b Hz Hn.
induction n; intros; [ easy | cbn ].
rewrite fold_left_rng_add_fun_from_0.
rewrite IHn; [ | | flia Hn ]. {
  rewrite Hz; [ | flia Hn ].
  now do 2 rewrite rng_add_0_r.
} {
  intros i Hi.
  apply Hz; flia Hi.
}
Qed.

Theorem rng_summation_eq_compat {A} {rng : ring A} : ∀ b e g h,
  (∀ i, b ≤ i ≤ e → (g i = h i)%Rng)
  → (Σ (i = b, e), g i = Σ (i = b, e), h i)%Rng.
Proof.
intros * Hgh.
remember (S e - b) as n eqn:Hn.
remember 0%Rng as a eqn:Ha; clear Ha.
revert e a b Hn Hgh.
induction n as [| n IHn]; intros; [ easy | cbn ].
rewrite (IHn e); [ | flia Hn | ]. 2: {
  intros i Hbie.
  apply Hgh; flia Hbie.
}
rewrite fold_left_rng_add_fun_from_0; symmetry.
rewrite fold_left_rng_add_fun_from_0; symmetry.
rewrite Hgh; [ easy | ].
split; [ easy | flia Hn ].
Qed.

Theorem pol_add_0_l {A} {rng : ring A} : ∀ p1, (0 + p1)%pol = p1.
Proof. intros (la); easy. Qed.

Instance cons_rng_lap_morph {A} {rng : ring A} :
  Proper (rng_eq ==> lap_eq ==> lap_eq) cons.
Proof.
intros a b Hab la lb Hll.
now constructor.
Qed.

Instance mkpol_morph {A} {rng : ring A} :
  Proper (lap_eq ==> pol_eq) mkpol.
Proof. easy. Qed.

Theorem lap_eq_mkpol_eq {A} {rng : ring A} : ∀ la lb,
  lap_eq la lb → (mkpol la = mkpol lb)%pol.
Proof.
intros * Hll.
now rewrite Hll.
Qed.

Theorem pol_mul_1_l {A} {rng : ring A} : ∀ p1, (1 * p1 = p1)%pol.
Proof.
intros (la).
unfold "*"%pol; cbn.
rewrite Nat.sub_0_r.
apply lap_eq_mkpol_eq.
induction la as [| a la]; [ constructor | cbn ].
constructor. {
  rewrite rng_add_0_l.
  rewrite rng_mul_1_l.
  easy.
} {
Search lap_convol_mul_term.
...

f_equal.
induction la as [| a la]; [ easy | cbn ].
f_equal.
rewrite rng_add_0_l.
...

Theorem pol_mul_1_l {A} {rng : ring A} : ∀ p1, (1 * p1 = p1)%pol.
Proof.
intros (la).
induction la as [| a la]; [ easy | ].
cbn.
unfold "*"%pol; cbn.
rewrite rng_add_0_l.
...

intros (la).
unfold "*"%pol; cbn.
rewrite Nat.sub_0_r.
unfold lap_convol_mul_term.
unfold pol_eq.
cbn - [ nth ].
rewrite Nat.sub_0_r.

...

rewrite (map_ext _ (λ _, 0%Rng)). 2: {
  intros i.
Set Printing All.
  rewrite all_0_rng_summation_0.
...

Instance pol_mul_morph {A} {rng : ring A} :
  Proper (pol_eq ==> pol_eq ==> pol_eq) pol_mul.
Proof.
intros (la) (lb) Hab (lc) (ld) Hcd.
apply lap_eq_iff; intros i.
specialize (proj1 (lap_eq_iff _ _) Hab) as H1.
specialize (proj1 (lap_eq_iff _ _) Hcd) as H2.
clear Hab Hcd.
cbn in H1, H2 |-*.
unfold lap_convol_mul_term.
destruct (le_dec (length la + length lc - 1) i) as [Hila| Hila]. {
  rewrite nth_overflow; [ | now rewrite map_length, seq_length ].
  destruct (le_dec (length lb + length ld - 1) i) as [Hilb| Hilb]. {
    rewrite nth_overflow; [ easy | now rewrite map_length, seq_length ].
  } {
    apply Nat.nle_gt in Hilb.
    rewrite (List_map_nth_in _ 0); [ | now rewrite seq_length ].
    rewrite seq_nth; [ rewrite Nat.add_0_l | easy ].
    rewrite all_0_rng_summation_0; [ easy | ].
    intros j Hj.
    destruct (le_dec (length lb) j) as [Hbj| Hbj]. {
      rewrite nth_overflow; [ | easy ].
      now rewrite rng_mul_0_l.
    }
    apply Nat.nle_gt in Hbj.
    rewrite <- H1.
    destruct (le_dec (length la) j) as [Haj| Haj]. {
      rewrite nth_overflow; [ | easy ].
      now rewrite rng_mul_0_l.
    }
    apply Nat.nle_gt in Haj.
    rewrite rng_mul_comm.
    destruct (le_dec (length ld) (i - j)) as [Hdj| Hdj]. {
      rewrite nth_overflow; [ | easy ].
      now rewrite rng_mul_0_l.
    }
    apply Nat.nle_gt in Hdj.
    rewrite <- H2.
    destruct (le_dec (length lc) (i - j)) as [Hcj| Hcj]. {
      rewrite nth_overflow; [ | easy ].
      now rewrite rng_mul_0_l.
    }
    apply Nat.nle_gt in Hcj.
    flia Hbj Haj Hdj Hcj Hila.
  }
} {
  apply Nat.nle_gt in Hila.
  rewrite (List_map_nth_in _ 0); [ | now rewrite seq_length ].
  rewrite seq_nth; [ rewrite Nat.add_0_l | easy ].
  destruct (le_dec (length lb + length ld - 1) i) as [Hilb| Hilb]. {
    rewrite nth_overflow; [ | now rewrite map_length, seq_length ].
    rewrite all_0_rng_summation_0; [ easy | ].
    intros j Hj.
    rewrite H1.
    destruct (le_dec (length lb) j) as [Hbj| Hbj]. {
      rewrite nth_overflow; [ | easy ].
      now rewrite rng_mul_0_l.
    }
    apply Nat.nle_gt in Hbj.
    rewrite <- H1.
    destruct (le_dec (length la) j) as [Haj| Haj]. {
      rewrite nth_overflow; [ | easy ].
      now rewrite rng_mul_0_l.
    }
    apply Nat.nle_gt in Haj.
    rewrite rng_mul_comm.
    rewrite H2.
    destruct (le_dec (length ld) (i - j)) as [Hdj| Hdj]. {
      rewrite nth_overflow; [ | easy ].
      now rewrite rng_mul_0_l.
    }
    apply Nat.nle_gt in Hdj.
    rewrite <- H2.
    destruct (le_dec (length lc) (i - j)) as [Hcj| Hcj]. {
      rewrite nth_overflow; [ | easy ].
      now rewrite rng_mul_0_l.
    }
    apply Nat.nle_gt in Hcj.
    flia Hbj Haj Hdj Hcj Hilb.
  } {
    apply Nat.nle_gt in Hilb.
    rewrite (List_map_nth_in _ 0); [ | now rewrite seq_length ].
    rewrite seq_nth; [ | easy ].
    rewrite Nat.add_0_l.
    apply rng_summation_eq_compat.
    intros j Hj.
    now rewrite H1, H2.
  }
}
Qed.

Theorem xpow_0 {A} {rng : ring A} : (ⓧ^0 = 1)%pol.
Proof. easy. Qed.

Theorem pol_pow_sub_1 {A} {rng : ring A} : ∀ k,
  k ≠ 0
  → (ⓧ^k - 1 = (ⓧ - 1) * (Σ (i = 0, k - 1), ⓧ^(k-i-1)))%pol.
Proof.
intros * Hkz.
destruct k; [ easy | clear Hkz ].
rewrite Nat.sub_succ, (Nat.sub_0_r k).
induction k. {
  cbn - [ pol_mul ].
  rewrite pol_add_0_l.
  rewrite xpow_0.
...
  rewrite pol_mul_1_r.
...

Instance pol_add_morph : Proper (pol_eq ==> pol_eq ==> pol_eq) pol_add.
...

Instance pol_sub_morph : Proper (pol_eq ==> pol_eq ==> pol_eq) pol_sub.
...

Fixpoint lap_eval la x :=
  match la with
  | [] => 0%Rng
  | a :: la' => (a + x * lap_eval la' x)%Rng
  end.

Definition pol_eval p x := lap_eval (al p) x.

(*
Instance polm_add_morph {A} {rng : ring A} :
  Proper (pol_eq ==> pol_eq ==> pol_eq) pol_add.
Proof.
intros la lb Hab lc ld Hcd.
Admitted. (*
apply polm_eq_iff; intros i.
specialize (proj1 (polm_eq_iff _ _) Hab i) as H1.
specialize (proj1 (polm_eq_iff _ _) Hcd i) as H2.
clear Hab Hcd.
do 2 rewrite nth_polm_add.
destruct (Nat.eq_dec mn 0) as [Hnz| Hnz]; [ now rewrite Hnz | ].
rewrite <- Nat.add_mod_idemp_l; [ | easy ].
rewrite <- Nat.add_mod_idemp_r; [ | easy ].
rewrite H1, H2.
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite Nat.add_mod_idemp_r; [ | easy ].
easy.
Qed.
*)
*)

Theorem polm_summation_split_first {A} {rng : ring A} : ∀ b e f,
  b ≤ e
  → (Σ (i = b, e), f i)%pol = (f b + Σ (i = S b, e), f i)%pol.
Proof.
intros * Hbe.
rewrite Nat.sub_succ.
replace (S e - b) with (S (e - b)) by flia Hbe.
cbn.
...
apply fold_left_polm_add_fun_from_0.
Qed.

Theorem polm_summation_split_last {n : mod_num} : ∀ g b e,
  b ≤ S e
  → (Σ (i = b, S e), g i)%pol = (Σ (i = b, e), g i + g (S e))%pol.
Proof.
intros * Hbe.
replace (S (S e) - b) with (S (S e - b)) by flia Hbe.
rewrite seq_S.
rewrite fold_left_app.
rewrite fold_left_polm_add_fun_from_0.
now rewrite Nat.add_comm, Nat.sub_add.
Qed.

Theorem polm_mul_1_l {A} {rng : ring A} : ∀ p1, (1 * p1)%pol = p1.
Proof.
intros (la).
unfold "*"%pol; cbn.
f_equal.
rewrite Nat.sub_0_r.
f_equal.
unfold lap_convol_mul_term.
rewrite (map_ext _ (λ i, nth i la 0%Rng)). 2: {
  intros i.
...
  rewrite summation_split_first; [ | ].
  rewrite Nat.mul_1_l, Nat.sub_0_r.
  rewrite all_0_summation_0; [ apply Nat.add_0_r | ].
  intros j Hj.
  cbn.
  destruct j; [ flia Hj | now destruct j ].
}
induction la as [| a la]; [ easy | cbn; f_equal ].
rewrite <- seq_shift.
rewrite map_map.
apply IHla.
Qed.

Theorem polm_mul_1_r {n : mod_num} : ∀ la, (la * 1)%pol = la.
Proof.
intros.
rewrite polm_mul_comm.
apply polm_mul_1_l.
Qed.
