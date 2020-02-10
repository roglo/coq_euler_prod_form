(* Rpolynomial.v *)

(* polynomials on a ring *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Setoid.
Import List List.ListNotations.

(* ring *)

Class ring A :=
  { rng_zero : A;
    rng_one : A;
    rng_add : A → A → A;
    rng_mul : A → A → A;
    rng_opp : A → A;
    rng_eq : A → A → Prop;
    rng_eq_refl : ∀ a, rng_eq a a;
    rng_eq_sym : ∀ a b, rng_eq a b → rng_eq b a;
    rng_eq_trans : ∀ a b c, rng_eq a b → rng_eq b c → rng_eq a c }.

Declare Scope ring_scope.
Delimit Scope ring_scope with Rng.
Bind Scope ring_scope with ring.
Notation "0" := rng_zero : ring_scope.
Notation "1" := rng_one : ring_scope.
Notation "a = b" := (rng_eq a b) : ring_scope.
Notation "a ≠ b" := (¬ rng_eq a b) : ring_scope.
Notation "a + b" := (rng_add a b) : ring_scope.
Notation "a * b" := (rng_mul a b) : ring_scope.
Notation "- a" := (rng_opp a) : ring_scope.

Notation "'Σ' ( i = b , e ) , g" :=
  (fold_left (λ c i, (c + g)%Rng) (seq b (S e - b)) 0%Rng)
  (at level 45, i at level 0, b at level 60, e at level 60) : ring_scope.

Add Parametric Relation A (K : ring A) : A rng_eq
 reflexivity proved by rng_eq_refl
 symmetry proved by rng_eq_sym
 transitivity proved by rng_eq_trans
 as eq_rel.

Section Polynomials.

Variable A : Type.
Variable rng : ring A.

Record polynomial := mkpol { al : list A }.

Definition pol_0 := mkpol [].
Definition pol_1 := mkpol [1%Rng].

Fixpoint lap_add al₁ al₂ :=
  match al₁ with
  | [] => al₂
  | a₁ :: bl₁ =>
      match al₂ with
      | [] => al₁
      | a₂ :: bl₂ => (a₁ + a₂)%Rng :: lap_add bl₁ bl₂
      end
  end.

Definition pol_add p1 p2 := mkpol (lap_add (al p1) (al p2)).

Definition pol_opp p := mkpol (map (λ a, (- a)%Rng) (al p)).
Definition pol_sub p1 p2 := pol_add p1 (pol_opp p2).

Definition lap_convol_mul_term la lb i :=
  (Σ (j = 0, i), List.nth j la 0 * List.nth (i - j)%nat lb 0)%Rng.

Definition pol_mul p1 p2 :=
  mkpol
    (map
       (lap_convol_mul_term (al p1) (al p2))
       (seq 0 (length (al p1) + length (al p2) - 1))).

Definition xpow i := mkpol (repeat 0%Rng i ++ [1%Rng]).

Inductive lap_eq : list A → list A → Prop :=
  | lap_eq_nil_nil : lap_eq [] []
  | lap_eq_nil_cons : ∀ b bl, (b = 0)%Rng → lap_eq bl [] → lap_eq [] (b :: bl)
  | lap_eq_cons_nil : ∀ a al, (a = 0)%Rng → lap_eq al [] → lap_eq (a :: al) []
  | lap_eq_cons_cons : ∀ a b al bl,
      (a = b)%Rng → lap_eq al bl → lap_eq (a :: al) (b :: bl).

Definition pol_eq p1 p2 := lap_eq (al p1) (al p2).

Declare Scope pol_scope.
Delimit Scope pol_scope with pol.
Bind Scope pol_scope with polynomial.
Notation "0" := pol_0 : pol_scope.
Notation "1" := pol_1 : pol_scope.
Notation "- a" := (pol_opp a) : pol_scope.
Notation "a + b" := (pol_add a b) : pol_scope.
Notation "a - b" := (pol_sub a b) : pol_scope.
Notation "a * b" := (pol_mul a b) : pol_scope.
Notation "a = b" := (pol_eq a b) : pol_scope.
Notation "'ⓧ' ^ a" := (xpow a) (at level 30, format "'ⓧ' ^ a") : pol_scope.
Notation "'ⓧ'" := (xpow 1) (at level 30, format "'ⓧ'") : pol_scope.

Notation "'Σ' ( i = b , e ) , g" :=
  (fold_left (λ c i, (c + g)%pol) (seq b (S e - b)) 0%pol) : pol_scope.

Fixpoint lap_eval la x :=
  match la with
  | [] => 0%Rng
  | a :: la' => (a + x * lap_eval la' x)%Rng
  end.

Definition pol_eval p x := lap_eval (al p) x.

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

Theorem lap_eq_refl : reflexive _ lap_eq.
Proof.
intros l.
induction l; constructor; [ reflexivity | assumption ].
Qed.

Theorem lap_eq_sym : symmetric _ lap_eq.
Proof.
intros l₁ l₂ Heq.
revert l₂ Heq.
induction l₁ as [| x₁]; intros. {
  now induction l₂; constructor; apply lap_eq_nil_cons_inv in Heq.
}
induction l₂ as [| x₂]. {
  apply lap_eq_cons_nil_inv in Heq.
  now constructor.
}
apply lap_eq_cons_cons_inv in Heq; destruct Heq.
constructor; [ easy | now apply IHl₁ ].
Qed.

Theorem lap_eq_trans : transitive _ lap_eq.
Proof.
intros l₁ l₂ l₃ H₁ H₂.
...
revert l₁ l₃ H₁ H₂.
induction l₂ as [| x₂]; intros.
 revert l₃ H₂.
 induction l₁ as [| x₁]; intros; [ assumption | idtac ].
 destruct l₃ as [| x₃]; [ assumption | idtac ].
 apply lap_eq_cons_nil_inv in H₁.
 apply lap_eq_nil_cons_inv in H₂.
 constructor.
  etransitivity; [ destruct H₁; eassumption | idtac ].
  destruct H₂; symmetry; assumption.

  apply IHl₁; [ destruct H₁ | destruct H₂ ]; assumption.

 destruct l₁ as [| x₁].
  apply lap_eq_nil_cons_inv in H₁.
  destruct l₃ as [| x₃]; constructor.
   apply lap_eq_cons_inv in H₂.
   destruct H₁, H₂.
   etransitivity; [ symmetry; eassumption | assumption ].

   apply lap_eq_cons_inv in H₂.
   apply IHl₂; [ destruct H₁ | destruct H₂ ]; assumption.

  apply lap_eq_cons_inv in H₁.
  destruct l₃ as [| x₃]; constructor.
   apply lap_eq_cons_nil_inv in H₂.
   destruct H₁, H₂.
   etransitivity; eassumption.

   apply lap_eq_cons_nil_inv in H₂.
   apply IHl₂; [ destruct H₁ | destruct H₂ ]; assumption.

   apply lap_eq_cons_inv in H₂.
   apply IHl₂; [ destruct H₁ | destruct H₂ ]; assumption.
Qed.

Add Parametric Relation : (list α) lap_eq
 reflexivity proved by lap_eq_refl
 symmetry proved by lap_eq_sym
 transitivity proved by lap_eq_trans
 as lap_eq_rel.

...

Theorem pol_eq_iff : ∀ p1 p2,
  (p1 = p2)%pol ↔ ∀ i, (nth i (al p1) 0 = nth i (al p2) 0)%Rng.
Proof.
intros.
destruct p1 as [la].
destruct p2 as [lb].
unfold "="%pol; cbn.
(*
destruct (Nat.eq_dec mn 0) as [Hnz| Hnz]. {
  rewrite Hnz; cbn.
  split; intros Hll; [ easy | ].
  unfold "="%pol.
  clear Hll.
  revert lb.
  induction la as [| a la]; intros. {
    destruct lb as [| b lb]; [ easy | cbn ].
    rewrite Hnz; cbn.
    now apply forallb_forall.
  } {
    cbn; rewrite Hnz; cbn.
    destruct lb as [| b lb]; [ now apply forallb_forall | ].
    apply IHla.
  }
}
*)
split; intros Hll. {
  intros i.
  revert i lb Hll.
  induction la as [| a la]; intros. {
    cbn.
    destruct lb as [| b lb]; [ easy | cbn ].
Theorem glop : ∀ b lb, lap_eq [] (b :: lb) → (b = 0)%Rng ∧ lap_eq lb [].
Proof.
intros.
inversion H; subst.
easy.
Qed.
apply glop in Hll.
destruct i; [ easy | ].
destruct Hll as (_, Hll); symmetry.
clear - Hll.
revert i.
induction lb as [| b lb]; intros; [ now destruct i | cbn ].
...
symmetry in Hll.
destruct i.

...
(* find a solution not using inversion;
   need a lemma or lemmas dealing with it *)
...
    destruct i; [ now inversion Hll | symmetry ].
    inversion_clear Hll; subst.
    clear - H0.
    revert i.
    induction lb as [| b lb]; intros; [ now destruct i | ].
    cbn.
    destruct i; [ now inversion H0 | ].
    apply IHlb.
    now inversion H0.
  }
...
    unfold "="%pol in Hll.
    cbn in Hll.
    apply Bool.andb_true_iff in Hll.
    destruct Hll as (Hb, Hlb).
    apply Nat.eqb_eq in Hb.
    destruct i; [ now rewrite Hb, Nat.mod_0_l | ].
    specialize (proj1 (forallb_forall _ _) Hlb) as H1.
    cbn in H1.
    destruct (lt_dec i (length lb)) as [Hib| Hib]. {
      assert (H : nth i lb 0 ∈ lb) by now apply nth_In.
      specialize (H1 _ H); clear H.
      apply Nat.eqb_eq in H1.
      rewrite H1.
      now apply Nat.mod_0_l.
    } {
      apply Nat.nlt_ge in Hib.
      rewrite nth_overflow; [ | easy ].
      now rewrite Nat.mod_0_l.
    }
  } {
    cbn.
    destruct i. {
      destruct lb as [| b lb]. {
        unfold "="%pol in Hll.
        cbn in Hll |-*.
        apply Bool.andb_true_iff in Hll.
        destruct Hll as (Hb, Hlb).
        apply Nat.eqb_eq in Hb.
        rewrite Hb.
        now symmetry; apply Nat.mod_0_l.
      } {
        unfold "="%pol in Hll.
        cbn in Hll |-*.
        now destruct (Nat.eq_dec _ _).
      }
    } {
      destruct lb as [| b lb]. {
        unfold "="%pol in Hll.
        cbn in Hll |-*.
        apply Bool.andb_true_iff in Hll.
        destruct Hll as (Hb, Hlb).
        specialize (proj1 (forallb_forall _ _) Hlb) as H1.
        cbn in H1.
        destruct (lt_dec i (length la)) as [Hia| Hia]. {
          assert (H : nth i la 0 ∈ la) by now apply nth_In.
          specialize (H1 _ H); clear H.
          apply Nat.eqb_eq in H1.
          rewrite H1.
          now symmetry; apply Nat.mod_0_l.
        } {
          apply Nat.nlt_ge in Hia.
          rewrite nth_overflow; [ | easy ].
          now rewrite Nat.mod_0_l.
        }
      } {
        unfold "="%pol in Hll.
        cbn in Hll |-*.
        destruct (Nat.eq_dec _ _) as [H1| H1]; [ | easy ].
        now apply IHla.
      }
    }
  }
} {
  unfold "="%pol.
  revert lb Hll.
  induction la as [| a la]; intros. {
    cbn in Hll; cbn.
    assert (Hlb : ∀ i, nth i lb 0 ≡ 0 mod mn). {
      intros i; specialize (Hll i).
      now destruct i.
    }
    clear Hll.
    apply forallb_forall.
    intros b Hb.
    apply Nat.eqb_eq.
    apply (In_nth _ _ 0) in Hb.
    destruct Hb as (i & Hil & Hb).
    specialize (Hlb i).
    rewrite Hb in Hlb.
    rewrite Hlb.
    now apply Nat.mod_0_l.
  } {
    destruct lb as [| b lb]. {
      remember (a :: la) as l; cbn in Hll; subst l.
      assert (Hla : ∀ i, nth i (a :: la) 0 ≡ 0 mod mn). {
        intros i; specialize (Hll i).
        now destruct i.
      }
      clear Hll.
      apply forallb_forall.
      intros a1 Ha.
      apply Nat.eqb_eq.
      apply (In_nth _ _ 0) in Ha.
      destruct Ha as (i & Hil & Ha).
      specialize (Hla i).
      rewrite Ha in Hla.
      rewrite Hla.
      now apply Nat.mod_0_l.
    } {
      cbn.
      destruct (Nat.eq_dec _ _) as [Hab| Hab]. {
        apply IHla.
        intros i.
        now specialize (Hll (S i)).
      } {
        now specialize (Hll 0).
      }
    }
  }
}
Qed.

(*
... to be continued from "Formula.v"
*)

End Polynomials.
