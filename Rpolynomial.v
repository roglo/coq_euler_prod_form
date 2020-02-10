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

Add Parametric Relation A (r : ring A) : A rng_eq
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

Fixpoint lap_add al1 al2 :=
  match al1 with
  | [] => al2
  | a1 :: bl1 =>
      match al2 with
      | [] => al1
      | a2 :: bl2 => (a1 + a2)%Rng :: lap_add bl1 bl2
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

(*
Theorem lap_eq_refl : reflexive _ lap_eq.
Proof.
intros l.
induction l; constructor; [ reflexivity | assumption ].
Qed.

Theorem lap_eq_sym : symmetric _ lap_eq.
Proof.
intros l1 l2 Heq.
revert l2 Heq.
induction l1 as [| x1]; intros. {
  now induction l2; constructor; apply lap_eq_nil_cons_inv in Heq.
}
induction l2 as [| x2]. {
  apply lap_eq_cons_nil_inv in Heq.
  now constructor.
}
apply lap_eq_cons_cons_inv in Heq; destruct Heq.
constructor; [ easy | now apply IHl1 ].
Qed.

Theorem lap_eq_trans : transitive _ lap_eq.
Proof.
intros l1 l2 l3 H1 H2.
revert l1 l3 H1 H2.
induction l2 as [| x2]; intros. {
  revert l3 H2.
  induction l1 as [| x1]; intros; [ assumption | idtac ].
  destruct l3 as [| x3]; [ assumption | idtac ].
  apply lap_eq_cons_nil_inv in H1.
  apply lap_eq_nil_cons_inv in H2.
  constructor. {
    etransitivity; [ destruct H1; eassumption | idtac ].
    destruct H2; symmetry; assumption.
  } {
    apply IHl1; [ now destruct H1 | destruct H2 ].
    now apply lap_eq_sym.
  }
} {
  destruct l1 as [| x1]. {
    apply lap_eq_nil_cons_inv in H1.
    destruct l3 as [| x3]; constructor. {
      apply lap_eq_cons_cons_inv in H2.
      destruct H1, H2.
      etransitivity; [ symmetry; eassumption | assumption ].
    } {
      apply lap_eq_cons_cons_inv in H2.
      apply IHl2; [ destruct H1 | now destruct H2 ].
      now apply lap_eq_sym.
    }
  } {
    apply lap_eq_cons_cons_inv in H1.
    destruct l3 as [| x3]; constructor. {
      apply lap_eq_cons_nil_inv in H2.
      destruct H1, H2.
      etransitivity; eassumption.
    } {
      apply lap_eq_cons_nil_inv in H2.
      apply IHl2; [ destruct H1 | destruct H2 ]; assumption.
    } {
      apply lap_eq_cons_cons_inv in H2.
      etransitivity; [ apply H1 | apply H2 ].
    } {
      apply IHl2; [ easy | ].
      now apply lap_eq_cons_cons_inv in H2.
    }
  }
}
Qed.

Add Parametric Relation : (list A) lap_eq
 reflexivity proved by lap_eq_refl
 symmetry proved by lap_eq_sym
 transitivity proved by lap_eq_trans
 as lap_eq_rel.
*)

Theorem pol_eq_iff : ∀ p1 p2,
  (p1 = p2)%pol ↔ ∀ i, (nth i (al p1) 0 = nth i (al p2) 0)%Rng.
Proof.
intros.
destruct p1 as [la].
destruct p2 as [lb].
unfold "="%pol; cbn.
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

Theorem pol_eq_refl : reflexive _ pol_eq.
Proof.
intros p.
unfold "="%pol.
remember (al p) as la; clear p Heqla.
now induction la; constructor.
Qed.

Theorem pol_eq_sym : symmetric _ pol_eq.
Proof.
intros p1 p2 Hll.
specialize (proj1 (pol_eq_iff _ _) Hll) as H1.
clear Hll.
apply pol_eq_iff.
intros i; symmetry.
apply H1.
Qed.

(*
... to be continued from "Formula.v"
*)

End Polynomials.
