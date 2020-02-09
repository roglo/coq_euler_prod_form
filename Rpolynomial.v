(* Rpolynomial.v *)

(* polynomials on a ring *)

Require Import Utf8.
Require Import Arith.
Import List List.ListNotations.

(* ring *)

Class ring A :=
  { rng_zero : A;
    rng_one : A;
    rng_add : A → A → A;
    rng_mul : A → A → A;
    rng_opp : A → A;
    rng_eq : A → A → Prop }.

Declare Scope ring_scope.
Delimit Scope ring_scope with Rng.
Bind Scope ring_scope with ring.
Notation "0" := rng_zero : ring_scope.
Notation "1" := rng_one : ring_scope.
Notation "a + b" := (rng_add a b) : ring_scope.
Notation "a * b" := (rng_mul a b) : ring_scope.
Notation "- a" := (rng_opp a) : ring_scope.

Notation "'Σ' ( i = b , e ) , g" :=
  (fold_left (λ c i, (c + g)%Rng) (seq b (S e - b)) 0%Rng)
  (at level 45, i at level 0, b at level 60, e at level 60) : ring_scope.

Section Polynomials.

Variable A : Type.
Variable rng : ring A.

Record polynomial := mkpol { al : list A }.

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

...

Definition lap_convol_mul_term la lb i :=
  (Σ (j = 0, i), List.nth j la 0 * List.nth (i - j)%nat lb 0)%Rng.
Definition polm_mul la lb :=
  map (lap_convol_mul_term la lb) (seq 0 (length la + length lb - 1)).

Definition xpow i := repeat 0%Rng i ++ [1%Rng].

Inductive lap_zerop : list A → Prop :=
  | lap_nil : lap_zerop []
  | lap_cons : ∀ a la, rng_eq a 0%Rng → lap_zerop la → lap_zerop (a :: la).

Definition lap_eq la lb := lap_zerop (lap_sub la lb).

Declare Scope lap_scope.
Delimit Scope lap_scope with pol.
Bind Scope lap_scope with list A.
Notation "1" := lap_1 : polm_scope.
...
Notation "- a" := (polm_opp a) : polm_scope.
Notation "a + b" := (polm_add a b) : polm_scope.
Notation "a - b" := (polm_sub a b) : polm_scope.
Notation "a * b" := (polm_mul a b) : polm_scope.
Notation "a = b" := (polm_eq a b) : polm_scope.
Notation "'ⓧ' ^ a" := (xpow a) (at level 30, format "'ⓧ' ^ a") : polm_scope.
Notation "'ⓧ'" := (xpow 1) (at level 30, format "'ⓧ'") : polm_scope.

(*
... to be continued from "Formula.v"
*)

End Lap.
