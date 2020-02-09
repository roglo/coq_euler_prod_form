(* Rpolynomial.v *)

(* polynomials on a ring *)

Require Import Utf8.
Require Import Arith.
Import List List.ListNotations.

(* ring *)

Class ring α :=
  { rng_zero : α;
    rng_one : α;
    rng_add : α → α → α;
    rng_opp : α → α }.

Declare Scope ring_scope.
Delimit Scope ring_scope with Rng.
Notation "1" := rng_one : ring_scope.
Notation "a + b" := (rng_add a b) : ring_scope.
Notation "- a" := (rng_opp a) : ring_scope.

(* lap : list as polynomial, i.e. the only field of the record in the
   definition of polynomial after *)

Definition lap_1 {A} {rng : ring A} := [1%Rng].

Fixpoint lap_add {A} {rng : ring A} al₁ al₂ :=
  match al₁ with
  | [] => al₂
  | a₁ :: bl₁ =>
      match al₂ with
      | [] => al₁
      | a₂ :: bl₂ => (a₁ + a₂)%Rng :: lap_add bl₁ bl₂
      end
  end.

Definition lap_opp {A} {rng : ring A} l := map (λ a, (- a)%Rng) l.
Definition lap_sub {A} {rng : ring A} la lb := lap_add la (lap_opp lb).

... to be continued from "Formula.v"
