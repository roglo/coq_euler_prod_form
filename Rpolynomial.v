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
    rng_mul : α → α → α;
    rng_opp : α → α }.

Declare Scope ring_scope.
Delimit Scope ring_scope with Rng.
Notation "0" := rng_zero : ring_scope.
Notation "1" := rng_one : ring_scope.
Notation "a + b" := (rng_add a b) : ring_scope.
Notation "a * b" := (rng_mul a b) : ring_scope.
Notation "- a" := (rng_opp a) : ring_scope.

Notation "'Σ' ( i = b , e ) , g" :=
  (fold_left (λ c i, (c + g)%Rng) (seq b (S e - b)) 0%Rng)
  (at level 45, i at level 0, b at level 60, e at level 60) : ring_scope.

(* lap : list as polynomial, i.e. the only field of the record in the
   definition of polynomial after *)

Section Lap.

Variable A : Type.
Variable rng : ring A.

Definition lap_1 := [1%Rng].

Fixpoint lap_add al₁ al₂ :=
  match al₁ with
  | [] => al₂
  | a₁ :: bl₁ =>
      match al₂ with
      | [] => al₁
      | a₂ :: bl₂ => (a₁ + a₂)%Rng :: lap_add bl₁ bl₂
      end
  end.

Definition lap_opp l := map (λ a, (- a)%Rng) l.
Definition lap_sub la lb := lap_add la (lap_opp lb).

Definition lap_convol_mul_term la lb i :=
  (Σ (j = 0, i), List.nth j la 0 * List.nth (i - j)%nat lb 0)%Rng.
Definition polm_mul la lb :=
  map (lap_convol_mul_term la lb) (seq 0 (length la + length lb - 1)).

Definition xpow i := repeat 0%Rng i ++ [1%Rng].

(*
... to be continued from "Formula.v"
*)

