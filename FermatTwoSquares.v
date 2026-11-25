Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith(* Init.Nat*).
Import List ListNotations.

Require Import Misc Primes.

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

Definition prime_decomp_with_power n := list_regroup Nat.eqb (prime_decomp n).

(* to be completed
Theorem Fermat_two_squares_any :
  ∀ n,
  (∀ p k, (p, k) ∈ prime_decomp_with_power n → p mod 4 ≠ 3 ∨ Nat.Even k)
  ↔ ∃ a b, n = a² + b².
...

Theorem Fermat_two_squares :
  ∀ p, prime p → p mod 4 = 1 → ∃! a b, (p = a² + b²).

*)
