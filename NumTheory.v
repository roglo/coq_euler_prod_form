Require Import Utf8 Arith.
Import List List.ListNotations.

(* Euler's totient function *)

Definition coprimes n := filter (λ d, Nat.gcd n d =? 1) (seq 1 (n - 1)).
Definition φ n := length (coprimes n).
