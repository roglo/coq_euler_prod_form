(* Euler's four square identity *)

From Stdlib Require Import Utf8 ZArith.

Definition Z_Euler_s_four_square_sol a b c d p q r s :=
  (a * p + b * q + c * r + d * s,
   a * q + d * r - (b * p + c * s),
   a * r + b * s - (c * p + d * q),
   a * s + c * q - (b * r + d * p))%Z.

Theorem Z_Euler_s_four_square_identity : ∀ a b c d p q r s,
  let '(x, y, z, t) := Z_Euler_s_four_square_sol a b c d p q r s in
  ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2))%Z =
  (x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2)%Z.
Proof.
intros.
unfold Z_Euler_s_four_square_sol.
ring.
Qed.
