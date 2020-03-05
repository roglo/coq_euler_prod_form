(* Euler's four square identity *)

Require Import Utf8 ZArith Psatz.
Require Import Misc.

Definition Z_diff x y := (x - y)%Z.

Theorem Z_Euler_s_four_square_identity_v2 : ∀ a b c d p q r s,
  ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2))%Z =
     ((a * p + b * q + c * r + d * s) ^ 2 +
      Z_diff (a * q + d * r) (b * p + c * s) ^ 2 +
      Z_diff (a * r + b * s) (c * p + d * q) ^ 2 +
      Z_diff (a * s + c * q) (b * r + d * p) ^ 2)%Z.
Proof.
intros.
unfold Z_diff.
ring.
Qed.

Definition diff x y := if lt_dec x y then y - x else x - y.

Ltac Z_ring_for_Euler_v1 H1 H2 H3 H4 :=
  apply Nat2Z.inj_iff;
  rewrite Nat2Z.inj_mul;
  do 9 rewrite Nat2Z.inj_add;
  do 12 rewrite Nat2Z.inj_mul;
  do 12 rewrite <- Z.pow_2_r;
  rewrite Nat2Z.inj_sub; [ | flia H1 ];
  rewrite Nat2Z.inj_sub; [ | flia H2 ];
  rewrite Nat2Z.inj_sub; [ | flia H3 ];
  rewrite Nat2Z.inj_sub; [ | flia H4 ];
  repeat rewrite Nat2Z.inj_add;
  repeat rewrite Nat2Z.inj_mul;
  ring.

Theorem Euler_s_four_square_identity_v1 : ∀ a1 a2 a3 a4 b1 b2 b3 b4,
  (a1 ^ 2 + a2 ^ 2 + a3 ^ 2 + a4 ^2) * (b1 ^ 2 + b2 ^ 2 + b3 ^ 2 + b4 ^ 2) =
     diff (a1 * b1) (a2 * b2 + a3 * b3 + a4 * b4) ^ 2 +
     diff (a1 * b2 + a2 * b1 + a3 * b4) (a4 * b3) ^ 2 +
     diff (a1 * b3 + a3 * b1 + a4 * b2) (a2 * b4) ^ 2 +
     diff (a1 * b4 + a2 * b3 + a4 * b1) (a3 * b2) ^ 2.
Proof.
intros.
unfold diff.
do 12 rewrite Nat.pow_2_r.
destruct (lt_dec (a1 * b1) (a2 * b2 + a3 * b3 + a4 * b4)) as [H1| H1]. {
  destruct (lt_dec (a1 * b2 + a2 * b1 + a3 * b4) (a4 * b3)) as [H2| H2]. {
    destruct (lt_dec (a1 * b3 + a3 * b1 + a4 * b2) (a2 * b4)) as [H3| H3]. {
      destruct (lt_dec (a1 * b4 + a2 * b3 + a4 * b1) (a3 * b2)) as [H4| H4]. {
        lia.
      } {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      }
    } {
      destruct (lt_dec (a1 * b4 + a2 * b3 + a4 * b1) (a3 * b2)) as [H4| H4]. {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      } {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      }
    }
  } {
    destruct (lt_dec (a1 * b3 + a3 * b1 + a4 * b2) (a2 * b4)) as [H3| H3]. {
      destruct (lt_dec (a1 * b4 + a2 * b3 + a4 * b1) (a3 * b2)) as [H4| H4]. {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      } {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      }
    } {
      destruct (lt_dec (a1 * b4 + a2 * b3 + a4 * b1) (a3 * b2)) as [H4| H4]. {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      } {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      }
    }
  }
} {
  destruct (lt_dec (a1 * b2 + a2 * b1 + a3 * b4) (a4 * b3)) as [H2| H2]. {
    destruct (lt_dec (a1 * b3 + a3 * b1 + a4 * b2) (a2 * b4)) as [H3| H3]. {
      destruct (lt_dec (a1 * b4 + a2 * b3 + a4 * b1) (a3 * b2)) as [H4| H4]. {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      } {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      }
    } {
      destruct (lt_dec (a1 * b4 + a2 * b3 + a4 * b1) (a3 * b2)) as [H4| H4]. {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      } {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      }
    }
  } {
    destruct (lt_dec (a1 * b3 + a3 * b1 + a4 * b2) (a2 * b4)) as [H3| H3]. {
      destruct (lt_dec (a1 * b4 + a2 * b3 + a4 * b1) (a3 * b2)) as [H4| H4]. {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      } {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      }
    } {
      destruct (lt_dec (a1 * b4 + a2 * b3 + a4 * b1) (a3 * b2)) as [H4| H4]. {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      } {
        Z_ring_for_Euler_v1 H1 H2 H3 H4.
      }
    }
  }
}
Qed.

Ltac Z_ring_for_Euler_v2 H1 H2 H3 :=
  apply Nat2Z.inj_iff;
  rewrite Nat2Z.inj_mul;
  do 9 rewrite Nat2Z.inj_add;
  do 12 rewrite Nat2Z.inj_mul;
  do 12 rewrite <- Z.pow_2_r;
  rewrite Nat2Z.inj_sub; [ | flia H1 ];
  rewrite Nat2Z.inj_sub; [ | flia H2 ];
  rewrite Nat2Z.inj_sub; [ | flia H3 ];
  do 9 rewrite Nat2Z.inj_add;
  do 16 rewrite Nat2Z.inj_mul;
  do 12 rewrite Z.pow_2_r;
  ring.

Theorem Euler_s_four_square_identity_v2 : ∀ a b c d p q r s,
  (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) =
     (a * p + b * q + c * r + d * s) ^ 2 +
     diff (a * q + d * r) (b * p + c * s) ^ 2 +
     diff (a * r + b * s) (c * p + d * q) ^ 2 +
     diff (a * s + c * q) (b * r + d * p) ^ 2.
Proof.
intros.
unfold diff.
do 12 rewrite Nat.pow_2_r.
destruct (lt_dec (a * q + d * r) (b * p + c * s)) as [H1| H1]. {
  destruct (lt_dec (a * r + b * s) (c * p + d * q)) as [H2| H2]. {
    destruct (lt_dec (a * s + c * q) (b * r + d * p)) as [H3| H3]. {
      lia.
    } {
      Z_ring_for_Euler_v2 H1 H2 H3.
    }
  } {
    destruct (lt_dec (a * s + c * q) (b * r + d * p)) as [H3| H3]. {
      Z_ring_for_Euler_v2 H1 H2 H3.
    } {
      Z_ring_for_Euler_v2 H1 H2 H3.
    }
  }
} {
  destruct (lt_dec (a * r + b * s) (c * p + d * q)) as [H2| H2]. {
    destruct (lt_dec (a * s + c * q) (b * r + d * p)) as [H3| H3]. {
      Z_ring_for_Euler_v2 H1 H2 H3.
    } {
      Z_ring_for_Euler_v2 H1 H2 H3.
    }
  } {
    destruct (lt_dec (a * s + c * q) (b * r + d * p)) as [H3| H3]. {
      Z_ring_for_Euler_v2 H1 H2 H3.
    } {
      Z_ring_for_Euler_v2 H1 H2 H3.
    }
  }
}
Qed.

(*
with ε = - 1
Theorem Euler_s_four_square_identity_v3 : ∀ a b c d p q r s ε,
  (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) =
     (a * p + b * q + c * r + d * s) ^ 2 +
     (a * q - b * p - ε * c * s + ε * d * r) ^ 2 +
     (a * r + ε * b * s - c * p - ε * d * q) ^ 2 +
     (a * s - ε * b * r + ε * c * q - d * p) ^ 2.
Proof.
intros.
unfold diff.
do 12 rewrite Nat.pow_2_r.
*)
