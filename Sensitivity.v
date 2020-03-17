(* Sensitivity Theorem.
   https://arxiv.org/pdf/1907.00847.pdf
   https://eccc.weizmann.ac.il/report/2020/002/?fbclid=IwAR19mpxfIuoSaWq3HO8MdV8i8x_xlvwMKHjfElzBUK0GditlyaLeJiC8gJY *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Misc.

(* adjacent vertices of a cube graph in any dimension;
   a vertex is represented by a natural number. *)

Fixpoint are_adj_vert_loop it a b :=
  match it with
  | 0 => false
  | S it' =>
      if Nat.eq_dec (a mod 2) (b mod 2) then
        are_adj_vert_loop it' (a / 2) (b / 2)
      else
        if Nat.eq_dec (a / 2) (b / 2) then true else false
  end.

Definition are_adjacent_vertices a b :=
  are_adj_vert_loop (max a b) a b.

Compute (let n := 3 in map (λ a, (a, filter (are_adjacent_vertices a) (seq 0 (2^n)))) (seq 0 (2^n))).

(* subgraph of the n-dimensional cube graph *)

Definition subgraph_prop n vl :=
  ∀ a b, (a, b) ∈ vl →
  a < b < 2 ^ n ∧ are_adjacent_vertices a b = true.

Record subgraph n := mksg
  { sg_vert : list (nat * nat);
    sg_prop : subgraph_prop n sg_vert }.

Arguments sg_vert {n}.

Definition number_of_vertices {n} (sg : subgraph n) := length (sg_vert sg).

(* degree of a vertex = number of edges adjacents to the vertex *)

Definition vdeg vl v :=
  count_occ Bool.bool_dec (map (λ '(a, b), Nat.eqb a v) vl) true +
  count_occ Bool.bool_dec (map (λ '(a, b), Nat.eqb v b) vl) true.

Definition deg {n} (sg : subgraph n) v := vdeg (sg_vert sg) v.

(* Δ : maximum degree of a subgraph *)

Definition vΔ n vl :=
  fold_left (λ m v, max m (vdeg vl v)) (seq 0 (2 ^ n - 1)) 0.

Definition Δ {n} (sg : subgraph n) := vΔ n (sg_vert sg).

(* testing... *)

Definition cube_vert :=
  [(0, 1); (0, 2); (0, 4); (1, 3); (1, 5); (2, 3); (2, 6);
   (3, 7); (4, 5); (4, 6); (5, 7); (6, 7)].
Definition cube_prop : subgraph_prop 3 cube_vert.
Proof.
intros a b Hab.
unfold cube_vert in Hab.
cbn in Hab.
do 12 (destruct Hab as [H| Hab]; [
  injection H; clear H; intros; subst; cbn;
  split; [ flia | easy ] | ]).
easy.
Qed.

Definition full_cube := mksg 3 cube_vert cube_prop.

Compute (Δ full_cube, Nat.sqrt 3).
Compute (2 ^ (3 - 1) + 1).

Compute (length cube_vert).

Compute (vdeg cube_vert 0).
Compute (vdeg (map (λ i, nth i cube_vert (0, 0)) [0; 3; 6]) 0).
Compute (vdeg (map (λ i, nth i cube_vert (0, 0)) [0; 3; 6]) 3).
Compute (vdeg (map (λ i, nth i cube_vert (0, 0)) [0; 3; 6]) 6).
Compute (vΔ 3 (map (λ i, nth i cube_vert (0, 0)) [0; 3; 6])).

(* ah merde, ça déconne *)

...

(* The theorem *)

Theorem sensitivity : ∀ n (sg : subgraph n),
  number_of_vertices sg = 2 ^ (n - 1) + 1
  → Δ sg ≥ Nat.sqrt n.
Proof.
...
