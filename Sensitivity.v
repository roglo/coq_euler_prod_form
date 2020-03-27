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

Record subgraph := mksg { sg_vert : list nat }.

Definition edges vl :=
  fold_right
    (λ a l,
     fold_right
       (λ b l,
        if lt_dec a b then
          if are_adjacent_vertices a b then (a, b) :: l else l
        else l) l vl)
    [] (nodup Nat.eq_dec vl).

Compute (edges [1; 2; 7; 4]).

Definition sg_edges sg := edges (sg_vert sg).

(* Example *)

Definition cube_vert := seq 0 (2 ^ 3).
Definition full_cube := mksg cube_vert.

(* edges and vertices count *)

Definition number_of_edges sg := length (sg_edges sg).
Definition number_of_vertices sg := length (sg_vert sg).
Compute (number_of_edges full_cube).
Compute (number_of_vertices full_cube).

(* degree of a vertex = number of edges adjacents to the vertex *)

Definition vdeg el v :=
  count_occ Bool.bool_dec (map (λ '(a, b), Nat.eqb a v) el) true +
  count_occ Bool.bool_dec (map (λ '(a, b), Nat.eqb v b) el) true.

Definition deg sg v := vdeg (sg_edges sg) v.

(* Δ : maximum degree of a subgraph *)

Definition vΔ vl :=
  let el := edges vl in
  fold_left (λ m v, max m (vdeg el v)) vl 0.

Compute (vΔ [0; 1; 0]).
Compute (edges [0; 1; 0]).

Compute (vΔ [0; 1; 2; 4; 0]).
Compute (vdeg (edges [0; 1; 2; 4]) 0).

Definition Δ sg := vΔ (sg_vert sg).

(* sensitivity *)

Search (nat → nat → nat).

Definition Nat_togglebit x i :=
  if Nat.testbit x i then Nat.clearbit x i else Nat.setbit x i.

Definition flip x S := fold_right Nat_togglebit x S.

Notation "x ^^ S" := (flip x S) (at level 30).

Definition loc_sens_list n (f : nat → bool) x :=
  filter (λ i, negb (Bool.eqb (f x) (f (x ^^ [i])))) (seq 0 n).

Definition local_sensitivity (n : nat) (f : nat → bool) (x : nat) :=
  length (loc_sens_list n f x).

Definition sensitivity n f :=
  fold_right max 0 (map (local_sensitivity n f) (seq 0 (2 ^ n))).

(* Hamming distance *)

Fixpoint cnt_1_loop it n :=
  match it with
  | 0 => 0
  | S it' =>
      if Nat.eq_dec (n mod 2) 1 then 1 + cnt_1_loop it' (n / 2)
      else cnt_1_loop it' (n / 2)
  end.

Definition count_ones n := cnt_1_loop n n.

Definition Hamming_distance x y := count_ones (Nat.lxor x y).

(* To define local_block_sensitivity later, we need an algorithm to
   generate all lists of disjoint blocks *)

Fixpoint next_in_radix n dl :=
  match dl with
  | [] => [1]
  | d :: dl' =>
      if lt_dec (d + 1) n then (d + 1) :: dl'
      else 0 :: next_in_radix n dl'
  end.

Fixpoint count_in_radix n start len :=
  match len with
  | 0 => []
  | S len' => start :: count_in_radix n (next_in_radix n start) len'
  end.

Definition count_upto_n_to_n n :=
  map (@rev nat) (count_in_radix n (repeat 0 n) (n ^ n)).

Compute (count_upto_n_to_n 3).

Definition set_nth {A} i (l : list A) v :=
  firstn i l ++ v :: skipn (i + 1) l.

Definition is_nil {A} (l : list A) :=
  match l with
  | [] => true
  | _ => false
  end.

Fixpoint disp_loop n i v r :=
  match i with
  | 0 => r
  | S i' =>
      disp_loop n i' (v / n) (set_nth (v mod n) r (i' :: nth (v mod n) r []))
  end.

Definition dispatch n i := disp_loop n n i (repeat [] n).

Definition raw_partitions n := map (dispatch n) (seq 0 (n ^ n)).

Compute (raw_partitions 4).

Fixpoint list_nat_le la lb :=
  match (la, lb) with
  | ([], _) => true
  | (_, []) => false
  | (a :: la', b :: lb') =>
      match a ?= b with
      | Eq => list_nat_le la' lb'
      | Lt => true
      | Gt => false
      end
  end.

Fixpoint list_list_nat_le lla llb :=
  match (lla, llb) with
  | ([], _) => true
  | (_, []) => false
  | (la :: lla', lb :: llb') =>
      if list_nat_le la lb then
        if list_nat_le lb la then list_list_nat_le lla' llb'
        else true
      else false
  end.

Definition all_partitions n :=
  bsort list_list_nat_le
    (nodup (list_eq_dec (list_eq_dec Nat.eq_dec))
       (map (bsort list_nat_le)
          (map (filter (λ s, negb (is_nil s))) (raw_partitions n)))).

Compute (map (bsort list_nat_le) (raw_partitions 4)).
Compute (nodup (list_eq_dec (list_eq_dec Nat.eq_dec)) (map (bsort list_nat_le) (raw_partitions 4))).
Compute (all_partitions 4).

(* Local block sensitivity *)

Definition loc_bl_sens_list Bl f x :=
  filter (λ Bi, negb (Bool.eqb (f x) (f (x ^^ Bi)))) Bl.

Definition local_block_sensitivity n f x :=
  fold_right max 0
    (map (λ Bl, length (loc_bl_sens_list Bl f x)) (raw_partitions n)).

Definition block_sensitivity n f :=
  fold_right max 0 (map (local_block_sensitivity n f) (seq 0 (2 ^ n))).

(* Proving Theorem: bs(f) ≥ s(f) *)

Require Import Sorting.

(* property of partitions of {0,1,..,n-1} returned by raw_partitions *)
Definition is_partition n p :=
  length p = n ∧
  (∀ s, s ∈ p → ∀ i, i ∈ s → i < n) ∧
  (∀ i, i < n → ∃ s, s ∈ p ∧ i ∈ s) ∧
  NoDup (concat p).

Theorem is_partition_iff : ∀ n p, n ≠ 0 →
  is_partition n p ↔ p ∈ raw_partitions n.
Proof.
intros * Hnz.
split; intros Hn. {
  destruct Hn as (Hel & Hne & Hu & Hi).
  unfold raw_partitions.
Print dispatch.
Compute (raw_partitions 3).
Compute (all_partitions 3).
(* perhaps I could write a function that, from a given partition p
   having property "is_partition", returns its rank in the list
   raw_partitions(n)? *)
Fixpoint find_in_nth_loop {A} (mem : A → list A → bool) a ll i :=
  match ll with
  | [] => i
  | l :: ll' => if mem a l then i else find_in_nth_loop mem a ll' (i + 1)
  end.
Definition find_in_nth {A} mem a ll := @find_in_nth_loop A mem a ll 0.
Fixpoint nat_in_list i l :=
  match l with
  | [] => false
  | j :: l' => if Nat.eq_dec i j then true else nat_in_list i l'
  end.
Compute (find_in_nth nat_in_list 0 [[]; [0; 2]; [1]]).
Compute (find_in_nth nat_in_list 1 [[]; [0; 2]; [1]]).
Compute (find_in_nth nat_in_list 2 [[]; [0; 2]; [1]]).
Compute (find_in_nth nat_in_list 3 [[]; [0; 2]; [1]]).
...

Theorem length_loc_loc_bl_sens_list : ∀ n f x,
  length (loc_sens_list n f x) =
  length (loc_bl_sens_list (map (λ i, [i]) (seq 0 n)) f x).
Proof.
intros.
unfold loc_sens_list.
unfold loc_bl_sens_list.
cbn; unfold "^^"; cbn.
remember 0 as s eqn:Hs; clear Hs.
revert s.
induction n; intros s; cbn; [ easy | ].
remember (negb (Bool.eqb (f x) (f (Nat_togglebit s x)))) as b eqn:Hb.
symmetry in Hb.
destruct b; [ cbn; f_equal; apply IHn | apply IHn ].
Qed.

Theorem loc_length_loc_bl_sens_list : ∀ n f x,
  local_sensitivity n f x =
  length (loc_bl_sens_list (map (λ i, [i]) (seq 0 n)) f x).
Proof.
intros.
apply length_loc_loc_bl_sens_list.
Qed.

Theorem map_loc_sens : ∀ n f l,
  map (local_sensitivity n f) l =
  map (λ x, length (loc_bl_sens_list (map (λ i, [i]) (seq 0 n)) f x)) l.
Proof.
intros.
induction l; cbn; [ easy | ].
rewrite <- loc_length_loc_bl_sens_list; f_equal.
apply IHl.
Qed.

Theorem bs_ge_s : ∀ n f, block_sensitivity n f ≥ sensitivity n f.
Proof.
intros.
unfold block_sensitivity, sensitivity.
rewrite map_loc_sens.
unfold local_block_sensitivity.
Print loc_bl_sens_list.
Abort. (*
...
unfold local_block_sensitivity, local_sensitivity.
...
*)

(* chais pas si c'est vrai, ça, mais si ça l'est, ça implique le
   truc ci-dessus *)
Theorem x_bs_ge_s : ∀ n f x,
  local_block_sensitivity n f x ≥ local_sensitivity n f x.
Proof.
intros.
rewrite loc_length_loc_bl_sens_list.
unfold local_block_sensitivity.
(* among all partitions, there must exist one which is exactly
    [[0]; [1]; [2]; ... ; [n-1]]
   I believe it is this one which corresponds to local_sensitivity *)
assert (H : map (λ i, [i]) (seq 0 n) ∈ raw_partitions n). {
  unfold raw_partitions.
  assert (H1 : is_partition n (map (λ i, [i]) (seq 0 n))). {
    split. {
      rewrite map_length.
      now rewrite seq_length.
    }
    split. {
      intros s Hs i Hi.
      apply in_map_iff in Hs.
      destruct Hs as (j & Hjn & Hjs); subst s.
      apply in_seq in Hjs.
      destruct Hi as [Hi| ]; [ now subst j | easy ].
    }
    split. {
      intros j Hjn.
      exists [j].
      split; [ | now left ].
      apply in_map_iff.
      exists j.
      split; [ easy | ].
      apply in_seq.
      split; [ | easy ].
      flia.
    } {
      clear x.
      remember 0 as s; clear Heqs.
      revert s.
      induction n; intros s; [ constructor | cbn ].
      constructor; [ | apply IHn ].
      intros H.
      rewrite <- flat_map_concat_map in H.
      apply in_flat_map in H.
      destruct H as (x & Hx & Hsx).
      apply in_seq in Hx.
      destruct Hsx as [Hsx| ]; [ | easy ].
      subst x; flia Hx.
    }
  }
...
  now is_partition_iff (proj1 (H2 _) H1) as H3.
}
*)
  idtac.
Compute (nth 27 (raw_partitions 4) []).
...
1→0 = 0 radix 1
2→1 = 01 radix 2
3→5 = 012 radix 3
4→27 = 0123 radix 4
1*n^2 + 2*n^1 + 3*n^0
(n-1)n^0+(n-2)n^1+(n-3)^n^2+...+1*n^(n-2)+0*n^(n-1)
  Σ (i=0,n-1) i*n^(n-1-i)
= Σ (i=0,n-1) (n-1-i)*n^i

map (λ i, [i]) (seq 0 n) = nth ... (raw_partitions n) []
...
}
apply in_split in H.
destruct H as (l1 & l2 & Hll).
rewrite Hll.
(* prove that the "map (λ i, [i]) (seq 0 n)" has the maximum length *)
...
(* previous attempt to prove
    map (λ i, [i]) (seq 0 n) ∈ raw_partitions n *)
  unfold raw_partitions.
  assert (H : map (λ i, [i]) (seq 0 n) = dispatch n (seq 0 n)). {
    unfold dispatch.
    rewrite List_filter_all_true. 2: {
      intros a Ha.
      clear - Ha.
      destruct a; [ exfalso | easy ].
      assert (H : ∀ i s n r, length r = n → [] ∉ disp_loop i (seq s n) r). {
        clear.
        intros i s n r Hr Ha.
        revert i s r Hr Ha.
        induction n; intros i s r Hr Ha. {
          now apply length_zero_iff_nil in Hr; subst r.
        }
        cbn in Ha.
...
destruct n. {
  cbn in Ha.
  destruct r as [| r1]; [ easy | ].
  destruct r; [ | easy ].
  cbn in Ha.
  destruct s. {
    cbn in Ha.
    now destruct Ha.
  }
  cbn in Ha.
  destruct Ha as [Ha| Ha]. {
...
  unfold set_nth in Ha.
...
        specialize (IHn (i + 1) (S s)) as H1.
        specialize (H1 (set_nth s r (i :: nth s r []))).
...
        assert (H : length (set_nth s r (i :: nth s r [])) = n). {
Print set_nth.
Theorem glop {A} : ∀ i (l : list A) v, length (set_nth i l v) = length l.
Proof.
intros.
revert i v.
induction l as [| a]; intros. {
  cbn.
  unfold set_nth.
(* ouais non c'est faux *)
...
rewrite glop.
...

        destruct r as [| a]; [ easy | ].
        cbn in Hr.
        apply Nat.succ_inj in Hr.
        specialize (IHn (i + 1) (S s) r Hr) as H1.
Print set_nth.
...
      assert
        (H : ∀ s n r1 r2,
         (∀ l, l ∈ r1 → l ≠ [])
         → length r2 = n
         → [] ∉ disp_loop s (seq s n) (r1 ++ r2)). {
        clear.
        intros s * Hr1 Hr2 Ha.
        revert s r1 r2 Hr1 Hr2 Ha.
        induction n; intros s *; intros. {
          cbn in Ha.
          apply length_zero_iff_nil in Hr2; subst r2.
          rewrite app_nil_r in Ha.
          now specialize (Hr1 _ Ha).
        }
        cbn in Ha.
        destruct r2 as [| a r2]; [ easy | ].
        cbn in Hr2.
        apply Nat.succ_inj in Hr2.
        specialize (IHn (S n) r1 r2 Hr1 Hr2) as H1.
...
      destruct n; [ easy | ].
      cbn in Ha.
      destruct n; [ now destruct Ha | ].
      cbn in Ha.
  Ha : [] ∈ disp_loop 0 (seq 0 n) (repeat [] n)
  Ha : [] ∈ disp_loop 1 (seq 1 n) ([0] :: repeat [] n)
  Ha : [] ∈ disp_loop 2 (seq 2 n) ([0] :: [1] :: repeat [] n)
      destruct n. {
        cbn in Ha.

      cbn in Ha.
...
      assert (H : ∀ i l a r, [] ∉ disp_loop i l (a :: r)). {
        clear.
        intros * Ha.
        revert i a r Ha.
        induction l as [| b l]; intros.
cbn in Ha.

    induction n; [ easy | ].
    rewrite <- Nat.add_1_r.
    rewrite seq_app.
    rewrite map_app.
    rewrite IHn.
    rewrite Nat.add_0_l.
    rewrite disp_loop_app.
    rewrite seq_length, Nat.add_0_l.
Print dispatch.
...
    replace (repeat [] (n + 1)) with (repeat ([] : list nat) n ++ [[]]). 2: {
      clear.
      induction n; [ easy | cbn ].
      now rewrite IHn.
    }
    cbn.
Print disp_loop.
...
    rewrite disp_loop_app.
...

Theorem bs_ge_s : ∀ n f, bs n f ≥ s n f.
Proof.
intros.
unfold bs, s.
unfold block_sensitivity, sensitivity.
...

(* testing... *)

Compute (Δ full_cube, Nat.sqrt 3).
Compute (2 ^ (3 - 1) + 1).

Compute (length (sg_edges full_cube)).
Compute (vdeg (edges cube_vert) 0).

Compute (edges [1; 2; 4; 7]).
Compute (length (edges [1; 2; 4; 7])).
Compute (2 ^ (3 - 1) + 1).

Compute (vΔ [0; 1; 4; 5; 7]).
Compute (edges [0; 1; 4; 5; 7]).

Compute (edges [0; 3; 5; 6; 9; 10; 12; 15]).
Compute (vΔ [0; 3; 5; 6; 9; 10; 12; 15]).
Compute (2 ^ (4 - 1) + 1).
Compute (Nat.sqrt 4).
Compute (let n := 4 in 2 ^ (n - 1) + 1).
Compute (map (λ i, vΔ [0; 3; 5; 6; 9; 10; 12; 15; i]) (seq 0 16)).
Compute (let n := 4 in Nat.sqrt n).
Compute (let n := 3 in 2 ^ (n - 1) + 1).
Compute (map (λ i, (i, vΔ [0; 3; 5; 6; i])) (seq 0 8)).
Compute (let n := 3 in Nat.sqrt n).

Compute (edges [0; 3; 5; 6]).
Compute (edges [0; 3; 5; 6; 2]).
Compute (vdeg (edges [0; 3; 5; 6; 1])) 1.

Compute (Nat.sqrt 5).
Compute (let n := 5 in 2 ^ (n - 1) + 1).
Compute (length [0; 3; 5; 6; 9; 10; 12; 15; 17; 18; 20; 23; 24; 27; 29; 30]).
Compute (edges [0; 3; 5; 6; 9; 10; 12; 15; 17; 18; 20; 23; 24; 27; 29; 30]).
Compute (map (λ i, vΔ [0; 3; 5; 6; 9; 10; 12; 15; 17; 18; 20; 23; 24; 27; 29; 30; i]) (seq 0 32)).

Compute (Nat.sqrt 4).
Compute (let n := 4 in 2 ^ (n - 1) + 1). (* 9 *)
Compute (length [0; 3; 5; 6; 9; 10; 12; 15]).
Compute (edges [0; 3; 5; 6; 9; 10; 12; 15]).
Compute (map (λ i, vΔ [0; 3; 5; 6; 9; 10; 12; 15; i]) (seq 0 16)).

Compute (vΔ [0; 1; 6; 7; 10; 11; 12; 13]).
Compute (map (λ i, vΔ [0; 1; 6; 7; 10; 11; 12; 13; i]) (seq 0 16)).

Compute (Nat.sqrt 2).
Compute (let n := 2 in 2 ^ (n - 1) + 1).
Compute (length [0; 3]).

Compute (Nat.sqrt 3).
Compute (let n := 3 in 2 ^ (n - 1) + 1).
Compute (length [0; 3; 5; 6]).
Compute (edges [0; 3; 5; 6]).
Compute (map (λ i, vΔ [0; 3; 5; 6; i]) (seq 0 8)).
Compute (map (λ i, vΔ [0; 1; 2; 4; i]) (seq 0 8)).

Compute (map (λ i, vΔ [0; 1; 6; 7; i]) (seq 0 8)).
Compute (vΔ [0; 1; 6; 7]).
Compute (edges [0; 1; 2; 4]).

(* The theorem *)

Theorem sensitivity : ∀ sg n,
  number_of_vertices sg = 2 ^ (n - 1) + 1
  → Δ sg ≥ Nat.sqrt n.
Proof.
...
