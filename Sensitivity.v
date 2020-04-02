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

(* alternative version *)

Fixpoint to_radix_loop it n i :=
  match it with
  | 0 => []
  | S it' => i mod n :: to_radix_loop it' n (i / n)
  end.

Definition to_radix n i := to_radix_loop n n i.

Fixpoint disp_loop' i l ll :=
  match i with
  | 0 => ll
  | S i' =>
      disp_loop' i' (tl l)
        (set_nth (hd 0 l) ll (i' :: nth (hd 0 l) ll []))
  end.

Definition dispatch' n i := disp_loop' n (to_radix n i) (repeat [] n).

Definition raw_partitions' n := map (dispatch' n) (seq 0 (n ^ n)).

Compute (raw_partitions 3 = raw_partitions' 3).

(* perhaps, showing they are equivalent (Compute says it), would
   help? *)

Theorem glop : ∀ n i, dispatch n i = dispatch' n i.
Proof.
intros.
unfold dispatch, dispatch'.
revert i.
induction n; intros; [ easy | ].
cbn - [ "mod" "/" ].
unfold to_radix in IHn.
...

(* *)

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

Definition is_raw_partition n ll :=
  length ll = n ∧
  (∀ l, l ∈ ll → ∀ i, i ∈ l → i < n) ∧
  (∀ i, i < n → ∃ l, l ∈ ll ∧ i ∈ l) ∧
  NoDup (concat ll).

(* locate: inverse of "dispatch" *)

Fixpoint nth_find_loop {A} (f : A → bool) l i :=
  match l with
  | [] => i
  | a :: l' => if f a then i else nth_find_loop f l' (i + 1)
  end.

Definition nth_find A f l := @nth_find_loop A f l 0.

Arguments nth_find [A]%type_scope _%function_scope _%list_scope.

Fixpoint nat_in_list i l :=
  match l with
  | [] => false
  | j :: l' => if Nat.eq_dec i j then true else nat_in_list i l'
  end.

Definition locate_list ll :=
  map (λ i, nth_find (nat_in_list i) ll) (seq 0 (length ll)).

Definition locate ll :=
  fold_left (λ a i, a * length ll + i) (locate_list ll) 0.

Compute (locate [[2]; []; [0; 1]]).
Compute (dispatch 3 24).
Compute (locate [[]; [0; 2]; [1]]).
Compute (dispatch 3 16).
Compute (dispatch 4 23).
Compute (locate [[0]; [1; 2]; []; [3]]).

Theorem set_nth_length : ∀ {A} i l (v : A),
  i < length l → length (set_nth i l v) = length l.
Proof.
intros * Hi.
revert i v Hi.
induction l as [| a]; intros; cbn in Hi; [ flia Hi | ].
destruct i; [ easy | cbn ].
apply Nat.succ_lt_mono in Hi.
f_equal.
now apply IHl.
Qed.

Theorem disp_loop_length : ∀ n i v r,
  n ≠ 0
  → length r = n
  → length (disp_loop n i v r) = length r.
Proof.
intros * Hnz Hrn.
revert n v r Hnz Hrn.
induction i; intros; [ easy | cbn ].
rewrite IHi; [ | easy | ]. 2: {
  rewrite set_nth_length; [ easy | ].
  rewrite Hrn.
  now apply Nat.mod_upper_bound.
}
apply set_nth_length.
rewrite Hrn.
now apply Nat.mod_upper_bound.
Qed.

Theorem disp_loop_0_r : ∀ n i ll,
  n ≠ 0
  → disp_loop n i 0 ll =
       match ll with
       | l :: ll' => (seq 0 i ++ l) :: ll'
       | [] => if Nat.eq_dec i 0 then [] else [seq 0 i]
       end.
Proof.
intros * Hnz.
destruct n; [ easy | clear Hnz; cbn ].
revert n ll.
induction i; intros; [ now destruct ll | cbn ].
rewrite Nat.sub_diag; cbn.
rewrite IHi; f_equal.
replace (0 :: seq 1 i) with (seq 0 (i + 1)) by now rewrite Nat.add_1_r.
rewrite seq_app.
destruct ll as [| l]; [ easy | ].
rewrite app_comm_cons.
replace (0 :: seq 1 i) with (seq 0 (i + 1)) by now rewrite Nat.add_1_r.
rewrite seq_app; cbn.
now rewrite <- app_assoc.
Qed.

Definition sub_list {A} (l : list A) start len :=
  firstn len (skipn start l).

Theorem seq_app_last : ∀ start len,
  seq start len ++ [start + len] = start :: seq (start + 1) len.
Proof.
intros.
revert start.
induction len; intros; cbn; [ now rewrite Nat.add_0_r | f_equal ].
rewrite <- Nat.add_succ_comm.
rewrite Nat.add_1_r.
rewrite <- (Nat.add_1_r (S start)).
apply IHlen.
Qed.

Theorem disp_loop_seq_sub_list : ∀ n i, i ≠ 0 → ∀ v r,
  0 < v < n
  → length r = n
  → disp_loop n i v r =
       (seq 0 (i - 1) ++ nth 0 r []) :: sub_list r 1 (v - 1) ++
       [[i - 1] ++ nth v r []] ++
       sub_list r (v + 1) (n - v - 1).
Proof.
intros * Hiz * Hvn Hrn.
destruct i; [ easy | clear Hiz ].
rewrite Nat.sub_succ, Nat.sub_0_r.
revert n v r Hvn Hrn.
induction i; intros. {
  cbn.
  unfold set_nth.
  unfold sub_list.
  rewrite Nat.mod_small; [ | easy ].
  rewrite app_comm_cons.
  destruct r as [| a l]; [ cbn in Hrn; flia Hvn Hrn | ].
  cbn.
  rewrite app_comm_cons.
  f_equal. {
    destruct v; [ easy | ].
    rewrite Nat.sub_succ, Nat.sub_0_r.
    apply firstn_cons.
  } {
    f_equal.
    rewrite firstn_skipn_comm.
    f_equal.
    replace (v + 1 + (n - v - 1)) with n by flia Hvn.
    destruct n; [ easy | cbn; f_equal ].
    cbn in Hrn.
    apply Nat.succ_inj in Hrn; subst n.
    symmetry; apply firstn_all.
  }
}
remember (S i) as si; cbn; subst si.
rewrite Nat.mod_small; [ | easy ].
rewrite Nat.div_small; [ | easy ].
cbn.
rewrite Nat.mod_0_l; [ | flia Hvn ].
rewrite Nat.div_0_l; [ | flia Hvn ].
rewrite disp_loop_0_r; [ | flia Hvn ].
remember (set_nth _ _ _) as sn eqn:Hsn.
symmetry in Hsn.
destruct sn as [| l ll]. {
  apply (f_equal (@length _)) in Hsn.
  rewrite set_nth_length in Hsn; cbn in Hsn; [ | easy ].
  rewrite set_nth_length in Hsn; cbn in Hsn; [ | now rewrite Hrn ].
  now rewrite <- Hrn, Hsn in Hvn.
}
cbn in Hsn.
injection Hsn; clear Hsn; intros H1 H2.
remember (set_nth _ _ _) as l2 eqn:Hl2.
symmetry in Hl2.
destruct l2 as [| l2 ll2]. {
  apply (f_equal (@length _)) in Hl2.
  rewrite set_nth_length in Hl2; [ | now rewrite Hrn ].
  subst ll.
  apply length_zero_iff_nil in Hl2; subst r.
  now rewrite <- Hrn in Hvn.
}
subst ll2.
cbn in H2; subst l.
f_equal. {
  rewrite app_comm_cons.
  replace (0 :: seq 1 i) with (seq 0 i ++ [i]). 2: {
    replace i with (0 + i) by easy.
    now rewrite seq_app_last.
  }
  rewrite <- app_assoc.
  f_equal; cbn; f_equal.
  destruct v; [ easy | ].
  cbn in Hl2.
  destruct r as [| l ll']; [ now rewrite <- Hrn in Hvn | ].
  cbn in Hl2.
  now injection Hl2.
} {
  destruct v; [ easy | ].
  unfold sub_list.
  cbn in Hl2; cbn.
  rewrite Nat.sub_0_r.
  destruct r as [| l ll']; [ now rewrite <- Hrn in Hvn | ].
  cbn in Hl2; cbn.
  injection Hl2; intros; subst l2 ll.
  f_equal; f_equal.
  rewrite firstn_skipn_comm.
  f_equal.
  replace (v + 1 + (n - S v - 1)) with (n - 1) by flia Hvn.
  cbn in Hrn.
  rewrite <- Hrn, Nat.sub_succ, Nat.sub_0_r.
  symmetry; apply firstn_all.
}
Qed.

Theorem List_cons_app A (a : A) l : a :: l = [a] ++ l.
Proof. easy. Qed.

Theorem List_skipn_1 : ∀ A (l : list A), skipn 1 l = tl l.
Proof. easy. Qed.

Theorem nth_find_loop_app_2 : ∀ A f (l1 l2 : list A) i,
  (∀ j, j ∈ l1 → f j = false)
  → nth_find_loop f (l1 ++ l2) i = nth_find_loop f l2 (i + length l1).
intros * Hl1.
revert l2 i.
induction l1 as [| a1]; intros; cbn; [ now rewrite Nat.add_0_r | ].
rewrite Hl1; [ | now left ].
rewrite Nat.add_1_r.
rewrite <- Nat.add_succ_comm.
apply IHl1.
intros j Hj.
apply Hl1.
now right.
Qed.

Theorem locate_dispatch : ∀ n i, i < n → locate (dispatch n i) = i.
Proof.
intros * Hin.
unfold locate, dispatch.
unfold locate_list.
rewrite disp_loop_length; [ | flia Hin | apply repeat_length ].
rewrite repeat_length.
destruct (Nat.eq_dec i 0) as [Hiz| Hiz]. {
  subst i; cbn.
  specialize (disp_loop_0_r n n (repeat [] n)) as H1.
  assert (Hnz : n ≠ 0) by flia Hin.
  specialize (H1 Hnz); cbn in H1.
  destruct (Nat.eq_dec n 0) as [H| H] in H1; [ easy | clear H ].
  rewrite H1; clear H1.
  replace (map _ (seq 0 n)) with (repeat 0 n). 2: {
    symmetry.
    replace (repeat 0 n) with (map (λ _, 0) (seq 0 n)). 2: {
      clear.
      remember (seq 0 n) as sn eqn:Hsn.
      remember 0 as s in Hsn; clear Heqs; subst sn.
      revert s.
      induction n; intros; [ easy | now cbn; rewrite IHn ].
    }
    apply map_ext_in_iff.
    intros i Hi; cbn.
    replace n with (S (n - 1)) at 1 by flia Hnz; cbn.
    rewrite app_nil_r.
    remember (nat_in_list i (seq 0 n)) as b eqn:Hb.
    symmetry in Hb.
    destruct b; [ easy | exfalso ].
    apply Bool.not_true_iff_false in Hb.
    apply Hb; clear Hb.
    clear Hin Hnz.
    remember (seq 0 n) as l; clear - Hi.
    revert i Hi.
    induction l as [| a]; intros; [ easy | cbn ].
    destruct (Nat.eq_dec i a) as [Hia| Hia]; [ easy | ].
    destruct Hi as [Hi| Hi]; [ now subst a | ].
    now apply IHl.
  }
  clear.
  remember (repeat 0 n) as l.
  remember n as m in Heql; clear Heqm; subst l.
  induction m; [ easy | ].
  apply IHm.
}
Compute (
   let n := 6 in let i := 1 in let v := n - 1 in
(*
   let r := map (λ i, [i; i + 1]) (seq 42 n) in
*)
   let r := repeat [] n in
(**)
   disp_loop n i v r =
     (seq 0 (i - 1) ++ nth 0 r []) :: sub_list r 1 (v - 1) ++
     [[i - 1] ++ nth v r []] ++
     sub_list r (v + 1) (n - v - 1)).
assert (Hnz : n ≠ 0) by flia Hin.
rewrite (disp_loop_seq_sub_list n n Hnz); [ | flia Hiz Hin | ]. 2: {
  apply repeat_length.
}
replace (nth 0 (repeat [] n) []) with ([] : list nat) by now destruct n.
rewrite app_nil_r.
replace (nth i (repeat [] n) []) with ([] : list nat). 2: {
  clear; revert i.
  induction n; intros; [ now destruct i | cbn ].
  destruct i; [ easy | apply IHn ].
}
rewrite app_nil_r.
replace (sub_list (repeat [] n) (i + 1) (n - i - 1)) with
    (repeat ([] : list nat) (n - i - 1)). 2: {
  clear - Hin.
  unfold sub_list.
  revert i Hin.
  induction n; intros; [ easy | cbn ].
  destruct i; cbn. {
    rewrite Nat.sub_0_r.
    replace n with (length (repeat ([] : list nat) n)) at 2. 2: {
      apply repeat_length.
    }
    symmetry; apply firstn_all.
  }
  apply Nat.succ_lt_mono in Hin.
  now apply IHn.
}
replace (sub_list (repeat [] n) 1 (i - 1)) with
    (repeat ([] : list nat) (i - 1)). 2: {
  clear - Hin.
  unfold sub_list.
  destruct n; intros; [ easy | cbn ].
  destruct i; [ easy | cbn ].
  rewrite Nat.sub_0_r.
  apply Nat.succ_lt_mono in Hin.
  revert i Hin.
  induction n; intros; [ easy | cbn ].
  destruct i; [ easy | cbn ].
  apply Nat.succ_lt_mono in Hin.
  now f_equal; apply IHn.
}
Compute
  (let n := 6 in let i := 4 in
   map
     (λ j,
      nth_find (nat_in_list j)
        (seq 0 (n - 1) ::
         repeat [] (i - 1) ++ [[n - 1]] ++ repeat [] (n - i - 1)))
       (seq 0 n)).
replace (map _ _) with (repeat 0 (n - 1) ++ [i]). 2: {
  symmetry.
  destruct n; [ easy | clear Hnz ].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  replace (S n - i - 1) with (n - i) by flia Hin.
  rewrite <- (Nat.add_1_r n).
  rewrite seq_app, Nat.add_0_l.
  replace (seq n 1) with [n] by easy.
  rewrite map_app.
  f_equal. {
    rewrite map_ext_in with (g := λ j, 0). 2: {
      intros j Hj; cbn.
      remember (nat_in_list j (seq 0 n)) as b eqn:Hb.
      symmetry in Hb.
      destruct b; [ easy | exfalso ].
      apply Bool.not_true_iff_false in Hb; apply Hb; clear Hb.
      remember (seq 0 n) as l eqn:Hl.
      clear - Hj.
      revert j Hj.
      induction l as [| a]; intros; [ easy | cbn ].
      destruct (Nat.eq_dec j a) as [Hia| Hia]; [ easy | ].
      destruct Hj as [Hi| Hi]; [ now subst a | ].
      now apply IHl.
    }
    clear.
    remember (seq 0 n) as l.
    remember 0 as s in Heql.
    clear Heqs; subst l.
    revert s.
    induction n; intros; [ easy | cbn ].
    now rewrite IHn.
  } {
    cbn.
    assert (H : ∀ i, nat_in_list (i + n) (seq i n) = false). {
      clear.
      induction n; intros; [ easy | cbn ].
      destruct (Nat.eq_dec (i + S n) i) as [Hin| Hin]; [ flia Hin | ].
      rewrite <- Nat.add_succ_comm.
      apply IHn.
    }
    specialize (H 0); cbn in H; rewrite H; clear H.
    f_equal.
    rewrite nth_find_loop_app_2. 2: {
      intros l Hl.
      now apply repeat_spec in Hl; subst l.
    }
    rewrite repeat_length.
    rewrite Nat.add_comm, Nat.sub_add; [ cbn | flia Hiz ].
    now destruct (Nat.eq_dec n n).
  }
}
rewrite fold_left_app; cbn.
rewrite <- Nat.add_0_l; f_equal.
apply Nat.eq_mul_0.
left; clear.
remember (n - 1) as m eqn:Hm; clear Hm.
now induction m.
Qed.

Compute (let n := 3 in map (λ ll, dispatch n (locate ll) = ll) (raw_partitions n)).

Theorem dispatch_locate : ∀ n ll,
  is_raw_partition n ll
  → dispatch n (locate ll) = ll.
Proof.
intros * Hll.
unfold locate.
Print locate.
Print locate_list.
...
intros * Hll.
revert n Hll.
induction ll as [| l]; intros. {
  destruct Hll as (Hlen & Hall & Hin & Hnd).
  now subst n.
}
cbn.
Print locate.
(* faudrait prouver déjà que locate renvoit bien une valeur entre
   0 et n^n *)
Print locate_list.
...
unfold dispatch.
unfold locate.
unfold locate_list.
Search (fold_left _ (map _ _)).
Print nth_find.
Search nth_find_loop.
...

Theorem is_partition_iff : ∀ n p, n ≠ 0 →
  is_partition n p ↔ p ∈ raw_partitions n.
Proof.
intros * Hnz.
split; intros Hn. {
(*
  destruct Hn as (Hlen & Hmem & Hin & Hnp).
*)
  unfold raw_partitions.
...
  specialize (dispatch_locate n p Hn) as H1.
  rewrite <- H1.
...
Print dispatch.
Compute (raw_partitions 3).
Compute (all_partitions 3).
Search locate.
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
...
unfold local_block_sensitivity, local_sensitivity.
...

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
