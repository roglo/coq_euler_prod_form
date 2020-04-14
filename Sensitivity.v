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

(* pre-partitions
   A pre-partition (my naming) of a finite set of n elements is a set
   of n subsets such that
   - the union of all these subsets is the initial set
   - the intersection of two subsets is the empty set
   It has always n subsets, some of them can be empty.
   A partition is a pre-partition where empty sets have been eliminated.
   There are exactly n^n pre-partitions of a set of cardinal n.
   Each pre-partition can be associated (bijection) with a number
   between 0 and n^n-1.
   Actually, we implemented the sets as lists, and a finite set of
   cardinal n as the natural numbers between 0 and n-1.
   Below, the definitions of the functions
     dispatch : number → pre-partition
     locate : pre-partition → number
*)

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

Definition cons_nth {A} i (a : A) ll :=
  firstn i ll ++  (a :: nth i ll []) :: skipn (i + 1) ll.

Definition is_nil {A} (l : list A) :=
  match l with
  | [] => true
  | _ => false
  end.

Fixpoint disp_loop n i v r :=
  match i with
  | 0 => r
  | S i' => disp_loop n i' (v / n) (cons_nth (v mod n) i' r)
  end.

Definition dispatch n i := disp_loop n n i (repeat [] n).

Definition pre_partitions n := map (dispatch n) (seq 0 (n ^ n)).

Compute (pre_partitions 3).

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
  | S i' => disp_loop' i' (tl l) (cons_nth (hd 0 l) i' ll)
  end.

Definition dispatch' n i := disp_loop' n (to_radix n i) (repeat [] n).

Definition pre_partitions' n := map (dispatch' n) (seq 0 (n ^ n)).

Compute (pre_partitions 3 = pre_partitions' 3).

(* perhaps, showing they are equivalent (Compute says it), would
   help?

Theorem glop : ∀ n i, dispatch n i = dispatch' n i.
Proof.
intros.
unfold dispatch, dispatch'.
revert i.
induction n; intros; [ easy | ].
cbn - [ "mod" "/" ].
unfold to_radix in IHn.
...
*)

Definition dispatch_list l :=
  disp_loop' (length l) (rev l) (repeat [] (length l)).

Fixpoint disp_loop'' n i l :=
  match l with
  | [] => repeat [] n
  | a :: l' => cons_nth a i (disp_loop'' n (S i) l')
  end.

Definition dispatch'' n i := disp_loop'' n 0 (rev (to_radix n i)).

Definition pre_partitions'' n := map (dispatch'' n) (seq 0 (n ^ n)).

Compute (pre_partitions 2 = pre_partitions'' 2).
Compute (pre_partitions 3 = pre_partitions'' 3).

Definition dispatch_list'' l := disp_loop'' (length l) 0 l.

(* third attempt to define dispatch *)

Fixpoint nth_find_all_loop {A} (f : A → bool) l i :=
  match l with
  | [] => []
  | a :: l' =>
      if f a then i :: nth_find_all_loop f l' (i + 1)
      else nth_find_all_loop f l' (i + 1)
  end.

Definition nth_find_all A f l := @nth_find_all_loop A f l 0.
Arguments nth_find_all [A]%type_scope _%function_scope _%list_scope.

Definition dispatch''' n i :=
  map (λ j, nth_find_all (Nat.eqb j) (rev (to_radix n i))) (seq 0 n).

Definition pre_partitions''' n :=
  map (dispatch''' n) (seq 0 (n ^ n)).

Compute (pre_partitions 2 = pre_partitions''' 2).
Compute (pre_partitions 3 = pre_partitions''' 3).

Definition dispatch_list''' l :=
  map (λ j, nth_find_all (Nat.eqb j) l) (seq 0 (length l)).

Compute (let l := [3; 2; 1; 1] in (dispatch_list'' l, dispatch_list''' l)).

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
          (map (filter (λ s, negb (is_nil s))) (pre_partitions''' n)))).

Compute (map (bsort list_nat_le) (pre_partitions 4)).
Compute (nodup (list_eq_dec (list_eq_dec Nat.eq_dec)) (map (bsort list_nat_le) (pre_partitions 4))).
Compute (all_partitions 4).

(* Local block sensitivity *)

Definition loc_bl_sens_list Bl f x :=
  filter (λ Bi, negb (Bool.eqb (f x) (f (x ^^ Bi)))) Bl.

Definition local_block_sensitivity n f x :=
  fold_right max 0
    (map (λ Bl, length (loc_bl_sens_list Bl f x)) (pre_partitions''' n)).

Definition block_sensitivity n f :=
  fold_right max 0 (map (local_block_sensitivity n f) (seq 0 (2 ^ n))).

(* Proving Theorem: bs(f) ≥ s(f) *)

Require Import Sorting.

(* property of partitions of {0,1,..,n-1} returned by pre_partitions *)

Definition is_pre_partition n ll :=
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

Check cons_nth.

Theorem cons_nth_length : ∀ {A} i ll (v : A),
  i < length ll → length (cons_nth i v ll) = length ll.
Proof.
intros * Hi.
revert i v Hi.
induction ll as [| l]; intros; cbn in Hi; [ flia Hi | ].
destruct i; [ easy | cbn ].
apply Nat.succ_lt_mono in Hi.
f_equal.
now apply IHll.
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
  rewrite cons_nth_length; [ easy | ].
  rewrite Hrn.
  now apply Nat.mod_upper_bound.
}
apply cons_nth_length.
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

Theorem disp_loop_small_r : ∀ n i, i ≠ 0 → ∀ v ll,
  0 < v < n
  → length ll = n
  → disp_loop n i v ll =
       (seq 0 (i - 1) ++ nth 0 ll []) :: sub_list ll 1 (v - 1) ++
       [[i - 1] ++ nth v ll []] ++
       sub_list ll (v + 1) (n - v - 1).
Proof.
intros * Hiz * Hvn Hrn.
destruct i; [ easy | clear Hiz ].
rewrite Nat.sub_succ, Nat.sub_0_r.
revert n v ll Hvn Hrn.
induction i; intros. {
  cbn.
  unfold cons_nth.
  unfold sub_list.
  rewrite Nat.mod_small; [ | easy ].
  rewrite app_comm_cons.
  destruct ll as [| a l]; [ cbn in Hrn; flia Hvn Hrn | ].
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
remember (cons_nth _ _ _) as sn eqn:Hsn.
symmetry in Hsn.
destruct sn as [| l]. {
  apply (f_equal (@length _)) in Hsn.
  rewrite cons_nth_length in Hsn; cbn in Hsn; [ | easy ].
  rewrite cons_nth_length in Hsn; cbn in Hsn; [ | now rewrite Hrn ].
  now rewrite <- Hrn, Hsn in Hvn.
}
cbn in Hsn.
injection Hsn; clear Hsn; intros H1 H2.
remember (cons_nth _ _ _) as l2 eqn:Hl2.
symmetry in Hl2.
destruct l2 as [| l2 ll2]. {
  apply (f_equal (@length _)) in Hl2.
  rewrite cons_nth_length in Hl2; [ | now rewrite Hrn ].
  subst sn.
  apply length_zero_iff_nil in Hl2; subst ll.
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
  destruct ll as [| l ll']; [ now rewrite <- Hrn in Hvn | ].
  cbn in Hl2.
  now injection Hl2.
} {
  destruct v; [ easy | ].
  unfold sub_list.
  cbn in Hl2; cbn.
  rewrite Nat.sub_0_r.
  destruct ll as [| l ll']; [ now rewrite <- Hrn in Hvn | ].
  cbn in Hl2; cbn.
  injection Hl2; intros; subst l2 sn.
  f_equal; f_equal.
  rewrite firstn_skipn_comm.
  f_equal.
  replace (v + 1 + (n - S v - 1)) with (n - 1) by flia Hvn.
  cbn in Hrn.
  rewrite <- Hrn, Nat.sub_succ, Nat.sub_0_r.
  symmetry; apply firstn_all.
}
Qed.

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

Compute (let ll := [[1; 2]; []; [0]] in locate_list ll).
Compute (let l := [2; 0; 0] in dispatch_list l).

Theorem disp_loop'_length : ∀ i l ll,
  ll ≠ []
  → (∀ a, a ∈ l → a < length ll)
  → length (disp_loop' i l ll) = length ll.
Proof.
intros * Hllz Hll.
revert l ll Hllz Hll.
induction i; intros; [ easy | cbn ].
rewrite IHi; cycle 1. {
  intros H; apply Hllz.
  apply length_zero_iff_nil in H.
  rewrite cons_nth_length in H. {
    now apply length_zero_iff_nil in H.
  }
  destruct l as [| b]; [ easy | ].
  apply Hll.
  now left.
} {
  intros a Ha.
  destruct l as [| b]; [ easy | cbn in Ha; cbn ].
  rewrite app_length; cbn.
  rewrite firstn_length.
  rewrite skipn_length.
  destruct (lt_dec b (length ll)) as [Hbl| Hbl]. {
    rewrite min_l; [ | flia Hbl ].
    rewrite <- Nat.add_succ_comm.
    rewrite Nat.add_1_r, Nat.add_comm.
    rewrite Nat.sub_add; [ | easy ].
    now apply Hll; right.
  } {
    exfalso; apply Hbl.
    apply Hll.
    now left.
  }
}
destruct ll as [| l1]; [ easy | ].
destruct l as [| a]; [ easy | ].
apply cons_nth_length.
cbn; apply Hll.
now left.
Qed.

Print disp_loop''.

Theorem disp_loop''_length : ∀ n i l,
  (∀ a, a ∈ l → a < n)
  → length (disp_loop'' n i l) = n.
Proof.
intros * Hln.
revert i n Hln.
induction l as [| b]; intros; [ apply repeat_length | cbn ].
rewrite cons_nth_length. 2: {
  rewrite IHl; [ now apply Hln; left | ].
  now intros a Ha; apply Hln; right.
}
apply IHl.
now intros a Ha; apply Hln; right.
Qed.

Compute (locate_list (dispatch_list [2; 0; 0])).
Compute (locate_list (dispatch_list'' [1; 2; 0])).

Theorem List_app_cons : ∀ A (l1 l2 : list A) a,
  l1 ++ a :: l2 = l1 ++ [a] ++ l2.
Proof. easy. Qed.

(* return the rank (from 0) in the pre-partition i where we j is found
   (j < n) *)
Definition in_nth_list_of_pre_part n j i :=
  i mod n ^ (n - j) / n ^ (n - j - 1).

Lemma not_in_nth_find_all_loop : ∀ A f (l : list A) i j,
  i < j → i ∉ nth_find_all_loop f l j.
Proof.
intros * Hij.
revert i j Hij.
induction l as [| a]; intros; [ easy | ].
cbn; intros H1.
assert (Hij1 : i < j + 1) by flia Hij.
destruct (f a). {
  destruct H1 as [H1| H1]; [ flia Hij H1 | ].
  now specialize (IHl i (j + 1) Hij1).
}
now specialize (IHl i (j + 1) Hij1).
Qed.

Lemma in_nth_find_all_loop_eq : ∀ l i k b,
  b ∈ nth_find_all_loop (Nat.eqb i) l k
  → k ≤ b
  → nth (b - k) l 0 = i.
Proof.
intros * Hb1 Hbk.
revert i k b Hb1 Hbk.
induction l as [| a]; intros; [ easy | ].
cbn.
remember (b - (k(* + 1*))) as bk eqn:Hbk1; symmetry in Hbk1.
destruct bk. {
  cbn in Hb1.
  remember (i =? a) as ia eqn:Hia; symmetry in Hia.
  destruct ia; [ now apply Nat.eqb_eq in Hia | ].
  replace k with b in Hb1 by flia Hbk Hbk1.
  exfalso.
  revert Hb1.
  apply not_in_nth_find_all_loop; flia.
}
cbn in Hb1.
remember (i =? a) as ia eqn:Hia; symmetry in Hia.
destruct ia. {
  apply Nat.eqb_eq in Hia; subst a.
  destruct Hb1 as [Hb1| Hb1]; [ flia Hb1 Hbk1 | ].
  specialize (IHl i (k + 1) b Hb1) as H1.
  assert (H : k + 1 ≤ b) by flia Hbk1.
  specialize (H1 H); clear H.
  now replace (b - (k + 1)) with bk in H1 by flia Hbk1.
}
specialize (IHl i (k + 1) b Hb1) as H1.
assert (H : k + 1 ≤ b) by flia Hbk1.
specialize (H1 H); clear H.
now replace (b - (k + 1)) with bk in H1 by flia Hbk1.
Qed.

Lemma in_flat_map_nth_find_all_loop_eq : ∀ l j k len b,
  b ∈ flat_map (λ i, nth_find_all_loop (Nat.eqb i) l k) (seq j len)
  → k ≤ b
  → j ≤ nth (b - k) l 0 < j + len.
Proof.
intros * Hbf Hkb.
apply in_flat_map in Hbf.
destruct Hbf as (i & Hi & Hik).
apply in_nth_find_all_loop_eq in Hik; [ | easy ].
rewrite Hik.
now apply in_seq in Hi.
Qed.

Lemma flat_map_nth_find_all_loop_cons : ∀ a l k i len,
  a < i ∨ i + len ≤ a
  → flat_map (λ j, nth_find_all_loop (Nat.eqb j) (a :: l) k) (seq i len) =
    flat_map (λ j, nth_find_all_loop (Nat.eqb j) l (k + 1)) (seq i len).
Proof.
intros * Hai.
do 2 rewrite flat_map_concat_map; f_equal; cbn.
apply map_ext_in_iff.
intros b Hb.
apply in_seq in Hb.
remember (b =? a) as c eqn:Hc; symmetry in Hc.
destruct c; [ | easy ].
apply Nat.eqb_eq in Hc; subst b.
flia Hai Hb.
Qed.

Theorem dispatch_list'''_is_pre_partition : ∀ l,
  (∀ a, a ∈ l → a < length l)
  → is_pre_partition (length l) (dispatch_list''' l).
Proof.
intros * Hl.
split. {
  unfold dispatch_list'''.
  now rewrite map_length, seq_length.
}
split. {
  intros l1 Hl1 i Hi.
  unfold dispatch_list''' in Hl1.
  move i at top.
  move l1 before l.
  apply in_map_iff in Hl1.
  destruct Hl1 as (b & Hb & Hbs).
  subst l1; move b before i.
  unfold nth_find_all in Hi.
  assert
    (H : ∀ A f (l : list A) i j,
     j < length (nth_find_all_loop f l i)
     → nth j (nth_find_all_loop f l i) 0 < i + length l). {
    clear.
    intros * Hj.
    revert i j Hj.
    induction l as [| a]; intros; [ easy | ].
    cbn in Hj; cbn.
    destruct (f a). {
      cbn in Hj; cbn.
      destruct j; [ flia | ].
      apply Nat.succ_lt_mono in Hj.
      rewrite Nat.add_1_r in Hj.
      rewrite Nat.add_1_r.
      rewrite <- Nat.add_succ_comm.
      now apply IHl.
    } {
      rewrite Nat.add_1_r in Hj.
      rewrite Nat.add_1_r.
      rewrite <- Nat.add_succ_comm.
      now apply IHl.
    }
  }
  apply in_split in Hi.
  destruct Hi as (l1 & l2 & Hi).
  specialize (H nat (Nat.eqb b) l 0 (length l1)) as H1.
  rewrite Hi in H1.
  rewrite app_nth2 in H1; [ | now unfold "≥" ].
  rewrite Nat.sub_diag in H1; cbn in H1.
  apply H1.
  rewrite app_length; cbn; flia.
}
split. {
  intros i Hi.
  exists (nth (nth i l 0) (dispatch_list''' l) []).
  split. {
    apply nth_In.
    unfold dispatch_list'''.
    rewrite map_length.
    rewrite seq_length.
    apply Hl.
    now apply nth_In.
  }
  unfold dispatch_list'''.
  rewrite List_map_nth_in with (a := 0). 2: {
    rewrite seq_length.
    apply Hl.
    now apply nth_In.
  }
  rewrite seq_nth. 2: {
    apply Hl.
    now apply nth_In.
  }
  cbn.
  unfold nth_find_all.
  assert (H : ∀ d, i + d ∈ nth_find_all_loop (Nat.eqb (nth i l 0)) l d). {
    revert i Hi.
    clear Hl.
    induction l as [| a]; intros; [ easy | ].
    destruct i; [ now cbn; rewrite Nat.eqb_refl; left | cbn ].
    enough (S i + d ∈ nth_find_all_loop (Nat.eqb (nth i l 0)) l (d + 1)). {
      destruct (nth i l 0 =? a); [ now right | easy ].
    }
    cbn in Hi; apply Nat.succ_lt_mono in Hi.
    rewrite Nat.add_succ_comm, Nat.add_1_r.
    now apply IHl.
  }
  replace i with (i + 0) at 1 by easy.
  apply H.
}
unfold dispatch_list'''.
rewrite <- flat_map_concat_map.
assert (Hnd : ∀ l i j, NoDup (nth_find_all_loop (Nat.eqb i) l j)). {
  clear.
  intros.
  revert i j (*Hij*).
  induction l as [| a]; intros; [ constructor | ].
  cbn - [ Nat.eqb ].
  remember (i =? a) as ia eqn:Hia; symmetry in Hia.
  destruct ia. {
    constructor; [ apply not_in_nth_find_all_loop; flia | ].
    apply IHl.
  }
  apply IHl.
}
assert
  (H : ∀ i k len,
   NoDup
     (flat_map (λ j, nth_find_all_loop (Nat.eqb j) l k)
        (seq i len))). {
  clear Hl.
  induction l as [| a]; intros. {
    cbn; clear.
    revert i.
    induction len; intros; [ constructor | apply IHlen ].
  }
  destruct (lt_dec a i) as [Hai| Hai]. {
    rewrite flat_map_nth_find_all_loop_cons; [ | now left ].
    apply IHl.
  }
  apply Nat.nlt_ge in Hai.
  destruct (le_dec (i + len) a) as [Hila| Hila]. {
    rewrite flat_map_nth_find_all_loop_cons; [ | now right ].
    apply IHl.
  }
  apply Nat.nle_gt in Hila.
  rewrite flat_map_concat_map.
  replace len with (a - i + (len - (a - i))) by flia Hila.
  rewrite seq_app.
  rewrite map_app.
  rewrite concat_app.
  do 2 rewrite <- flat_map_concat_map.
  rewrite flat_map_nth_find_all_loop_cons; [ | right; flia Hai ].
  rewrite (Nat.add_comm i), Nat.sub_add; [ | easy ].
  replace (len - (a - i)) with (1 + (len - (a - i) - 1)) by flia Hai Hila.
  rewrite seq_app.
  do 2 rewrite flat_map_concat_map.
  rewrite map_app, concat_app.
  unfold seq at 2, map at 2, concat at 2.
  rewrite app_nil_r.
  remember (nth_find_all_loop (Nat.eqb a) _ _) as x; cbn in Heqx; subst x.
  rewrite Nat.eqb_refl.
  do 2 rewrite <- flat_map_concat_map.
  apply NoDup_app; [ apply IHl | | ]. {
    apply NoDup_app. {
      constructor; [ | apply Hnd ].
      apply not_in_nth_find_all_loop; flia.
    } {
      rewrite flat_map_nth_find_all_loop_cons; [ | left; flia ].
      apply IHl.
    }
    intros b Hb Hbf.
    apply in_flat_map_nth_find_all_loop_eq in Hbf. 2: {
      destruct Hb as [Hb| Hb]; [ now subst b | ].
      apply Nat.nlt_ge; intros H; revert Hb.
      apply not_in_nth_find_all_loop; flia H.
    }
    destruct Hb as [Hb| Hb]. {
      subst k.
      rewrite Nat.sub_diag in Hbf; cbn in Hbf; flia Hbf.
    }
    remember (b - k) as bk eqn:Hbk; symmetry in Hbk.
    destruct bk; [ cbn in Hbf; flia Hbf | ].
    cbn in Hbf.
    apply in_nth_find_all_loop_eq in Hb; [ | flia Hbk ].
    replace (b - (k + 1)) with bk in Hb by flia Hbk.
    flia Hb Hbf.
  }
  intros b Hb1 Hb2.
  destruct Hb2 as [Hb2| Hb2]. {
    subst k.
    apply in_flat_map in Hb1.
    destruct Hb1 as (j & Hj & Hjb).
    revert Hjb.
    apply not_in_nth_find_all_loop; flia.
  }
  apply in_app_iff in Hb2.
  destruct Hb2 as [Hb2| Hb2]. {
    destruct (le_dec (k + 1) b) as [Hkb| Hkb]. {
      apply in_flat_map_nth_find_all_loop_eq in Hb1; [ | easy ].
      apply in_nth_find_all_loop_eq in Hb2; [ | easy ].
      rewrite Hb2 in Hb1.
      flia Hb1.
    }
    apply Nat.nle_gt in Hkb.
    revert Hb2.
    now apply not_in_nth_find_all_loop.
  }
  rewrite flat_map_nth_find_all_loop_cons in Hb2; [ | left; flia ].
  destruct (le_dec (k + 1) b) as [Hkb| Hkb]. {
    apply in_flat_map_nth_find_all_loop_eq in Hb1; [ | easy ].
    apply in_flat_map_nth_find_all_loop_eq in Hb2; [ | easy ].
    flia Hb1 Hb2.
  }
  apply Nat.nle_gt in Hkb.
  apply in_flat_map in Hb1.
  destruct Hb1 as (x & Hx & Hxl).
  revert Hxl.
  now apply not_in_nth_find_all_loop.
}
apply H.
Qed.

Inspect 1.

(*
Theorem dispatch_list''_is_pre_partition : ∀ l,
  (∀ a, a ∈ l → a < length l)
  → is_pre_partition (length l) (dispatch_list'' l).
Proof.
intros * Hl.
split. {
  unfold dispatch_list''.
  now apply disp_loop''_length.
}
split. {
  intros l1 Hl1 i Hi.
  unfold dispatch_list'' in Hl1.
  move i at top.
  move l1 before l.
  apply in_split in Hi.
  destruct Hi as (l2 & l3 & Hlil).
  apply in_split in Hl1.
  destruct Hl1 as (ll2 & ll3 & Hllll).
  subst l1.
  remember (length l) as n; clear Heqn.
  remember 0 as j.
  assert (Hji : j ≤ i) by (subst j; flia).
  clear Heqj.
  clear Hl.
  revert n j ll2 ll3 i l2 l3 Hji Hllll.
  induction l as [| a]; intros. {
    cbn in Hllll; cbn; symmetry in Hllll; exfalso.
    clear - Hllll.
    revert n Hllll.
    induction ll2 as [| l]; intros. {
      cbn in Hllll.
      destruct n; [ easy | ].
      cbn in Hllll.
      injection Hllll; intros H1 H2.
      now destruct l2.
    }
    destruct n; [ easy | ].
    cbn in Hllll.
    injection Hllll; intros H1 H2.
    now specialize (IHll2 _ H1).
  }
  cbn in Hllll.
...
    revert ll2 Hllll.
    induction n; intros; cbn in Hllll. {
      now apply app_eq_nil in Hllll.
    }
    destruct ll2 as [| l]. {
      cbn in Hllll.
      injection Hllll; clear Hllll; intros H1 H2.
      now apply app_eq_nil in H2.
    }
    cbn in Hllll.
    injection Hllll; clear Hllll; intros H1 H2; subst l.
...
    congruence.
  }
  cbn in Hllll.
  remember (disp_loop'' n (S j) l) as ll eqn:Hll.
  unfold cons_nth in Hllll.
  do 2 rewrite List_app_cons in Hllll.
  do 2 rewrite app_assoc in Hllll.
  destruct (Nat.eq_dec i a) as [Hia| Hia]; [ now left | right ].
  symmetry in Hll.
  destruct i. {
    apply Nat.le_0_r in Hji; subst j.
...
  intros l1 Hl1 i Hi.
  apply Hl.
  unfold dispatch_list'' in Hl1.
  move i at top.
  move l1 before l.
...
  remember (length l) as n.
  remember 0 as j.
  assert (Hnj : n = j + length l) by flia Heqn Heqj.
  replace l with (skipn j l) in Hl1 by now subst j.
  clear Heqn Heqj.
  (* lemma to do *)
  assert (Hln : l1 = nth (nth i l 0) (disp_loop'' n j (skipn j l)) []). {
    revert i j n l1 Hl1 Hi Hnj Hl.
    induction l as [| b]; intros. {
      cbn in Hnj; rewrite Nat.add_0_r in Hnj.
      subst j; cbn.
      rewrite match_id.
      destruct n; [ easy | ].
      cbn in Hl1.
      destruct Hl1 as [Hl1| Hl1]; [ now subst l1 | cbn ].
      now apply repeat_spec in Hl1.
    }
    cbn in Hl1, Hnj; cbn.
    destruct i. {
...
Print disp_loop''.
disp_loop'' n j l
cons_nth a₀ 0 (disp_loop'' n (j+1) l)
cons_nth a₀ 0 (cons_nth a₁ 1 (disp_loop'' n (j+2) l))
cons_nth a₀ 0 (cons_nth a₁ 1 ... (cons_nth a_{i} i (disp_loop'' n (j+i+1) l)))

cons_nth a₀ 0 (disp_loop'' n 1 l)
cons_nth a₀ 0 (cons_nth a₁ 1 (disp_loop'' n 2 l))
cons_nth a₀ 0 (cons_nth a₁ 1 ... (cons_nth a_{i} i (disp_loop'' n (i+1) l)))
(* clearly each element of l is in disp_loop'' _ _ l
   less clearly but true too, each elememt in disp_loop'' _ _ l comes
   from l. But how to formally prove it? *)
...
  apply in_split in Hi.
  destruct Hi as (l2 & l3 & Hlil).
  apply in_split in Hl1.
  destruct Hl1 as (ll2 & ll3 & Hllll).
  subst l1.
  remember (length l) as n; clear Heqn.
  remember 0 as j.
  assert (Hji : j ≤ i) by (subst j; flia).
  clear Heqj.
  revert n j ll2 ll3 i l2 l3 Hji Hllll.
  induction l as [| a]; intros. {
    cbn in Hllll; cbn; symmetry in Hllll.
    revert ll2 Hllll.
    induction n; intros; cbn in Hllll. {
      now apply app_eq_nil in Hllll.
    }
    destruct ll2 as [| l]. {
      cbn in Hllll.
      injection Hllll; clear Hllll; intros H1 H2.
      now apply app_eq_nil in H2.
    }
    cbn in Hllll.
    injection Hllll; clear Hllll; intros H1 H2; subst l.
    congruence.
  }
  cbn in Hllll.
  remember (disp_loop'' n (S j) l) as ll eqn:Hll.
  unfold cons_nth in Hllll.
  do 2 rewrite List_app_cons in Hllll.
  do 2 rewrite app_assoc in Hllll.
  destruct (Nat.eq_dec i a) as [Hia| Hia]; [ now left | right ].
  symmetry in Hll.
  destruct i. {
    apply Nat.le_0_r in Hji; subst j.
Search (_ ++ _ = _ ++ _).
...
    injection Hllll.
...

  apply (IHl n (S j) ll2 ll3 i l2 l3). {
  rewrite Hll.
  rewrite List_app_cons, app_assoc.
  rewrite <- Hllll.
...
  intros l1 Hl1 i Hi.
  apply Hl.
  clear Hl.
  unfold dispatch_list'' in Hl1.
  revert i l1 Hl1 Hi.
  destruct l as [| a]; intros; [ easy | ].
  cbn in Hl1.
  remember (S (length l)) as n.
  remember 1 as j.
  clear - Hl1 Hi.
  revert a i l1 n j Hl1 Hi.
  induction l as [| b]; intros; cbn in Hl1. {
    left.
    unfold cons_nth in Hl1.
    apply in_app_iff in Hl1.
    destruct Hl1 as [Hl1| Hl1]. {
      revert a Hl1.
      induction n; intros; [ now rewrite firstn_nil in Hl1 | ].
      cbn in Hl1.
      destruct a; [ easy | cbn in Hl1 ].
      destruct Hl1 as [Hl1| Hl1]; [ now subst l1 | ].
      apply IHn.
      clear - Hl1.
      revert a Hl1.
      induction n; intros. {
        cbn in Hl1.
        now rewrite firstn_nil in Hl1.
      }
      cbn.
      cbn in Hl1.
      destruct a; [ easy | ].
      cbn in Hl1.
      destruct Hl1 as [Hl1| Hl1]; [ now left | right ].
      now apply IHn.
    }
...
  intros l1 Hl1 i Hi.
  remember (λ a, a < length l) as P.
  replace (i < length l) with (P i) by now subst P.
  assert (H : ∀ a, a ∈ l → P a) by now subst P.
  move H before Hl; clear Hl; rename H into Hl.
  clear HeqP.
  unfold dispatch_list'' in Hl1.
  remember 0 as j eqn:Hj in Hl1; clear Hj.
  remember (length l) as n eqn:Hn; clear Hn.
  revert n i j l1 Hl Hl1 Hi.
  induction l as [| b]; intros. {
    cbn in Hl1.
    apply repeat_spec in Hl1.
    now subst l1.
  }
  cbn in Hl1.
  unfold cons_nth in Hl1.
  apply in_app_iff in Hl1.
  destruct Hl1 as [Hl1| Hl1]. {
    apply (IHl n _ (S j) l1); [ | | easy ]. 2: {
      remember (disp_loop'' n (S j) l) as ll eqn:Hll.
      clear - Hl1.
      revert b Hl1.
      induction ll as [| l]; intros. {
        now rewrite firstn_nil in Hl1.
      }
      destruct b; [ easy | cbn in Hl1 ].
      destruct Hl1 as [Hl1| Hl1]; [ now subst l1; left | right ].
      now apply (IHll b).
    }
    intros a Ha.
    now apply Hl; right.
  }
  cbn in Hl1.
  destruct Hl1 as [Hl1| Hl1]. {
    subst l1.
    destruct Hi as [Hi| Hi].
...
  intros l1 Hl1 i Hi.
  unfold dispatch_list'' in Hl1.
  remember (length l) as n eqn:Hn; clear Hn.
  remember 0 as j eqn:Hj in Hl1; clear Hj.
  revert n i j l1 Hl Hl1 Hi.
  induction l as [| b]; intros. {
    cbn in Hl1.
    apply repeat_spec in Hl1.
    now subst l1.
  }
  cbn in Hl1.
  unfold cons_nth in Hl1.
  apply in_app_iff in Hl1.
  destruct Hl1 as [Hl1| Hl1]. {
    apply (IHl _ _ (S j) l1); [ | | easy ]. 2: {
      remember (disp_loop'' n (S j) l) as ll eqn:Hll.
      clear - Hl1.
      revert b Hl1.
      induction ll as [| l]; intros. {
        now rewrite firstn_nil in Hl1.
      }
      destruct b; [ easy | cbn in Hl1 ].
      destruct Hl1 as [Hl1| Hl1]; [ now subst l1; left | right ].
      now apply (IHll b).
    }
    intros a Ha.
    now apply Hl; right.
  }
  cbn in Hl1.
...
clear j l1 Hl1 Hi.
...
  destruct Hl1 as [Hl1| Hl1]. {
    subst l1.
    cbn in Hi.
    destruct Hi as [Hi| Hi]. {
      clear j Hi.
  b : nat
  l : list nat
  IHl : ∀ (n i j : nat) (l1 : list nat),
          (∀ a : nat, a ∈ l → a < n) → l1 ∈ disp_loop'' n j l → i ∈ l1 → i < n
  n, i : nat
  Hl : ∀ a : nat, a ∈ b :: l → a < n
  ============================
  i < n
      apply (IHl _ _ 0 [i]).
...
  apply In_nth with (d := []) in Hl1.
  rewrite disp_loop''_length in Hl1; [ | easy ].
  destruct Hl1 as (i1 & Hi1 & Hl1).
  subst l1.
  apply In_nth with (d := 0) in Hi.
  destruct Hi as (j & Hj & Hi).
  subst i.
  apply Hl.
  destruct l as [| b]; [ easy | cbn ].
...
  revert l i Hl Hl1 Hi.
  induction l1; intros; [ easy | cbn ].
  destruct Hi as [Hi| Hi]. {
    subst a.
    apply Hl.
...
  revert l1 i Hl1 Hi.
  induction l as [| b]; intros; [ easy | cbn ].
  cbn in Hl1.
  unfold cons_nth in Hl1.
  apply in_app_iff in Hl1.
  destruct Hl1 as [Hl1| Hl1]. {
Search (_ ∈ firstn _ _).
    apply in_firstn in Hl1.

...
  apply Hl. (* non *)
Print dispatch_list''.
Print disp_loop''.
...
*)

Lemma nth_find_loop_map : ∀ A B f (g : A → B) i l,
  nth_find_loop f (map g l) i =
  nth_find_loop (λ a, f (g a)) l i.
Proof.
intros.
revert f g i.
induction l as [| a]; intros; [ easy | cbn ].
destruct (f (g a)); [ easy | ].
apply IHl.
Qed.

Theorem nat_in_list_false_iff : ∀ i l,
  nat_in_list i l = false ↔ ∀ j, j ∈ l → i ≠ j.
Proof.
intros.
split. {
  intros Hil j Hjl Hij.
  subst j.
  revert i Hil Hjl.
  induction l as [| a]; intros; [ easy | ].
  cbn in Hil, Hjl.
  destruct Hjl as [Hjl| Hjl]. {
    subst a.
    now destruct (Nat.eq_dec i i).
  }
  destruct (Nat.eq_dec i a) as [Hia| Hia]; [ easy | ].
  now apply (IHl i).
} {
  intros Hil.
  revert i Hil.
  induction l as [| a]; intros; [ easy | cbn ].
  destruct (Nat.eq_dec i a) as [Hia| Hia]. {
    subst i.
    now specialize (Hil a (or_introl eq_refl)).
  }
  apply IHl.
  intros j Hj.
  now apply Hil; right.
}
Qed.

Theorem locate_dispatch_list''' : ∀ l,
  (∀ a : nat, a ∈ l → a < length l)
  → locate_list (dispatch_list''' l) = l.
Proof.
intros * Hl.
specialize (dispatch_list'''_is_pre_partition l Hl) as H1.
unfold is_pre_partition in H1.
destruct H1 as (_ & Hin & Huni & Hint).
remember (dispatch_list''' l) as ll.
unfold dispatch_list''' in Heqll.
rewrite Heqll.
unfold locate_list.
unfold dispatch_list'''.
rewrite map_length, seq_length.
Compute (let l := [2; 2; 0; 3] in map (λ i, nth_find (nat_in_list i) (map (λ j, nth_find_all (Nat.eqb j) l) (seq 0 (length l)))) (seq 0 (length l))).
(**)
replace l with (map (λ i, nth i l 0) (seq 0 (length l))) at 2. 2: {
  clear.
  induction l as [| a]; [ easy | ].
  f_equal; cbn; f_equal.
  rewrite <- seq_shift.
  now rewrite map_map.
}
apply map_ext_in_iff.
intros a Ha.
unfold nth_find.
(*
rewrite nth_find_loop_map.
*)
unfold nth_find_all.
(**)
Compute (let l := [2; 2; 3; 6; 0; 0; 2] in map (λ j, nth_find_all (Nat.eqb j) l) (seq 0 (length l))).
replace (length l) with (nth a l 0 + 1 + (length l - (nth a l 0 + 1))). 2: {
  apply in_seq in Ha; cbn in Ha.
  destruct Ha as (_, Ha).
  specialize (Hl (nth a l 0) (nth_In l 0 Ha)) as H1.
  flia H1.
}
do 2 rewrite seq_app.
do 2 rewrite Nat.add_0_l.
replace (seq _ 1) with [nth a l 0] by easy.
do 2 rewrite map_app.
rewrite <- app_assoc.
rewrite nth_find_loop_app_2. 2: {
  intros l1 Hl1.
  apply nat_in_list_false_iff.
  intros j Hj Haj; subst j.
  apply in_map_iff in Hl1.
  destruct Hl1 as (k & Hkl & Hka); subst l1.
  apply in_seq in Hka; destruct Hka as (_, Hka); cbn in Hka.
  apply in_nth_find_all_loop_eq in Hj; [ | flia ].
  rewrite Nat.sub_0_r in Hj; subst k.
  flia Hka.
}
rewrite map_length, seq_length, Nat.add_0_l.
...
induction a. {
  cbn - [ Nat.eqb ].
  destruct l as [| a]; [ easy | ].
  clear Ha.
  cbn - [ Nat.eqb ].
  destruct a; [ easy | ].
  unfold Nat.eqb at 1.
  replace (nat_in_list _ _) with false. 2: {
    symmetry.
    apply nat_in_list_false_iff.
    intros j Hj H; subst j.
    revert Hj.
    apply not_in_nth_find_all_loop; flia.
  }
  destruct l as [| b]. {
    specialize (Hl (S a) (or_introl eq_refl)); cbn in Hl.
    flia Hl.
  }
  destruct a; [ easy | ].
  replace (length (b :: l)) with (1 + (length (b :: l) - 1)) by (cbn; flia).
  rewrite seq_app, map_app.
  rewrite nth_find_loop_app_2. 2: {
    intros l1 Hl1.
    unfold seq, map in Hl1.
    destruct Hl1 as [Hl1| Hl1]; [ | easy ].
    apply nat_in_list_false_iff.
    intros j Hj Hjz.
    subst j l1.
    replace (1 =? S (S a)) with false in Hj by easy.
    revert Hj.
    apply not_in_nth_find_all_loop; flia.
  }
...
Compute (map (λ j, nth_find_all (Nat.eqb j) [2; 2; 0]) (seq 0 3)).
Compute (let l := [2; 2; 3; 1; 0; 4; 2] in map (map (λ i, nth i l 0)) (map (λ j, nth_find_all (Nat.eqb j) l) (seq 0 (length l)))).
Search dispatch_list'''.
Compute (map (λ i, nat_in_list i (nth_find_all (Nat.eqb 1) [2; 2; 0])) (seq 0 3)).
Compute (map (λ i, nat_in_list i (nth_find_all (Nat.eqb 2) [2; 2; 0])) (seq 0 3)).
unfold nth_find_all.
Check disp_loop_small_r.
Print disp_loop.
Print nth_find_all_loop.
Theorem nth_find_all_loop_eqb f l i =
  nth_find_all_loop (Nat.eqb j) l i =
(* les rangs de tous ceux dont la valeur vaut j *)
...
  match l with
  | [] => []
  | a :: l' =>
      if Nat.eqb j a then i :: nth_find_all_loop A f l' (i + 1)
      else nth_find_all_loop A f l' (i + 1)
...
rewrite nth_find_loop_map.
apply in_seq in Ha.
destruct Ha as (_, Ha); cbn in Ha.
unfold nth_find_all.
Search nth_find_all_loop.
...
Search nat_in_list.
  assert
    (Hij : ∀ i j k, i < j →
    nat_in_list i (nth_find_all_loop (Nat.eqb k) l j) = false). {
...
Print nth_find_loop.
Compute (map (λ i, nat_in_list i (nth_find_all (Nat.eqb 0) [2; 2; 0])) (seq 0 3)).
Compute (map (λ i, nat_in_list i (nth_find_all (Nat.eqb 1) [2; 2; 0])) (seq 0 3)).
Compute (map (λ i, nat_in_list i (nth_find_all (Nat.eqb 2) [2; 2; 0])) (seq 0 3)).
...
replace (length l) with (a + (length l - a)) by flia Ha.
rewrite seq_app; cbn.
rewrite nth_find_loop_app_2. 2: {
  intros j Hj.
  apply in_seq in Hj; cbn in Hj; destruct Hj as (_, Hja).
  unfold nth_find_all.
...
  clear - Hja.
  apply nat_in_list_false_iff.
  intros k Ha Hak; subst k.
Check not_in_nth_find_all_loop.
Theorem not_in_nth_find_all_loop2 : ∀ A f (l : list A) i j,
  j + length l < i → i ∉ nth_find_all_loop f l j.
...
revert Ha.
apply not_in_nth_find_all_loop2.
...
  revert Ha.
  apply not_in_nth_find_all_loop.
...
  assert (H : ∀ i j a l,
    j + i < a
    → nat_in_list a (nth_find_all_loop (Nat.eqb j) l i) = false). {
... (* oui, bon, c'est pas ça *)
    clear.
    intros * Hja.
    revert i j a Hja.
    induction l as [| b]; intros; [ easy | cbn ].
    remember (j =? b) as jb eqn:Hjb; symmetry in Hjb.
    destruct jb. {
      apply Nat.eqb_eq in Hjb; subst j; cbn.
      destruct (Nat.eq_dec a i) as [Haz| Haz]; [ now subst a; flia Hja | ].
      apply IHl.
...
clear Hl; revert a Ha.
induction l as [| b]; intros; [ now cbn; rewrite match_id | ].
cbn - [ Nat.eqb ].
...
destruct l as [| b]; [ easy | ].
cbn - [ nth_find_loop nth_find_all_loop Nat.eqb ].
f_equal. {
  destruct b; [ easy | ].
  cbn - [ Nat.eqb ].
  remember (0 =? S b) as c; cbn in Heqc; subst c.
  assert
    (Hij : ∀ i j k, i < j →
    nat_in_list i (nth_find_all_loop (Nat.eqb k) l j) = false). {
    clear.
    intros * Hij.
    revert i j Hij.
    induction l; intros; [ easy | ].
    cbn - [ Nat.eqb ].
    destruct (k =? a). {
      cbn - [ Nat.eqb ].
      destruct (Nat.eq_dec i j) as [Hiej| Hiej]; [ flia Hij Hiej | ].
      apply IHl; flia Hij.
    }
    apply IHl; flia Hij.
  }
  rewrite Hij; [ | flia ].
  replace (length l) with (b + (length l - b)). 2: {
    specialize (Hl (S b) (or_introl eq_refl)); cbn in Hl.
    flia Hl.
  }
  rewrite seq_app, map_app; cbn.
  rewrite nth_find_loop_app_2. 2: {
    intros j Hj.
    apply in_map_iff in Hj.
    destruct Hj as (k & Hk & Hkb).
    remember (k =? S b) as kb eqn:Hkb1; symmetry in Hkb1.
    destruct kb. {
      apply Nat.eqb_eq in Hkb1; subst k.
      apply in_seq in Hkb; flia Hkb.
    }
    rewrite <- Hk.
    apply Hij; flia.
  }
  rewrite map_length, seq_length; cbn.
  replace (length l - b) with (1 + (length l - S b)). 2: {
    specialize (Hl (S b) (or_introl eq_refl)); cbn in Hl.
    flia Hl.
  }
  rewrite seq_app, map_app; cbn.
  now rewrite Nat.eqb_refl.
}
replace l with (map (λ i, i) (seq 1 (length l)) at 2. 2: {
  clear; induction l; [ easy | now cbn; rewrite IHl ].
}
...

Theorem locate_dispatch_list : ∀ l,
  (∀ a : nat, a ∈ l → a < length l)
  → locate_list (dispatch_list'' l) = l.
Proof.
intros * Hll.
Print dispatch_list''.
...
destruct l as [| b]; [ easy | ].
remember (b :: l) as l' eqn:Hl'.
assert (Hlz : l' ≠ []) by now subst l'.
clear b l Hl'; rename l' into l.
unfold locate_list.
unfold dispatch_list'' at 2.
rewrite disp_loop''_length; [ | now destruct l ].
unfold dispatch_list''.
remember (length l) as n eqn:Hn.
destruct l as [| a1]; [ easy | cbn ].
rewrite Hn; cbn.
f_equal. {
  unfold cons_nth.
  rewrite nth_find_loop_app_2. 2: {
    intros j Hj.
...
... suite ok
  }
  cbn.
  rewrite firstn_length.
  cbn in Hn; rewrite <- Hn.
  rewrite disp_loop''_length. 2: {
    intros a Ha.
    now apply Hll; right.
  }
  apply Nat.min_l.
  now apply Nat.lt_le_incl, Hll; left.
}
...
*)

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
assert (Hnz : n ≠ 0) by flia Hin.
rewrite (disp_loop_small_r n n Hnz); [ | flia Hiz Hin | ]. 2: {
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

(* pre_partition_in n j k i = true ↔ pre-partition i has the j in k-th set
        0 ≤ i < n^n
        0 ≤ j < n
        0 ≤ k < n
   e.g.
      dispatch n i = [_; _; [...; j; ...]; _; ...]  (* some pre-partition *)
                      <----> <--------->
                         k      k-th
                      <------------------------->
                                  n
   then
     pre_partition_in n j k i = true
 *)

Definition pre_partition_in n j k i :=
  (i + n ^ n - k * n ^ (n - j - 1)) mod (n ^ (n - j)) <? n ^ (n - j - 1).

(* example: all pre-partitions that have the j in k-th set *)
Compute (let n := 3 in let j := 1 in let k := 2 in map (λ i, (i, dispatch n i))
(filter (pre_partition_in n j k) (seq 0 (n ^ n)))).

(* perhaps useless, but for the sport...
   this is supposed to be a property of pre-partitions *)

(* ... but hard to prove
Theorem pre_partition_in_iff : ∀ n j k i,
  i < n ^ n
  → j < n
  → k < n
  → pre_partition_in n j k i = true ↔ j ∈ nth k (dispatch n i) [].
Proof.
intros * Hin Hjn Hkn.
split. {
  intros Hpp.
  apply Nat.ltb_lt in Hpp.
  destruct n; [ easy | ].
  destruct n. {
    destruct j; [ clear Hjn | flia Hjn ].
    destruct k; [ clear Hkn | flia Hkn ].
    now left.
  }
  destruct n. {
    cbn - [ "/" "mod" ].
    destruct j; [ clear Hjn | ]. {
      destruct k; [ clear Hkn | ]. {
        cbn - [ "/" "mod" ].
        cbn - [ "mod" ] in Hpp.
        rewrite Nat.sub_0_r in Hpp.
        rewrite <- Nat.add_mod_idemp_r in Hpp; [ | easy ].
        rewrite Nat.mod_same in Hpp; [ | easy ].
        rewrite Nat.add_0_r in Hpp.
        rewrite Nat.mod_small in Hpp; [ | easy ].
        destruct i; [ now left | ].
        destruct i; [ now left | flia Hpp ].
      }
      destruct k; [ clear Hkn | flia Hkn ].
      cbn - [ "mod" ] in Hpp.
      replace (i + 4 - 2) with (i + 2) in Hpp by flia.
      destruct i; [ cbn in Hpp; flia Hpp | ].
      destruct i; [ cbn in Hpp; flia Hpp | ].
      destruct i; [ now left | ].
      destruct i; [ now left | cbn in Hin; flia Hin ].
    }
    destruct j; [ clear Hjn | flia Hjn ].
    destruct k; [ clear Hkn | ]. {
      cbn - [ "mod" ] in Hpp.
      rewrite Nat.sub_0_r in Hpp.
      rewrite <- Nat.add_mod_idemp_r in Hpp; [ | easy ].
      replace 4 with (2 * 2) in Hpp by easy.
      rewrite Nat.mod_mul in Hpp; [ | easy ].
      rewrite Nat.add_0_r in Hpp.
      destruct i; [ now right; left | ].
      destruct i. {
        rewrite Nat.mod_small in Hpp; [ flia Hpp | flia ].
      }
      destruct i; [ now left | ].
      destruct i; [ | cbn in Hin; flia Hin ].
      replace 3 with (1 + 1 * 2) in Hpp by flia.
      rewrite Nat.mod_add in Hpp; [ | easy ].
      rewrite Nat.mod_small in Hpp; [ flia Hpp | flia ].
    }
    destruct k; [ clear Hkn | flia Hkn ].
    cbn - [ "mod" ] in Hpp.
    replace (i + 4 - 1) with (i + 1 + 1 * 2) in Hpp by flia.
    rewrite Nat.mod_add in Hpp; [ | easy ].
    destruct i. {
      rewrite Nat.mod_small in Hpp; [ flia Hpp | flia ].
    }
    destruct i; [ now left | ].
    destruct i; [ cbn in Hpp; flia Hpp | ].
    destruct i; [ now right; left | cbn in Hin; flia Hin ].
  }
  destruct n. {
(* etc, etc. *)
...
*)

Theorem dispatch_locate : ∀ n ll,
  is_pre_partition n ll
  → dispatch n (locate ll) = ll.
Proof.
intros * Hll.
destruct Hll as (Hlen & Hall & Hin & Hnd).
unfold dispatch.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  rewrite Hnz; cbn.
  now apply length_zero_iff_nil in Hnz.
}
unfold locate.
(* example: (18, [2; 0; 0], [[1; 2]; []; [0]]) *)
Compute (let n := 3 in let ll := [[1; 2]; []; [0]] in locate_list ll).
Compute (let n := 3 in let l := [2; 0; 0] in dispatch_list n l).
...
Search (list nat → list (list nat)).
Check locate_list.
...
unfold locate_list.
rewrite Hlen.
destruct ll as [| l1]; [ now symmetry in Hlen | ].
Print locate_list.
cbn.
...
rewrite List_fold_left_map.
Compute (let n := 3 in let ll := [[1; 2]; []; [0]] in
fold_left (λ c b : nat, c * n + nth_find (nat_in_list b) ll) (seq 0 n) 0).
...
Compute (let n := 3 in map (λ p, (locate p, rev (to_radix n (locate p)), p)) (pre_partitions n)).
...
= [ (0, [0; 0; 0], [[0; 1; 2]; []; []]);
    (1, [0; 0; 1], [[0; 1]; [2]; []]);
    (2, [0; 0; 2], [[0; 1]; []; [2]]);
    (3, [0; 1; 0], [[0; 2]; [1]; []]);
    (4, [0; 1; 1], [[0]; [1; 2]; []]);
    (5, [0; 1; 2], [[0]; [1]; [2]]);
    (6, [0; 2; 0], [[0; 2]; []; [1]]);
    (7, [0; 2; 1], [[0]; [2]; [1]]);
    (8, [0; 2; 2], [[0]; []; [1; 2]]);
    (9, [1; 0; 0], [[1; 2]; [0]; []]);
   (10, [1; 0; 1], [[1]; [0; 2]; []]);
   (11, [1; 0; 2], [[1]; [0]; [2]]);
   (12, [1; 1; 0], [[2]; [0; 1]; []]);
   (13, [1; 1; 1], [[]; [0; 1; 2]; []]);
   (14, [1; 1; 2], [[]; [0; 1]; [2]]);
   (15, [1; 2; 0], [[2]; [0]; [1]]);
   (16, [1; 2; 1], [[]; [0; 2]; [1]]);
   (17, [1; 2; 2], [[]; [0]; [1; 2]]);
   (18, [2; 0; 0], [[1; 2]; []; [0]]);
   (19, [2; 0; 1], [[1]; [2]; [0]]);
   (20, [2; 0; 2], [[1]; []; [0; 2]]);
   (21, [2; 1; 0], [[2]; [1]; [0]]);
   (22, [2; 1; 1], [[]; [1; 2]; [0]]);
   (23, [2; 1; 2], [[]; [1]; [0; 2]]);
   (24, [2; 2; 0], [[2]; []; [0; 1]]);
   (25, [2; 2; 1], [[]; [2]; [0; 1]]);
   (26, [2; 2; 2], [[]; []; [0; 1; 2]])]
     : list (nat * list nat * list (list nat))
...

(* not so simple to prove...
Theorem is_partition_iff : ∀ n p, n ≠ 0 →
  is_pre_partition n p ↔ p ∈ pre_partitions n.
Proof.
intros * Hnz.
split; intros Hn. {
  destruct Hn as (Hlen & Hmem & Hin & Hnp).
  unfold pre_partitions.
...
*)
*)

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
unfold pre_partitions'''.
unfold dispatch'''.
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
assert (H : map (λ i, [i]) (seq 0 n) ∈ pre_partitions n). {
  unfold pre_partitions.
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
Compute (nth 27 (pre_partitions 4) []).
...
1→0 = 0 radix 1
2→1 = 01 radix 2
3→5 = 012 radix 3
4→27 = 0123 radix 4
1*n^2 + 2*n^1 + 3*n^0
(n-1)n^0+(n-2)n^1+(n-3)^n^2+...+1*n^(n-2)+0*n^(n-1)
  Σ (i=0,n-1) i*n^(n-1-i)
= Σ (i=0,n-1) (n-1-i)*n^i

map (λ i, [i]) (seq 0 n) = nth ... (pre_partitions n) []
...
}
apply in_split in H.
destruct H as (l1 & l2 & Hll).
rewrite Hll.
(* prove that the "map (λ i, [i]) (seq 0 n)" has the maximum length *)
...
(* previous attempt to prove
    map (λ i, [i]) (seq 0 n) ∈ pre_partitions n *)
  unfold pre_partitions.
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
