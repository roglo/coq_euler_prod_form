(* Fpolynomial.v *)

(* polynomials on a ring *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Import List ListNotations.

Require Import Misc Ring2 Rsummation.

(* (lap : list as polynomial) *)

Record poly {A} {rng : ring A} := mkpoly
  { lap : list A;
    lap_prop : last lap 1%Rng ≠ 0%Rng }.

Arguments mkpoly {_} {_}.

Definition lap_zero {α} {r : ring α} := mkpoly [] rng_1_neq_0.
Definition lap_one {α} {r : ring α} := mkpoly [1%Rng] rng_1_neq_0.

(* normalization *)

Fixpoint strip_0s {A} {rng : ring A} la :=
  match la with
  | [] => []
  | a :: la' => if rng_eq_dec a 0%Rng then strip_0s la' else la
  end.

Lemma strip_0s_app {A} {rng : ring A} : ∀ la lb,
  strip_0s (la ++ lb) =
  match strip_0s la with
  | [] => strip_0s lb
  | lc => lc ++ lb
  end.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]; [ apply IHla | easy ].
Qed.

Definition lap_norm {A} {rng : ring A} la := rev (strip_0s (rev la)).

Theorem poly_norm_prop {A} {rng : ring A} : ∀ la,
  last (lap_norm la) 1%Rng ≠ 0%Rng.
Proof.
intros.
unfold lap_norm.
induction la as [| a]; [ apply rng_1_neq_0 | cbn ].
rewrite strip_0s_app.
remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; cbn. {
  destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]; [ apply rng_1_neq_0 | easy ].
}
cbn in IHla.
rewrite List_last_app.
now rewrite List_last_app in IHla.
Qed.

Definition poly_norm {A} {rng : ring A} la :=
  mkpoly (lap_norm la) (poly_norm_prop la).

(**)
Require Import ZArith.

Theorem Z_1_neq_0 : (1 ≠ 0)%Z.
Proof. easy. Qed.

Definition Z_ring : ring Z :=
  {| rng_zero := 0%Z;
     rng_one := 1%Z;
     rng_add a b := (a + b)%Z;
     rng_mul a b := (a * b)%Z;
     rng_opp a := (- a)%Z;
     rng_1_neq_0 := Z_1_neq_0;
     rng_eq_dec := Z.eq_dec;
     rng_add_comm := Z.add_comm;
     rng_add_assoc := Z.add_assoc;
     rng_add_0_l := Z.add_0_l;
     rng_add_opp_l := Z.add_opp_diag_l;
     rng_mul_comm := Z.mul_comm;
     rng_mul_assoc := Z.mul_assoc;
     rng_mul_1_l := Z.mul_1_l;
     rng_mul_add_distr_l := Z.mul_add_distr_l |}.

(*
Compute (@lap_norm Z Z_ring [3; 4; 0; 5; 0; 0; 0]%Z).
*)
(**)

(* addition *)

Fixpoint lap_add {α} {r : ring α} al1 al2 :=
  match al1 with
  | [] => al2
  | a1 :: bl1 =>
      match al2 with
      | [] => al1
      | a2 :: bl2 => (a1 + a2)%Rng :: lap_add bl1 bl2
      end
  end.

Definition lap_opp {α} {r : ring α} la := List.map rng_opp la.
Definition lap_sub {A} {rng : ring A} la lb := lap_add la (lap_opp lb).

Definition poly_add {A} {rng : ring A} p1 p2 :=
  poly_norm (lap_add (lap p1) (lap p2)).

(*
Compute (@poly_add Z Z_ring (poly_norm [3;4;5]%Z) (poly_norm [2;3;-4;5]%Z)).
Compute (@poly_add Z Z_ring (poly_norm [3;4;5]%Z) (poly_norm [2;3;-5]%Z)).
*)

(* multiplication *)

Fixpoint lap_convol_mul {α} {r : ring α} al1 al2 i len :=
  match len with
  | O => []
  | S len1 =>
      (Σ (j = 0, i), List.nth j al1 0 * List.nth (i - j) al2 0)%Rng ::
      lap_convol_mul al1 al2 (S i) len1
  end.

Definition lap_mul {α} {R : ring α} la lb :=
  lap_convol_mul la lb 0 (pred (length la + length lb)).

Definition poly_mul {A} {rng : ring A} p1 p2 :=
  poly_norm (lap_mul (lap p1) (lap p2)).

(*
Compute (@lap_mul Z Z_ring [3;4;5]%Z [2;3;-4;5]%Z).
Compute (@poly_mul Z Z_ring (poly_norm [3;4;5]%Z) (poly_norm [2;3;-4;5]%Z)).
*)

(* power *)

Fixpoint lap_power {α} {r : ring α} la n :=
  match n with
  | O => [1%Rng]
  | S m => lap_mul la (lap_power la m)
  end.

Definition poly_power {A} {rng : ring A} pol n :=
  poly_norm (lap_power (lap pol) n).

(*
Compute (@poly_power Z Z_ring (poly_norm [1; -1]%Z) 4).
*)

(* composition *)

Definition lap_compose {α} {r : ring α} la lb :=
  List.fold_right (λ c accu, lap_add (lap_mul accu lb) [c]) [] la.

Definition lap_compose2 {α} {r : ring α} la lb :=
  List.fold_right
    (λ i accu,
     lap_add accu (lap_mul [List.nth i la 0] (lap_power lb i)))%Rng
    [] (List.seq 0 (length la)).

(* *)

Fixpoint list_pad {α} n (zero : α) rem :=
  match n with
  | O => rem
  | S n1 => zero :: list_pad n1 zero rem
  end.

Declare Scope lap_scope.
Delimit Scope lap_scope with lap.
Notation "0" := lap_zero : lap_scope.
Notation "1" := lap_one : lap_scope.
Notation "- a" := (lap_opp a) : lap_scope.
Notation "a + b" := (lap_add a b) : lap_scope.
Notation "a - b" := (lap_sub a b) : lap_scope.
Notation "a * b" := (lap_mul a b) : lap_scope.
Notation "a ^ b" := (lap_power a b) : lap_scope.

Definition list_nth_def_0 {α} {R : ring α} n l := List.nth n l 0%Rng.

(* *)

Theorem lap_convol_mul_comm : ∀ α (R : ring α) l1 l2 i len,
  lap_convol_mul l1 l2 i len = lap_convol_mul l2 l1 i len.
Proof.
intros α R l1 l2 i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
rewrite summation_rtl.
apply summation_compat; intros j (_, Hj).
rewrite Nat.add_0_r.
rewrite rng_mul_comm.
apply rng_mul_compat; [ idtac | reflexivity ].
rewrite Nat_sub_sub_distr; [ idtac | easy ].
rewrite Nat.sub_diag, Nat.add_0_l; reflexivity.
Qed.

Theorem lap_convol_mul_nil_l : ∀ α (R : ring α) l i len,
  lap_norm (lap_convol_mul [] l i len) = [].
Proof.
intros α R l i len.
unfold lap_norm.
revert i.
induction len; intros; [ reflexivity | ].
cbn - [ summation ].
rewrite all_0_summation_0. {
  rewrite strip_0s_app; cbn.
  specialize (IHlen (S i)).
  apply List_eq_rev_nil in IHlen.
  rewrite IHlen.
  now destruct (rng_eq_dec 0%Rng 0%Rng).
}
intros k (_, Hk).
now rewrite match_id, rng_mul_0_l.
Qed.

Theorem lap_convol_mul_nil_r : ∀ α (R : ring α) l i len,
  lap_norm (lap_convol_mul l [] i len) = [].
Proof.
intros α R l i len.
rewrite lap_convol_mul_comm.
apply lap_convol_mul_nil_l.
Qed.

(*
Theorem lap_convol_mul_succ : ∀ α (r : ring α) la lb i len,
  lap_norm (lap_convol_mul la lb i (S len)) =
  lap_norm
    (lap_convol_mul la lb i len ++
     [Σ (j = 0, i + len),
      List.nth j la 0 * List.nth (i + len - j) lb 0])%Rng.
Proof.
intros α r la lb i len.
unfold lap_norm; f_equal.
cbn - [ summation ].
rewrite rev_app_distr.
cbn - [ strip_0s summation ].
...
revert la lb i.
induction len; intros. {
  cbn - [ summation ].
  now rewrite Nat.add_0_r.
}
cbn - [ strip_0s summation ].
rewrite strip_0s_app.
rewrite IHlen.
...
intros α r la lb i len.
revert la lb i.
induction len; intros; simpl.
 rewrite Nat.add_0_r; reflexivity.

 constructor; [ reflexivity | idtac ].
 simpl in IHlen.
 rewrite IHlen.
 rewrite Nat.add_succ_r, Nat.add_succ_l.
 reflexivity.
Qed.
*)

(*
Theorem lap_eq_app_0s : ∀ α (r : ring α) la lb,
  List.Forall (λ b, b = 0)%Rng lb
  → ap_eq la (la ++ lb).
Proof.
intros α r la lb Hz.
induction la as [| a]; simpl.
 induction lb as [| b]; [ reflexivity | idtac ].
 constructor.
  now apply Forall_inv in Hz.

  apply IHlb.
  now apply Forall_inv_tail in Hz.

 constructor; [ reflexivity | assumption ].
Qed.

Theorem lap_convol_mul_more : ∀ α (r : ring α) la lb i n,
  lap_eq (lap_convol_mul la lb i (pred (length la + length lb)))
    (lap_convol_mul la lb i (pred (length la + length lb) + n)).
Proof.
intros α r la lb i n.
induction n; [ rewrite Nat.add_0_r; reflexivity | idtac ].
rewrite Nat.add_succ_r.
rewrite lap_convol_mul_succ.
rewrite IHn.
apply lap_eq_app_0s.
constructor; [ idtac | constructor ].
apply all_0_summation_0.
intros j (_, Hj).
apply rng_mul_eq_0.
destruct (le_dec (length la) j) as [H1| H1].
 left.
 rewrite List.nth_overflow; [ reflexivity | assumption ].

 apply Nat.nle_gt in H1.
 destruct (le_dec (length lb) (i + (pred (length la + length lb) + n) - j))
  as [H2| H2].
  right.
  rewrite List.nth_overflow; [ reflexivity | assumption ].

  exfalso; apply H2; clear H2.
  rewrite <- Nat.add_pred_l.
   apply Nat.lt_le_pred in H1.
   apply Nat.le_add_le_sub_l.
   rewrite Nat.add_shuffle0, Nat.add_assoc.
   apply Nat.add_le_mono_r.
   rewrite Nat.add_comm, <- Nat.add_assoc.
   eapply Nat.le_trans; eauto .
   apply Nat.le_sub_le_add_l.
   rewrite Nat.sub_diag.
   apply Nat.le_0_l.

   intros H; rewrite H in H1.
   revert H1; apply Nat.nlt_0_r.
Qed.

Instance lap_mul_morph {A} {rng : ring A} :
  Proper (lap_eq ==> lap_eq ==> lap_eq) lap_mul.
Proof.
intros a c Hac b d Hbd.
unfold lap_mul; simpl.
do 2 rewrite lap_convol_mul_more.
rewrite Hac, Hbd in |- * at 1.
rewrite Nat.add_comm.
reflexivity.
Qed.

Instance lap_power_morph {A} {rng : ring A} :
  Proper (lap_eq ==> eq ==> lap_eq) lap_power.
Proof.
intros la lb Hlab n n' Hnn.
subst n'.
induction n; [ reflexivity | simpl ].
rewrite IHn, Hlab; reflexivity.
Qed.

Instance cons_lap_eq_morph {A} {rng : ring A} :
  Proper (rng_eq ==> lap_eq ==> lap_eq) cons.
Proof.
intros a b H la lb Hab.
constructor; assumption.
Qed.
*)

Theorem list_nth_lap_eq : ∀ α (r : ring α) la lb,
  (∀ i, (List.nth i la 0 = List.nth i lb 0)%Rng)
  → lap_norm la = lap_norm lb.
Proof.
intros α r la lb Hi.
unfold lap_norm; f_equal.
revert lb Hi.
induction la as [| a]; intros. {
  induction lb as [| b]; [ reflexivity | ].
  specialize (Hi 0) as H; cbn in H.
  subst b; cbn.
  rewrite strip_0s_app; cbn.
  remember (strip_0s (rev lb)) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]; [ now destruct (rng_eq_dec _ _) | ].
  assert (H : lap_norm [] = lap_norm lb). {
    unfold lap_norm; cbn.
    cbn in IHlb.
    change (rev [] = rev (strip_0s (rev lb))).
    f_equal.
    rewrite Hlc.
    apply IHlb.
    intros i; cbn; rewrite match_id.
    now specialize (Hi (S i)); cbn in Hi.
  }
  cbn in H.
  unfold lap_norm in H.
  rewrite Hlc in H.
  symmetry in H.
  now apply List_eq_rev_nil in H.
} {
  cbn.
  rewrite strip_0s_app.
  remember (strip_0s (rev la)) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]. {
    assert (Hla : ∀ i, nth i la 0%Rng = 0%Rng). {
      intros i.
      clear - Hlc.
      revert i.
      induction la as [| a]; intros; [ now cbn; rewrite match_id | cbn ].
      destruct i. {
        cbn in Hlc.
        rewrite strip_0s_app in Hlc; cbn in Hlc.
        remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
        destruct lb as [| b]; [ now destruct (rng_eq_dec a 0%Rng) | easy ].
      }
      apply IHla.
      cbn in Hlc.
      rewrite strip_0s_app in Hlc; cbn in Hlc.
      remember (strip_0s (rev la)) as lb eqn:Hlb; symmetry in Hlb.
      destruct lb as [| b]; [ now destruct (rng_eq_dec a 0%Rng) | easy ].
    }
    cbn.
    destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
      assert (Hlb : ∀ i, nth i lb 0%Rng = 0%Rng). {
        intros.
        rewrite <- Hi; cbn.
        destruct i; [ easy | ].
        apply Hla.
      }
      clear - Hlb.
      induction lb as [| b]; [ easy | cbn ].
      specialize (Hlb 0) as H1; cbn in H1; subst b.
      rewrite strip_0s_app; cbn.
      rewrite <- IHlb; [ now destruct (rng_eq_dec 0%Rng 0%Rng) | ].
      intros i.
      now specialize (Hlb (S i)).
    }
    destruct lb as [| b]; [ now specialize (Hi 0); cbn in Hi | cbn ].
    rewrite strip_0s_app; cbn.
    remember (strip_0s (rev lb)) as ld eqn:Hld; symmetry in Hld.
    destruct ld as [| d]. {
      destruct (rng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
        subst b.
        now specialize (Hi 0).
      }
      f_equal.
      now specialize (Hi 0).
    }
    specialize (IHla lb).
    assert (H : ∀ i : nat, nth i la 0%Rng = nth i lb 0%Rng). {
      intros i.
      now specialize (Hi (S i)); cbn in Hi.
    }
    specialize (IHla H); clear H.
    now rewrite Hld in IHla.
  }
  destruct lb as [| b]. {
    specialize (IHla []).
    assert (H : ∀ i : nat, nth i la 0%Rng = nth i [] 0%Rng). {
      intros i; cbn; rewrite match_id.
      now specialize (Hi (S i)).
    }
    now specialize (IHla H).
  }
  cbn.
  rewrite strip_0s_app; cbn.
  remember (strip_0s (rev lb)) as ld eqn:Hld; symmetry in Hld.
  destruct ld as [| d]. {
    destruct (rng_eq_dec b 0%Rng) as [Hbz| Hbz]. {
      subst b.
      specialize (IHla lb).
      assert (H : ∀ i : nat, nth i la 0%Rng = nth i lb 0%Rng). {
        intros i.
        now specialize (Hi (S i)); cbn in Hi.
      }
      specialize (IHla H); clear H.
      now rewrite Hld in IHla.
    }
    specialize (IHla lb).
    assert (H : ∀ i : nat, nth i la 0%Rng = nth i lb 0%Rng). {
      intros i.
      now specialize (Hi (S i)); cbn in Hi.
    }
    specialize (IHla H); clear H.
    now rewrite Hld in IHla.
  }
...
      subst a.
      clear - Hi Hla.
      revert la Hi Hla.
      induction lb as [| b]; intros; [ easy | ].
      cbn.
...
    destruct (rng_eq_dec a 0%Rng) as [Haz| Haz]. {
      subst a.
      clear - Hlc Hi.
      revert la Hlc Hi.
      induction lb as [| b]; intros; [ easy | ].
      specialize (Hi 0) as H1; cbn in H1; subst b; cbn.
      rewrite strip_0s_app; cbn.
      remember (strip_0s (rev lb)) as ld eqn:Hld; symmetry in Hld.
      destruct ld as [| d]; [ now destruct (rng_eq_dec _ _) | ].
      specialize (IHlb _ Hlc).
      assert (H : ∀ i : nat, nth i (0%Rng :: la) 0%Rng = nth i lb 0%Rng). {
        intros i; cbn.
        destruct i. {
          specialize (Hi 1) as H1.
          cbn in H1; rewrite <- H1.
          clear - Hi Hlc.
          induction la as [| a]; [ easy | ].
          cbn in Hlc; cbn.
          rewrite strip_0s_app in Hlc.
          remember (strip_0s (rev la)) as ld eqn:Hld; symmetry in Hld.
          destruct ld as [| d]; [ | easy ].
          cbn in Hlc.
          now destruct (rng_eq_dec a 0%Rng).
        }
...
  apply IHlb; intros i.
  pose proof (Hi (S i)) as H; simpl in H; rewrite <- H.
  destruct i; reflexivity.

 induction lb as [| b].
  constructor.
   pose proof (Hi O) as H.
   assumption.

   apply IHla; intros i.
   pose proof (Hi (S i)) as H; simpl in H; rewrite H.
   destruct i; reflexivity.

  constructor.
   pose proof (Hi O) as H.
   assumption.

   apply IHla; intros i.
   pose proof (Hi (S i)) as H.
   assumption.
Qed.
*)

Theorem lap_add_0_l {α} {r : ring α} : ∀ la, lap_add [] la = la.
Proof. easy. Qed.

Theorem lap_add_0_r {α} {r : ring α} : ∀ la, lap_add la [] = la.
Proof. intros; now destruct la. Qed.

Theorem lap_mul_0_l {α} {r : ring α} : ∀ la, lap_norm (lap_mul [] la) = [].
Proof. intros; apply lap_convol_mul_nil_l. Qed.

Theorem lap_mul_0_r : ∀ α (r : ring α) la, lap_norm (lap_mul la []) = [].
Proof. intros α r la; apply lap_convol_mul_nil_r. Qed.

Section lap.

Context {α : Type}.
Context {r : ring α}.

(* addition theorems *)

Theorem lap_add_comm : ∀ al1 al2,
  lap_add al1 al2 = lap_add al2 al1.
Proof.
intros al1 al2.
revert al2.
induction al1; intros; [ now destruct al2 | ].
destruct al2; [ easy | cbn ].
now rewrite rng_add_comm, IHal1.
Qed.

Theorem lap_add_assoc : ∀ al1 al2 al3,
  lap_add al1 (lap_add al2 al3) = lap_add (lap_add al1 al2) al3.
Proof.
intros al1 al2 al3.
revert al2 al3.
induction al1; intros; [ easy | ].
destruct al2; [ easy | cbn ].
destruct al3; [ easy | cbn ].
rewrite rng_add_assoc.
now rewrite IHal1.
Qed.

Theorem lap_add_add_swap : ∀ la lb lc,
  lap_add (lap_add la lb) lc = lap_add (lap_add la lc) lb.
Proof.
intros la lb lc.
do 2 rewrite <- lap_add_assoc.
now rewrite (lap_add_comm lb).
Qed.

(*
Theorem lap_app_add : ∀ la lb,
  (la ++ lb = la + list_pad (length la) 0%Rng lb)%lap.
Proof.
intros la lb.
induction la as [| a]; [ reflexivity | simpl ].
rewrite rng_add_0_r.
constructor; [ reflexivity | assumption ].
Qed.

Theorem lap_app_at_eq : ∀ a b la,
  (a = b)%Rng → (la ++ [a] = la ++ [b])%lap.
Proof.
intros * Hab.
revert a b Hab.
induction la as [| c]; intros; [ now constructor | cbn ].
constructor; [ easy | ].
now apply IHla.
Qed.

Theorem lap_add_map2 : ∀ β (f g : β → α) la,
  (List.map f la + List.map g la = List.map (λ b, (f b + g b)%Rng) la)%lap.
Proof.
intros β f g la.
induction la as [| b]; [ reflexivity | simpl ].
constructor; auto with Arith.
Qed.
*)

(* multiplication theorems *)

Theorem lap_mul_comm : ∀ a b, lap_mul a b = lap_mul b a.
Proof.
intros a b.
unfold lap_mul.
now rewrite lap_convol_mul_comm, Nat.add_comm.
Qed.

(*
Theorem list_nth_lap_convol_mul_aux : ∀ la lb n i len,
  pred (List.length la + List.length lb) = (i + len)%nat
  → (List.nth n (lap_convol_mul la lb i len) 0%Rng =
     Σ (j = 0, n + i),
     List.nth j la 0 * List.nth (n + i - j) lb 0)%Rng.
Proof.
intros la lb n i len Hlen.
revert la lb i n Hlen.
induction len; intros.
 simpl.
 rewrite Nat.add_0_r in Hlen.
 rewrite all_0_summation_0; [ destruct n; reflexivity | idtac ].
 intros j (_, Hj).
 destruct (le_dec (length la) j) as [H1| H1].
  rewrite List.nth_overflow; [ idtac | assumption ].
  rewrite rng_mul_0_l; reflexivity.

  destruct (le_dec (length lb) (n + i - j)) as [H2| H2].
   rewrite rng_mul_comm.
   rewrite List.nth_overflow; [ idtac | assumption ].
   rewrite rng_mul_0_l; reflexivity.

   exfalso; apply H2; clear Hj H2.
   apply Nat.nle_gt in H1; subst i.
   rewrite <- Nat.add_pred_l.
    apply Nat.lt_le_pred in H1.
    apply Nat.le_add_le_sub_l.
    rewrite Nat.add_assoc.
    apply Nat.add_le_mono_r.
    rewrite Nat.add_comm.
    eapply Nat.le_trans; eauto .
    apply Nat.le_sub_le_add_l.
    rewrite Nat.sub_diag.
    apply Nat.le_0_l.

    intros H; rewrite H in H1.
    revert H1; apply Nat.nlt_0_r.

 simpl.
 destruct n; [ reflexivity | idtac ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
 rewrite IHlen; [ idtac | assumption ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l; reflexivity.
Qed.

(* to be unified perhaps with list_nth_convol_mul below *)
Theorem list_nth_lap_convol_mul : ∀ la lb i len,
  len = pred (length la + length lb)
  → (List.nth i (lap_convol_mul la lb 0 len) 0 =
     Σ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%Rng.
Proof.
intros la lb i len Hlen.
symmetry in Hlen.
rewrite list_nth_lap_convol_mul_aux; [ idtac | assumption ].
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul : ∀ la lb lc k,
  (Σ (i = 0, k),
     List.nth i la 0 *
     List.nth (k - i)
       (lap_convol_mul lb lc 0 (pred (length lb + length lc)))
       0 =
   Σ (i = 0, k),
     List.nth i la 0 *
     Σ (j = 0, k - i),
       List.nth j lb 0 * List.nth (k - i - j) lc 0)%Rng.
Proof.
intros la lb lc k.
apply summation_compat; intros i (_, Hi).
apply rng_mul_compat_l.
rewrite list_nth_lap_convol_mul; reflexivity.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul_2 : ∀ la lb lc k,
   (Σ (i = 0, k),
      List.nth i lc 0 *
      List.nth (k - i)
        (lap_convol_mul la lb 0 (pred (length la + length lb)))  0 =
    Σ (i = 0, k),
      List.nth (k - i) lc 0 *
      Σ (j = 0, i),
        List.nth j la 0 * List.nth (i - j) lb 0)%Rng.
Proof.
intros la lb lc k.
rewrite summation_rtl.
apply summation_compat; intros i (_, Hi).
rewrite Nat.add_0_r.
apply rng_mul_compat_l.
rewrite Nat_sub_sub_distr; [ idtac | easy ].
rewrite Nat.sub_diag.
apply list_nth_lap_convol_mul; reflexivity.
Qed.
*)

Theorem lap_mul_assoc : ∀ la lb lc,
  lap_mul la (lap_mul lb lc) = lap_mul (lap_mul la lb) lc.
Proof.
intros la lb lc.
symmetry; rewrite lap_mul_comm.
unfold lap_mul.
...
apply list_nth_lap_eq; intros k.
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
rewrite summation_mul_list_nth_lap_convol_mul_2; symmetry.
rewrite summation_mul_list_nth_lap_convol_mul; symmetry.
rewrite <- summation_summation_mul_swap.
rewrite <- summation_summation_mul_swap.
rewrite summation_summation_exch.
rewrite summation_summation_shift.
apply summation_compat; intros i Hi.
apply summation_compat; intros j Hj.
rewrite rng_mul_comm, rng_mul_assoc.
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm, Nat.sub_add_distr.
reflexivity.
Qed.

Theorem lap_mul_shuffle0 : ∀ la lb lc,
  lap_eq (lap_mul (lap_mul la lb) lc) (lap_mul (lap_mul la lc) lb).
Proof.
intros la lb lc.
do 2 rewrite <- lap_mul_assoc.
apply lap_mul_compat; [ reflexivity | apply lap_mul_comm ].
Qed.

Theorem lap_eq_skipn_succ : ∀ cl i,
  lap_eq (List.nth i cl 0%Rng :: List.skipn (S i) cl) (List.skipn i cl).
Proof.
intros cl i.
revert i.
induction cl as [| c]; intros; simpl.
 destruct i; constructor; reflexivity.

 destruct i; [ reflexivity | apply IHcl ].
Qed.

Theorem lap_convol_mul_1_l : ∀ cl i len,
  length cl = (i + len)%nat
  → lap_eq (lap_convol_mul [1%Rng] cl i len) (List.skipn i cl).
Proof.
intros cl i len Hlen.
revert cl i Hlen.
induction len; intros.
 simpl.
 rewrite Nat.add_0_r in Hlen.
 rewrite <- Hlen.
 now rewrite skipn_none.

 simpl.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite rng_mul_1_l, Nat.sub_0_r.
 rewrite all_0_summation_0.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
  rewrite rng_add_0_r, IHlen; [ clear | assumption ].
  apply lap_eq_skipn_succ.

  intros j (Hj, Hji).
  destruct j; [ exfalso; revert Hj; apply Nat.nle_succ_0 | idtac ].
  destruct j; rewrite rng_mul_0_l; reflexivity.
Qed.

Fixpoint lap_convol_mul_add al1 al2 al3 i len :=
  match len with
  | O => []
  | S len1 =>
      (Σ (j = 0, i),
       List.nth j al1 0 *
       (List.nth (i - j) al2 0 + List.nth (i - j) al3 0))%Rng ::
       lap_convol_mul_add al1 al2 al3 (S i) len1
  end.

(* *)

Theorem list_nth_add : ∀ k la lb,
  (List.nth k (lap_add la lb) 0 =
   List.nth k la 0 + List.nth k lb 0)%Rng.
Proof.
intros k la lb.
revert la lb.
induction k; intros.
 destruct la as [| a]; simpl; [ rewrite rng_add_0_l; reflexivity | idtac ].
 destruct lb as [| b]; simpl; [ rewrite rng_add_0_r; reflexivity | idtac ].
 reflexivity.

 destruct la as [| a]; simpl; [ rewrite rng_add_0_l; reflexivity | idtac ].
 destruct lb as [| b]; simpl; [ rewrite rng_add_0_r; reflexivity | idtac ].
 apply IHk.
Qed.

Theorem lap_convol_mul_lap_add : ∀ la lb lc i len,
  lap_eq
    (lap_convol_mul la (lap_add lb lc) i len)
    (lap_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
apply summation_compat; intros j (_, Hj).
apply rng_mul_compat_l.
rewrite list_nth_add; reflexivity.
Qed.

Theorem lap_add_lap_convol_mul : ∀ la lb lc i len,
   lap_eq
     (lap_add
        (lap_convol_mul la lb i len)
        (lap_convol_mul la lc i len))
     (lap_convol_mul_add la lb lc i len).
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite <- summation_add_distr.
apply summation_compat; intros j (_, Hj).
rewrite rng_mul_add_distr_l; reflexivity.
Qed.

Theorem lap_mul_add_distr_l : ∀ la lb lc,
  lap_eq (lap_mul la (lap_add lb lc))
    (lap_add (lap_mul la lb) (lap_mul la lc)).
Proof.
intros la lb lc.
unfold lap_mul.
remember (pred (length la + length (lap_add lb lc))) as labc.
remember (pred (length la + length lb)) as lab.
remember (pred (length la + length lc)) as lac.
rewrite Heqlabc.
rewrite lap_convol_mul_more with (n := (lab + lac)%nat).
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite lap_convol_mul_more with (n := (labc + lac)%nat).
rewrite <- Heqlab.
rewrite lap_add_comm.
rewrite Heqlac.
rewrite lap_convol_mul_more with (n := (labc + lab)%nat).
rewrite <- Heqlac.
rewrite Nat.add_comm.
rewrite lap_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite lap_convol_mul_lap_add.
rewrite lap_add_lap_convol_mul.
reflexivity.
Qed.

Theorem lap_mul_add_distr_r : ∀ la lb lc,
  lap_eq (lap_mul (lap_add la lb) lc)
    (lap_add (lap_mul la lc) (lap_mul lb lc)).
Proof.
intros la lb lc.
rewrite lap_mul_comm, lap_mul_add_distr_l, lap_mul_comm.
apply lap_add_compat; [ reflexivity | apply lap_mul_comm ].
Qed.

Theorem lap_convol_mul_1_r : ∀ la i len,
  (i + len = length la)%nat
  → lap_eq (lap_convol_mul la [1%Rng] i len) (List.skipn i la).
Proof.
intros la i len Hlen.
revert la i Hlen.
induction len; intros; simpl.
 rewrite Nat.add_0_r in Hlen; subst i.
 now rewrite skipn_none.

 rewrite summation_rtl.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite Nat.add_0_r, Nat.sub_0_r.
 rewrite Nat.sub_diag; simpl.
 rewrite rng_mul_1_r.
 rewrite all_0_summation_0.
  rewrite rng_add_0_r.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
  rewrite IHlen; [ idtac | assumption ].
  apply lap_eq_skipn_succ.

  intros j (Hj, Hji).
  rewrite Nat_sub_sub_distr; [ idtac | easy ].
  rewrite Nat.sub_diag.
  destruct j; [ exfalso; revert Hj; apply Nat.nle_succ_0 | idtac ].
  destruct j; rewrite rng_mul_0_r; reflexivity.
Qed.

Theorem lap_mul_1_l : ∀ la, lap_eq (lap_mul [1%Rng] la) la.
Proof.
intros la.
unfold lap_mul.
apply lap_convol_mul_1_l; simpl.
reflexivity.
Qed.

Theorem lap_mul_1_r : ∀ la, lap_eq (lap_mul la [1%Rng]) la.
Proof.
intros la.
unfold lap_mul.
apply lap_convol_mul_1_r; simpl.
rewrite Nat.add_comm; reflexivity.
Qed.

(* to be unified perhaps with list_nth_lap_convol_mul above *)
Theorem list_nth_convol_mul : ∀ la lb i k len,
  (i + len)%nat = pred (length la + length lb)
  → (List.nth k (lap_convol_mul la lb i len) 0 =
     Σ (j = 0, i + k),
     List.nth j la 0 * List.nth (i + k - j) lb 0)%Rng.
Proof.
intros la lb i k len Hilen.
revert la lb i k Hilen.
induction len; intros; simpl.
 rewrite match_id; simpl.
 rewrite all_0_summation_0; [ reflexivity | simpl ].
 intros j (_, Hj).
 destruct (lt_dec j (length la)) as [Hja| Hja].
  destruct (lt_dec (i + k - j) (length lb)) as [Hjb| Hjb].
   exfalso; flia Hilen Hja Hjb.

   apply rng_mul_eq_0; right.
   apply Nat.nlt_ge in Hjb.
   rewrite List.nth_overflow; [ reflexivity | assumption ].

  apply rng_mul_eq_0; left.
  apply Nat.nlt_ge in Hja.
  rewrite List.nth_overflow; [ reflexivity | assumption ].

 destruct k; [ rewrite Nat.add_0_r; reflexivity | idtac ].
 rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hilen.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 apply IHlen; assumption.
Qed.

Theorem list_nth_lap_mul : ∀ la lb k,
  (List.nth k (lap_mul la lb) 0 =
   Σ (i = 0, k), List.nth i la 0 * List.nth (k - i) lb 0)%Rng.
Proof.
intros la lb k.
apply list_nth_convol_mul; reflexivity.
Qed.

(* compose theorems *)

Theorem lap_mul_fold_add_distr : ∀ β la li (g : β → list α) x,
  lap_eq
    (lap_mul x (List.fold_right (λ i accu, lap_add accu (g i)) la li))
    (List.fold_right (λ i accu, lap_add accu (lap_mul x (g i)))
       (lap_mul x la) li).
Proof.
intros uβ la li g x.
revert la x.
induction li as [| j]; intros; [ reflexivity | simpl ].
rewrite lap_mul_add_distr_l.
rewrite IHli; reflexivity.
Qed.

Theorem list_fold_right_seq : ∀ g h la lb s t len,
  lap_eq la lb
  → (∀ x y z, lap_eq y z → lap_eq (g x y) (g x z))
    → (∀ i accu, lap_eq (g (s + i)%nat accu) (h (t + i)%nat accu))
      → lap_eq
          (List.fold_right g la (List.seq s len))
          (List.fold_right h lb (List.seq t len)).
Proof.
intros g h la lb s t len Hab Hg Hgh.
revert g h la lb s t Hab Hg Hgh.
induction len; intros; [ assumption | simpl ].
pose proof (Hgh O (List.fold_right h lb (List.seq (S t) len))) as H.
do 2 rewrite Nat.add_0_r in H.
rewrite <- H.
apply Hg.
apply IHlen; [ assumption | assumption | idtac ].
intros i accu.
do 2 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
apply Hgh.
Qed.

Theorem lap_compose_compose2 : ∀ la lb,
  lap_eq (lap_compose la lb) (lap_compose2 la lb).
Proof.
intros la lb.
revert lb.
induction la as [| a]; intros; [ reflexivity | simpl ].
rewrite IHla.
symmetry; clear.
unfold lap_compose2.
rewrite lap_mul_comm.
rewrite lap_mul_fold_add_distr.
rewrite lap_add_comm.
remember [a] as aa; simpl; subst aa.
rewrite lap_add_comm.
apply lap_add_compat; [ apply lap_mul_1_r | idtac ].
apply list_fold_right_seq.
 rewrite lap_mul_0_r; reflexivity.

 intros x y z Hyz.
 rewrite Hyz; reflexivity.

 intros i accu; simpl.
 apply lap_add_compat; [ reflexivity | simpl ].
 rewrite lap_mul_comm, <- lap_mul_assoc.
 apply lap_mul_compat; [ reflexivity | idtac ].
 apply lap_mul_comm.
Qed.

Theorem lap_compose_compat : ∀ la lb lc ld,
  lap_eq la lc
  → lap_eq lb ld
    → lap_eq (lap_compose la lb) (lap_compose lc ld).
Proof.
intros la lb lc ld Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

(* power *)

Theorem lap_power_add : ∀ la i j,
  lap_eq (lap_power la (i + j))
    (lap_mul (lap_power la i) (lap_power la j)).
Proof.
intros la i j.
revert j.
induction i; intros; simpl.
 rewrite lap_mul_1_l; reflexivity.

 rewrite IHi, lap_mul_assoc; reflexivity.
Qed.

Theorem lap_power_mul : ∀ la lb n,
  lap_eq
    (lap_power (lap_mul la lb) n)
    (lap_mul (lap_power la n) (lap_power lb n)).
Proof.
intros la lb n.
revert la lb.
induction n; intros; simpl.
 rewrite lap_mul_1_l; reflexivity.

 rewrite IHn.
 do 2 rewrite <- lap_mul_assoc.
 apply lap_mul_compat; [ reflexivity | idtac ].
 do 2 rewrite lap_mul_assoc.
 apply lap_mul_compat; [ idtac | reflexivity ].
 apply lap_mul_comm.
Qed.

Theorem lap_power_1 : ∀ la, (la ^ 1 = la)%lap.
Proof.
intros la; simpl.
rewrite lap_mul_1_r; reflexivity.
Qed.

Theorem list_nth_pad_lt : ∀ i s (v : α) cl d,
  (i < s)%nat
  → List.nth i (list_pad s v cl) d = v.
Proof.
intros i s v cl d His.
revert i His.
induction s; intros.
 exfalso; revert His; apply lt_n_0.

 simpl.
 destruct i; [ reflexivity | idtac ].
 apply IHs, lt_S_n; assumption.
Qed.

Theorem list_nth_pad_sub : ∀ i s (v : α) cl d,
  (s ≤ i)%nat
  → List.nth i (list_pad s v cl) d = List.nth (i - s) cl d.
Proof.
intros i s v cl d Hsi.
revert i Hsi.
induction s; intros; [ rewrite Nat.sub_0_r; reflexivity | simpl ].
destruct i; [ exfalso; revert Hsi; apply Nat.nle_succ_0 | idtac ].
apply le_S_n in Hsi.
rewrite Nat.sub_succ.
apply IHs; assumption.
Qed.

Theorem lap_mul_cons_l : ∀ a la lb,
  lap_eq (lap_mul (a :: la) lb)
    (lap_add (lap_mul [a] lb) (0%Rng :: lap_mul la lb)).
Proof.
intros a la lb.
unfold lap_mul.
apply list_nth_lap_eq; intros k.
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
rewrite list_nth_add.
rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
destruct k.
 rewrite summation_only_one.
 rewrite summation_only_one.
 rewrite rng_add_0_r; reflexivity.

 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite Nat.sub_0_r.
 symmetry.
 rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
 rewrite all_0_summation_0.
  rewrite Nat.sub_0_r.
  simpl.
  rewrite rng_add_0_r.
  apply rng_add_compat_l.
  rewrite list_nth_lap_convol_mul; [ idtac | reflexivity ].
  rewrite summation_succ_succ; reflexivity.

  intros i (Hi, Hik); simpl.
  destruct i; [ exfalso; flia Hi | simpl ].
  destruct i; rewrite rng_mul_0_l; reflexivity.
Qed.

Theorem lap_mul_cons_r : ∀ la b lb,
  lap_eq (lap_mul la (b :: lb))
    (lap_add (lap_mul la [b]) (0%Rng :: lap_mul la lb)).
Proof.
intros la b lb.
rewrite lap_mul_comm.
rewrite lap_mul_cons_l.
rewrite lap_mul_comm.
apply lap_add_compat; [ reflexivity | idtac ].
rewrite lap_mul_comm; reflexivity.
Qed.

Theorem lap_eq_0 : lap_eq [0%Rng] [].
Proof. constructor; reflexivity. Qed.

Theorem lap_convol_mul_cons_succ : ∀ b la lb i len,
  length la ≤ S i
  → lap_eq (lap_convol_mul la (b :: lb) (S i) len)
       (lap_convol_mul la lb i len).
Proof.
intros * Hla.
revert b la lb i Hla.
induction len; intros; [ reflexivity | idtac ].
constructor; [ idtac | apply IHlen; flia Hla ].
rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
rewrite List.nth_overflow; [ | easy ].
rewrite rng_mul_0_l, rng_add_0_r.
apply summation_compat; intros j (_, Hj).
apply rng_mul_compat_l.
rewrite Nat.sub_succ_l; [ reflexivity | assumption ].
Qed.

Theorem lap_mul_cons : ∀ a b la lb,
  lap_eq (lap_mul (a :: la) (b :: lb))
     ((a * b)%Rng
      :: lap_add (lap_add (lap_mul la [b]) (lap_mul [a] lb))
         (0%Rng :: lap_mul la lb)).
Proof.
intros a b la lb.
rewrite lap_mul_cons_l; simpl.
rewrite summation_only_one.
rewrite rng_add_0_r.
constructor; [ reflexivity | idtac ].
rewrite lap_mul_cons_r.
unfold lap_mul; simpl.
rewrite lap_add_assoc.
apply lap_add_compat; [ idtac | reflexivity ].
rewrite lap_add_comm.
apply lap_add_compat; [ reflexivity | idtac ].
now apply lap_convol_mul_cons_succ.
Qed.

(* *)

Theorem lap_fold_compat_l : ∀ A (g h : A → _) la lb l,
  lap_eq la lb
  → lap_eq
      (List.fold_right (λ v accu, lap_add accu (lap_mul (g v) (h v)))
         la l)
      (List.fold_right (λ v accu, lap_add accu (lap_mul (g v) (h v)))
         lb l).
Proof.
intros A g h la lb l Heq.
induction l; [ assumption | simpl; rewrite IHl; reflexivity ].
Qed.

Theorem lap_compose_single : ∀ a lb lc,
  (lap_compose ([a] * lb) lc = [a] * lap_compose lb lc)%lap.
Proof.
intros a lb lc.
induction lb as [| b].
 simpl; rewrite lap_mul_0_r; reflexivity.

 rewrite lap_mul_cons_r; simpl.
 rewrite summation_only_one, rng_add_0_r, IHlb.
 rewrite lap_mul_add_distr_l, lap_mul_assoc.
 apply lap_add_compat; [ reflexivity | idtac ].
 rewrite lap_mul_cons; simpl.
 rewrite lap_mul_0_r.
 constructor; [ reflexivity | idtac ].
 rewrite lap_eq_0; reflexivity.
Qed.

Theorem lap_compose_add : ∀ la lb lc,
  (lap_compose (la + lb) lc = lap_compose la lc + lap_compose lb lc)%lap.
Proof.
intros la lb lc.
revert lb lc.
induction la as [| a]; intros; [ reflexivity | simpl ].
destruct lb as [| b]; simpl.
 rewrite lap_add_0_r; reflexivity.

 rewrite IHla.
 rewrite lap_mul_add_distr_r.
 do 2 rewrite <- lap_add_assoc.
 apply lap_add_compat_l.
 symmetry.
 rewrite lap_add_comm.
 rewrite <- lap_add_assoc.
 apply lap_add_compat_l.
 rewrite lap_add_comm; reflexivity.
Qed.

Theorem lap_compose_mul : ∀ la lb lc,
  (lap_compose (la * lb) lc = lap_compose la lc * lap_compose lb lc)%lap.
Proof.
(* inspiré de apply_lap_mul *)
intros la lb lc.
revert lb lc.
induction la as [| a]; intros; simpl.
 do 2 rewrite lap_mul_0_l; reflexivity.

 destruct lb as [| b]; simpl.
  do 2 rewrite lap_mul_0_r; reflexivity.

  rewrite lap_mul_cons; simpl.
  do 2 rewrite lap_compose_add; simpl.
  do 2 rewrite IHla; simpl.
  rewrite lap_mul_0_l, lap_add_0_l.
  do 3 rewrite lap_mul_add_distr_r; simpl.
  rewrite lap_mul_add_distr_l; simpl.
  rewrite lap_mul_add_distr_r; simpl.
  rewrite lap_mul_add_distr_r; simpl.
  do 2 rewrite lap_mul_assoc.
  do 2 rewrite lap_add_assoc; simpl.
  apply lap_add_compat.
   rewrite lap_eq_0, lap_mul_0_l, lap_add_0_r.
   rewrite lap_add_comm, lap_add_assoc.
   rewrite <- lap_add_assoc.
   rewrite <- lap_add_assoc.
   apply lap_add_compat.
    apply lap_mul_compat; [ idtac | reflexivity ].
    rewrite lap_mul_shuffle0; reflexivity.

    symmetry; rewrite lap_add_comm.
    apply lap_add_compat.
     rewrite lap_mul_shuffle0; reflexivity.

     apply lap_mul_compat; [ idtac | reflexivity ].
     symmetry.
     apply lap_compose_single.

   rewrite lap_mul_cons; simpl.
   rewrite lap_mul_0_r.
   constructor; [ reflexivity | idtac ].
   rewrite lap_eq_0; reflexivity.
Qed.

End lap.

Theorem lap_add_opp_l {α} {r : ring α} : ∀ la, (- la + la = 0)%lap.
Proof.
intros.
induction la as [| a]; [ reflexivity | simpl ].
rewrite IHla, rng_add_opp_l.
constructor; reflexivity.
Qed.

Theorem lap_mul_compat_l {α} {r : ring α} : ∀ a b c,
  lap_eq a b
  → lap_eq (lap_mul c a) (lap_mul c b).
Proof.
intros a b c Hab.
rewrite Hab; reflexivity.
Qed.

Definition lap_ring {α} {r : ring α} : ring (list α) :=
  {| rng_zero := lap_zero;
     rng_one := lap_one;
     rng_add := lap_add;
     rng_mul := lap_mul;
     rng_opp := lap_opp;
     rng_eq := lap_eq;
     rng_eq_refl := lap_eq_refl;
     rng_eq_sym := lap_eq_sym;
     rng_eq_trans := lap_eq_trans;
     rng_add_comm := lap_add_comm;
     rng_add_assoc := lap_add_assoc;
     rng_add_0_l := lap_add_0_l';
     rng_add_opp_l := lap_add_opp_l;
     rng_add_compat_l := lap_add_compat_l;
     rng_mul_comm := lap_mul_comm;
     rng_mul_assoc := lap_mul_assoc;
     rng_mul_1_l := lap_mul_1_l;
     rng_mul_compat_l := lap_mul_compat_l;
     rng_mul_add_distr_l := lap_mul_add_distr_l |}.

Canonical Structure lap_ring.

(* polynomial type *)

Record polynomial α := mkpol { al : list α }.
Arguments mkpol {_}.
Arguments al {_}.

Declare Scope poly_scope.
Delimit Scope poly_scope with pol.

Definition poly_eq {α} {r : ring α} x y := lap_eq (al x) (al y).

Definition poly_zero {α} {r : ring α} : polynomial α := mkpol [].
Definition poly_one {α} {r : ring α} : polynomial α := mkpol [1]%Rng.

Definition poly_add {α} {r : ring α} pol1 pol2 :=
  {| al := lap_add (al pol1) (al pol2) |}.

Definition poly_opp {α} {r : ring α} pol :=
  {| al := lap_opp (al pol) |}.

Definition poly_sub {α} {r : ring α} pol1 pol2 :=
  poly_add pol1 (poly_opp pol2).

Definition poly_mul {α} {r : ring α} pol1 pol2 :=
  {| al := lap_mul (al pol1) (al pol2) |}.

Definition poly_power {α} {r : ring α} pol n :=
  mkpol (lap_power (al pol) n).

Definition poly_compose {α} {r : ring α} a b :=
  mkpol (lap_compose (al a) (al b)).

Definition poly_compose2 {α} {r : ring α} a b :=
  mkpol (lap_compose2 (al a) (al b)).

Definition xpow {α} {r : ring α} i := mkpol (repeat 0%Rng i ++ [1%Rng]).

Notation "0" := poly_zero : poly_scope.
Notation "1" := poly_one : poly_scope.
Notation "- a" := (poly_opp a) : poly_scope.
Notation "a = b" := (poly_eq a b) : poly_scope.
Notation "a ≠ b" := (¬poly_eq a b) : poly_scope.
Notation "a + b" := (poly_add a b) : poly_scope.
Notation "a - b" := (poly_sub a b) : poly_scope.
Notation "a * b" := (poly_mul a b) : poly_scope.
Notation "a ^ b" := (poly_power a b) : poly_scope.
Notation "a ∘ b" := (poly_compose a b) (left associativity, at level 40) :
  poly_scope.
Notation "'ⓧ' ^ a" := (xpow a) (at level 30, format "'ⓧ' ^ a") : poly_scope.
Notation "'ⓧ'" := (xpow 1) (at level 30, format "'ⓧ'") : poly_scope.
Notation "a × x" := (poly_mul {| al := [a] |} x) (at level 40).

Theorem poly_eq_refl {α} {r : ring α} : reflexive _ poly_eq.
Proof.
intros pol.
unfold poly_eq; reflexivity.
Qed.

Theorem poly_eq_sym {α} {r : ring α} : symmetric _ poly_eq.
Proof.
intros pol1 pol2 Heq.
unfold poly_eq; symmetry; assumption.
Qed.

Theorem poly_eq_trans {α} {r : ring α} : transitive _ poly_eq.
Proof.
intros pol1 pol2 pol3 H1 H2.
unfold poly_eq; etransitivity; eassumption.
Qed.

Add Parametric Relation {α} {r : ring α} : (polynomial α) poly_eq
 reflexivity proved by poly_eq_refl
 symmetry proved by poly_eq_sym
 transitivity proved by poly_eq_trans
 as poly_eq_rel.

Instance al_morph {A} {rng : ring A} :
  Proper (poly_eq ==> lap_eq) al.
Proof. intros a b Hab; easy. Qed.

Instance mkpol_morph {A} {rng : ring A} :
  Proper (lap_eq ==> poly_eq) mkpol.
Proof. now intros la lb Hlab. Qed.

Instance poly_add_morph {A} {rng : ring A} :
  Proper (poly_eq ==> poly_eq ==> poly_eq) poly_add.
Proof.
intros a c Hac b d Hbd.
unfold poly_eq, poly_add; simpl.
unfold poly_eq in Hac, Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Instance poly_mul_morph {A} {rng : ring A} :
  Proper (poly_eq ==> poly_eq ==> poly_eq) poly_mul.
Proof.
intros a c Hac b d Hbd.
unfold poly_eq, poly_mul, lap_mul; simpl.
unfold poly_eq in Hac, Hbd.
remember (al a) as la.
remember (al b) as lb.
remember (al c) as lc.
remember (al d) as ld.
revert Hac Hbd; clear; intros.
do 2 rewrite lap_convol_mul_more.
rewrite Hac, Hbd in |- * at 1.
rewrite Nat.add_comm.
reflexivity.
Qed.

Instance poly_compose_morph {A} {rng : ring A} :
  Proper (poly_eq ==> poly_eq ==> poly_eq) poly_compose.
Proof.
intros a c Hac b d Hbd.
unfold poly_eq; simpl.
rewrite Hac, Hbd; reflexivity.
Qed.

Section poly.

Context {α : Type}.
Context {r : ring α}.

Theorem poly_add_compat : ∀ a b c d,
  (a = c)%pol
  → (b = d)%pol
    → (a + b = c + d)%pol.
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Theorem poly_add_comm : ∀ a b, (a + b = b + a)%pol.
Proof.
intros.
unfold poly_eq; cbn.
apply lap_add_comm.
Qed.

Theorem poly_add_assoc : ∀ pol1 pol2 pol3,
  (pol1 + (pol2 + pol3) = (pol1 + pol2) + pol3)%pol.
Proof. intros; apply lap_add_assoc. Qed.

Theorem poly_add_0_l : ∀ pol, (0 + pol = pol)%pol.
Proof. intros; apply lap_add_0_l'. Qed.

Theorem poly_add_opp_l : ∀ pol, (- pol + pol = 0)%pol.
Proof. intros; apply lap_add_opp_l. Qed.

Theorem poly_add_compat_l : ∀ a b c,
  (a = b)%pol → (c + a = c + b)%pol.
Proof. now intros; apply lap_add_compat_l. Qed.

Theorem poly_mul_compat_l : ∀ a b c,
  (a = b)%pol → (c * a = c * b)%pol.
Proof. now intros; apply lap_mul_compat_l. Qed.

Theorem poly_mul_compat : ∀ a b c d,
  (a = c)%pol
  → (b = d)%pol
    → (a * b = c * d)%pol.
Proof.
intros a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Theorem poly_mul_comm : ∀ a b, (a * b = b * a)%pol.
Proof.
intros a b.
unfold poly_eq; simpl.
unfold lap_mul; simpl.
rewrite Nat.add_comm.
rewrite lap_convol_mul_comm; reflexivity.
Qed.

Theorem poly_mul_assoc : ∀ P Q R,
  (P * (Q * R) = (P * Q) * R)%pol.
Proof.
intros P Q R.
apply lap_mul_assoc.
Qed.

Theorem poly_mul_1_l : ∀ a, (1 * a = a)%pol.
Proof. intros; apply lap_mul_1_l. Qed.

Theorem poly_mul_1_r : ∀ a, (a * 1 = a)%pol.
Proof. intros; rewrite poly_mul_comm; apply poly_mul_1_l. Qed.

Theorem poly_mul_add_distr_l : ∀ P Q R,
  (P * (Q + R) = P * Q + P * R)%pol.
Proof.
intros P Q R.
apply lap_mul_add_distr_l.
Qed.

End poly.

Definition polynomial_ring {α} {r : ring α} : ring (polynomial α) :=
  {| rng_zero := poly_zero;
     rng_one := poly_one;
     rng_add := poly_add;
     rng_mul := poly_mul;
     rng_opp := poly_opp;
     rng_eq := poly_eq;
     rng_eq_refl := poly_eq_refl;
     rng_eq_sym := poly_eq_sym;
     rng_eq_trans := poly_eq_trans;
     rng_add_comm := poly_add_comm;
     rng_add_assoc := poly_add_assoc;
     rng_add_0_l := poly_add_0_l;
     rng_add_opp_l := poly_add_opp_l;
     rng_add_compat_l := poly_add_compat_l;
     rng_mul_comm := poly_mul_comm;
     rng_mul_assoc := poly_mul_assoc;
     rng_mul_1_l := poly_mul_1_l;
     rng_mul_compat_l := poly_mul_compat_l;
     rng_mul_add_distr_l := poly_mul_add_distr_l |}.

(* allows to use ring theorems on polynomials *)
Canonical Structure polynomial_ring.

(* *)

Definition eval_lap {α} {R : ring α} la x :=
  (List.fold_right (λ c accu, accu * x + c) 0 la)%Rng.

Definition eval_poly {α} {R : ring α} pol :=
  eval_lap (al pol).

Theorem lap_add_map : ∀ α β (Rα : ring α) (Rβ : ring β) (f : α → β) la lb,
  (∀ a b, (f (a + b) = f a + f b)%Rng)
  → (List.map f (la + lb) = List.map f la + List.map f lb)%lap.
Proof.
clear.
intros α β Rα Rβ f la lb Hab.
revert lb.
induction la as [| a]; intros; [ reflexivity | simpl ].
destruct lb as [| b]; [ reflexivity | simpl ].
rewrite Hab, IHla; reflexivity.
Qed.

Instance eval_lap_morph {A} {rng : ring A} :
  Proper (lap_eq ==> rng_eq ==> rng_eq) eval_lap.
Proof.
intros la lb Hll x y Hxy.
destruct la as [| a]. {
  unfold eval_lap; cbn; symmetry.
  clear - Hll.
  induction lb as [| b]; [ easy | cbn ].
  apply lap_eq_nil_cons_inv in Hll.
  destruct Hll as (Hb, Hlb).
  specialize (IHlb Hlb).
  now rewrite IHlb, rng_mul_0_l, rng_add_0_l.
} {
  unfold eval_lap; cbn.
  revert a la Hll.
  induction lb as [| b]; intros. {
    cbn.
    apply lap_eq_cons_nil_inv in Hll.
    destruct Hll as (Ha, Hla).
    rewrite Ha, rng_add_0_r.
    clear - Hla.
    induction la as [| a]; [ now rewrite rng_mul_0_l | cbn ].
    apply lap_eq_cons_nil_inv in Hla.
    destruct Hla as (Ha, Hla).
    specialize (IHla Hla).
    rewrite IHla, Ha, rng_add_0_l.
    apply rng_mul_0_l.
  } {
    cbn.
    apply lap_eq_cons_cons_inv in Hll.
    destruct Hll as (Hab, Hll).
    rewrite Hab.
    destruct la as [| a']. {
      cbn.
      rewrite rng_mul_0_l, rng_add_0_l.
      clear - Hll.
      revert b.
      induction lb as [| b']; intros. {
        cbn.
        now rewrite rng_mul_0_l, rng_add_0_l.
      } {
        cbn.
        apply lap_eq_nil_cons_inv in Hll.
        destruct Hll as (Hb', Hlb).
        specialize (IHlb Hlb).
        now rewrite <- IHlb, Hb', rng_mul_0_l, rng_add_0_l.
      }
    } {
      cbn.
      rewrite IHlb; [ | easy ].
      now rewrite Hxy.
    }
  }
}
Qed.

Instance eval_poly_morph {A} {rng : ring A} :
  Proper (poly_eq ==> rng_eq ==> rng_eq) eval_poly.
Proof.
intros (la) (lb) Hpp x y Hxy.
unfold "="%pol in Hpp; cbn in Hpp.
unfold eval_poly.
cbn - [ eval_lap ].
now rewrite Hxy, Hpp.
Qed.

Theorem eval_lap_const {A} {rng : ring A} : ∀ c x, (eval_lap [c] x = c)%Rng.
Proof.
intros; cbn.
now rewrite rng_mul_0_l, rng_add_0_l.
Qed.

Theorem eval_poly_add {A} {rng : ring A} : ∀ p1 p2 x,
  (eval_poly (p1 + p2)%pol x = eval_poly p1 x + eval_poly p2 x)%Rng.
Proof.
intros (la) (lb) *.
unfold eval_poly; cbn.
revert lb.
induction la as [| a]; intros. {
  cbn.
  now rewrite rng_add_0_l.
} {
  cbn.
  destruct lb as [| b]. {
    cbn.
    now rewrite rng_add_0_r.
  } {
    cbn.
    rewrite rng_add_comm.
    rewrite (rng_add_comm _ a).
    do 2 rewrite <- rng_add_assoc.
    apply rng_add_compat_l.
    rewrite rng_add_comm.
    rewrite rng_add_assoc.
    rewrite IHla.
    now rewrite rng_mul_add_distr_r.
  }
}
Qed.

Theorem eval_poly_opp {A} {rng : ring A} : ∀ pol x,
  (eval_poly (- pol)%pol x = - eval_poly pol x)%Rng.
Proof.
intros (la) *.
induction la as [| a]; intros. {
  cbn.
  symmetry; apply rng_opp_0.
} {
  cbn.
  rewrite rng_opp_add_distr.
  apply rng_add_compat_r.
  rewrite <- rng_mul_opp_l.
  now rewrite IHla.
}
Qed.

Theorem eval_poly_sub {A} {rng : ring A} : ∀ p1 p2 x,
  (eval_poly (p1 - p2)%pol x = eval_poly p1 x - eval_poly p2 x)%Rng.
Proof.
intros (la) (lb) *.
unfold poly_sub, rng_sub.
rewrite eval_poly_add.
apply rng_add_compat_l.
apply eval_poly_opp.
Qed.

Theorem eval_poly_sum {A} {rng : ring A} (pr := polynomial_ring) : ∀ b e f x,
  (eval_poly (Σ (i = b, e), f i)%pol x = Σ (i = b, e), eval_poly (f i) x)%Rng.
Proof.
intros.
unfold summation.
remember (S e - b) as n.
clear Heqn.
revert b.
induction n; intros; [ easy | ].
cbn - [ eval_poly ].
rewrite eval_poly_add.
now rewrite IHn.
Qed.

Theorem eval_poly_one {A} {rng : ring A} : ∀ x, (eval_poly 1%pol x = 1)%Rng.
Proof.
intros; cbn.
now rewrite rng_mul_0_l, rng_add_0_l.
Qed.

Theorem eval_lap_cons {A} {rng : ring A} : ∀ a la x,
  (eval_lap (a :: la) x = a + eval_lap la x * x)%Rng.
Proof.
intros.
cbn; rewrite rng_add_comm.
now apply rng_add_compat_l.
Qed.

Theorem lap_add_cons_cons {A} {rng : ring A} : ∀ a b la lb,
  ((a :: la) + (b :: lb) = (a + b)%Rng :: la + lb)%lap.
Proof. easy. Qed.

Theorem eval_lap_add {A} {rng : ring A} : ∀ la lb x,
  (eval_lap (la + lb)%lap x = eval_lap la x + eval_lap lb x)%Rng.
Proof.
intros.
revert lb.
induction la as [| a]; intros. {
  now rewrite lap_add_0_l, rng_add_0_l.
}
destruct lb as [| b]. {
  now rewrite lap_add_0_r, rng_add_0_r.
}
rewrite lap_add_cons_cons.
do 3 rewrite eval_lap_cons.
rewrite IHla.
do 2 rewrite <- rng_add_assoc.
apply rng_add_compat_l.
rewrite (rng_add_comm (_ * _)%Rng).
rewrite <- rng_add_assoc.
apply rng_add_compat_l.
rewrite rng_add_comm.
apply rng_mul_add_distr_r.
Qed.

Theorem eval_poly_mul {A} {rng : ring A} : ∀ p1 p2 x,
  (eval_poly (p1 * p2)%pol x = eval_poly p1 x * eval_poly p2 x)%Rng.
Proof.
intros (la) (lb) *.
unfold eval_poly.
cbn - [ eval_lap ].
revert lb.
induction la as [| a]; intros. {
  now rewrite rng_mul_0_l, lap_mul_0_l.
} {
  rewrite eval_lap_cons.
  rewrite rng_mul_add_distr_r.
  rewrite rng_mul_mul_swap.
  rewrite <- IHla.
  rewrite lap_mul_cons_l.
  rewrite eval_lap_add.
  rewrite eval_lap_cons, rng_add_0_l.
  apply rng_add_compat_r.
  clear.
  induction lb as [| b]. {
    cbn.
    now rewrite rng_mul_0_r.
  }
  rewrite lap_mul_cons.
  do 2 rewrite eval_lap_cons.
  rewrite rng_mul_add_distr_l.
  apply rng_add_compat_l.
  rewrite lap_mul_0_l, lap_add_0_l.
  rewrite lap_mul_0_l.
  rewrite eval_lap_add.
  rewrite eval_lap_const.
  rewrite rng_add_0_r.
  rewrite IHlb.
  now rewrite rng_mul_assoc.
}
Qed.

Theorem eval_poly_xpow {A} {rng : ring A} : ∀ k x,
  (eval_poly (ⓧ ^ k)%pol x = x ^ k)%Rng.
Proof.
intros; cbn.
induction k. {
  cbn.
  now rewrite rng_mul_0_l, rng_add_0_l.
} {
  cbn.
  rewrite IHk, rng_add_0_r.
  apply rng_mul_comm.
}
Qed.
