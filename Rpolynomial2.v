(* Fpolynomial.v *)

(* polynomials on a ring *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Setoid Morphisms.
Import List ListNotations.

Require Import Misc Ring2 Rsummation.

(* lap : list as polynomial, i.e. the only field of the record in the
   definition of polynomial after *)

Inductive lap_eq {α} {r : ring α} : list α → list α → Prop :=
  | lap_eq_nil : lap_eq [] []
  | lap_eq_cons : ∀ x1 x2 l1 l2,
      (x1 = x2)%Rng → lap_eq l1 l2 → lap_eq (x1 :: l1) (x2 :: l2)
  | lap_eq_cons_nil : ∀ x l,
      (x = 0)%Rng → lap_eq l [] → lap_eq (x :: l) []
  | lap_eq_nil_cons : ∀ x l,
      (x = 0)%Rng → lap_eq [] l → lap_eq [] (x :: l).

Definition lap_zero {α} {r : ring α} := ([] : list α).
Definition lap_one {α} {r : ring α} := [1%Rng].

Theorem lap_eq_cons_cons_inv : ∀ α (r : ring α) x1 x2 l1 l2,
  lap_eq (x1 :: l1) (x2 :: l2)
  → (x1 = x2)%Rng ∧ lap_eq l1 l2.
Proof.
intros α r x1 x2 l1 l2 H.
inversion H; split; assumption.
Qed.

Theorem lap_eq_cons_nil_inv : ∀ α (r : ring α) x l,
  lap_eq (x :: l) []
  → (x = 0)%Rng ∧ lap_eq l [].
Proof.
intros α r x l H.
inversion H; split; assumption.
Qed.

Theorem lap_eq_nil_cons_inv : ∀ α (r : ring α) x l,
  lap_eq [] (x :: l)
  → (x = 0)%Rng ∧ lap_eq [] l.
Proof.
intros α r x l H.
inversion H; split; assumption.
Qed.

Theorem lap_eq_refl {α} {r : ring α} : reflexive _ lap_eq.
Proof.
intros l.
induction l; constructor; [ reflexivity | assumption ].
Qed.

Theorem lap_eq_sym {α} {r : ring α} : symmetric _ lap_eq.
Proof.
intros l1 l2 Heq.
revert l2 Heq.
induction l1 as [| x1]; intros. {
  induction l2 as [| x2]; constructor; apply lap_eq_nil_cons_inv in Heq. {
    now destruct Heq.
  } {
    now apply IHl2; destruct Heq.
  }
} {
  induction l2 as [| x2]. {
    apply lap_eq_cons_nil_inv in Heq; destruct Heq.
    constructor; [ easy | now apply IHl1 ].
  } {
    apply lap_eq_cons_cons_inv in Heq; destruct Heq.
    constructor; [ easy | now apply IHl1 ].
  }
}
Qed.

Theorem lap_eq_trans {α} {r : ring α} : transitive _ lap_eq.
Proof.
intros l1 l2 l3 H1 H2.
revert l1 l3 H1 H2.
induction l2 as [| x2]; intros.
 revert l3 H2.
 induction l1 as [| x1]; intros; [ assumption | idtac ].
 destruct l3 as [| x3]; [ assumption | idtac ].
 apply lap_eq_cons_nil_inv in H1.
 apply lap_eq_nil_cons_inv in H2.
 constructor.
  etransitivity; [ destruct H1; eassumption | idtac ].
  destruct H2; symmetry; assumption.

  apply IHl1; [ destruct H1 | destruct H2 ]; assumption.

 destruct l1 as [| x1].
  apply lap_eq_nil_cons_inv in H1.
  destruct l3 as [| x3]; constructor.
   apply lap_eq_cons_cons_inv in H2.
   destruct H1, H2.
   etransitivity; [ symmetry; eassumption | assumption ].

   apply lap_eq_cons_cons_inv in H2.
   apply IHl2; [ destruct H1 | destruct H2 ]; assumption.

  apply lap_eq_cons_cons_inv in H1.
  destruct l3 as [| x3]; constructor.
   apply lap_eq_cons_nil_inv in H2.
   destruct H1, H2.
   etransitivity; eassumption.

   apply lap_eq_cons_nil_inv in H2.
   apply IHl2; [ destruct H1 | destruct H2 ]; assumption.

   apply lap_eq_cons_cons_inv in H2.
   destruct H1, H2.
   etransitivity; eassumption.

   apply lap_eq_cons_cons_inv in H2.
   apply IHl2; [ destruct H1 | destruct H2 ]; assumption.
Qed.

Add Parametric Relation α (r : ring α) : (list α) lap_eq
 reflexivity proved by lap_eq_refl
 symmetry proved by lap_eq_sym
 transitivity proved by lap_eq_trans
 as lap_eq_rel.

Theorem lap_eq_list_fold_right : ∀ α (K : ring α) β g h x (l : list β),
  (∀ i a b, i ∈ l → lap_eq a b → lap_eq (g i a) (h i b))
  → lap_eq (List.fold_right g x l) (List.fold_right h x l).
Proof.
intros α K β g h x l H.
induction l as [| y]; intros; [ reflexivity | simpl ].
apply H; [ left; reflexivity | idtac ].
apply IHl; intros i a b Hi Heq.
apply H; [ right; assumption | assumption ].
Qed.

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

(* power *)

Fixpoint lap_power {α} {r : ring α} la n :=
  match n with
  | O => [1%Rng]
  | S m => lap_mul la (lap_power la m)
  end.

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
Notation "a = b" := (lap_eq a b) : lap_scope.
Notation "a ≠ b" := (¬lap_eq a b) : lap_scope.
Notation "a + b" := (lap_add a b) : lap_scope.
Notation "a - b" := (lap_sub a b) : lap_scope.
Notation "a * b" := (lap_mul a b) : lap_scope.
Notation "a ^ b" := (lap_power a b) : lap_scope.

Definition list_nth_def_0 {α} {R : ring α} n l := List.nth n l 0%Rng.

(* *)

Instance list_nth_rng_morph {A} {rng : ring A} :
  Proper (eq ==> lap_eq ==> rng_eq) list_nth_def_0.
Proof.
intros n n' Hnn la lb Hab.
subst n'.
unfold list_nth_def_0.
revert n lb Hab.
induction la as [| a]; intros; simpl.
 rewrite match_id.
 symmetry.
 revert n.
 induction lb as [| b]; intros; [ destruct n; reflexivity | idtac ].
 apply lap_eq_nil_cons_inv in Hab.
 destruct Hab as (Hb, Hlb).
 destruct n; [ assumption | simpl ].
 apply IHlb; assumption.

 destruct n; simpl.
  destruct lb as [| b]; simpl.
   apply lap_eq_cons_nil_inv in Hab.
   destruct Hab; assumption.

   apply lap_eq_cons_cons_inv in Hab.
   destruct Hab; assumption.

  destruct lb as [| b]; simpl.
   apply lap_eq_cons_nil_inv in Hab.
   destruct Hab as (_, Hla).
   clear a IHla.
   revert n.
   induction la as [| a]; intros.
    destruct n; reflexivity.

    destruct n; simpl.
     apply lap_eq_cons_nil_inv in Hla.
     destruct Hla; assumption.

     apply lap_eq_cons_nil_inv in Hla.
     apply IHla; destruct Hla; assumption.

   apply lap_eq_cons_cons_inv in Hab.
   destruct Hab as (_, Hab).
   apply IHla; assumption.
Qed.

Theorem lap_eq_nil_lap_add_r : ∀ α (r : ring α) la lb,
  lap_eq [] la
  → lap_eq lb (lap_add la lb).
Proof.
intros α r la lb H.
revert lb.
induction la as [| a]; intros; [ reflexivity | simpl ].
destruct lb as [| b]; [ assumption | idtac ].
apply lap_eq_nil_cons_inv in H.
destruct H as (Ha, Hla).
constructor; [ rewrite Ha, rng_add_0_l; reflexivity | idtac ].
apply IHla; assumption.
Qed.

Theorem lap_eq_nil_lap_add_l : ∀ α (r : ring α) la lb,
  lap_eq [] lb
  → lap_eq la (lap_add la lb).
Proof.
intros α r la lb H.
revert la.
induction lb as [| b]; intros; [ destruct la; reflexivity | idtac ].
destruct la as [| a]; [ assumption | simpl ].
apply lap_eq_nil_cons_inv in H.
destruct H as (Hb, Hlb).
constructor; [ rewrite Hb, rng_add_0_r; reflexivity | idtac ].
apply IHlb; assumption.
Qed.

Instance lap_add_morph {A} {rng : ring A} :
  Proper (lap_eq ==> lap_eq ==> lap_eq) lap_add.
Proof.
intros la lc Hac lb ld Hbd.
revert lb lc ld Hac Hbd.
induction la as [| a]; intros.
 destruct lc as [| c]; intros; [ assumption | idtac ].
 apply lap_eq_nil_cons_inv in Hac.
 destruct Hac as (Hc, Hlc); simpl.
 destruct ld as [| d].
  etransitivity; [ eassumption | constructor; assumption ].

  destruct lb as [| b].
   apply lap_eq_nil_cons_inv in Hbd.
   destruct Hbd as (Hd, Hld).
   constructor; [ rewrite Hc, rng_add_0_l; assumption | idtac ].
   etransitivity; [ eassumption | idtac ].
   apply lap_eq_nil_lap_add_r; assumption.

   apply lap_eq_cons_cons_inv in Hbd.
   destruct Hbd as (Hbd, Hlbd).
   constructor; [ rewrite Hc, rng_add_0_l; assumption | idtac ].
   etransitivity; [ eassumption | idtac ].
   apply lap_eq_nil_lap_add_r; assumption.

 destruct lb as [| b].
  destruct lc as [| c]; [ etransitivity; eassumption | idtac ].
  destruct ld as [| d]; [ assumption | simpl ].
  apply lap_eq_cons_cons_inv in Hac.
  destruct Hac as (Hac, Hlac).
  apply lap_eq_nil_cons_inv in Hbd.
  destruct Hbd as (Hd, Hld).
  constructor; [ rewrite Hd, rng_add_0_r; assumption | idtac ].
  etransitivity; [ eassumption | idtac ].
  apply lap_eq_nil_lap_add_l; assumption.

  destruct lc as [| c].
   apply lap_eq_cons_nil_inv in Hac.
   destruct Hac as (Ha, Hla); simpl.
   destruct ld as [| d].
    apply lap_eq_cons_nil_inv in Hbd.
    destruct Hbd as (Hb, Hlb).
    constructor; [ rewrite Ha, rng_add_0_l; assumption | idtac ].
    rewrite IHla; try eassumption; reflexivity.

    apply lap_eq_cons_cons_inv in Hbd.
    destruct Hbd as (Hbd, Hlbd).
    constructor; [ rewrite Ha, rng_add_0_l; assumption | idtac ].
    rewrite IHla; try eassumption; reflexivity.

   apply lap_eq_cons_cons_inv in Hac.
   destruct Hac as (Hac, Hlac); simpl.
   destruct ld as [| d].
    apply lap_eq_cons_nil_inv in Hbd.
    destruct Hbd as (Hb, Hlb).
    constructor; [ rewrite Hb, rng_add_0_r; assumption | idtac ].
    rewrite IHla; try eassumption.
    destruct lc; reflexivity.

    apply lap_eq_cons_cons_inv in Hbd.
    destruct Hbd as (Hbd, Hlbd).
    constructor; [ rewrite Hac, Hbd; reflexivity | apply IHla; assumption ].
Qed.

Theorem lap_convol_mul_comm : ∀ α (R : ring α) l1 l2 i len,
  lap_eq (lap_convol_mul l1 l2 i len) (lap_convol_mul l2 l1 i len).
Proof.
intros α R l1 l2 i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite summation_rtl.
apply summation_compat; intros j (_, Hj).
rewrite Nat.add_0_r.
rewrite rng_mul_comm.
apply rng_mul_compat; [ idtac | reflexivity ].
rewrite Nat_sub_sub_distr; [ idtac | easy ].
rewrite Nat.sub_diag, Nat.add_0_l; reflexivity.
Qed.

Theorem lap_convol_mul_nil_l : ∀ α (R : ring α) l i len,
  lap_eq (lap_convol_mul [] l i len) [].
Proof.
intros α R l i len.
revert i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen ].
rewrite all_0_summation_0; [ reflexivity | idtac ].
intros k (_, Hk).
destruct k; rewrite rng_mul_0_l; reflexivity.
Qed.

Theorem lap_convol_mul_nil_r : ∀ α (R : ring α) l i len,
  lap_eq (lap_convol_mul l [] i len) [].
Proof.
intros α R l i len.
rewrite lap_convol_mul_comm.
apply lap_convol_mul_nil_l.
Qed.

Theorem list_nth_rng_eq : ∀ α (r : ring α) la lb n,
  lap_eq la lb → (List.nth n la 0 = List.nth n lb 0)%Rng.
Proof.
intros α r la lb n Hlab.
revert lb n Hlab.
induction la as [| a]; intros.
 revert n.
 induction lb as [| b]; intros; [ reflexivity | simpl ].
 apply lap_eq_nil_cons_inv in Hlab.
 destruct Hlab as (Hb, Hlb).
 symmetry in Hb.
 destruct n; [ assumption | idtac ].
 rewrite <- IHlb; [ destruct n; reflexivity | assumption ].

 revert n.
 induction lb as [| b]; intros.
  simpl.
  apply lap_eq_cons_nil_inv in Hlab.
  destruct Hlab as (Ha, Hla).
  destruct n; [ assumption | idtac ].
  rewrite IHla; [ idtac | eassumption ].
  destruct n; reflexivity.

  apply lap_eq_cons_cons_inv in Hlab.
  destruct Hlab as (Hab, Hlab).
  destruct n; [ assumption | simpl ].
  apply IHla; assumption.
Qed.

Instance lap_convol_mul_morph {A} {rng : ring A} :
  Proper (lap_eq ==> lap_eq ==> eq ==> eq ==> lap_eq) lap_convol_mul.
Proof.
intros la lb Hlab lc ld Hlcd i i' Hii len len' Hll.
subst i' len'.
revert la lb lc ld Hlab Hlcd i.
induction len; intros; [ reflexivity | simpl ].
constructor; [ idtac | apply IHlen; assumption ].
apply summation_compat; intros j (_, Hj).
apply rng_mul_compat; apply list_nth_rng_eq; assumption.
Qed.

Theorem lap_convol_mul_succ : ∀ α (r : ring α) la lb i len,
  lap_eq
    (lap_convol_mul la lb i (S len))
    (lap_convol_mul la lb i len ++
     [Σ (j = 0, i + len),
      List.nth j la 0 * List.nth (i + len - j) lb 0])%Rng.
Proof.
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

Theorem lap_eq_app_0s : ∀ α (r : ring α) la lb,
  List.Forall (λ b, b = 0)%Rng lb
  → lap_eq la (la ++ lb).
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

Theorem list_nth_lap_eq : ∀ α (r : ring α) la lb,
  (∀ i, (List.nth i la 0 = List.nth i lb 0)%Rng)
  → lap_eq la lb.
Proof.
intros α r la lb Hi.
revert lb Hi.
induction la as [| a]; intros.
 induction lb as [| b]; [ reflexivity | constructor ].
  pose proof (Hi O) as H.
  symmetry; assumption.

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

Theorem lap_add_0_l {α} {r : ring α} : ∀ la,
  lap_add [] la = la.
Proof. easy. Qed.

Theorem lap_add_0_r : ∀ α (r : ring α) la,
  lap_add la [] = la.
Proof. intros; now destruct la. Qed.

Theorem lap_mul_0_l : ∀ α (r : ring α) la, lap_eq (lap_mul [] la) [].
Proof. intros α r la; apply lap_convol_mul_nil_l. Qed.

Theorem lap_mul_0_r : ∀ α (r : ring α) la, lap_eq (lap_mul la []) [].
Proof. intros α r la; apply lap_convol_mul_nil_r. Qed.

Theorem lap_add_compat : ∀ α (r : ring α) a b c d,
  lap_eq a c
  → lap_eq b d
    → lap_eq (lap_add a b) (lap_add c d).
Proof.
intros α r a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Theorem lap_add_compat_l {α} {r : ring α} : ∀ a b c,
  lap_eq a b
  → lap_eq (lap_add c a) (lap_add c b).
Proof.
intros a b c Hab.
rewrite Hab; reflexivity.
Qed.

Theorem lap_mul_compat : ∀ α (r : ring α) a b c d,
  lap_eq a c
  → lap_eq b d
    → lap_eq (lap_mul a b) (lap_mul c d).
Proof.
intros α r a b c d Hac Hbd.
rewrite Hac, Hbd; reflexivity.
Qed.

Instance lap_compose_morph {A} {rng : ring A} :
  Proper (lap_eq ==> lap_eq ==> lap_eq) lap_compose.
Proof.
intros la lb Hlab lc ld Hlcd.
revert lb lc ld Hlab Hlcd.
induction la as [| a]; intros.
 induction lb as [| b]; [ reflexivity | simpl ].
 apply lap_eq_nil_cons_inv in Hlab.
 destruct Hlab as (Hb, Hlb).
 simpl in IHlb.
 assert (lap_eq [b] []) as H by (rewrite Hb; constructor; reflexivity).
 rewrite H; clear H.
 rewrite lap_add_0_r.
 rewrite <- IHlb; [ rewrite lap_mul_0_l; reflexivity | assumption ].

 simpl.
 destruct lb as [| b]; simpl.
  apply lap_eq_cons_nil_inv in Hlab.
  destruct Hlab as (Ha, Hla).
  assert (lap_eq [a] []) as H by (rewrite Ha; constructor; reflexivity).
  rewrite H; clear H.
  rewrite lap_add_0_r.
  rewrite IHla; try eassumption; simpl.
  rewrite lap_mul_0_l; reflexivity.

  apply lap_eq_cons_cons_inv in Hlab.
  destruct Hlab as (Hab, Hlab).
  rewrite Hab.
  rewrite IHla; try eassumption.
  apply lap_add_compat; [ idtac | reflexivity ].
  apply lap_mul_compat; [ idtac | assumption ].
  reflexivity.
Qed.

Section lap.

Context {α : Type}.
Context {r : ring α}.

(* addition theorems *)

Theorem lap_add_comm : ∀ al1 al2,
  lap_eq (lap_add al1 al2) (lap_add al2 al1).
Proof.
intros al1 al2.
revert al2.
induction al1; intros.
 destruct al2; [ apply lap_eq_refl | simpl ].
 constructor; [ reflexivity | apply lap_eq_refl ].

 destruct al2.
  constructor; [ reflexivity | apply lap_eq_refl ].

  constructor; [ apply rng_add_comm | apply IHal1 ].
Qed.

Theorem lap_add_assoc : ∀ al1 al2 al3,
  lap_eq (lap_add al1 (lap_add al2 al3))
    (lap_add (lap_add al1 al2) al3).
Proof.
intros al1 al2 al3.
revert al2 al3.
induction al1; intros.
 destruct al2.
  destruct al3; [ apply lap_eq_refl | idtac ].
  constructor; [ reflexivity | apply lap_eq_refl ].

  destruct al3; simpl.
   constructor; [ reflexivity | apply lap_eq_refl ].

   constructor; [ reflexivity | apply lap_eq_refl ].

 destruct al2.
  destruct al3; simpl.
   constructor; [ reflexivity | apply lap_eq_refl ].

   constructor; [ reflexivity | apply lap_eq_refl ].

  destruct al3; simpl.
   constructor; [ reflexivity | apply lap_eq_refl ].

   constructor; [ apply rng_add_assoc | apply IHal1 ].
Qed.

Theorem lap_add_shuffle0 : ∀ la lb lc,
  lap_eq (lap_add (lap_add la lb) lc)
     (lap_add (lap_add la lc) lb).
Proof.
intros la lb lc.
do 2 rewrite <- lap_add_assoc.
apply lap_add_compat; [ reflexivity | simpl ].
apply lap_add_comm.
Qed.

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

(* multiplication theorems *)

Theorem lap_mul_comm : ∀ a b, lap_eq (lap_mul a b) (lap_mul b a).
Proof.
intros a b.
unfold lap_mul.
rewrite lap_convol_mul_comm, Nat.add_comm; reflexivity.
Qed.

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

(* inspired from series_mul_assoc *)
Theorem lap_mul_assoc : ∀ la lb lc,
  lap_eq (lap_mul la (lap_mul lb lc))
    (lap_mul (lap_mul la lb) lc).
Proof.
intros la lb lc.
symmetry; rewrite lap_mul_comm.
unfold lap_mul.
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

Theorem lap_convol_mul_cons_succ : ∀ a b lb i len,
  lap_eq (lap_convol_mul [a] (b :: lb) (S i) len)
    (lap_convol_mul [a] lb i len).
Proof.
intros a b lb i len.
revert a b lb i.
induction len; intros; [ reflexivity | idtac ].
constructor; [ idtac | apply IHlen ].
rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
rewrite List.nth_overflow; [ idtac | simpl; flia ].
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
apply lap_convol_mul_cons_succ.
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

Theorem glop {A} {rng : ring A} : ∀ la lb,
  la = lb → (la = lb)%lap.
Proof. now intros; subst. Qed.

Check (λ la lb, glop la lb).
Check lap_add_0_l.

...

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
     rng_add_0_l a b := glop a b lap_add_0_l;
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
Notation "'POL' l" := {| al := l |} (at level 1) : poly_scope.

Definition poly_eq {α} {r : ring α} x y := lap_eq (al x) (al y).

Definition poly_zero {α} {r : ring α} : polynomial α := POL []%pol.
Definition poly_one {α} {r : ring α} : polynomial α := POL [1%Rng]%pol.

Definition poly_add {α} {r : ring α} pol1 pol2 :=
  {| al := lap_add (al pol1) (al pol2) |}.

Definition poly_opp {α} {r : ring α} pol :=
  {| al := lap_opp (al pol) |}.

Definition poly_sub {α} {r : ring α} pol1 pol2 :=
  poly_add pol1 (poly_opp pol2).

Definition poly_mul {α} {r : ring α} pol1 pol2 :=
  {| al := lap_mul (al pol1) (al pol2) |}.

Definition poly_power {α} {r : ring α} pol n :=
  (POL (lap_power (al pol) n))%pol.

Definition poly_compose {α} {r : ring α} a b :=
  POL (lap_compose (al a) (al b))%pol.

Definition poly_compose2 {α} {r : ring α} a b :=
  POL (lap_compose2 (al a) (al b))%pol.

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
Proof. intros; apply lap_add_0_l. Qed.

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

Definition apply_lap {α} {R : ring α} la x :=
  (List.fold_right (λ c accu, accu * x + c) 0 la)%Rng.

Definition apply_poly {α} {R : ring α} pol :=
  apply_lap (al pol).

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

Instance apply_lap_morph {A} {rng : ring A} :
  Proper (lap_eq ==> rng_eq ==> rng_eq) apply_lap.
Proof.
intros la lb Hll x y Hxy.
destruct la as [| a]. {
  unfold apply_lap; cbn; symmetry.
  clear - Hll.
  induction lb as [| b]; [ easy | cbn ].
  apply lap_eq_nil_cons_inv in Hll.
  destruct Hll as (Hb, Hlb).
  specialize (IHlb Hlb).
  now rewrite IHlb, rng_mul_0_l, rng_add_0_l.
} {
  unfold apply_lap; cbn.
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

Instance apply_poly_morph {A} {rng : ring A} :
  Proper (poly_eq ==> rng_eq ==> rng_eq) apply_poly.
Proof.
intros (la) (lb) Hpp x y Hxy.
unfold "="%pol in Hpp; cbn in Hpp.
unfold apply_poly.
cbn - [ apply_lap ].
now rewrite Hxy, Hpp.
Qed.

Theorem apply_lap_const {A} {rng : ring A} : ∀ c x, (apply_lap [c] x = c)%Rng.
Proof.
intros; cbn.
now rewrite rng_mul_0_l, rng_add_0_l.
Qed.

Theorem apply_poly_add {A} {rng : ring A} : ∀ p1 p2 x,
  (apply_poly (p1 + p2)%pol x = apply_poly p1 x + apply_poly p2 x)%Rng.
Proof.
intros (la) (lb) *.
unfold apply_poly; cbn.
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

Theorem apply_poly_opp {A} {rng : ring A} : ∀ pol x,
  (apply_poly (- pol)%pol x = - apply_poly pol x)%Rng.
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

Theorem apply_poly_sub {A} {rng : ring A} : ∀ p1 p2 x,
  (apply_poly (p1 - p2)%pol x = apply_poly p1 x - apply_poly p2 x)%Rng.
Proof.
intros (la) (lb) *.
unfold poly_sub, rng_sub.
rewrite apply_poly_add.
apply rng_add_compat_l.
apply apply_poly_opp.
Qed.

Theorem apply_poly_sum {A} {rng : ring A} (pr := polynomial_ring) : ∀ b e f x,
  (apply_poly (Σ (i = b, e), f i)%pol x = Σ (i = b, e), apply_poly (f i) x)%Rng.
Proof.
intros.
unfold summation.
remember (S e - b) as n.
clear Heqn.
revert b.
induction n; intros; [ easy | ].
cbn - [ apply_poly ].
rewrite apply_poly_add.
now rewrite IHn.
Qed.

Theorem apply_poly_one {A} {rng : ring A} : ∀ x, (apply_poly 1%pol x = 1)%Rng.
Proof.
intros; cbn.
now rewrite rng_mul_0_l, rng_add_0_l.
Qed.

Theorem apply_lap_cons {A} {rng : ring A} : ∀ a la x,
  (apply_lap (a :: la) x = a + apply_lap la x * x)%Rng.
Proof.
intros.
cbn; rewrite rng_add_comm.
now apply rng_add_compat_l.
Qed.

Theorem lap_add_cons_cons {A} {rng : ring A} : ∀ a b la lb,
  ((a :: la) + (b :: lb) = (a + b)%Rng :: la + lb)%lap.
Proof. easy. Qed.

Theorem apply_lap_add {A} {rng : ring A} : ∀ la lb x,
  (apply_lap (la + lb)%lap x = apply_lap la x + apply_lap lb x)%Rng.
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
do 3 rewrite apply_lap_cons.
rewrite IHla.
do 2 rewrite <- rng_add_assoc.
apply rng_add_compat_l.
rewrite (rng_add_comm (_ * _)%Rng).
rewrite <- rng_add_assoc.
apply rng_add_compat_l.
rewrite rng_add_comm.
apply rng_mul_add_distr_r.
Qed.

Theorem apply_poly_mul {A} {rng : ring A} : ∀ p1 p2 x,
  (apply_poly (p1 * p2)%pol x = apply_poly p1 x * apply_poly p2 x)%Rng.
Proof.
intros (la) (lb) *.
unfold apply_poly.
cbn - [ apply_lap ].
revert lb.
induction la as [| a]; intros. {
  now rewrite rng_mul_0_l, lap_mul_0_l.
} {
  rewrite apply_lap_cons.
  rewrite rng_mul_add_distr_r.
  rewrite rng_mul_mul_swap.
  rewrite <- IHla.
  rewrite lap_mul_cons_l.
  rewrite apply_lap_add.
  rewrite apply_lap_cons, rng_add_0_l.
  apply rng_add_compat_r.
  clear.
  induction lb as [| b]. {
    cbn.
    now rewrite rng_mul_0_r.
  }
  rewrite lap_mul_cons.
  do 2 rewrite apply_lap_cons.
  rewrite rng_mul_add_distr_l.
  apply rng_add_compat_l.
  rewrite lap_mul_0_l, lap_add_0_l.
  rewrite lap_mul_0_l.
  rewrite apply_lap_add.
  rewrite apply_lap_const.
  rewrite rng_add_0_r.
  rewrite IHlb.
  now rewrite rng_mul_assoc.
}
Qed.

Theorem apply_poly_xpow {A} {rng : ring A} : ∀ k x,
  (apply_poly (ⓧ ^ k)%pol x = x ^ k)%Rng.
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
