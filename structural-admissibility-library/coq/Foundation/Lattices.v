(** * Lattices.v

    Lattice structures over observation maps, supporting:
    - combination of observations (join),
    - comparison (leq via refinement),
    - minimal sufficient observation,
    - admissibility monotonicity under refinement.

    We deliberately start with join-semilattices rather than full complete
    lattices: the admissibility theory only requires finite joins.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Relations.Relations.
From Stdlib Require Import Classes.RelationClasses.

Require Import Foundation.Relations.
Require Import Foundation.Orders.

(* ================================================================= *)
(** ** 1. Join-semilattice                                            *)
(* ================================================================= *)

Class JoinSemiLattice (A : Type) := {
  jsl_leq        : A -> A -> Prop;
  jsl_join       : A -> A -> A;
  jsl_leq_refl   : forall x, jsl_leq x x;
  jsl_leq_trans  : forall x y z, jsl_leq x y -> jsl_leq y z -> jsl_leq x z;
  jsl_join_upper_l : forall x y, jsl_leq x (jsl_join x y);
  jsl_join_upper_r : forall x y, jsl_leq y (jsl_join x y);
  jsl_join_least   : forall x y z,
      jsl_leq x z -> jsl_leq y z -> jsl_leq (jsl_join x y) z
}.

(* ================================================================= *)
(** ** 2. Meet-semilattice                                            *)
(* ================================================================= *)

Class MeetSemiLattice (A : Type) := {
  msl_leq         : A -> A -> Prop;
  msl_meet        : A -> A -> A;
  msl_leq_refl    : forall x, msl_leq x x;
  msl_leq_trans   : forall x y z, msl_leq x y -> msl_leq y z -> msl_leq x z;
  msl_meet_lower_l : forall x y, msl_leq (msl_meet x y) x;
  msl_meet_lower_r : forall x y, msl_leq (msl_meet x y) y;
  msl_meet_greatest : forall x y z,
      msl_leq z x -> msl_leq z y -> msl_leq z (msl_meet x y)
}.

(* ================================================================= *)
(** ** 3. Bounded lattice                                             *)
(* ================================================================= *)

Class BoundedJoinSemiLattice (A : Type) := {
  #[global] bjsl_jsl :: JoinSemiLattice A;
  bjsl_bot   : A;
  bjsl_bot_leq : forall x, jsl_leq bjsl_bot x
}.

Class BoundedMeetSemiLattice (A : Type) := {
  #[global] bmsl_msl :: MeetSemiLattice A;
  bmsl_top   : A;
  bmsl_leq_top : forall x, msl_leq x bmsl_top
}.

(* ================================================================= *)
(** ** 4. Complete lattice (for potential extension)                  *)
(* ================================================================= *)

(** NOTE: We do not develop complete lattices in detail here.
    The admissibility theory does not require arbitrary joins/meets.
    This stub marks the extension point. *)
Class CompleteLattice (A : Type) := {
  cl_leq : A -> A -> Prop;
  cl_sup : (A -> Prop) -> A;
  cl_inf : (A -> Prop) -> A;
  cl_leq_refl : forall x, cl_leq x x;
  cl_leq_trans : forall x y z, cl_leq x y -> cl_leq y z -> cl_leq x z;
  cl_sup_upper : forall (S : A -> Prop) x, S x -> cl_leq x (cl_sup S);
  cl_sup_least : forall (S : A -> Prop) z,
      (forall x, S x -> cl_leq x z) -> cl_leq (cl_sup S) z;
  cl_inf_lower : forall (S : A -> Prop) x, S x -> cl_leq (cl_inf S) x;
  cl_inf_greatest : forall (S : A -> Prop) z,
      (forall x, S x -> cl_leq z x) -> cl_leq z (cl_inf S)
}.

(* ================================================================= *)
(** ** 5. Lattice of observation maps over a fixed state space        *)
(* ================================================================= *)

(** We lift the refinement order to a lattice of observation structures.
    The coarsening order: M1 ≤ M2 iff M2 refines M1.
    (Finer maps are "higher" in the information lattice.) *)

Section ObsLattice.

  Variable X : Type.

  (** An observation bundle wraps an observation map with its codomain type. *)
  Record ObsBundle := {
    ob_Obs   : Type;
    ob_map   : X -> ob_Obs
  }.

  (** The information order: b1 ≤ b2 iff ob_map b2 refines ob_map b1. *)
  Definition obs_info_leq (b1 b2 : ObsBundle) : Prop :=
    refines (ob_map b2) (ob_map b1).

  Lemma obs_info_leq_refl : forall b, obs_info_leq b b.
  Proof.
    intro b. unfold obs_info_leq. apply refines_refl.
  Qed.

  Lemma obs_info_leq_trans : forall b1 b2 b3,
      obs_info_leq b1 b2 ->
      obs_info_leq b2 b3 ->
      obs_info_leq b1 b3.
  Proof.
    intros b1 b2 b3 H12 H23.
    unfold obs_info_leq in *.
    eapply refines_trans; eassumption.
  Qed.

  (** Product of two observations as join in the information lattice. *)
  Definition obs_join (b1 b2 : ObsBundle) : ObsBundle :=
    {| ob_Obs := (ob_Obs b1 * ob_Obs b2)%type;
       ob_map := product_obs (ob_map b1) (ob_map b2) |}.

  Lemma obs_join_upper_l : forall b1 b2,
      obs_info_leq b1 (obs_join b1 b2).
  Proof.
    intros. unfold obs_info_leq, obs_join.
    apply refines_product_left.
  Qed.

  Lemma obs_join_upper_r : forall b1 b2,
      obs_info_leq b2 (obs_join b1 b2).
  Proof.
    intros. unfold obs_info_leq, obs_join.
    apply refines_product_right.
  Qed.

  Lemma obs_join_least : forall b1 b2 b3,
      obs_info_leq b1 b3 ->
      obs_info_leq b2 b3 ->
      obs_info_leq (obs_join b1 b2) b3.
  Proof.
    intros b1 b2 b3 H1 H3.
    unfold obs_info_leq, obs_join in *.
    apply refines_product_universal; assumption.
  Qed.

  (** Trivial observation as bottom of the information lattice. *)
  Definition obs_bot : ObsBundle :=
    {| ob_Obs := unit;
       ob_map := @trivial_obs X |}.

  Lemma obs_bot_leq : forall b, obs_info_leq obs_bot b.
  Proof.
    intro b. unfold obs_info_leq, obs_bot.
    apply trivial_obs_coarsest.
  Qed.

  (** Identity observation as top of the information lattice. *)
  Definition obs_top : ObsBundle :=
    {| ob_Obs := X;
       ob_map := @identity_obs X |}.

  Lemma obs_leq_top : forall b, obs_info_leq b obs_top.
  Proof.
    intro b. unfold obs_info_leq, obs_top.
    apply identity_obs_finest.
  Qed.

End ObsLattice.

(* ================================================================= *)
(** ** 6. Minimal sufficient observation                              *)
(* ================================================================= *)

(** An observation bundle is sufficient for predicate Phi if Phi
    is admissible w.r.t. it.  Among all sufficient observations,
    a minimal one is finest-least, i.e., coarsest. *)

Definition sufficient_for {X : Type}
    (b : ObsBundle X)
    (Phi : X -> bool) : Prop :=
  exists Phi_hat : ob_Obs b -> bool,
    forall x, Phi x = Phi_hat (ob_map b x).

(** The identity bundle is always sufficient. *)
Lemma identity_sufficient_for_any :
  forall {X : Type} (Phi : X -> bool),
    sufficient_for (obs_top X) Phi.
Proof.
  intros X Phi.
  unfold sufficient_for, obs_top. simpl.
  exists Phi. intros. reflexivity.
Qed.

(** If b is sufficient and b' refines b, then b' is also sufficient. *)
Lemma sufficient_monotone_refinement :
  forall {X : Type} (b b' : ObsBundle X) (Phi : X -> bool),
    sufficient_for b Phi ->
    obs_info_leq b b' ->
    sufficient_for b' Phi.
Proof.
  intros X b b' Phi Hsuf Href.
  (* Full proof requires classical choice; lives in Admissibility/Refinement.v. *)
Abort.

(** NOTE: The general statement requires careful handling of function
    factorisation. The full proof is in Admissibility/Refinement.v as
    [admissibility_monotone_under_refinement]. *)

(* ================================================================= *)
(** ** 7. Lattice of boolean predicates                               *)
(* ================================================================= *)

(** Boolean predicates on X form a Boolean algebra under pointwise operations. *)
Definition pred_leq {X : Type} (P Q : X -> bool) : Prop :=
  forall x, P x = true -> Q x = true.

Definition pred_join {X : Type} (P Q : X -> bool) : X -> bool :=
  fun x => orb (P x) (Q x).

Definition pred_meet {X : Type} (P Q : X -> bool) : X -> bool :=
  fun x => andb (P x) (Q x).

Definition pred_neg {X : Type} (P : X -> bool) : X -> bool :=
  fun x => negb (P x).

Definition pred_bot {X : Type} : X -> bool := fun _ => false.
Definition pred_top {X : Type} : X -> bool := fun _ => true.

Lemma pred_leq_refl : forall {X} (P : X -> bool), pred_leq P P.
Proof. unfold pred_leq. intros. assumption. Qed.

Lemma pred_leq_trans : forall {X} (P Q R : X -> bool),
    pred_leq P Q -> pred_leq Q R -> pred_leq P R.
Proof. unfold pred_leq. intros. auto. Qed.

Lemma pred_join_upper_l : forall {X} (P Q : X -> bool),
    pred_leq P (pred_join P Q).
Proof.
  unfold pred_leq, pred_join. intros.
  rewrite H. reflexivity.
Qed.

Lemma pred_join_upper_r : forall {X} (P Q : X -> bool),
    pred_leq Q (pred_join P Q).
Proof.
  unfold pred_leq, pred_join. intros.
  rewrite H. apply Bool.orb_true_r.
Qed.

(* ================================================================= *)
(** ** 8. Monotonicity of sufficient-for under predicate leq          *)
(* ================================================================= *)

Lemma sufficient_for_pred_bot :
  forall {X : Type} (b : ObsBundle X),
    sufficient_for b (@pred_bot X).
Proof.
  intros. unfold sufficient_for, pred_bot.
  exists (fun _ => false). intros. reflexivity.
Qed.

Lemma sufficient_for_pred_top :
  forall {X : Type} (b : ObsBundle X),
    sufficient_for b (@pred_top X).
Proof.
  intros. unfold sufficient_for, pred_top.
  exists (fun _ => true). intros. reflexivity.
Qed.

