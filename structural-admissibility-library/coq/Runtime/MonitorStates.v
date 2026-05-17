(** * MonitorStates.v

    Monitor state machine for structural admissibility at runtime.

    Three states: CLOSED (nominal), META_REVIEW (latent structural risk),
    HARD_RUPTURE (absorbing failure).

    Key theorem (hard_rupture_absorbing):
        status s = HARD_RUPTURE -> step s s' -> status s' = HARD_RUPTURE.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Logic.Classical_Prop.

Require Import Foundation.Relations.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.WarrantDebt.

(* ================================================================= *)
(** ** 1. Monitor status type                                         *)
(* ================================================================= *)

Inductive MonitorStatus :=
| CLOSED       : MonitorStatus   (** nominal: no detected structural risk *)
| META_REVIEW  : MonitorStatus   (** latent: structural fatigue present   *)
| HARD_RUPTURE : MonitorStatus.  (** absorbing: structural failure proven *)

Definition status_eq_dec : forall s t : MonitorStatus, {s = t} + {s <> t}.
Proof. decide equality. Defined.

(* ================================================================= *)
(** ** 2. Monitor snapshot                                            *)
(* ================================================================= *)

Record MonitorSnapshot := {
  fatigue  : nat;
  tension  : nat;
  horizon  : nat;
  lag      : nat;
  status   : MonitorStatus
}.

(** Default/initial snapshot. *)
Definition initial_snapshot : MonitorSnapshot :=
  {| fatigue := 0;
     tension := 0;
     horizon := 10;
     lag     := 0;
     status  := CLOSED |}.

(* ================================================================= *)
(** ** 3. Threshold parameters                                        *)
(* ================================================================= *)

Parameter fatigue_threshold    : nat.  (** F_max: fatigue limit              *)
Parameter tension_threshold    : nat.  (** T_max: tension limit              *)
Parameter meta_review_trigger  : nat.  (** when fatigue > this -> META_REVIEW *)

Axiom meta_review_trigger_lt_fatigue_threshold :
  meta_review_trigger < fatigue_threshold.

(* ================================================================= *)
(** ** 4. Transition conditions                                       *)
(* ================================================================= *)

Definition is_stable (s : MonitorSnapshot) : Prop :=
  fatigue s <= meta_review_trigger /\
  tension s <= tension_threshold /\
  lag s <= horizon s.

Definition triggers_meta_review (s : MonitorSnapshot) : Prop :=
  fatigue s > meta_review_trigger /\
  fatigue s <= fatigue_threshold /\
  lag s <= horizon s.

Definition triggers_hard_rupture (s : MonitorSnapshot) : Prop :=
  fatigue s > fatigue_threshold \/
  tension s > tension_threshold \/
  lag s > horizon s.

(* ================================================================= *)
(** ** 5. Transition relation                                         *)
(* ================================================================= *)

Inductive step : MonitorSnapshot -> MonitorSnapshot -> Prop :=

| StepClosedStable :
    forall s s',
      status s = CLOSED ->
      is_stable s ->
      is_stable s' ->
      status s' = CLOSED ->
      fatigue s' >= fatigue s ->
      step s s'

| StepClosedToMetaReview :
    forall s s',
      status s = CLOSED ->
      triggers_meta_review s ->
      status s' = META_REVIEW ->
      fatigue s' = fatigue s ->
      step s s'

| StepMetaReviewToClosed :
    forall s s',
      status s = META_REVIEW ->
      is_stable s' ->
      status s' = CLOSED ->
      fatigue s' < fatigue s ->
      step s s'

| StepMetaReviewToRupture :
    forall s s',
      status s = META_REVIEW ->
      triggers_hard_rupture s ->
      status s' = HARD_RUPTURE ->
      fatigue s' = fatigue s ->
      step s s'

| StepHardRuptureAbsorbing :
    forall s s',
      status s = HARD_RUPTURE ->
      status s' = HARD_RUPTURE ->
      step s s'.

(* ================================================================= *)
(** ** 6. Key theorems                                                *)
(* ================================================================= *)

(** HARD_RUPTURE is an absorbing state. *)
Theorem hard_rupture_absorbing :
  forall s s',
    status s = HARD_RUPTURE ->
    step s s' ->
    status s' = HARD_RUPTURE.
Proof.
  intros s s' Hrup Hstep.
  inversion Hstep; subst.
  - rewrite Hrup in H. discriminate.
  - rewrite Hrup in H. discriminate.
  - rewrite Hrup in H. discriminate.
  - rewrite Hrup in H. discriminate.
  - assumption.
Qed.

(** Once in HARD_RUPTURE, all reachable states are HARD_RUPTURE. *)
Inductive reachable : MonitorSnapshot -> MonitorSnapshot -> Prop :=
| Reach_refl : forall s, reachable s s
| Reach_step : forall s t u, step s t -> reachable t u -> reachable s u.

Theorem hard_rupture_absorbing_reachable :
  forall s t,
    status s = HARD_RUPTURE ->
    reachable s t ->
    status t = HARD_RUPTURE.
Proof.
  intros s t Hrup Hreach.
  induction Hreach as [? | ? mid ? Hstep ? IH].
  - exact Hrup.
  - apply IH. eapply hard_rupture_absorbing; [exact Hrup | exact Hstep].
Qed.

(** CLOSED -> META_REVIEW -> HARD_RUPTURE is irreversible after HARD_RUPTURE. *)
Corollary no_return_from_rupture :
  forall s t,
    status s = HARD_RUPTURE ->
    reachable s t ->
    status t <> CLOSED /\ status t <> META_REVIEW.
Proof.
  intros s t Hrup Hreach.
  pose proof (hard_rupture_absorbing_reachable Hrup Hreach) as Ht.
  split; rewrite Ht; discriminate.
Qed.

(* ================================================================= *)
(** ** 7. Monitor invariant                                           *)
(* ================================================================= *)

Definition monitor_invariant (s : MonitorSnapshot) : Prop :=
  match status s with
  | CLOSED       => fatigue s <= meta_review_trigger
  | META_REVIEW  => meta_review_trigger < fatigue s /\ fatigue s <= fatigue_threshold
  | HARD_RUPTURE => True
  end.

Lemma initial_snapshot_invariant : monitor_invariant initial_snapshot.
Proof.
  unfold monitor_invariant, initial_snapshot. simpl. apply Nat.le_0_l.
Qed.

Lemma step_preserves_invariant :
  forall s s',
    monitor_invariant s ->
    step s s' ->
    monitor_invariant s'.
Proof.
  intros s s' Hinv Hstep.
  inversion Hstep; subst.
  - (* StepClosedStable: H1 : is_stable s', H2 : status s' = CLOSED *)
    unfold monitor_invariant. rewrite H2. simpl.
    unfold is_stable in H1. tauto.
  - (* StepClosedToMetaReview: H0 : triggers_meta_review s, H1 : status s' = META_REVIEW, H2 : fatigue s' = fatigue s *)
    unfold monitor_invariant. rewrite H1. simpl. rewrite H2.
    unfold triggers_meta_review in H0. tauto.
  - (* StepMetaReviewToClosed: H0 : is_stable s', H1 : status s' = CLOSED *)
    unfold monitor_invariant. rewrite H1. simpl.
    unfold is_stable in H0. tauto.
  - (* StepMetaReviewToRupture: H1 : status s' = HARD_RUPTURE *)
    unfold monitor_invariant. rewrite H1. simpl. trivial.
  - (* StepHardRuptureAbsorbing: H0 : status s' = HARD_RUPTURE *)
    unfold monitor_invariant. rewrite H0. simpl. trivial.
Qed.

(* ================================================================= *)
(** ** 8. Trace definition                                            *)
(* ================================================================= *)

Definition Trace := list MonitorSnapshot.

Inductive valid_trace : Trace -> Prop :=
| VT_single : forall s, monitor_invariant s -> valid_trace [s]
| VT_cons   : forall s t rest,
    step s t ->
    valid_trace (t :: rest) ->
    valid_trace (s :: t :: rest).

Definition reaches_hard_rupture (trace : Trace) (s : MonitorSnapshot) : Prop :=
  List.In s trace /\ status s = HARD_RUPTURE.

