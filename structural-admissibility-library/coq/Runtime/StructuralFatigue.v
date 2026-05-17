(** * StructuralFatigue.v

    Formalisation of fatigue accumulation in structural admissibility monitoring.

    Fatigue accumulates when the system oscillates between states or when
    the observation kernel widens (more states collapse).

    Key theorems:
    - fatigue_monotone: update never reduces fatigue.
    - fatigue_zero_preserved_under_zero_strain: if no strain is applied, fatigue stays.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import Runtime.MonitorStates.

(* ================================================================= *)
(** ** 1. Fatigue state record                                        *)
(* ================================================================= *)

Record FatigueState := {
  F             : nat;   (** accumulated fatigue                     *)
  oscillations  : nat;   (** number of kernel oscillation events     *)
  widenings     : nat    (** number of kernel widening events        *)
}.

Definition initial_fatigue : FatigueState :=
  {| F := 0; oscillations := 0; widenings := 0 |}.

(* ================================================================= *)
(** ** 2. Fatigue update function                                     *)
(* ================================================================= *)

(** Update fatigue given:
    - strain  : direct additive strain from the current event
    - osc     : whether an oscillation was detected
    - widened : whether the kernel widened *)
Definition update_fatigue
    (f       : FatigueState)
    (strain  : nat)
    (osc     : bool)
    (widened : bool) : FatigueState :=
  let new_F :=
    F f + strain +
    (if osc     then 1 else 0) +
    (if widened then 2 else 0) in
  {| F            := new_F;
     oscillations := oscillations f + (if osc     then 1 else 0);
     widenings    := widenings    f + (if widened then 1 else 0) |}.

(* ================================================================= *)
(** ** 3. Fatigue monotonicity                                        *)
(* ================================================================= *)

(** Fatigue never decreases on update. *)
Theorem fatigue_monotone :
  forall f strain osc widened,
    F f <= F (update_fatigue f strain osc widened).
Proof.
  intros f strain osc widened.
  unfold update_fatigue. simpl.
  destruct osc; destruct widened; lia.
Qed.

(** Zero strain and no oscillation/widening preserves fatigue exactly. *)
Theorem fatigue_zero_preserved_under_zero_strain :
  forall f,
    F (update_fatigue f 0 false false) = F f.
Proof.
  intro f. unfold update_fatigue. simpl. lia.
Qed.

(** Oscillation strictly increases fatigue. *)
Lemma oscillation_increases_fatigue :
  forall f strain widened,
    F f < F (update_fatigue f strain true widened).
Proof.
  intros. unfold update_fatigue. simpl.
  destruct widened; lia.
Qed.

(** Widening strictly increases fatigue. *)
Lemma widening_increases_fatigue :
  forall f strain osc,
    F f < F (update_fatigue f strain osc true).
Proof.
  intros. unfold update_fatigue. simpl.
  destruct osc; lia.
Qed.

(* ================================================================= *)
(** ** 4. Accumulated fatigue over a trace                            *)
(* ================================================================= *)

Fixpoint accumulated_fatigue
    (events : list (nat * bool * bool)) : nat :=
  match events with
  | [] => 0
  | ((strain, osc), widened) :: rest =>
    strain + (if osc then 1 else 0) + (if widened then 2 else 0) +
    accumulated_fatigue rest
  end.

Lemma accumulated_fatigue_nonneg :
  forall events,
    0 <= accumulated_fatigue events.
Proof.
  induction events.
  - simpl. lia.
  - destruct a as [[strain osc] widened]. simpl.
    destruct osc; destruct widened; lia.
Qed.

(* ================================================================= *)
(** ** 5. Fatigue threshold crossing                                  *)
(* ================================================================= *)

Definition fatigue_exceeds_threshold (f : FatigueState) : Prop :=
  F f > fatigue_threshold.

Definition fatigue_in_review_zone (f : FatigueState) : Prop :=
  meta_review_trigger < F f /\ F f <= fatigue_threshold.

(** Once fatigue exceeds the threshold, further updates keep it above. *)
Lemma fatigue_stays_above_threshold :
  forall f strain osc widened,
    F f > fatigue_threshold ->
    F (update_fatigue f strain osc widened) > fatigue_threshold.
Proof.
  intros f strain osc widened H.
  apply Nat.lt_le_trans with (m := F f).
  - assumption.
  - apply fatigue_monotone.
Qed.

(* ================================================================= *)
(** ** 6. Fatigue-to-snapshot lifting                                 *)
(* ================================================================= *)

Definition snapshot_with_fatigue
    (f : FatigueState)
    (tension horizon lag : nat)
    (st : MonitorStatus) : MonitorSnapshot :=
  {| fatigue  := F f;
     tension  := tension;
     horizon  := horizon;
     lag      := lag;
     status   := st |}.

(** Updating the snapshot fatigue from a fatigue state update. *)
Definition update_snapshot_fatigue
    (s : MonitorSnapshot)
    (strain : nat) (osc widened : bool) : MonitorSnapshot :=
  {| fatigue  := F (update_fatigue
                    {| F := fatigue s;
                       oscillations := 0;
                       widenings    := 0 |}
                    strain osc widened);
     tension  := tension s;
     horizon  := horizon s;
     lag      := lag s;
     status   := status s |}.

Lemma update_snapshot_fatigue_monotone :
  forall s strain osc widened,
    fatigue s <= fatigue (update_snapshot_fatigue s strain osc widened).
Proof.
  intros. unfold update_snapshot_fatigue, update_fatigue. simpl.
  destruct osc; destruct widened; lia.
Qed.

(* ================================================================= *)
(** ** 7. Fatigue and structural fatigue                              *)
(* ================================================================= *)

(** Structural fatigue is the component of fatigue arising specifically from
    kernel widening (observational degradation), not from oscillation alone. *)
Definition structural_fatigue_component (f : FatigueState) : nat :=
  2 * widenings f.

(** Well-formedness invariant: total fatigue accounts for all components. *)
Definition fatigue_wf (f : FatigueState) : Prop :=
  2 * widenings f + oscillations f <= F f.

Lemma initial_fatigue_wf : fatigue_wf initial_fatigue.
Proof. unfold fatigue_wf, initial_fatigue. simpl. lia. Qed.

Lemma update_fatigue_wf :
  forall f strain osc widened,
    fatigue_wf f ->
    fatigue_wf (update_fatigue f strain osc widened).
Proof.
  intros f strain osc widened Hwf.
  unfold fatigue_wf, update_fatigue in *. simpl.
  destruct osc; destruct widened; lia.
Qed.

Lemma structural_fatigue_le_total :
  forall f, fatigue_wf f -> structural_fatigue_component f <= F f.
Proof.
  intros f Hwf.
  unfold structural_fatigue_component, fatigue_wf in *.
  lia.
Qed.
