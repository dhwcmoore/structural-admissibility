(** * TimelyAdmissibility.v

    Admissibility connected to intervention timing.

    A predicate is timely admissible w.r.t. an observation map when the
    observation map can be refined in time to act before the rupture horizon.

    Key theorem (untimely_refinement_cannot_restore_safety):
    Even if a refinement would make a predicate admissible in principle,
    it is not operationally sufficient if it arrives after the rupture horizon.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.ClassicalDescription.

Require Import Foundation.Relations.
Require Import Admissibility.ObservationMaps.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.

(* ================================================================= *)
(** ** 1. Intervention record                                         *)
(* ================================================================= *)

Record Intervention := {
  latency  : nat;   (** time from detection to effect *)
  gain     : nat;   (** benefit if applied in time    *)
  cost     : nat    (** cost of the intervention      *)
}.

Definition intervention_net_benefit (i : Intervention) : Z :=
  Z.of_nat (gain i) - Z.of_nat (cost i).

(* ================================================================= *)
(** ** 2. Timely admissibility                                        *)
(* ================================================================= *)

(** An observation is timely for a given horizon if the lag required to
    compute the observation does not exceed the horizon. *)
Definition timely_admissible (lag horizon : nat) : Prop :=
  lag <= horizon.

Definition untimely (lag horizon : nat) : Prop :=
  horizon < lag.

Lemma timely_or_untimely : forall lag horizon,
    timely_admissible lag horizon \/ untimely lag horizon.
Proof.
  intros lag horizon.
  destruct (le_lt_dec lag horizon).
  - left. unfold timely_admissible. assumption.
  - right. unfold untimely. assumption.
Qed.

(** No forced lag: the required lag does not exceed the horizon. *)
Definition no_forced_lag (required_lag horizon : nat) : Prop :=
  required_lag <= horizon.

(* ================================================================= *)
(** ** 3. Observation lag model                                       *)
(* ================================================================= *)

(** An observation structure with timing. *)
Record TimedObservation (X O : Type) := {
  to_obs     : X -> O;
  to_lag     : nat           (** computation delay in time steps *)
}.

Definition timed_timely_admissible {X O : Type}
    (to : TimedObservation X O)
    (horizon : nat)
    (Phi : X -> bool) : Prop :=
  timely_admissible (to_lag to) horizon /\
  boolean_admissible Phi (to_obs to).

(* ================================================================= *)
(** ** 4. Refinement lag                                              *)
(* ================================================================= *)

(** Refinement may require additional computation time. *)
Record TimedRefinement {X O1 O2 : Type}
    (to1 : TimedObservation X O1)
    (to2 : TimedObservation X O2) := {
  tr_refines     : refines (to_obs to2) (to_obs to1);
  tr_lag_increase : to_lag to1 <= to_lag to2
}.

(** A timed refinement is operationally useful only if the refined
    observation arrives before the horizon. *)
Definition operationally_useful_refinement {X O1 O2 : Type}
    (to1 : TimedObservation X O1)
    (to2 : TimedObservation X O2)
    (horizon : nat)
    (_ : TimedRefinement to1 to2) : Prop :=
  timely_admissible (to_lag to2) horizon.

(* ================================================================= *)
(** ** 5. Untimely refinement cannot restore safety                   *)
(* ================================================================= *)

(** Even if refining from M1 to M2 would make Phi admissible, the
    refinement is operationally useless if the lag of M2 exceeds the horizon. *)
Theorem untimely_refinement_cannot_restore_safety :
  forall {X O1 O2 : Type}
    (to1 : TimedObservation X O1)
    (to2 : TimedObservation X O2)
    (horizon : nat)
    (Phi : X -> bool)
    (tr  : TimedRefinement to1 to2),
    untimely (to_lag to2) horizon ->
    boolean_admissible Phi (to_obs to2) ->
    ~ timed_timely_admissible to2 horizon Phi.
Proof.
  intros X O1 O2 to1 to2 horizon Phi tr Huntimely Hadm.
  unfold timed_timely_admissible, timely_admissible. intros [Hlag _].
  unfold untimely in Huntimely. lia.
Qed.

(** Interpretation: even though Phi is admissible w.r.t. to2 (the refined
    observation), the refinement arrives too late to matter.  The structural
    admissibility is present in principle but absent in operation. *)

(* ================================================================= *)
(** ** 6. Horizon debt induced by untimeliness                        *)
(* ================================================================= *)

(** If the best available observation that makes Phi admissible has lag L,
    and the horizon is H < L, then the system has horizon_debt = L - H. *)
Definition timely_warrant_gap (required_lag horizon : nat) : nat :=
  if le_lt_dec required_lag horizon
  then 0
  else required_lag - horizon.

Lemma zero_timely_gap_iff_timely :
  forall required_lag horizon,
    timely_warrant_gap required_lag horizon = 0 <->
    timely_admissible required_lag horizon.
Proof.
  intros required_lag horizon.
  unfold timely_warrant_gap, timely_admissible.
  destruct (le_lt_dec required_lag horizon).
  - split. intros _. assumption. intros _. reflexivity.
  - split.
    + intro H. lia.
    + intro H. lia.
Qed.

(* ================================================================= *)
(** ** 7. Timely admissibility with a fixed set of operations         *)
(* ================================================================= *)

(** If multiple observations are available, the minimum-lag admissible
    one should be chosen. *)
Definition min_lag_admissible {X : Type}
    (Phi : X -> bool)
    (options : list { O : Type & TimedObservation X O }) : option nat :=
  List.fold_left
    (fun acc opt =>
       let to := projT2 opt in
       if excluded_middle_informative (boolean_admissible Phi (to_obs to))
       then match acc with
            | None   => Some (to_lag to)
            | Some n => Some (Nat.min n (to_lag to))
            end
       else acc)
    options
    None.
