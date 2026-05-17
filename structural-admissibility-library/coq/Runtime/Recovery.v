(** * Recovery.v

    Distinguishing genuine recovery from metastable reclosure.

    Genuine recovery requires both:
    (a) the monitor returning to CLOSED, AND
    (b) the observation map being refined so the predicate is admissible.

    Metastable reclosure is (a) without (b): the monitor re-enters CLOSED
    but structural safety has not been restored.

    Key theorem (reclosure_not_recovery):
    Metastable reclosure is not genuine recovery.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Logic.Classical_Prop.

Require Import Foundation.Relations.
Require Import Admissibility.ObservationMaps.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.Refinement.
Require Import Admissibility.WarrantDebt.
Require Import Runtime.MonitorStates.
Require Import Runtime.MetastableClosure.

(* ================================================================= *)
(** ** 1. Genuine recovery                                            *)
(* ================================================================= *)

(** Genuine recovery: the monitor returns to CLOSED AND the structural
    safety predicate is now admissible. *)
Definition genuine_recovery {X O : Type}
    (Phi : X -> bool)
    (M   : X -> O)
    (s_before s_after : MonitorSnapshot) : Prop :=
  reachable s_before s_after /\
  operationally_closed s_after /\
  structurally_safe Phi M.

(** Genuine recovery requires both a monitor transition and structural fix. *)
Lemma genuine_recovery_structurally_safe :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O) s1 s2,
    genuine_recovery Phi M s1 s2 ->
    structurally_safe Phi M.
Proof.
  intros X O Phi M s1 s2 [_ [_ Hsafe]]. assumption.
Qed.

(* ================================================================= *)
(** ** 2. Metastable reclosure                                        *)
(* ================================================================= *)

(** Metastable reclosure: the monitor returns to CLOSED but structural
    safety has NOT been restored. *)
Definition metastable_reclosure {X O : Type}
    (Phi : X -> bool)
    (M   : X -> O)
    (s_before s_after : MonitorSnapshot) : Prop :=
  reachable s_before s_after /\
  operationally_closed s_after /\
  structurally_unsafe Phi M.

(** Metastable reclosure implies ongoing warrant debt. *)
Lemma metastable_reclosure_has_warrant_debt :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O) s1 s2,
    metastable_reclosure Phi M s1 s2 ->
    has_warrant_debt Phi M.
Proof.
  intros X O Phi M s1 s2 [_ [_ Hunsafe]].
  unfold has_warrant_debt. assumption.
Qed.

(* ================================================================= *)
(** ** 3. Reclosure is not recovery                                   *)
(* ================================================================= *)

Theorem reclosure_not_recovery :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O) s1 s2,
    metastable_reclosure Phi M s1 s2 ->
    ~ genuine_recovery Phi M s1 s2.
Proof.
  intros X O Phi M s1 s2 [_ [_ Hunsafe]] [_ [_ Hsafe]].
  apply Hunsafe. assumption.
Qed.

(** They are mutually exclusive under the same observation map. *)
Theorem recovery_and_reclosure_exclusive :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O) s1 s2,
    ~ (genuine_recovery Phi M s1 s2 /\ metastable_reclosure Phi M s1 s2).
Proof.
  intros X O Phi M s1 s2 [[_ [_ Hsafe]] [_ [_ Hunsafe]]].
  apply Hunsafe. assumption.
Qed.

(* ================================================================= *)
(** ** 4. Conditions for genuine recovery                             *)
(* ================================================================= *)

(** A necessary condition for genuine recovery is an observation upgrade. *)
Definition involves_observation_refinement {X O1 O2 : Type}
    (M1 : X -> O1) (M2 : X -> O2) : Prop :=
  strictly_refines M2 M1.

(** Genuine recovery via observation refinement. *)
Definition recovery_via_refinement {X O1 O2 : Type}
    (Phi   : X -> bool)
    (M1    : X -> O1)
    (M2    : X -> O2)
    (s_before s_after : MonitorSnapshot) : Prop :=
  metastable_closure Phi M1 s_before /\
  reachable s_before s_after /\
  operationally_closed s_after /\
  boolean_admissible Phi M2 /\
  strictly_refines M2 M1.

Theorem recovery_via_refinement_is_genuine :
  forall {X O1 O2 : Type}
    (Phi   : X -> bool)
    (M1    : X -> O1)
    (M2    : X -> O2)
    (s1 s2 : MonitorSnapshot),
    recovery_via_refinement Phi M1 M2 s1 s2 ->
    genuine_recovery Phi M2 s1 s2.
Proof.
  intros X O1 O2 Phi M1 M2 s1 s2
    [_ [Hreach [Hclosed [Hadm _]]]].
  unfold genuine_recovery. repeat split; assumption.
Qed.

(* ================================================================= *)
(** ** 5. Reclosure risk after rupture                                *)
(* ================================================================= *)

(** After a HARD_RUPTURE, reclosure without refinement is always metastable. *)
Theorem post_rupture_reclosure_is_metastable :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O) s1 s2,
    status s1 = HARD_RUPTURE ->
    reachable s1 s2 ->
    operationally_closed s2 ->
    structurally_unsafe Phi M ->
    metastable_reclosure Phi M s1 s2.
Proof.
  intros X O Phi M s1 s2 Hrup Hreach Hclosed Hunsafe.
  unfold metastable_reclosure. repeat split; assumption.
Qed.

(** After HARD_RUPTURE, genuine recovery requires a structural fix. *)
Theorem post_rupture_genuine_recovery_requires_fix :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O) s1 s2,
    status s1 = HARD_RUPTURE ->
    reachable s1 s2 ->
    genuine_recovery Phi M s1 s2 ->
    structurally_safe Phi M.
Proof.
  intros X O Phi M s1 s2 _ _ [_ [_ Hsafe]]. assumption.
Qed.

