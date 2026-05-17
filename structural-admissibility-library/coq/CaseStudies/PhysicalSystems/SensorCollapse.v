(** * SensorCollapse.v

    Case Study A: Sensor Boundary Collapse.

    Central results:
    1. sensor_observation_inadmissible: thermal_safe is NOT admissible
       w.r.t. the basic sensor_obs.
    2. enriched_sensor_restores_admissibility: with temperature added,
       thermal_safe IS admissible.

    This case study directly validates the admissibility theory in the
    context of physical monitoring.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.Classical_Prop.

Require Import Foundation.Relations.
Require Import Foundation.Orders.
Require Import Admissibility.ObservationMaps.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.Collapse.
Require Import Admissibility.Refinement.
Require Import Admissibility.WarrantDebt.
Require Import Runtime.RuptureCertificates.
Require Import CaseStudies.PhysicalSystems.BoundaryConditions.

(* ================================================================= *)
(** ** 1. Sensor collapse witness                                     *)
(* ================================================================= *)

(** Two physical states:
    s1 : safe temperature (below max_temp), same flux and pressure as s2.
    s2 : unsafe temperature (at max_temp), same flux and pressure as s1.

    Both yield the same sensor reading, but s1 is thermally safe and s2 is not. *)

Definition s1_safe : PhysicalState :=
  {| temperature   := max_temp - 1;  (* safe: below threshold *)
     pressure      := 5;
     boundary_flux := 3 |}.

Definition s2_unsafe : PhysicalState :=
  {| temperature   := max_temp;     (* unsafe: at threshold *)
     pressure      := 5;
     boundary_flux := 3 |}.

Lemma sensor_collapse_pair_same_obs :
    sensor_obs s1_safe = sensor_obs s2_unsafe.
Proof.
  unfold sensor_obs, s1_safe, s2_unsafe. simpl. reflexivity.
Qed.

Lemma sensor_collapse_pair_predicate_disagrees :
    thermal_safe s1_safe <> thermal_safe s2_unsafe.
Proof.
  unfold thermal_safe, s1_safe, s2_unsafe. simpl.
  pose proof max_temp_positive as Hpos.
  destruct (Nat.ltb (max_temp - 1) max_temp) eqn:H1;
  destruct (Nat.ltb max_temp max_temp) eqn:H2;
  try discriminate.
  - apply Nat.ltb_lt in H2. exfalso. exact (Nat.lt_irrefl _ H2).
  - exfalso. assert (Nat.ltb (max_temp - 1) max_temp = true) by
      (apply Nat.ltb_lt; lia). congruence.
Qed.

(** Existence of a collapse witness. *)
Example sensor_collapse_witness :
  exists s1 s2 : PhysicalState,
    sensor_obs s1 = sensor_obs s2 /\
    thermal_safe s1 <> thermal_safe s2.
Proof.
  exists s1_safe. exists s2_unsafe.
  split.
  - apply sensor_collapse_pair_same_obs.
  - apply sensor_collapse_pair_predicate_disagrees.
Qed.

(* ================================================================= *)
(** ** 2. Main theorem: basic sensor is inadequate                    *)
(* ================================================================= *)

Theorem sensor_observation_inadmissible :
  ~ boolean_admissible thermal_safe sensor_obs.
Proof.
  apply safety_relevant_collapse_iff_inadmissible.
  exists s1_safe. exists s2_unsafe.
  split.
  - apply sensor_collapse_pair_same_obs.
  - apply sensor_collapse_pair_predicate_disagrees.
Qed.

(* ================================================================= *)
(** ** 3. Main theorem: enriched sensor restores admissibility        *)
(* ================================================================= *)

(** The enriched sensor measures temperature directly, so thermal_safe
    can be computed from the observation alone. *)
Theorem enriched_sensor_restores_admissibility :
  boolean_admissible thermal_safe enriched_sensor_obs.
Proof.
  unfold boolean_admissible.
  exists (fun r => Nat.ltb (er_temperature r) max_temp).
  intro s. unfold thermal_safe, enriched_sensor_obs. simpl.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** 4. Refinement: enriched sensor refines basic sensor            *)
(* ================================================================= *)

Theorem enriched_sensor_refines_basic :
  refines enriched_sensor_obs sensor_obs.
Proof.
  unfold refines, enriched_sensor_obs, sensor_obs.
  intros s1 s2 H. inversion H. reflexivity.
Qed.

(** Consistency check: admissibility_monotone_under_refinement says
    admissible w.r.t. sensor_obs => admissible w.r.t. enriched_sensor_obs.
    The reverse (enriched => basic) is false, as shown by sensor_observation_inadmissible. *)

(* ================================================================= *)
(** ** 5. Rupture certificate for sensor collapse                     *)
(* ================================================================= *)

Definition sensor_rupture_certificate :
    RuptureCertificate thermal_safe sensor_obs :=
  {| cert_left                   := s1_safe;
     cert_right                  := s2_unsafe;
     cert_same_observation       := sensor_collapse_pair_same_obs;
     cert_predicate_disagreement := sensor_collapse_pair_predicate_disagrees;
     cert_fatigue                := 1;
     cert_fatigue_positive       := Nat.lt_0_succ 0 |}.

Theorem sensor_rupture_cert_sound :
  ~ boolean_admissible thermal_safe sensor_obs.
Proof.
  apply rupture_certificate_sound.
  exact sensor_rupture_certificate.
Qed.

(* ================================================================= *)
(** ** 6. Warrant debt analysis                                       *)
(* ================================================================= *)

Definition sensor_warrant_witness :
    WarrantDebtWitness thermal_safe sensor_obs :=
  {| wd_left      := s1_safe;
     wd_right     := s2_unsafe;
     wd_collapsed := sensor_collapse_pair_same_obs;
     wd_disagrees := sensor_collapse_pair_predicate_disagrees |}.

Theorem sensor_has_warrant_debt :
  has_warrant_debt thermal_safe sensor_obs.
Proof.
  apply warrant_debt_witness_sound.
  exact sensor_warrant_witness.
Qed.

(* ================================================================= *)
(** ** 7. Full safety predicate analysis                              *)
(* ================================================================= *)

(** Witnesses using threshold-relative values, guaranteed safe/unsafe by
    the positivity axioms alone. *)
Definition s1_fully_safe : PhysicalState :=
  {| temperature   := max_temp - 1;
     pressure      := max_pressure - 1;
     boundary_flux := max_flux - 1 |}.

Definition s2_fully_unsafe : PhysicalState :=
  {| temperature   := max_temp;
     pressure      := max_pressure - 1;
     boundary_flux := max_flux - 1 |}.

Lemma fully_safe_s1_true : fully_safe s1_fully_safe = true.
Proof.
  unfold fully_safe, thermal_safe, pressure_safe, flux_safe, s1_fully_safe. simpl.
  pose proof max_temp_positive as Ht.
  pose proof max_pressure_positive as Hp.
  pose proof max_flux_positive as Hf.
  rewrite Bool.andb_true_iff. split.
  - rewrite Bool.andb_true_iff. split.
    + apply Nat.ltb_lt. lia.
    + apply Nat.ltb_lt. lia.
  - apply Nat.ltb_lt. lia.
Qed.

Lemma fully_safe_s2_false : fully_safe s2_fully_unsafe = false.
Proof.
  unfold fully_safe, thermal_safe, s2_fully_unsafe. simpl.
  assert (Hx : Nat.ltb max_temp max_temp = false).
  { destruct (Nat.ltb max_temp max_temp) eqn:Heq.
    - apply Nat.ltb_lt in Heq. exfalso. exact (Nat.lt_irrefl _ Heq).
    - reflexivity. }
  rewrite Hx. simpl. reflexivity.
Qed.

(** The fully_safe predicate (temperature AND pressure AND flux) is also
    inadmissible w.r.t. the basic sensor, because it still depends on temperature. *)
Theorem full_safety_sensor_inadmissible :
  ~ boolean_admissible fully_safe sensor_obs.
Proof.
  apply safety_relevant_collapse_iff_inadmissible.
  exists s1_fully_safe. exists s2_fully_unsafe.
  split.
  - unfold sensor_obs, s1_fully_safe, s2_fully_unsafe. simpl. reflexivity.
  - assert (H1 := fully_safe_s1_true).
    assert (H2 := fully_safe_s2_false).
    rewrite H1, H2. discriminate.
Qed.

