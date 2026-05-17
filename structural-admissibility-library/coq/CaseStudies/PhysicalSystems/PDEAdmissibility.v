(** * PDEAdmissibility.v

    Connecting the thermal PDE model to the admissibility framework.

    The key result: a boundary-only sensor is inadmissible for predicates
    that depend on the interior temperature field.  An enriched sensor
    that samples both boundary and interior is admissible.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import Foundation.Relations.
Require Import Foundation.Orders.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.Collapse.
Require Import Admissibility.Refinement.
Require Import CaseStudies.PhysicalSystems.BoundaryConditions.
Require Import CaseStudies.PhysicalSystems.ThermalModel.

(* ================================================================= *)
(** ** 1. Field-based physical state                                  *)
(* ================================================================= *)

Record FieldState := {
  fs_field    : ThermalField;   (** full temperature field *)
  fs_pressure : nat;
  fs_flux     : nat
}.

(** The boundary-only sensor maps a field state to boundary temperature + flux. *)
Record BoundaryObs := {
  bo_temp  : nat;  (** boundary temperature *)
  bo_flux  : nat
}.

Definition field_boundary_obs (fs : FieldState) : BoundaryObs :=
  {| bo_temp := boundary_temp (fs_field fs);
     bo_flux := fs_flux fs |}.

(** The full-field sensor observes the entire temperature field. *)
Definition field_full_obs (fs : FieldState) : (ThermalField * nat * nat) :=
  (fs_field fs, fs_pressure fs, fs_flux fs).

(** Interior safety predicate: interior temperature must be below max_temp. *)
Definition interior_safe (fs : FieldState) : bool :=
  Nat.ltb (interior_temp (fs_field fs)) max_temp.

(* ================================================================= *)
(** ** 2. Boundary sensor is inadmissible for interior safety         *)
(* ================================================================= *)

(** Two field states: identical boundary and flux, but different interior temperatures. *)
Definition fs_boundary_safe : FieldState :=
  {| fs_field    := [max_temp - 1; max_temp - 1]; (* safe at both positions *)
     fs_pressure := 5;
     fs_flux     := 3 |}.

Definition fs_interior_unsafe : FieldState :=
  {| fs_field    := [max_temp - 1; max_temp]; (* safe boundary, unsafe interior *)
     fs_pressure := 5;
     fs_flux     := 3 |}.

Lemma boundary_obs_same :
    field_boundary_obs fs_boundary_safe = field_boundary_obs fs_interior_unsafe.
Proof.
  unfold field_boundary_obs, fs_boundary_safe, fs_interior_unsafe.
  unfold boundary_temp. simpl. reflexivity.
Qed.

Lemma interior_safe_disagrees :
    interior_safe fs_boundary_safe <> interior_safe fs_interior_unsafe.
Proof.
  unfold interior_safe, fs_boundary_safe, fs_interior_unsafe.
  unfold interior_temp. simpl.
  pose proof max_temp_predecessor_lt as Hpred.
  destruct (Nat.ltb (max_temp - 1) max_temp) eqn:H1;
  destruct (Nat.ltb max_temp max_temp) eqn:H2;
  try discriminate.
  - apply Nat.ltb_lt in H2. exfalso. exact (Nat.lt_irrefl _ H2).
  - exfalso. assert (Nat.ltb (max_temp - 1) max_temp = true) by
      (apply Nat.ltb_lt; exact Hpred). congruence.
Qed.

Theorem boundary_sensor_inadmissible_for_interior_safety :
  ~ boolean_admissible interior_safe field_boundary_obs.
Proof.
  apply safety_relevant_collapse_iff_inadmissible.
  exists fs_boundary_safe. exists fs_interior_unsafe.
  split.
  - apply boundary_obs_same.
  - apply interior_safe_disagrees.
Qed.

(* ================================================================= *)
(** ** 3. Full field sensor restores admissibility                    *)
(* ================================================================= *)

Theorem full_field_sensor_admissible :
  boolean_admissible interior_safe field_full_obs.
Proof.
  unfold boolean_admissible.
  exists (fun obs =>
    match obs with
    | (field, _, _) => Nat.ltb (interior_temp field) max_temp
    end).
  intro fs. unfold interior_safe, field_full_obs. simpl. reflexivity.
Qed.

(* ================================================================= *)
(** ** 4. Refinement: full field refines boundary-only               *)
(* ================================================================= *)

Theorem full_field_refines_boundary :
  refines field_full_obs field_boundary_obs.
Proof.
  unfold refines, field_full_obs, field_boundary_obs.
  intros s1 s2 H. inversion H.
  unfold boundary_temp. destruct (fs_field s1), (fs_field s2);
    simpl in *; congruence.
Qed.

(* ================================================================= *)
(** ** 5. Sensor placement theorem                                    *)
(* ================================================================= *)

(** Sensors placed only at the boundary cannot warrant interior safety claims.
    This theorem formalises the physical intuition: the safety predicate
    "the interior is below max_temp" is inadmissible w.r.t. boundary-only observation. *)
Theorem sensor_placement_inadmissibility :
  forall (obs_map : FieldState -> BoundaryObs),
    (forall fs, obs_map fs = field_boundary_obs fs) ->
    ~ boolean_admissible interior_safe obs_map.
Proof.
  intros obs_map Hobs.
  intros [Phi_hat Hfact].
  apply interior_safe_disagrees.
  rewrite Hfact, Hfact.
  rewrite Hobs, Hobs.
  rewrite boundary_obs_same. reflexivity.
Qed.

