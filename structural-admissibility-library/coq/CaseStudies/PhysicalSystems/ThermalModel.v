(** * ThermalModel.v

    Thermal dynamics model for Case Study A.

    Models heat diffusion at the boundary and how sensor placement
    relative to the heat source affects observational completeness.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import CaseStudies.PhysicalSystems.BoundaryConditions.

(* ================================================================= *)
(** ** 1. Heat source model                                           *)
(* ================================================================= *)

Record HeatSource := {
  hs_position : nat;
  hs_power    : nat
}.

(** Distance from heat source determines temperature. *)
Definition temperature_at_distance (hs : HeatSource) (d : nat) : nat :=
  if Nat.eqb d 0 then hs_power hs
  else (hs_power hs) / (d + 1).

(** Physical state given a heat source and sensor position. *)
Definition state_from_source (hs : HeatSource) (sensor_pos distance : nat) : PhysicalState :=
  {| temperature   := temperature_at_distance hs distance;
     pressure      := 5;
     boundary_flux := (hs_power hs) / (sensor_pos + 1) |}.

(* ================================================================= *)
(** ** 2. Thermal gradient                                            *)
(* ================================================================= *)

(** The thermal gradient: difference in temperature between interior and boundary. *)
Definition thermal_gradient (s : PhysicalState) (interior_temp : nat) : nat :=
  if Nat.leb interior_temp (temperature s) then
    temperature s - interior_temp
  else
    interior_temp - temperature s.

(** A large thermal gradient indicates potential for collapse:
    the boundary sensor may read safe while the interior is unsafe. *)
Definition large_gradient_witness (interior_max sensor_max : nat) :
    exists s1 s2 : PhysicalState,
      sensor_obs s1 = sensor_obs s2 /\
      thermal_safe s1 <> thermal_safe s2.
Proof.
  exists {| temperature := max_temp - 1; pressure := 5; boundary_flux := 3 |}.
  exists {| temperature := max_temp;     pressure := 5; boundary_flux := 3 |}.
  split.
  - unfold sensor_obs. simpl. reflexivity.
  - unfold thermal_safe. simpl.
    pose proof max_temp_predecessor_lt as Hpred.
    destruct (Nat.ltb (max_temp - 1) max_temp) eqn:H1;
    destruct (Nat.ltb max_temp max_temp) eqn:H2;
    try discriminate.
    + apply Nat.ltb_lt in H2. exfalso. exact (Nat.lt_irrefl _ H2).
    + exfalso. assert (Nat.ltb (max_temp - 1) max_temp = true) by
        (apply Nat.ltb_lt; exact Hpred). congruence.
Qed.

(* ================================================================= *)
(** ** 3. Thermal PDE discretisation                                  *)
(* ================================================================= *)

(** A discrete-time, discrete-space heat equation.
    State: temperature field as a list indexed by position. *)
Definition ThermalField := list nat.

Fixpoint heat_step (field : ThermalField) : ThermalField :=
  match field with
  | []          => []
  | [x]         => [x]
  | x :: ((y :: _) as tail) =>
    (x + y) / 2 :: heat_step tail
  end.

(** The boundary temperature is the first element. *)
Definition boundary_temp (field : ThermalField) : nat :=
  match field with
  | []    => 0
  | x :: _ => x
  end.

(** The interior temperature is the last element. *)
Fixpoint interior_temp (field : ThermalField) : nat :=
  match field with
  | []     => 0
  | [x]    => x
  | _ :: rest => interior_temp rest
  end.

