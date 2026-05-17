(** * BoundaryConditions.v

    Physical state space and boundary condition model for Case Study A:
    Sensor Boundary Collapse.

    Physical states encode temperature, pressure, and boundary flux.
    Boundary conditions define what a sensor at the physical boundary
    can and cannot observe.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.

(* ================================================================= *)
(** ** 1. Physical state                                              *)
(* ================================================================= *)

Record PhysicalState := {
  temperature   : nat;
  pressure      : nat;
  boundary_flux : nat
}.

(** Two states are boundary-equal when they agree on all boundary-observable
    fields (but may differ in interior fields). *)
Definition boundary_equal (s1 s2 : PhysicalState) : Prop :=
  boundary_flux s1 = boundary_flux s2 /\
  pressure s1 = pressure s2.

(** Boundary equality is an equivalence relation. *)
Lemma boundary_equal_refl : forall s, boundary_equal s s.
Proof. intro s. unfold boundary_equal. tauto. Qed.

Lemma boundary_equal_sym : forall s t,
    boundary_equal s t -> boundary_equal t s.
Proof. intros s t [H1 H2]. unfold boundary_equal. split; symmetry; assumption. Qed.

Lemma boundary_equal_trans : forall s t u,
    boundary_equal s t -> boundary_equal t u -> boundary_equal s u.
Proof.
  intros s t u [H1 H2] [H3 H4]. unfold boundary_equal. split; congruence.
Qed.

(* ================================================================= *)
(** ** 2. Safety thresholds                                           *)
(* ================================================================= *)

Parameter max_temp     : nat.   (** maximum safe temperature  *)
Parameter max_pressure : nat.   (** maximum safe pressure     *)
Parameter max_flux     : nat.   (** maximum safe boundary flux *)

Axiom max_temp_positive     : 0 < max_temp.
Axiom max_pressure_positive : 0 < max_pressure.
Axiom max_flux_positive     : 0 < max_flux.

(* ----------------------------------------------------------------- *)
(** The three positivity assumptions above are not three independent
    pieces of physics.  They are three instances of the same structural
    side condition: a threshold-based witness must be non-degenerate.

    The paper uses examples of the form [k - 1] versus [k].  In Rocq's
    natural-number arithmetic, that comparison is meaningful only when
    [0 < k].  The following record packages that obligation explicitly.
*)

Record NonDegenerateThreshold := {
  threshold_value    : nat;
  threshold_positive : 0 < threshold_value
}.

Definition max_temp_threshold : NonDegenerateThreshold :=
  {| threshold_value := max_temp;
     threshold_positive := max_temp_positive |}.

Definition max_pressure_threshold : NonDegenerateThreshold :=
  {| threshold_value := max_pressure;
     threshold_positive := max_pressure_positive |}.

Definition max_flux_threshold : NonDegenerateThreshold :=
  {| threshold_value := max_flux;
     threshold_positive := max_flux_positive |}.

Lemma threshold_predecessor_lt :
  forall t : NonDegenerateThreshold,
    threshold_value t - 1 < threshold_value t.
Proof.
  intros [k Hpos]. simpl. lia.
Qed.

Lemma max_temp_predecessor_lt : max_temp - 1 < max_temp.
Proof. apply (threshold_predecessor_lt max_temp_threshold). Qed.

Lemma max_pressure_predecessor_lt : max_pressure - 1 < max_pressure.
Proof. apply (threshold_predecessor_lt max_pressure_threshold). Qed.

Lemma max_flux_predecessor_lt : max_flux - 1 < max_flux.
Proof. apply (threshold_predecessor_lt max_flux_threshold). Qed.

(* ================================================================= *)
(** ** 3. Thermal safety predicate                                    *)
(* ================================================================= *)

Definition thermal_safe (s : PhysicalState) : bool :=
  Nat.ltb (temperature s) max_temp.

Definition pressure_safe (s : PhysicalState) : bool :=
  Nat.ltb (pressure s) max_pressure.

Definition flux_safe (s : PhysicalState) : bool :=
  Nat.ltb (boundary_flux s) max_flux.

Definition fully_safe (s : PhysicalState) : bool :=
  thermal_safe s && pressure_safe s && flux_safe s.

(* ================================================================= *)
(** ** 4. Sensor readings                                             *)
(* ================================================================= *)

Record SensorReading := {
  sr_flux     : nat;
  sr_pressure : nat
}.

(** Basic sensor: measures boundary flux and pressure but NOT temperature. *)
Definition sensor_obs (s : PhysicalState) : SensorReading :=
  {| sr_flux     := boundary_flux s;
     sr_pressure := pressure s |}.

(** The basic sensor collapses the temperature dimension:
    two states with different temperatures but same flux/pressure
    are observationally indistinguishable. *)

(* ================================================================= *)
(** ** 5. Enriched sensor reading                                     *)
(* ================================================================= *)

Record EnrichedReading := {
  er_flux        : nat;
  er_pressure    : nat;
  er_temperature : nat
}.

Definition enriched_sensor_obs (s : PhysicalState) : EnrichedReading :=
  {| er_flux        := boundary_flux s;
     er_pressure    := pressure s;
     er_temperature := temperature s |}.

(* ================================================================= *)
(** ** 6. Boundary regions                                            *)
(* ================================================================= *)

(** A boundary region is a spatial region at the physical boundary of the
    monitored system.  Sensors are attached to boundary regions. *)
Record BoundaryRegion := {
  br_id       : nat;
  br_position : nat   (** discretised spatial position *)
}.

(** Two boundary regions are adjacent when their positions differ by 1. *)
Definition adjacent (r1 r2 : BoundaryRegion) : Prop :=
  br_position r1 + 1 = br_position r2 \/
  br_position r2 + 1 = br_position r1.
