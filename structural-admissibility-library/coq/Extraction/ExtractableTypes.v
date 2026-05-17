(** * ExtractableTypes.v

    Coq types safe for extraction to OCaml.

    Extraction-safe constraints:
    - No Prop in computational paths.
    - Use bool, nat, lists, decidable equality.
    - Avoid Type polymorphism in runtime structures.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import Runtime.MonitorStates.

(* ================================================================= *)
(** ** 1. Extractable monitor status                                  *)
(* ================================================================= *)

(** Encoded as nat: 0=CLOSED, 1=META_REVIEW, 2=HARD_RUPTURE *)
Definition status_to_nat (st : MonitorStatus) : nat :=
  match st with
  | CLOSED       => 0
  | META_REVIEW  => 1
  | HARD_RUPTURE => 2
  end.

Definition nat_to_status (n : nat) : MonitorStatus :=
  match n with
  | 0 => CLOSED
  | 1 => META_REVIEW
  | _ => HARD_RUPTURE
  end.

Lemma status_nat_roundtrip : forall st,
    nat_to_status (status_to_nat st) = st.
Proof. intro st. destruct st; reflexivity. Qed.

(* ================================================================= *)
(** ** 2. Extractable snapshot                                        *)
(* ================================================================= *)

Record ExtractableSnapshot := {
  ex_fatigue  : nat;
  ex_tension  : nat;
  ex_horizon  : nat;
  ex_lag      : nat;
  ex_status   : nat   (** 0=CLOSED, 1=META_REVIEW, 2=HARD_RUPTURE *)
}.

Definition snapshot_to_extractable (s : MonitorSnapshot) : ExtractableSnapshot :=
  {| ex_fatigue := fatigue s;
     ex_tension := tension s;
     ex_horizon := horizon s;
     ex_lag     := lag s;
     ex_status  := status_to_nat (status s) |}.

Definition extractable_to_snapshot (e : ExtractableSnapshot) : MonitorSnapshot :=
  {| fatigue := ex_fatigue e;
     tension := ex_tension e;
     horizon := ex_horizon e;
     lag     := ex_lag e;
     status  := nat_to_status (ex_status e) |}.

Lemma snapshot_extractable_roundtrip : forall s,
    extractable_to_snapshot (snapshot_to_extractable s) = s.
Proof.
  intro s. unfold extractable_to_snapshot, snapshot_to_extractable.
  simpl. rewrite status_nat_roundtrip. destruct s. reflexivity.
Qed.

(* ================================================================= *)
(** ** 3. Extractable monitor input                                   *)
(* ================================================================= *)

Record ExtractableInput := {
  ei_tension  : nat;
  ei_lag      : nat;
  ei_strain   : nat;
  ei_osc      : bool;
  ei_widened  : bool
}.

(* ================================================================= *)
(** ** 4. Extractable rupture certificate                             *)
(* ================================================================= *)

(** Already defined in RuptureCertificates.v as ExtractableRuptureCert.
    Re-exported here for extraction convenience. *)

Require Export Runtime.RuptureCertificates.

(* ================================================================= *)
(** ** 5. Extractable engineering actions                             *)
(* ================================================================= *)

(** These numeric codes are deliberately simple.  They are meant for a
    dashboard, ticket generator, or integration test harness, not for proof
    search.

    Ticket kind:
      0 = no ticket
      1 = admissibility failure ticket
      2 = structural review ticket

    Repair recommendation:
      0 = no action
      1 = restrict the claim
      2 = refine the observation
      3 = choose restriction or refinement by cost review
      4 = carry explicit warrant debt under a stated limitation

    Warrant-debt kind:
      0 = generic
      1 = quorum debt
      2 = trace debt
      3 = boundary debt
      4 = threshold debt

    Cost band:
      0 = low
      1 = moderate
      2 = high
      3 = unknown
*)

Definition ticket_none : nat := 0.
Definition ticket_admissibility_failure : nat := 1.
Definition ticket_structural_review : nat := 2.

Definition repair_no_action : nat := 0.
Definition repair_restrict_claim : nat := 1.
Definition repair_refine_observation : nat := 2.
Definition repair_choose_by_cost : nat := 3.
Definition repair_carry_explicit_debt : nat := 4.

Definition debt_generic : nat := 0.
Definition debt_quorum : nat := 1.
Definition debt_trace : nat := 2.
Definition debt_boundary : nat := 3.
Definition debt_threshold : nat := 4.

Definition cost_low : nat := 0.
Definition cost_moderate : nat := 1.
Definition cost_high : nat := 2.
Definition cost_unknown : nat := 3.

Record ExtractableEngineeringAction := {
  ea_ticket_kind           : nat;
  ea_monitor_status        : nat;
  ea_repair_recommendation : nat;
  ea_debt_kind             : nat;
  ea_restriction_cost      : nat;
  ea_refinement_cost       : nat
}.

Definition recommended_repair_for_debt_kind (debt_kind : nat) : nat :=
  if Nat.eqb debt_kind debt_threshold then repair_carry_explicit_debt
  else if Nat.eqb debt_kind debt_boundary then repair_refine_observation
  else repair_choose_by_cost.

Definition engineering_action_from_status
    (status restriction_cost refinement_cost debt_kind : nat)
    : ExtractableEngineeringAction :=
  match status with
  | 0 =>
      {| ea_ticket_kind := ticket_none;
         ea_monitor_status := 0;
         ea_repair_recommendation := repair_no_action;
         ea_debt_kind := debt_kind;
         ea_restriction_cost := restriction_cost;
         ea_refinement_cost := refinement_cost |}
  | 1 =>
      {| ea_ticket_kind := ticket_structural_review;
         ea_monitor_status := 1;
         ea_repair_recommendation := recommended_repair_for_debt_kind debt_kind;
         ea_debt_kind := debt_kind;
         ea_restriction_cost := restriction_cost;
         ea_refinement_cost := refinement_cost |}
  | _ =>
      {| ea_ticket_kind := ticket_admissibility_failure;
         ea_monitor_status := status;
         ea_repair_recommendation := recommended_repair_for_debt_kind debt_kind;
         ea_debt_kind := debt_kind;
         ea_restriction_cost := restriction_cost;
         ea_refinement_cost := refinement_cost |}
  end.

Definition engineering_action_from_certificate
    (cert : ExtractableRuptureCert)
    (restriction_cost refinement_cost debt_kind : nat)
    : ExtractableEngineeringAction :=
  if extracted_cert_valid cert then
    engineering_action_from_status 2 restriction_cost refinement_cost debt_kind
  else
    engineering_action_from_status 0 restriction_cost refinement_cost debt_kind.

Lemma closed_status_emits_no_ticket :
  forall restriction_cost refinement_cost debt_kind,
    ea_ticket_kind
      (engineering_action_from_status 0 restriction_cost refinement_cost debt_kind)
    = ticket_none.
Proof. reflexivity. Qed.

Lemma hard_status_emits_admissibility_ticket :
  forall restriction_cost refinement_cost debt_kind,
    ea_ticket_kind
      (engineering_action_from_status 2 restriction_cost refinement_cost debt_kind)
    = ticket_admissibility_failure.
Proof. reflexivity. Qed.

Theorem valid_certificate_emits_admissibility_ticket :
  forall cert restriction_cost refinement_cost debt_kind,
    extracted_cert_valid cert = true ->
    ea_ticket_kind
      (engineering_action_from_certificate cert restriction_cost refinement_cost debt_kind)
    = ticket_admissibility_failure.
Proof.
  intros cert restriction_cost refinement_cost debt_kind Hvalid.
  unfold engineering_action_from_certificate.
  rewrite Hvalid.
  apply hard_status_emits_admissibility_ticket.
Qed.

(* ================================================================= *)
(** ** 6. Extraction directives                                       *)
(* ================================================================= *)

Require Extraction.

Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive nat  => "int" ["0" "succ"] "(fun fO fS n -> if n = 0 then fO () else fS (n-1))".
Extract Inductive list => "list" ["[]" "(::)"].
Extract Inductive option => "option" ["None" "Some"].

Extract Constant Nat.ltb => "(fun n m -> n < m)".
Extract Constant Nat.leb => "(fun n m -> n <= m)".
Extract Constant Nat.eqb => "(fun n m -> n = m)".
Extract Constant Nat.add => "(+)".
Extract Constant Nat.sub => "(fun n m -> max 0 (n - m))".
Extract Constant Nat.mul => "( * )".

