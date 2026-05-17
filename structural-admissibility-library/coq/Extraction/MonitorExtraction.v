(** * MonitorExtraction.v

    Verified monitor update function for extraction to OCaml.

    The update_monitor function is the trusted kernel that will be
    extracted.  Its correctness is stated and proved here.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.

Require Import Runtime.MonitorStates.
Require Import Runtime.RuntimeSoundness.
Require Import Runtime.RuptureCertificates.
Require Import Extraction.ExtractableTypes.

(* ================================================================= *)
(** ** 1. Monitor update on extractable types                         *)
(* ================================================================= *)

Definition update_monitor
    (s     : ExtractableSnapshot)
    (input : ExtractableInput) : ExtractableSnapshot :=
  let new_fatigue :=
    ex_fatigue s +
    ei_strain input +
    (if ei_osc    input then 1 else 0) +
    (if ei_widened input then 2 else 0) in
  let new_status :=
    if Nat.ltb fatigue_threshold new_fatigue
    then 2   (* HARD_RUPTURE *)
    else if Nat.ltb (ei_tension input) tension_threshold
    then (if Nat.ltb meta_review_trigger new_fatigue then 1 else 0)
    else 2
  in
  {| ex_fatigue := new_fatigue;
     ex_tension := ei_tension input;
     ex_horizon := ex_horizon s;
     ex_lag     := ei_lag input;
     ex_status  := new_status |}.

(* ================================================================= *)
(** ** 2. Monitor invariant (extractable version)                     *)
(* ================================================================= *)

Definition extractable_monitor_invariant (s : ExtractableSnapshot) : Prop :=
  match ex_status s with
  | 0 => ex_fatigue s <= meta_review_trigger      (* CLOSED *)
  | 1 => meta_review_trigger < ex_fatigue s /\    (* META_REVIEW *)
         ex_fatigue s <= fatigue_threshold
  | _ => True                                      (* HARD_RUPTURE *)
  end.

(* ================================================================= *)
(** ** 3. Invariant preservation                                      *)
(* ================================================================= *)

Theorem update_monitor_preserves_invariants :
  forall s input,
    extractable_monitor_invariant s ->
    extractable_monitor_invariant (update_monitor s input).
Proof.
  intros s input Hinv.
  unfold update_monitor, extractable_monitor_invariant. simpl.
  set (new_f := ex_fatigue s + ei_strain input +
                (if ei_osc input then 1 else 0) +
                (if ei_widened input then 2 else 0)).
  destruct (Nat.ltb fatigue_threshold new_f) eqn:Hfat.
  - (** HARD_RUPTURE case: trivially True *)
    trivial.
  - destruct (Nat.ltb (ei_tension input) tension_threshold) eqn:Htens.
    + destruct (Nat.ltb meta_review_trigger new_f) eqn:Hmeta.
      * (** META_REVIEW *)
        split.
        -- apply Nat.ltb_lt in Hmeta. assumption.
        -- assert (~ fatigue_threshold < new_f) by
             (intro H; apply Nat.ltb_lt in H; congruence). lia.
      * (** CLOSED *)
        assert (~ meta_review_trigger < new_f) by
          (intro H; apply Nat.ltb_lt in H; congruence). lia.
    + (** HARD_RUPTURE *)
      trivial.
Qed.

(* ================================================================= *)
(** ** 4. Hard rupture absorbing (extractable version)                *)
(* ================================================================= *)

Theorem update_monitor_hard_rupture_absorbing :
  forall s input,
    ex_status s = 2 ->
    fatigue_threshold < ex_fatigue s ->
    ex_status (update_monitor s input) = 2.
Proof.
  intros s input Hrup Hfat.
  unfold update_monitor. simpl.
  set (new_f := ex_fatigue s + ei_strain input +
                (if ei_osc input then 1 else 0) +
                (if ei_widened input then 2 else 0)).
  assert (Hlt : fatigue_threshold < new_f) by
    (unfold new_f; destruct (ei_osc input); destruct (ei_widened input); lia).
  apply Nat.ltb_lt in Hlt.
  rewrite Hlt. reflexivity.
Qed.

(* ================================================================= *)
(** ** 5. Dashboard-level action after a verified monitor update      *)
(* ================================================================= *)

Definition engineering_action_after_update
    (s : ExtractableSnapshot)
    (input : ExtractableInput)
    (restriction_cost refinement_cost debt_kind : nat)
    : ExtractableEngineeringAction :=
  engineering_action_from_status
    (ex_status (update_monitor s input))
    restriction_cost
    refinement_cost
    debt_kind.

Theorem engineering_action_after_update_tracks_monitor_status :
  forall s input restriction_cost refinement_cost debt_kind,
    ea_monitor_status
      (engineering_action_after_update
         s input restriction_cost refinement_cost debt_kind)
    = ex_status (update_monitor s input).
Proof.
  intros s input restriction_cost refinement_cost debt_kind.
  unfold engineering_action_after_update, engineering_action_from_status.
  destruct (ex_status (update_monitor s input)) as [| [| n]]; reflexivity.
Qed.

Theorem hard_rupture_update_emits_ticket :
  forall s input restriction_cost refinement_cost debt_kind,
    ex_status (update_monitor s input) = 2 ->
    ea_ticket_kind
      (engineering_action_after_update
         s input restriction_cost refinement_cost debt_kind)
    = ticket_admissibility_failure.
Proof.
  intros s input restriction_cost refinement_cost debt_kind Hstatus.
  unfold engineering_action_after_update.
  rewrite Hstatus.
  apply hard_status_emits_admissibility_ticket.
Qed.

(* ================================================================= *)
(** ** 6. Extraction command                                          *)
(* ================================================================= *)

Extraction Language OCaml.

Extraction "monitor_extracted.ml"
  update_monitor
  update_monitor_preserves_invariants
  engineering_action_after_update
  engineering_action_from_status
  engineering_action_from_certificate
  snapshot_to_extractable
  extractable_to_snapshot
  extracted_cert_valid.

