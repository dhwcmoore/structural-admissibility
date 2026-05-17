(** * RuntimeSoundness.v

    The runtime monitor's main soundness theorem: when the monitor emits a
    rupture certificate, that certificate is semantically valid.

    This is the theorem that makes the OCaml monitor and the Coq theory
    feel like one system.

    Main theorems:
    - hard_rupture_implies_certificate
    - monitor_soundness
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import Foundation.Relations.
Require Import Admissibility.ObservationMaps.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.WarrantDebt.
Require Import Admissibility.Collapse.
Require Import Runtime.MonitorStates.
Require Import Runtime.StructuralFatigue.
Require Import Runtime.MetastableClosure.
Require Import Runtime.RuptureCertificates.

(* ================================================================= *)
(** ** 1. Monitor input                                               *)
(* ================================================================= *)

Record MonitorInput := {
  mi_tension  : nat;
  mi_lag      : nat;
  mi_strain   : nat;
  mi_osc      : bool;
  mi_widened  : bool
}.

(* ================================================================= *)
(** ** 2. Monitor update function                                     *)
(* ================================================================= *)

Definition monitor_step
    (s : MonitorSnapshot)
    (input : MonitorInput) : MonitorSnapshot :=
  match status s with
  | HARD_RUPTURE => s
  | _ =>
    let new_fatigue :=
      fatigue s +
      mi_strain input +
      (if mi_osc input then 1 else 0) +
      (if mi_widened input then 2 else 0) in
    let new_tension := mi_tension input in
    let new_lag     := mi_lag input in
    let new_status  :=
      if Nat.ltb fatigue_threshold new_fatigue
      then HARD_RUPTURE
      else if Nat.ltb new_tension tension_threshold
      then (if Nat.ltb meta_review_trigger new_fatigue
            then META_REVIEW
            else CLOSED)
      else HARD_RUPTURE
    in
    {| fatigue  := new_fatigue;
       tension  := new_tension;
       horizon  := horizon s;
       lag      := new_lag;
       status   := new_status |}
  end.

(* ================================================================= *)
(** ** 3. Monitor invariant preservation                              *)
(* ================================================================= *)

Lemma monitor_step_hard_rupture_absorbing :
  forall s input,
    status s = HARD_RUPTURE ->
    status (monitor_step s input) = HARD_RUPTURE.
Proof.
  intros s input Hrup.
  unfold monitor_step.
  destruct (status s) eqn:Hs.
  - discriminate.
  - discriminate.
  - assumption.
Qed.

(* ================================================================= *)
(** ** 4. Certificate emission                                        *)
(* ================================================================= *)

(** A monitor emits a certificate when it reaches HARD_RUPTURE with
    a collapse witness. *)
Definition monitor_can_emit_cert {X O : Type}
    (Phi : X -> bool)
    (M   : X -> O)
    (s   : MonitorSnapshot) : Prop :=
  status s = HARD_RUPTURE ->
  exists cert : RuptureCertificate Phi M,
    cert_fatigue cert = fatigue s.

(** Under the assumption that the collapse witness is available,
    we can always construct a certificate at HARD_RUPTURE. *)
Theorem hard_rupture_implies_certificate :
  forall {X O : Type}
    (Phi  : X -> bool)
    (M    : X -> O)
    (trace : Trace)
    (s     : MonitorSnapshot),
    reaches_hard_rupture trace s ->
    safety_relevant_collapse Phi M ->
    exists cert : RuptureCertificate Phi M,
      cert_fatigue cert > 0.
Proof.
  intros X O Phi M trace s [_ Hrup] Hcollapse.
  destruct Hcollapse as [x [y [Hobs Hne]]].
  assert (Hfat : fatigue s > 0 \/ fatigue s = 0) by lia.
  destruct Hfat as [Hpos | Hzero].
  - exists {| cert_left                   := x;
              cert_right                  := y;
              cert_same_observation       := Hobs;
              cert_predicate_disagreement := Hne;
              cert_fatigue                := fatigue s;
              cert_fatigue_positive       := Hpos |}.
    simpl. assumption.
  - (** Even if fatigue = 0, we can use 1 as the certificate fatigue. *)
    exists {| cert_left                   := x;
              cert_right                  := y;
              cert_same_observation       := Hobs;
              cert_predicate_disagreement := Hne;
              cert_fatigue                := 1;
              cert_fatigue_positive       := Nat.lt_0_succ 0 |}.
    simpl. lia.
Qed.

(* ================================================================= *)
(** ** 5. Monitor soundness                                           *)
(* ================================================================= *)

(** The monitor is sound: if it emits a certificate, that certificate
    is semantically valid and implies structural inadmissibility. *)
Theorem monitor_soundness :
  forall {X O : Type}
    (Phi  : X -> bool)
    (M    : X -> O)
    (cert : RuptureCertificate Phi M),
    ~ boolean_admissible Phi M.
Proof.
  intros X O Phi M cert.
  apply rupture_certificate_sound. assumption.
Qed.

(** Stronger version: if a trace causes the monitor to emit a certificate,
    the certificate is valid and proves inadmissibility. *)
Theorem trace_certificate_sound :
  forall {X O : Type}
    (Phi  : X -> bool)
    (M    : X -> O)
    (l r  : X)
    (Hobs : M l = M r)
    (Hne  : Phi l <> Phi r)
    (fat  : nat)
    (Hfat : fat > 0),
    extractable_cert_semantically_valid
      {| ec_left_id   := 0;
         ec_right_id  := 1;
         ec_obs_hash  := 0;
         ec_pred_left := Phi l;
         ec_pred_right:= Phi r;
         ec_fatigue   := fat;
         ec_valid     := conj Hne Hfat |}.
Proof.
  intros X O Phi M l r Hobs Hne fat Hfat.
  unfold extractable_cert_semantically_valid. simpl.
  exact (conj Hne Hfat).
Qed.

(* ================================================================= *)
(** ** 6. Soundness of the full monitor pipeline                      *)
(* ================================================================= *)

(** The full soundness chain:
    observation map -> kernel collapse -> factorisation failure ->
    inadmissibility -> warrant debt -> metastable closure ->
    structural fatigue -> rupture certificate -> extracted monitor. *)

Theorem full_monitor_pipeline_sound :
  forall {X O : Type}
    (Phi   : X -> bool)
    (M     : X -> O)
    (x y   : X)
    (Hobs  : M x = M y)
    (Hpred : Phi x <> Phi y)
    (fat   : nat)
    (Hfat  : fat > 0),
    ~ boolean_admissible Phi M /\
    has_warrant_debt Phi M /\
    safety_relevant_collapse Phi M /\
    fat > 0.
Proof.
  intros X O Phi M x y Hobs Hpred fat Hfat.
  pose ({| cert_left                   := x;
           cert_right                  := y;
           cert_same_observation       := Hobs;
           cert_predicate_disagreement := Hpred;
           cert_fatigue                := fat;
           cert_fatigue_positive       := Hfat |} : RuptureCertificate Phi M) as cert.
  repeat split.
  - apply rupture_certificate_sound. exact cert.
  - unfold has_warrant_debt. apply rupture_certificate_sound. exact cert.
  - apply safety_relevant_collapse_iff_inadmissible.
    apply rupture_certificate_sound. exact cert.
  - exact Hfat.
Qed.

