(** * MetastableClosure.v

    Formalisation of the distinction between operational closure and structural safety.

    Metastable closure: the monitor reports CLOSED but the system has warrant debt
    and non-zero fatigue.  This is the key novel concept: a system can appear
    operationally safe while remaining structurally unsafe.

    Key theorems:
    - operational_closure_not_structural_safety (existential: they can diverge)
    - metastable_closure_has_warrant_debt (universal: metastable implies in debt)
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Logic.Classical_Prop.

Require Import Foundation.Relations.
Require Import Admissibility.ObservationMaps.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.WarrantDebt.
Require Import Runtime.MonitorStates.
Require Import Runtime.StructuralFatigue.

(* ================================================================= *)
(** ** 1. Operational closure                                         *)
(* ================================================================= *)

Definition operationally_closed (s : MonitorSnapshot) : Prop :=
  status s = CLOSED.

(* ================================================================= *)
(** ** 2. Structural safety                                           *)
(* ================================================================= *)

Definition structurally_safe {X O : Type}
    (Phi : X -> bool) (M : X -> O) : Prop :=
  boolean_admissible Phi M.

Definition structurally_unsafe {X O : Type}
    (Phi : X -> bool) (M : X -> O) : Prop :=
  ~ structurally_safe Phi M.

(* ================================================================= *)
(** ** 3. Metastable closure                                         *)
(* ================================================================= *)

(** Metastable closure: monitor says CLOSED but structural safety is absent
    and fatigue is positive — the closure is not warranted. *)
Definition metastable_closure {X O : Type}
    (Phi : X -> bool)
    (M   : X -> O)
    (s   : MonitorSnapshot) : Prop :=
  operationally_closed s /\
  structurally_unsafe Phi M /\
  fatigue s > 0.

(* ================================================================= *)
(** ** 4. Operational closure does not imply structural safety        *)
(* ================================================================= *)

Theorem operational_closure_not_structural_safety :
  exists (X : Type) (O : Type) (Phi : X -> bool) (M : X -> O)
    (s : MonitorSnapshot),
    operationally_closed s /\
    structurally_unsafe Phi M.
Proof.
  (** Concrete construction:
      X = nat, O = nat, M = mod 2, Phi = leb · 1,
      s = initial_snapshot (status = CLOSED). *)
  exists nat. exists nat.
  exists (fun x => if Nat.leb x 1 then true else false).
  exists (fun x => Nat.modulo x 2).
  exists initial_snapshot.
  split.
  - unfold operationally_closed, initial_snapshot. simpl. reflexivity.
  - unfold structurally_unsafe, structurally_safe, boolean_admissible.
    intros [Phi_hat Hfact].
    assert (H0 : Phi_hat (Nat.modulo 0 2) = true).
    { rewrite <- Hfact. simpl. reflexivity. }
    assert (H2 : Phi_hat (Nat.modulo 2 2) = false).
    { rewrite <- Hfact. simpl. reflexivity. }
    simpl in H0, H2. rewrite H0 in H2. discriminate.
Qed.

(* ================================================================= *)
(** ** 5. Metastable closure implies warrant debt                     *)
(* ================================================================= *)

Theorem metastable_closure_has_warrant_debt :
  forall {X : Type} {O : Type}
    (Phi : X -> bool)
    (M   : X -> O)
    (s   : MonitorSnapshot),
    metastable_closure Phi M s ->
    has_warrant_debt Phi M.
Proof.
  intros X O Phi M s [Hclosed [Hunsafe Hfat]].
  unfold has_warrant_debt.
  assumption.
Qed.

(* ================================================================= *)
(** ** 6. Metastable closure implies incomplete structural picture     *)
(* ================================================================= *)

(** A metastable-closed system has a collapse witness it cannot see. *)
Theorem metastable_closure_has_collapse_witness :
  forall {X : Type} {O : Type}
    (Phi : X -> bool)
    (M   : X -> O)
    (s   : MonitorSnapshot),
    metastable_closure Phi M s ->
    exists x y, M x = M y /\ Phi x <> Phi y.
Proof.
  intros X O Phi M s Hmc.
  apply inadmissible_implies_witness.
  exact (metastable_closure_has_warrant_debt Hmc).
Qed.

(* ================================================================= *)
(** ** 7. Closed status is not a safety certificate                   *)
(* ================================================================= *)

(** The monitor's CLOSED status is not equivalent to structural safety
    unless the monitor's observation is admissible w.r.t. the predicate. *)

Definition monitor_is_structurally_grounded {X O : Type}
    (Phi : X -> bool)
    (M   : X -> O)
    (s   : MonitorSnapshot) : Prop :=
  operationally_closed s -> structurally_safe Phi M.

(** Whether the monitor is grounded is independent of its status. *)
Theorem grounded_closure_implies_structural_safety :
  forall {X : Type} {O : Type}
    (Phi : X -> bool)
    (M   : X -> O)
    (s   : MonitorSnapshot),
    monitor_is_structurally_grounded Phi M s ->
    operationally_closed s ->
    structurally_safe Phi M.
Proof.
  intros X O Phi M s H Hclosed.
  apply H. assumption.
Qed.

(** In metastable closure, the monitor is NOT grounded. *)
Theorem metastable_ungrounded :
  forall {X : Type} {O : Type}
    (Phi : X -> bool)
    (M   : X -> O)
    (s   : MonitorSnapshot),
    metastable_closure Phi M s ->
    ~ monitor_is_structurally_grounded Phi M s.
Proof.
  intros X O Phi M s [Hclosed [Hunsafe _]] Hgrounded.
  apply Hunsafe. apply Hgrounded. assumption.
Qed.

(* ================================================================= *)
(** ** 8. Transition out of metastable closure requires refinement    *)
(* ================================================================= *)

(** The only way to exit metastable closure while staying closed is to
    either (a) refine the observation to restore structural safety, or
    (b) transition to META_REVIEW or HARD_RUPTURE. *)

Definition exits_metastable_closure {X O : Type}
    (Phi : X -> bool) (M : X -> O) (s : MonitorSnapshot) : Prop :=
  operationally_closed s /\ structurally_safe Phi M.

Theorem exit_metastable_requires_structural_fix :
  forall {X : Type} {O : Type}
    (Phi : X -> bool)
    (M   : X -> O)
    (s   : MonitorSnapshot),
    metastable_closure Phi M s ->
    exits_metastable_closure Phi M s ->
    False.
Proof.
  intros X O Phi M s [_ [Hunsafe _]] [_ Hsafe].
  apply Hunsafe. assumption.
Qed.

