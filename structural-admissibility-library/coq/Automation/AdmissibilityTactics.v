(** * AdmissibilityTactics.v

    Domain-specific tactics for the structural admissibility library.

    These tactics discharge recurring proof obligations:
    - kernel equivalence,
    - factorisation witnesses,
    - refinement chains,
    - collapse witnesses,
    - rupture certificate construction.

    IMPORTANT: tactics reduce proof pain, not proof content.
    Case-specific semantic obligations remain explicit.
*)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.ClassicalDescription.

Require Import Foundation.Relations.
Require Import Foundation.Orders.
Require Import Foundation.Quotients.
Require Import Admissibility.ObservationMaps.
Require Import Admissibility.Factorisation.
Require Import Admissibility.KernelPairs.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.Collapse.
Require Import Admissibility.WarrantDebt.
Require Import Runtime.RuptureCertificates.

(* ================================================================= *)
(** ** 1. Kernel tactics                                              *)
(* ================================================================= *)

(** Solve kernel equivalence goals by unfolding and congruence. *)
Ltac solve_kernel_equiv :=
  unfold kernel, respects_kernel, collapsed_by in *;
  intros;
  try subst;
  try reflexivity;
  try congruence;
  try assumption.

(** Solve goals of the form: kernel M x y *)
Ltac prove_kernel :=
  unfold kernel;
  try reflexivity;
  try congruence.

(** Solve kernel_included goals. *)
Ltac solve_kernel_included :=
  unfold kernel_included, kernel;
  intros;
  try congruence;
  try assumption.

Example kernel_tactic_test :
  forall (x : nat), kernel (fun n => n * 2) x x.
Proof. intro. prove_kernel. Qed.

(* ================================================================= *)
(** ** 2. Factorisation tactics                                       *)
(* ================================================================= *)

(** Solve boolean_admissible goals by providing an explicit factorisation. *)
Ltac solve_admissible :=
  unfold boolean_admissible;
  eexists;
  intros;
  try reflexivity;
  try (simpl; reflexivity).

(** Solve factorisation goals when Phi_hat is a simple composition. *)
Ltac solve_factorisation :=
  unfold factors_through, boolean_admissible;
  eexists;
  intro x;
  try reflexivity.

(** Prove admissibility by showing constant-on-kernel and applying main theorem. *)
Ltac admissible_by_kernel_constant :=
  apply constant_on_kernel_implies_admissible;
  intros;
  try congruence;
  try (unfold kernel in *; congruence).

(** Prove inadmissibility by providing a counterexample pair. *)
Ltac inadmissible_by_counterexample left_state right_state :=
  apply inadmissibility_witness_implies_inadmissible
    with (iw_left := left_state) (iw_right := right_state);
  constructor;
  [try (simpl; reflexivity) | try discriminate].

Example admissible_tactic_test :
  boolean_admissible (fun x : nat => Nat.eqb x x) (fun x => x).
Proof. solve_admissible. Qed.

(* ================================================================= *)
(** ** 3. Refinement tactics                                          *)
(* ================================================================= *)

(** Solve refinement goals by unfolding and applying congruence. *)
Ltac solve_refinement :=
  unfold refines;
  intros;
  try assumption;
  try congruence.

(** Build a refinement chain using registered hints. *)
Hint Resolve refines_refl refines_trans : refinement.
Hint Resolve trivial_obs_coarsest identity_obs_finest : refinement.
Hint Resolve refines_product_left refines_product_right : refinement.

Ltac refinement_chain :=
  eauto with refinement.

(** Prove a refinement by showing kernel inclusion. *)
Ltac refinement_by_kernel :=
  apply refines_iff_kernel_included;
  solve_kernel_included.

Example refinement_tactic_test :
  refines (fun x : nat => x) (fun x => x).
Proof. solve_refinement. Qed.

(* ================================================================= *)
(** ** 4. Collapse tactics                                            *)
(* ================================================================= *)

(** Prove safety_relevant_collapse by exhibiting a counterexample pair. *)
Ltac derive_collapse left_state right_state :=
  unfold safety_relevant_collapse;
  exists left_state; exists right_state;
  split;
  [try (simpl; reflexivity) | try discriminate].

(** Prove inadmissibility from collapse. *)
Ltac inadmissible_from_collapse left_state right_state :=
  apply safety_relevant_collapse_iff_inadmissible;
  derive_collapse left_state right_state.

Example collapse_tactic_test :
  safety_relevant_collapse
    (fun x : nat => if Nat.leb x 1 then true else false)
    (fun x => Nat.modulo x 2).
Proof.
  derive_collapse 0 2.
Qed.

(* ================================================================= *)
(** ** 5. Warrant witness tactics                                     *)
(* ================================================================= *)

(** Build a WarrantDebtWitness from a concrete pair. *)
Ltac build_warrant_witness left_state right_state :=
  refine {| wd_left      := left_state;
            wd_right     := right_state;
            wd_collapsed := _;
            wd_disagrees := _ |};
  [try (simpl; reflexivity) | try discriminate].

Example warrant_witness_test :
  WarrantDebtWitness
    (fun x : nat => if Nat.leb x 1 then true else false)
    (fun x => Nat.modulo x 2).
Proof.
  build_warrant_witness 0 2.
Qed.

(* ================================================================= *)
(** ** 6. Rupture certificate tactics                                 *)
(* ================================================================= *)

(** Build a rupture certificate from a concrete pair and fatigue value. *)
Ltac build_rupture_certificate left_state right_state fat :=
  refine {| cert_left                   := left_state;
            cert_right                  := right_state;
            cert_same_observation       := _;
            cert_predicate_disagreement := _;
            cert_fatigue                := fat;
            cert_fatigue_positive       := _ |};
  [try (simpl; reflexivity) | try discriminate | try lia].

Example cert_tactic_test :
  RuptureCertificate
    (fun x : nat => if Nat.leb x 1 then true else false)
    (fun x => Nat.modulo x 2).
Proof.
  build_rupture_certificate 0 2 1.
Qed.

(* ================================================================= *)
(** ** 7. No-recovery tactic                                         *)
(* ================================================================= *)

(** Prove that post-processing cannot repair inadmissibility. *)
Ltac no_recovery_tactic :=
  apply postprocessing_cannot_restore_admissibility.

(* ================================================================= *)
(** ** 8. Combined solver for standard inadmissibility goals         *)
(* ================================================================= *)

(** Full pipeline: exhibit counterexample, derive collapse, conclude inadmissible. *)
Ltac full_inadmissible left_state right_state :=
  apply safety_relevant_collapse_iff_inadmissible;
  exists left_state; exists right_state;
  repeat split;
  [simpl; try reflexivity | try discriminate].

