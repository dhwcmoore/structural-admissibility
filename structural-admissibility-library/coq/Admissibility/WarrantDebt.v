(** * WarrantDebt.v

    Warrant debt: the gap between what a system claims about safety
    and what its observational structure can warrant.

    Both qualitative and quantitative formulations are given.
    The central structure is WarrantDebtWitness: an explicit record of a
    collapsing pair with differing predicate values.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.IndefiniteDescription.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import Foundation.Relations.
Require Import Foundation.Orders.
Require Import Admissibility.ObservationMaps.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.Collapse.
Require Import Admissibility.Refinement.

(* ================================================================= *)
(** ** 1. Qualitative warrant debt                                    *)
(* ================================================================= *)

Definition has_warrant_debt {X O : Type}
    (Phi : X -> bool) (M : X -> O) : Prop :=
  ~ boolean_admissible Phi M.

Lemma has_warrant_debt_iff_safety_relevant_collapse :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    has_warrant_debt Phi M <-> safety_relevant_collapse Phi M.
Proof.
  intros. unfold has_warrant_debt.
  split.
  - intro H. apply safety_relevant_collapse_iff_inadmissible. assumption.
  - intro H. apply safety_relevant_collapse_iff_inadmissible. assumption.
Qed.

(* ================================================================= *)
(** ** 2. Witnessed warrant debt record                               *)
(* ================================================================= *)

Record WarrantDebtWitness {X O : Type}
    (Phi : X -> bool)
    (M : X -> O) := {
  wd_left      : X;
  wd_right     : X;
  wd_collapsed : M wd_left = M wd_right;
  wd_disagrees : Phi wd_left <> Phi wd_right
}.

(** A witnessed warrant debt is sufficient for inadmissibility. *)
Theorem warrant_debt_witness_sound :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    WarrantDebtWitness Phi M ->
    has_warrant_debt Phi M.
Proof.
  intros X O Phi M W.
  unfold has_warrant_debt, boolean_admissible.
  intros [Phi_hat Hfact].
  destruct W as [l r Hcol Hne]. apply Hne.
  rewrite Hfact, Hfact, Hcol. reflexivity.
Qed.

Theorem warrant_debt_witness_complete :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    WarrantDebtWitness Phi M ->
    ~ boolean_admissible Phi M.
Proof.
  intros X O Phi M W.
  apply warrant_debt_witness_sound. assumption.
Qed.

(* ================================================================= *)
(** ** 3. Constructive witness from inadmissibility (finite case)     *)
(* ================================================================= *)

(** For finite X, inadmissibility always yields an explicit witness. *)
Theorem finite_inadmissibility_has_witness :
  forall {O : Type} (enum_X : list nat) (Phi : nat -> bool) (M : nat -> O),
    (forall x, In x enum_X) ->   (* enum_X covers all states *)
    ~ boolean_admissible Phi M ->
    WarrantDebtWitness Phi M.
Proof.
  intros O enum_X Phi M Hcover Hinadm.
  assert (Hex : exists x y : nat, M x = M y /\ Phi x <> Phi y).
  { apply Classical_Prop.NNPP. intro Hnex.
    apply Hinadm.
    apply constant_on_kernel_implies_admissible.
    intros x y Hxy.
    apply Classical_Prop.NNPP. intro Hne.
    apply Hnex. exists x. exists y. exact (conj Hxy Hne). }
  destruct (constructive_indefinite_description
              (fun x : nat => exists y : nat, M x = M y /\ Phi x <> Phi y)
              Hex) as [x Hx].
  destruct (constructive_indefinite_description
              (fun y : nat => M x = M y /\ Phi x <> Phi y)
              Hx) as [y [Hcol Hne]].
  exact {| wd_left := x; wd_right := y;
           wd_collapsed := Hcol; wd_disagrees := Hne |}.
Qed.

(* ================================================================= *)
(** ** 4. Quantitative warrant debt                                   *)
(* ================================================================= *)

(** The warrant debt of Phi w.r.t. M is the number of distinct
    observation equivalence classes that contain a safety-relevant pair.
    For finite state spaces with explicit enumeration: *)

Definition warrant_debt_count {O : Type}
    (enum_X : list nat)
    (Phi : nat -> bool)
    (M : nat -> O)
    (O_dec : forall a b : O, {a = b} + {a <> b}) : nat :=
  List.length
    (List.filter (fun p =>
       match p with (x, y) =>
         if O_dec (M x) (M y) then
           negb (Bool.eqb (Phi x) (Phi y))
         else false
       end)
     (List.list_prod enum_X enum_X)).

(* ================================================================= *)
(** ** 5. Warrant debt monotone under degradation                     *)
(* ================================================================= *)

(** Degrading an observation (coarsening it) cannot reduce warrant debt
    below zero, and may increase it. *)

Theorem warrant_debt_monotone_under_degradation :
  forall {X O1 O2 : Type}
    (Phi : X -> bool)
    (M1 : X -> O1)
    (M2 : X -> O2),
    refines M2 M1 ->    (* M2 is finer than M1; M1 is coarser *)
    has_warrant_debt Phi M2 ->
    has_warrant_debt Phi M1.
Proof.
  intros X O1 O2 Phi M1 M2 Href Hdebt2.
  unfold has_warrant_debt in *.
  intro Hadm1.
  apply Hdebt2.
  apply admissibility_preserved_by_refinement with (M1 := M1); assumption.
Qed.

(** Refinement can reduce warrant debt. *)
Theorem refinement_can_eliminate_warrant_debt :
  exists (X : Type) (O1 O2 : Type)
    (Phi : X -> bool) (M1 : X -> O1) (M2 : X -> O2),
    refines M2 M1 /\
    has_warrant_debt Phi M1 /\
    ~ has_warrant_debt Phi M2.
Proof.
  (** Same construction as admissibility_not_antitone. *)
  destruct admissibility_not_antitone as
    [X [O1 [O2 [Phi [M1 [M2 [Href [Hadm2 Hinadm1]]]]]]]].
  exists X. exists O1. exists O2. exists Phi. exists M1. exists M2.
  split; [assumption | split].
  - unfold has_warrant_debt. assumption.
  - unfold has_warrant_debt. intro H. apply H. assumption.
Qed.

(* ================================================================= *)
(** ** 6. Warrant debt severity                                       *)
(* ================================================================= *)

(** Severity can be measured by the proportion of kernel classes
    that contain safety-relevant pairs. *)

Inductive WarrantDebtSeverity :=
| WD_None     : WarrantDebtSeverity  (** no warrant debt *)
| WD_Partial  : WarrantDebtSeverity  (** some classes safe, some unsafe *)
| WD_Total    : WarrantDebtSeverity  (** all classes contain collapse *).

(** Total warrant debt: every observation value sees both safe and unsafe states. *)
Definition total_warrant_debt {X O : Type}
    (Phi : X -> bool) (M : X -> O) : Prop :=
  forall o : O,
    (exists x, M x = o /\ Phi x = true) /\
    (exists y, M y = o /\ Phi y = false).

Lemma total_warrant_debt_implies_has_warrant_debt :
  forall {X O : Type} (x0 : X) (Phi : X -> bool) (M : X -> O),
    total_warrant_debt Phi M ->
    has_warrant_debt Phi M.
Proof.
  intros X O x0 Phi M Htotal.
  unfold has_warrant_debt, boolean_admissible.
  intros [Phi_hat Hfact].
  set (o := M x0).
  destruct (Htotal o) as [[x [HMx HPx]] [y [HMy HPy]]].
  assert (Heqt : Phi_hat o = true).
  { rewrite <- HPx. rewrite Hfact. rewrite HMx. reflexivity. }
  assert (Heqf : Phi_hat o = false).
  { rewrite <- HPy. rewrite Hfact. rewrite HMy. reflexivity. }
  congruence.
Qed.


(* ================================================================= *)
(** ** 7. Qualitative warrant-debt typology                          *)
(* ================================================================= *)

(** The critique of the paper asks that warrant debt stop being only a
    memorable name.  The following definitions give it a small analytical
    shape without pretending to compute quantitative risk.

    A debt kind records what distinction has been collapsed.  The repair and
    cost fields record the engineering pressure created by that collapse.
*)

Inductive WarrantDebtKind :=
| WD_GenericDebt
| WD_QuorumDebt      (** local view hides global quorum structure *)
| WD_TraceDebt       (** local trace hides global ordering structure *)
| WD_BoundaryDebt    (** boundary/sample observation hides physical behaviour *)
| WD_ThresholdDebt.  (** threshold witness requires non-degenerate arithmetic *)

Inductive RepairPressure :=
| RepairEither
| PreferRestriction
| PreferRefinement
| CarryExplicitly.

Inductive RepairCostBand :=
| CostLow
| CostModerate
| CostHigh
| CostUnknown.

Record WarrantDebtProfile := {
  wd_kind             : WarrantDebtKind;
  wd_repair_pressure  : RepairPressure;
  wd_restriction_cost : RepairCostBand;
  wd_refinement_cost  : RepairCostBand
}.

Definition quorum_debt_profile : WarrantDebtProfile :=
  {| wd_kind := WD_QuorumDebt;
     wd_repair_pressure := RepairEither;
     wd_restriction_cost := CostModerate;
     wd_refinement_cost := CostModerate |}.

Definition trace_debt_profile : WarrantDebtProfile :=
  {| wd_kind := WD_TraceDebt;
     wd_repair_pressure := RepairEither;
     wd_restriction_cost := CostModerate;
     wd_refinement_cost := CostLow |}.

Definition boundary_debt_profile : WarrantDebtProfile :=
  {| wd_kind := WD_BoundaryDebt;
     wd_repair_pressure := PreferRefinement;
     wd_restriction_cost := CostModerate;
     wd_refinement_cost := CostHigh |}.

Definition threshold_debt_profile : WarrantDebtProfile :=
  {| wd_kind := WD_ThresholdDebt;
     wd_repair_pressure := CarryExplicitly;
     wd_restriction_cost := CostLow;
     wd_refinement_cost := CostLow |}.

(** A profiled witness is still just a warrant-debt witness.  The profile
    does not add proof strength.  It adds repair information. *)
Record ProfiledWarrantDebtWitness {X O : Type}
    (Phi : X -> bool)
    (M : X -> O) := {
  pwd_witness : WarrantDebtWitness Phi M;
  pwd_profile : WarrantDebtProfile
}.

Theorem profiled_warrant_debt_witness_sound :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    ProfiledWarrantDebtWitness Phi M ->
    has_warrant_debt Phi M.
Proof.
  intros X O Phi M PW.
  destruct PW as [W _].
  apply warrant_debt_witness_sound.
  exact W.
Qed.

Definition carries_explicit_debt (p : WarrantDebtProfile) : bool :=
  match wd_repair_pressure p with
  | CarryExplicitly => true
  | _ => false
  end.

Definition refinement_cost_high (p : WarrantDebtProfile) : bool :=
  match wd_refinement_cost p with
  | CostHigh => true
  | _ => false
  end.

Definition restriction_cost_high (p : WarrantDebtProfile) : bool :=
  match wd_restriction_cost p with
  | CostHigh => true
  | _ => false
  end.

Lemma boundary_debt_has_high_refinement_cost :
  refinement_cost_high boundary_debt_profile = true.
Proof. reflexivity. Qed.

Lemma threshold_debt_is_carried_explicitly :
  carries_explicit_debt threshold_debt_profile = true.
Proof. reflexivity. Qed.
