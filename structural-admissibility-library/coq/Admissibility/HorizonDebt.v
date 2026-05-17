(** * HorizonDebt.v

    Temporal warrant debt: the gap between the admissibility lag and the
    rupture horizon.

    HorizonDebt = lag - horizon (clamped to 0 when lag <= horizon)

    Central theorem (zero_horizon_debt_iff_timely):
        horizon_debt lag horizon = 0 <-> lag <= horizon.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.Classical_Prop.

Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.TimelyAdmissibility.
Require Import Admissibility.Collapse.

(* ================================================================= *)
(** ** 1. Horizon debt (natural number version)                       *)
(* ================================================================= *)

Definition horizon_debt (lag horizon : nat) : nat :=
  lag - horizon.

(** Zero horizon debt iff observation arrives in time. *)
Theorem zero_horizon_debt_iff_timely :
  forall lag horizon,
    horizon_debt lag horizon = 0 <-> timely_admissible lag horizon.
Proof.
  intros lag horizon.
  unfold horizon_debt, timely_admissible.
  split.
  - intro H. lia.
  - intro H. lia.
Qed.

(* ================================================================= *)
(** ** 2. Horizon debt is monotone in lag                             *)
(* ================================================================= *)

Lemma horizon_debt_monotone_lag :
  forall lag1 lag2 horizon,
    lag1 <= lag2 ->
    horizon_debt lag1 horizon <= horizon_debt lag2 horizon.
Proof.
  intros. unfold horizon_debt. lia.
Qed.

(** Horizon debt decreases as horizon increases. *)
Lemma horizon_debt_antitone_horizon :
  forall lag horizon1 horizon2,
    horizon1 <= horizon2 ->
    horizon_debt lag horizon2 <= horizon_debt lag horizon1.
Proof.
  intros. unfold horizon_debt. lia.
Qed.

(* ================================================================= *)
(** ** 3. Horizon debt accumulation                                   *)
(* ================================================================= *)

(** Total horizon debt over a trace: sum of per-step debts. *)
Definition total_horizon_debt (trace : list (nat * nat)) : nat :=
  List.fold_left (fun acc p => acc + horizon_debt (fst p) (snd p)) trace 0.

(** Horizon debt is always non-negative (trivially, since it's nat). *)
Lemma horizon_debt_nonneg : forall lag horizon,
    0 <= horizon_debt lag horizon.
Proof. intros. apply Nat.le_0_l. Qed.

(* ================================================================= *)
(** ** 4. Critical horizon debt                                       *)
(* ================================================================= *)

(** A system is in critical horizon debt when the debt exceeds a threshold. *)
Definition critical_horizon_debt (lag horizon threshold : nat) : Prop :=
  threshold < horizon_debt lag horizon.

Lemma critical_horizon_debt_implies_untimely :
  forall lag horizon threshold,
    critical_horizon_debt lag horizon threshold ->
    untimely lag horizon.
Proof.
  intros lag horizon threshold Hcrit.
  unfold critical_horizon_debt, horizon_debt, untimely in *.
  lia.
Qed.

(* ================================================================= *)
(** ** 5. Rational and real extensions                                *)
(* ================================================================= *)

(** NOTE: The natural-number version suffices for discrete time.
    For continuous time, replace nat with Q or R.
    The key theorem structure is preserved:

    Theorem zero_horizon_debt_R_iff_timely :
      forall (lag horizon : R),
        0 <= horizon_debt_R lag horizon = 0 <-> lag <= horizon.

    where horizon_debt_R lag horizon = Rmax 0 (lag - horizon).
*)

(** Rational version (stated as comment; instantiate with Coq.QArith if needed):

    Definition horizon_debt_Q (lag horizon : Q) : Q :=
      Qmax 0 (lag - horizon).

    Theorem zero_horizon_debt_Q_iff_timely : ...
*)

(* ================================================================= *)
(** ** 6. Compound horizon debt: structural + temporal                *)
(* ================================================================= *)

(** A system has compound debt when it has both structural warrant debt
    (inadmissibility) and temporal horizon debt (lag > horizon). *)
Definition compound_debt {X O : Type}
    (Phi : X -> bool)
    (M : X -> O)
    (lag horizon : nat) : Prop :=
  ~ boolean_admissible Phi M /\
  horizon_debt lag horizon > 0.

Lemma compound_debt_iff_both :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O) lag horizon,
    compound_debt Phi M lag horizon
    <->
    (~ boolean_admissible Phi M /\ lag > horizon).
Proof.
  intros. unfold compound_debt, horizon_debt.
  split; intro H; destruct H; split; try assumption; lia.
Qed.

(** Maximum compound debt: both fully inadmissible and maximum temporal delay. *)
Definition maximum_compound_debt {X O : Type}
    (Phi : X -> bool) (M : X -> O)
    (lag horizon : nat) : Prop :=
  safety_relevant_collapse Phi M /\
  lag > horizon.

