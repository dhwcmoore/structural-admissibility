(** * CollapseTactics.v

    Tactics for automating safety-relevant collapse proofs.

    Standard pattern:
    1. exhibit two states,
    2. prove same observation,
    3. prove predicate disagreement,
    4. invoke collapse theorem.
*)

Require Import Foundation.Relations.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.Collapse.
Require Import Admissibility.WarrantDebt.

(* ================================================================= *)
(** ** 1. Collapse hint database                                      *)
(* ================================================================= *)

Hint Resolve safety_relevant_collapse_iff_inadmissible : collapse.
Hint Resolve postcompose_preserves_collapse            : collapse.
Hint Resolve postprocessing_preserves_inadmissibility  : collapse.

(* ================================================================= *)
(** ** 2. Core collapse tactic                                        *)
(* ================================================================= *)

Ltac derive_collapse l r :=
  exists l; exists r;
  split; [try (simpl; reflexivity; try congruence) | try discriminate].

Ltac prove_collapse :=
  unfold safety_relevant_collapse;
  eexists; eexists;
  split; [try (simpl; reflexivity) | try discriminate].

(** After deriving collapse, conclude inadmissibility. *)
Ltac conclude_inadmissible :=
  apply safety_relevant_collapse_iff_inadmissible.

Ltac inadmissible_by_collapse l r :=
  apply safety_relevant_collapse_iff_inadmissible;
  derive_collapse l r.

(* ================================================================= *)
(** ** 3. Collapse propagation                                        *)
(* ================================================================= *)

Ltac propagate_collapse :=
  apply postcompose_preserves_collapse; assumption.

