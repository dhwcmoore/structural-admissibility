(** * RefinementTactics.v

    Tactics for automating refinement chains and monotonicity proofs.
*)

Require Import Foundation.Relations.
Require Import Foundation.Orders.
Require Import Admissibility.Factorisation.
Require Import Admissibility.Refinement.
Require Import Admissibility.AdmissibilityBase.

(* ================================================================= *)
(** ** 1. Refinement hint database                                    *)
(* ================================================================= *)

Hint Resolve refines_refl           : refinement.
Hint Resolve refines_trans          : refinement.
Hint Resolve trivial_obs_coarsest   : refinement.
Hint Resolve identity_obs_finest    : refinement.
Hint Resolve refines_product_left   : refinement.
Hint Resolve refines_product_right  : refinement.
Hint Resolve refines_product_universal : refinement.
Hint Resolve postcompose_coarsens   : refinement.

(* ================================================================= *)
(** ** 2. Core refinement tactic                                      *)
(* ================================================================= *)

Ltac solve_refinement :=
  unfold refines;
  intros;
  try assumption;
  try congruence;
  try reflexivity.

Ltac refinement_chain :=
  eauto with refinement.

(* ================================================================= *)
(** ** 3. Admissibility monotonicity                                  *)
(* ================================================================= *)

Hint Resolve admissibility_monotone_under_refinement : admissibility.
Hint Resolve inadmissibility_antimonotone            : admissibility.
Hint Resolve admissibility_preserved_by_refinement_chain : admissibility.

Ltac admissibility_by_refinement :=
  eapply admissibility_monotone_under_refinement;
  [refinement_chain | assumption].

(* ================================================================= *)
(** ** 4. Refinement composition                                      *)
(* ================================================================= *)

Ltac compose_refinement :=
  eapply refines_trans; refinement_chain.

