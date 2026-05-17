(** * ConsensusAdmissibility.v

    Admissibility results for the distributed consensus case study.
    Combines the local view collapse results with the general theory.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import Foundation.Relations.
Require Import Foundation.Orders.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.Collapse.
Require Import Admissibility.WarrantDebt.
Require Import Runtime.RuptureCertificates.
Require Import CaseStudies.Consensus.NetworkModel.
Require Import CaseStudies.Consensus.PartitionCollapse.

(* ================================================================= *)
(** ** 1. Warrant debt in consensus                                   *)
(* ================================================================= *)

Theorem consensus_has_warrant_debt :
  has_warrant_debt quorum_safe (local_node_obs 0).
Proof.
  unfold has_warrant_debt.
  apply partition_is_structural_admissibility_failure.
Qed.

(* ================================================================= *)
(** ** 2. Remediation: global-view observation restores admissibility *)
(* ================================================================= *)

(** The global state itself (identity observation) is admissible for any predicate. *)
Theorem global_obs_admissible :
  boolean_admissible quorum_safe (@identity_obs NetworkState).
Proof.
  apply admissible_identity_obs.
Qed.

(** The global observation refines any local-view observation. *)
Theorem global_obs_refines_local :
  forall n : Node,
    refines (@identity_obs NetworkState) (local_node_obs n).
Proof.
  intro n. apply identity_obs_finest.
Qed.

(* ================================================================= *)
(** ** 3. Network state enrichment: consensus registry                *)
(* ================================================================= *)

(** A consensus registry is an observation that includes both the local view
    and the global reachability count. *)
Record ConsensusObs := {
  co_local_view       : LocalView;
  co_reachable_count  : nat;
  co_quorum_safe      : bool
}.

Definition consensus_obs (n : Node) (ns : NetworkState) : ConsensusObs :=
  {| co_local_view      := local_node_obs n ns;
     co_reachable_count := alive_reachable_count ns n;
     co_quorum_safe     := quorum_safe ns |}.

(** The consensus observation makes quorum_safe admissible: the observation
    captures quorum_safe by construction, so equality of observations implies
    equality of the predicate. *)
Theorem consensus_obs_admissible :
  forall n : Node,
    boolean_admissible quorum_safe (consensus_obs n).
Proof.
  intro n.
  apply constant_on_kernel_implies_admissible.
  intros ns1 ns2 Hobs.
  exact (f_equal co_quorum_safe Hobs).
Qed.

