(** * ConsensusRestriction.v

    Predicate restriction for the distributed consensus case study.

    The global quorum safety predicate [quorum_safe] is inadmissible
    relative to the local node observation (PartitionCollapse.v).
    One repair is observational refinement: enrich the observation
    to carry the global quorum status (ConsensusAdmissibility.v).

    This file mechanises the other repair: predicate restriction.
    Instead of asserting global quorum safety, we restrict to the
    predicate that is meaningful at the local observational grain —
    the node's local quorum belief, a direct projection of its
    local view.

    The restricted predicate is admissible by construction.
    The price is a weaker guarantee: local belief, not global truth.
    The final theorem [both_repairs_are_available] states the
    formal duality of both repair forms in a single proposition.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.
Require Import CaseStudies.Consensus.NetworkModel.
Require Import CaseStudies.Consensus.PartitionCollapse.
Require Import CaseStudies.Consensus.ConsensusAdmissibility.

(* ================================================================= *)
(** ** 1. The restricted predicate                                    *)
(* ================================================================= *)

(** [local_quorum_belief n ns] is the quorum belief that node [n]
    can compute from its own local view: the [lv_quorum] field of
    [local_node_obs n ns].  It is a strictly local computation —
    no global coordination is required. *)

Definition local_quorum_belief (n : Node) (ns : NetworkState) : bool :=
  lv_quorum (local_node_obs n ns).

(* ================================================================= *)
(** ** 2. Admissibility of the restricted predicate                  *)
(* ================================================================= *)

(** [local_quorum_belief n] is admissible relative to [local_node_obs n]
    because it is a projection of the observation record.  Equality of
    observations implies equality of the projected field by congruence.
    No axiom is needed. *)

Theorem local_quorum_belief_admissible :
  forall n : Node,
    boolean_admissible (local_quorum_belief n) (local_node_obs n).
Proof.
  intro n.
  apply constant_on_kernel_implies_admissible.
  intros ns1 ns2 Hobs.
  unfold local_quorum_belief.
  exact (f_equal lv_quorum Hobs).
Qed.

(* ================================================================= *)
(** ** 3. The restriction is genuinely weaker                        *)
(* ================================================================= *)

(** In [ns_intact] (all nodes alive, no partition), the local quorum
    belief for node 0 differs from the global quorum safety verdict.
    This confirms that restriction is a genuine weakening of the
    guarantee: local belief and global truth are not the same claim. *)

Lemma local_quorum_belief_intact : local_quorum_belief 0 ns_intact = false.
Proof.
  unfold local_quorum_belief, local_node_obs, ns_intact. simpl. reflexivity.
Qed.

Lemma restriction_disagrees_with_global :
  local_quorum_belief 0 ns_intact <> quorum_safe ns_intact.
Proof.
  rewrite local_quorum_belief_intact, quorum_safe_intact.
  discriminate.
Qed.

Theorem restriction_is_genuinely_weaker :
  exists (n : Node) (ns : NetworkState),
    local_quorum_belief n ns <> quorum_safe ns.
Proof.
  exists 0. exists ns_intact.
  exact restriction_disagrees_with_global.
Qed.

(* ================================================================= *)
(** ** 4. Formal duality of the two repair forms                     *)
(* ================================================================= *)

(** Both repairs are mechanised and can be stated together.
    Restriction keeps [local_node_obs n] fixed and weakens the claim
    to [local_quorum_belief n].  Refinement keeps [quorum_safe] fixed
    and enriches the observation to [consensus_obs n].
    Both restore admissibility.  They pay different costs. *)

Theorem both_repairs_are_available :
  (* Repair 1: restriction — admissible claim at the local grain *)
  (forall n, boolean_admissible (local_quorum_belief n) (local_node_obs n)) /\
  (* Repair 2: refinement — admissible global claim via enriched observation *)
  (forall n, boolean_admissible quorum_safe (consensus_obs n)).
Proof.
  split.
  - exact local_quorum_belief_admissible.
  - exact consensus_obs_admissible.
Qed.
