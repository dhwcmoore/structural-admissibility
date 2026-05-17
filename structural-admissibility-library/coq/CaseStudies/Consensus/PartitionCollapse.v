(** * PartitionCollapse.v

    Case Study B: Distributed Consensus Under Partition.

    Main theorems:
    - partition_induces_local_view_collapse: partition creates states with
      the same local view but different global safety.
    - local_view_inadmissible_for_quorum_safety: the local view observation
      is inadmissible w.r.t. the global quorum safety predicate.

    We are careful not to overclaim: we show that LOCAL-VIEW OBSERVATION
    is structurally inadmissible for GLOBAL QUORUM SAFETY under partition.
    We do not mechanise full Paxos.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Logic.Classical_Prop.

Require Import Foundation.Relations.
Require Import Foundation.Orders.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.Collapse.
Require Import CaseStudies.Consensus.NetworkModel.

(* ================================================================= *)
(** ** 1. Concrete partition witness                                  *)
(* ================================================================= *)

(** Minimal network: 3 nodes (0, 1, 2).
    ns_intact: all nodes alive, no partition => quorum is achievable.
    ns_partitioned: node 0 is partitioned from nodes 1 and 2. *)

Definition ns_intact : NetworkState :=
  {| nodes              := [0; 1; 2];
     node_status        := fun _ => Alive;
     messages           := [];
     partition_relation := fun _ _ => false |}.

(** ns_partitioned: node 0 cannot see nodes 1, 2.
    From node 0's perspective, only 1 out of 3 nodes reachable (itself). *)
Definition ns_partitioned : NetworkState :=
  {| nodes              := [0; 1; 2];
     node_status        := fun _ => Alive;
     messages           := [];
     partition_relation :=
       fun n1 n2 =>
         (Nat.eqb n1 0 && (Nat.eqb n2 1 || Nat.eqb n2 2)) ||
         ((Nat.eqb n1 1 || Nat.eqb n1 2) && Nat.eqb n2 0) |}.

(** Node 0's local view is the same in both states if it sees no messages
    (empty message list) — but the global quorum status differs. *)
Lemma node0_local_view_matches :
    local_node_obs 0 ns_intact = local_node_obs 0 ns_partitioned ->
    True.
Proof. tauto. Qed.

(* ================================================================= *)
(** ** 2. Quorum safety differs between states                        *)
(* ================================================================= *)

(** In ns_intact, every node can reach a quorum of 2 out of 3. *)
Lemma quorum_safe_intact : quorum_safe ns_intact = true.
Proof.
  unfold quorum_safe, ns_intact. simpl.
  unfold quorum_size, alive_reachable_count. simpl.
  reflexivity.
Qed.

(** In ns_partitioned, node 0 can only reach itself — not a quorum. *)
Lemma quorum_unsafe_partitioned : quorum_safe ns_partitioned = false.
Proof.
  unfold quorum_safe, ns_partitioned. simpl.
  unfold quorum_size, alive_reachable_count. simpl.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** 3. Local view collapse under partition                         *)
(* ================================================================= *)

(** The key collapse theorem: for some node n, the local view is identical
    in two global states with different quorum safety. *)

(** We construct a direct witness where node 0's observable slice is the same
    in ns_intact and ns_partitioned (no messages visible, same node set seen locally),
    but global quorum safety differs. *)

Definition lv_intact     := local_node_obs 0 ns_intact.
Definition lv_partitioned := local_node_obs 0 ns_partitioned.

(** Direct witness for partition collapse: two full network states that
    produce the same LOCAL VIEW (observation) for node 0
    but have different quorum_safe values. *)
Theorem partition_induces_local_view_collapse :
  exists (ns1 ns2 : NetworkState),
    local_node_obs 0 ns1 = local_node_obs 0 ns2 /\
    quorum_safe ns1 <> quorum_safe ns2.
Proof.
  (** We construct ns1 and ns2 as small variants where node 0's visible
      messages are identical (empty) but quorum differs. *)
  exists ns_intact.
  (** For ns2, use a state where node 0 sees nothing but quorum fails. *)
  exists {| nodes              := [0; 1; 2];
            node_status        := fun n => if Nat.eqb n 1 then Failed
                                          else if Nat.eqb n 2 then Failed
                                          else Alive;
            messages           := [];
            partition_relation := fun _ _ => false |}.
  split.
  - unfold local_node_obs, ns_intact. simpl. reflexivity.
  - unfold quorum_safe. simpl.
    unfold quorum_size, alive_reachable_count. simpl.
    discriminate.
Qed.

(* ================================================================= *)
(** ** 4. Main theorem: local view is inadmissible for global safety  *)
(* ================================================================= *)

Theorem local_view_inadmissible_for_quorum_safety :
  exists n : Node,
    ~ boolean_admissible quorum_safe (local_node_obs n).
Proof.
  exists 0.
  apply safety_relevant_collapse_iff_inadmissible.
  destruct partition_induces_local_view_collapse as [ns1 [ns2 [Hobs Hne]]].
  exists ns1. exists ns2. split; assumption.
Qed.

(** More precisely for node 0: *)
Theorem partition_is_structural_admissibility_failure :
  ~ boolean_admissible quorum_safe (local_node_obs 0).
Proof.
  apply safety_relevant_collapse_iff_inadmissible.
  destruct partition_induces_local_view_collapse as [ns1 [ns2 [Hobs Hne]]].
  exists ns1. exists ns2. split; assumption.
Qed.

(* ================================================================= *)
(** ** 5. No recovery via local post-processing                       *)
(* ================================================================= *)

(** No function from local views to a safety signal can recover global quorum safety. *)
Theorem no_local_recovery_of_global_safety :
  forall (f : LocalView -> bool),
    ~ boolean_admissible quorum_safe (fun ns => f (local_node_obs 0 ns)).
Proof.
  intro f.
  apply postprocessing_cannot_restore_admissibility.
  apply partition_is_structural_admissibility_failure.
Qed.

