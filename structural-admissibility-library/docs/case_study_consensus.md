# Case Study: Distributed Consensus Under Partition

## Setting

A 3-node distributed system. Each node can only observe its local view
(messages it can receive). A network partition silences some communication links.

## Precise Claim

We show that LOCAL-VIEW OBSERVATION is structurally inadmissible for GLOBAL
QUORUM SAFETY under partition.  We do NOT mechanise full Paxos or Raft.

## The Collapse

Two network states that look identical to node 0 (no visible messages,
same local node set) but have different global quorum safety values.

## Main Theorems

```coq
(* Partition produces states with same local view but different quorum safety *)
Theorem partition_induces_local_view_collapse :
  exists ns1 ns2 : NetworkState,
    local_node_obs 0 ns1 = local_node_obs 0 ns2 /\
    quorum_safe ns1 <> quorum_safe ns2.

(* Local view is inadmissible for global quorum safety *)
Theorem partition_is_structural_admissibility_failure :
  ~ boolean_admissible quorum_safe (local_node_obs 0).

(* No local post-processing can recover global safety *)
Theorem no_local_recovery_of_global_safety :
  forall f : LocalView -> bool,
    ~ boolean_admissible quorum_safe (fun ns => f (local_node_obs 0 ns)).
```

## Files

- `coq/CaseStudies/Consensus/NetworkModel.v`
- `coq/CaseStudies/Consensus/PartitionCollapse.v`
- `coq/CaseStudies/Consensus/ConsensusAdmissibility.v`
