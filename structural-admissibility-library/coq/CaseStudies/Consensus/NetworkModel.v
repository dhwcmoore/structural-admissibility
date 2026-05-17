(** * NetworkModel.v

    Network and node model for Case Study B: Distributed Consensus Under Partition.

    We model nodes, messages, and the partition relation.
    We do NOT claim to mechanise full Paxos or Raft.
    We mechanise a structural skeleton sufficient to show that
    local-view collapse under partition is an instance of the
    general admissibility failure.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* ================================================================= *)
(** ** 1. Node types                                                  *)
(* ================================================================= *)

Definition Node := nat.

Inductive NodeStatus :=
| Alive     : NodeStatus
| Failed    : NodeStatus
| Partitioned : NodeStatus.

(* ================================================================= *)
(** ** 2. Message model                                               *)
(* ================================================================= *)

Record Message := {
  msg_sender   : Node;
  msg_receiver : Node;
  msg_type     : nat;     (** 0=propose, 1=accept, 2=commit, 3=abort *)
  msg_value    : nat;
  msg_round    : nat
}.

(* ================================================================= *)
(** ** 3. Network state                                               *)
(* ================================================================= *)

Record NetworkState := {
  nodes              : list Node;
  node_status        : Node -> NodeStatus;
  messages           : list Message;
  partition_relation : Node -> Node -> bool  (** true = cannot communicate *)
}.

(** Two nodes are partitioned from each other. *)
Definition partitioned_pair (ns : NetworkState) (n1 n2 : Node) : Prop :=
  partition_relation ns n1 n2 = true.

(** The partition relation is symmetric. *)
Definition partition_symmetric (ns : NetworkState) : Prop :=
  forall n1 n2,
    partitioned_pair ns n1 n2 <-> partitioned_pair ns n2 n1.

(** A node can see a message if not partitioned from the sender. *)
Definition can_see_message (ns : NetworkState) (n : Node) (m : Message) : Prop :=
  partitioned_pair ns n (msg_sender m) = False /\
  partition_relation ns n (msg_sender m) = false.

(* ================================================================= *)
(** ** 4. Local view of a node                                        *)
(* ================================================================= *)

Record LocalView := {
  lv_node    : Node;
  lv_visible : list Message;
  lv_quorum  : bool  (** whether this node believes quorum is achievable *)
}.

(** A node's local view: only messages it can see. *)
Definition local_node_obs
    (n  : Node)
    (ns : NetworkState) : LocalView :=
  {| lv_node    := n;
     lv_visible := List.filter
                     (fun m => negb (partition_relation ns n (msg_sender m)))
                     (messages ns);
     lv_quorum  := Nat.leb
                     (List.length (List.filter
                       (fun n' => negb (partition_relation ns n n'))
                       (nodes ns)))
                     (List.length (nodes ns) / 2 + 1) |}.

(* ================================================================= *)
(** ** 5. Global quorum safety                                        *)
(* ================================================================= *)

(** A quorum requires a majority of nodes to be reachable and alive. *)
Definition quorum_size (ns : NetworkState) : nat :=
  List.length (nodes ns) / 2 + 1.

Definition alive_reachable_count (ns : NetworkState) (n : Node) : nat :=
  List.length (List.filter
    (fun n' =>
       match node_status ns n' with
       | Alive => negb (partition_relation ns n n')
       | _ => false
       end)
    (nodes ns)).

Definition quorum_safe (ns : NetworkState) : bool :=
  List.forallb
    (fun n =>
       Nat.leb (quorum_size ns) (alive_reachable_count ns n))
    (nodes ns).

(* ================================================================= *)
(** ** 6. Partition events                                            *)
(* ================================================================= *)

(** A full partition event: one group cannot see the other. *)
Record PartitionEvent := {
  pe_group_a : list Node;
  pe_group_b : list Node
}.

Definition apply_partition
    (ns : NetworkState) (pe : PartitionEvent) : NetworkState :=
  {| nodes         := nodes ns;
     node_status   := node_status ns;
     messages      := messages ns;
     partition_relation :=
       fun n1 n2 =>
         (List.existsb (Nat.eqb n1) (pe_group_a pe) &&
          List.existsb (Nat.eqb n2) (pe_group_b pe)) ||
         (List.existsb (Nat.eqb n1) (pe_group_b pe) &&
          List.existsb (Nat.eqb n2) (pe_group_a pe)) ||
         partition_relation ns n1 n2 |}.

