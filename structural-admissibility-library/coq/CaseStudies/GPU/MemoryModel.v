(** * MemoryModel.v

    GPU memory consistency model for Case Study C.

    WARNING: We do NOT claim to mechanise full GPU memory consistency.
    The precise claim is: certain relaxed-memory observations induce
    quotient collapses relative to stronger safety predicates.

    We model executions as lists of events, with thread-local observations
    that may collapse globally-distinct executions.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* ================================================================= *)
(** ** 1. Memory operations                                           *)
(* ================================================================= *)

Inductive Op :=
| Read  : Op
| Write : Op
| Fence : Op.

Record Event := {
  thread_id : nat;
  location  : nat;   (** memory address *)
  op        : Op;
  value     : nat;
  timestamp : nat
}.

(** An execution is a list of events. *)
Definition Execution := list Event.

(* ================================================================= *)
(** ** 2. Sequential consistency predicate                            *)
(* ================================================================= *)

(** An execution is sequentially consistent if there exists a total order
    that respects:
    1. program order (events within a thread respect thread_id + timestamp),
    2. reads-from: each read sees the most recent write to that location.

    For our purposes, we use a simplified check: *)

Definition events_by_location (loc : nat) (e : Execution) : list Event :=
  List.filter (fun ev => Nat.eqb (location ev) loc) e.

Definition last_write_before (loc : nat) (ts : nat) (e : Execution) : option nat :=
  List.fold_right
    (fun ev acc =>
       if Nat.eqb (location ev) loc &&
          match op ev with Write => true | _ => false end &&
          Nat.ltb (timestamp ev) ts
       then Some (value ev)
       else acc)
    None
    e.

(** A read is consistent if it sees the most recent write. *)
Definition read_consistent (ev : Event) (e : Execution) : bool :=
  match op ev with
  | Read =>
    match last_write_before (location ev) (timestamp ev) e with
    | None   => true   (** reads initial value if no prior write *)
    | Some v => Nat.eqb (value ev) v
    end
  | _ => true
  end.

Definition sequentially_consistent (e : Execution) : bool :=
  List.forallb (fun ev => read_consistent ev e) e.

(* ================================================================= *)
(** ** 3. Thread-local trace observation                              *)
(* ================================================================= *)

Definition thread_local_obs (tid : nat) (e : Execution) : list Event :=
  List.filter (fun ev => Nat.eqb (thread_id ev) tid) e.

Definition ThreadTrace := list Event.

(* ================================================================= *)
(** ** 4. Relaxed memory: store buffering                             *)
(* ================================================================= *)

(** A store buffer reorders writes: a thread may see its own writes
    before they are globally visible.  This is the classic source of
    relaxed-memory non-SC behaviour. *)

(** Store buffer event: write is buffered, not yet globally visible. *)
Definition buffered_write (tid loc val ts : nat) : Event :=
  {| thread_id := tid; location := loc; op := Write;
     value := val; timestamp := ts |}.

Definition flush_event (tid loc val ts : nat) : Event :=
  {| thread_id := 0; location := loc; op := Write;
     value := val; timestamp := ts + 1 |}.

