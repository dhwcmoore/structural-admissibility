(** * GPUAdmissibility.v

    Case Study C: GPU Memory Consistency as Observational Collapse.

    PRECISE CLAIM: Certain relaxed-memory observations induce quotient collapses
    relative to sequential consistency as a safety predicate.

    NOT claimed: a complete GPU memory model or full mechanisation of
    relaxed memory semantics.

    Main theorem (local_trace_not_admissible_for_sc):
    The thread-local trace observation is inadmissible w.r.t. sequential consistency.
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
Require Import CaseStudies.GPU.MemoryModel.

(* ================================================================= *)
(** ** 1. Concrete collapse witness: store-buffer reordering          *)
(* ================================================================= *)

(** Two executions that look identical to thread 0 locally,
    but one is SC and the other is not.

    Classic store-buffer litmus test:
    Thread 0: Write x=1, Read y
    Thread 1: Write y=1, Read x

    In the SC execution:  T0 sees y=1 or T1 sees x=1.
    In the relaxed execution: T0 sees y=0 AND T1 sees x=0 (both buffered). *)

(** SC execution: thread 0 writes x, then reads y=1 (thread 1 has written). *)
Definition exec_sc : Execution :=
  [ {| thread_id := 0; location := 0; op := Write; value := 1; timestamp := 0 |};
    {| thread_id := 1; location := 1; op := Write; value := 1; timestamp := 1 |};
    {| thread_id := 0; location := 1; op := Read;  value := 1; timestamp := 2 |};
    {| thread_id := 1; location := 0; op := Read;  value := 1; timestamp := 3 |}
  ].

(** Non-SC execution: both threads read initial values (0) due to store buffering.
    Thread 0's local trace is the same as in exec_sc (Write x, Read y with value 0). *)
Definition exec_relaxed : Execution :=
  [ {| thread_id := 0; location := 0; op := Write; value := 1; timestamp := 0 |};
    {| thread_id := 1; location := 1; op := Write; value := 1; timestamp := 0 |};
    {| thread_id := 0; location := 1; op := Read;  value := 0; timestamp := 1 |};
    {| thread_id := 1; location := 0; op := Read;  value := 0; timestamp := 1 |}
  ].

(** Thread 0's local trace is NOT identical in both executions (Read y value differs),
    so we construct a witness where the LOCAL OBSERVATION matches. *)

(** For the admissibility witness, we need same local trace but different SC status.
    We construct two executions where thread 0 sees exactly the same events
    but the global SC status differs. *)

Definition exec_t0_safe : Execution :=
  [ {| thread_id := 0; location := 0; op := Write; value := 1; timestamp := 0 |};
    {| thread_id := 0; location := 1; op := Read;  value := 1; timestamp := 2 |};
    {| thread_id := 1; location := 1; op := Write; value := 1; timestamp := 1 |}
  ].

Definition exec_t0_unsafe : Execution :=
  [ {| thread_id := 0; location := 0; op := Write; value := 1; timestamp := 0 |};
    {| thread_id := 0; location := 1; op := Read;  value := 1; timestamp := 2 |};
    {| thread_id := 1; location := 1; op := Write; value := 2; timestamp := 1 |}
  ].

Lemma thread0_obs_same :
    thread_local_obs 0 exec_t0_safe = thread_local_obs 0 exec_t0_unsafe.
Proof.
  unfold thread_local_obs, exec_t0_safe, exec_t0_unsafe. simpl. reflexivity.
Qed.

Lemma sc_status_differs :
    sequentially_consistent exec_t0_safe <> sequentially_consistent exec_t0_unsafe.
Proof.
  unfold sequentially_consistent, exec_t0_safe, exec_t0_unsafe.
  unfold read_consistent, last_write_before. simpl.
  discriminate.
Qed.

(* ================================================================= *)
(** ** 2. Main theorem: thread-local trace is not admissible for SC   *)
(* ================================================================= *)

Theorem local_trace_not_admissible_for_sc :
  exists (e1 e2 : Execution),
    thread_local_obs 0 e1 = thread_local_obs 0 e2 /\
    sequentially_consistent e1 <> sequentially_consistent e2.
Proof.
  exists exec_t0_safe. exists exec_t0_unsafe.
  split.
  - apply thread0_obs_same.
  - apply sc_status_differs.
Qed.

Theorem thread_local_obs_inadmissible_for_sc :
  ~ boolean_admissible sequentially_consistent (thread_local_obs 0).
Proof.
  apply safety_relevant_collapse_iff_inadmissible.
  destruct local_trace_not_admissible_for_sc as [e1 [e2 [Hobs Hne]]].
  exists e1. exists e2. split; assumption.
Qed.

(* ================================================================= *)
(** ** 3. Admissible observation for SC                               *)
(* ================================================================= *)

(** The full execution trace (global observation) is admissible for SC. *)
Theorem global_execution_admissible_for_sc :
  boolean_admissible sequentially_consistent (@identity_obs Execution).
Proof.
  apply admissible_identity_obs.
Qed.

(** The global observation refines any per-thread observation. *)
Theorem global_refines_thread_local :
  forall tid : nat,
    refines (@identity_obs Execution) (thread_local_obs tid).
Proof.
  intro tid. apply identity_obs_finest.
Qed.

