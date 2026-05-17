# Case Study: GPU Memory Consistency

## Setting

Multi-threaded GPU executions with relaxed memory ordering.
Each thread observes only its own events (thread-local trace).

## Precise Claim

Certain relaxed-memory observations induce quotient collapses relative to
sequential consistency as a safety predicate.

**NOT claimed**: a complete GPU memory model or full mechanisation of
all relaxed memory semantics.

## The Collapse

Two executions where thread 0 sees exactly the same local events
(Write x=1, Read y=1) but one execution is sequentially consistent
and the other is not.

## Main Theorems

```coq
(* Thread-local observation collapses globally-distinct executions *)
Theorem local_trace_not_admissible_for_sc :
  exists e1 e2 : Execution,
    thread_local_obs 0 e1 = thread_local_obs 0 e2 /\
    sequentially_consistent e1 <> sequentially_consistent e2.

(* Thread-local trace cannot determine sequential consistency *)
Theorem thread_local_obs_inadmissible_for_sc :
  ~ boolean_admissible sequentially_consistent (thread_local_obs 0).

(* Full execution (global view) is admissible *)
Theorem global_execution_admissible_for_sc :
  boolean_admissible sequentially_consistent (@identity_obs Execution).
```

## Files

- `coq/CaseStudies/GPU/MemoryModel.v`
- `coq/CaseStudies/GPU/GPUAdmissibility.v`
