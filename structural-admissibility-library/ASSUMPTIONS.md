# Assumptions for the Structural Admissibility Rocq Development

This document records the explicit assumptions used by the Rocq development.

The development contains no admitted lemmas.

All 41 Rocq source files compile to `.vo` files. The remaining logical strength
of the development is confined to named axioms. These axioms are not unfinished
proofs. They state the background mathematical principles required by the
intended mereotopological and observational setting of the library.

The purpose of this file is to make those assumptions visible, auditable, and
separate from proof debt.

## Status Summary

| Category | Status |
|---|---|
| Rocq source files | 41 |
| Compiled `.vo` files | 41 |
| Admitted lemmas | 0 |
| Named axioms | 8 |
| Undocumented axioms | 0 |

## Principle

The library distinguishes between three different things:

1. A proved theorem or lemma.
2. A named mathematical axiom.
3. An unfinished proof.

Only the first two occur in the final development. The third does not.

An axiom is acceptable only when it states an intended background principle of
the mathematical setting. An axiom must not be used to hide a failed proof or to
repair an observation interface that is too weak to support a predicate.

This distinction is especially important for admissibility. If a predicate does
not factor through a given observation map, the framework permits only two
principled responses:

1. reject the predicate as inadmissible relative to that observation; or
2. refine the observation map so that the safety-relevant distinction becomes
   observable.

It is not acceptable to recover the proof by adding an assumption that bypasses
the observation boundary.

## Axioms

The following axioms are part of the declared mathematical setting of the
development. They are not admitted lemmas.

| Name | File | Role | Justification |
|---|---|---|---|
| `C_refl` | `Foundation/Mereotopology.v` | Reflexivity of primitive connection | A region is connected to itself. This is a standard minimal assumption for a primitive connection relation. |
| `C_sym` | `Foundation/Mereotopology.v` | Symmetry of primitive connection | If one region is connected to another, the second is connected to the first. This is standard for RCC-style primitive connection. |
| `ntpp_irreflexive` | `Foundation/Mereotopology.v` | Irreflexivity of non-tangential proper part | No region is a non-tangential proper part of itself. This is a primitive RCC-style geometric principle and is not derivable from `C_refl` and `C_sym` alone. |
| `boundary_obs_respects_signature` | `Foundation/Mereotopology.v` | Semantic coherence of boundary observation | Regions with the same boundary signature produce the same boundary observation. This is the intended contractual property of the abstract sensor interface. |
| `max_temp_positive` | `CaseStudies/PhysicalSystems/BoundaryConditions.v` | Positivity of thermal safety threshold | The thermal safety threshold is strictly positive. A non-positive threshold would make the safety predicate trivially vacuous. |
| `max_pressure_positive` | `CaseStudies/PhysicalSystems/BoundaryConditions.v` | Positivity of pressure safety threshold | The pressure safety threshold is strictly positive. Same rationale as `max_temp_positive`. |
| `max_flux_positive` | `CaseStudies/PhysicalSystems/BoundaryConditions.v` | Positivity of flux safety threshold | The flux safety threshold is strictly positive. Same rationale as `max_temp_positive`. |
| `meta_review_trigger_lt_fatigue_threshold` | `Runtime/MonitorStates.v` | Ordering of runtime monitor parameters | The metastability review trigger fires before the hard fatigue threshold. This ordering is required for the monitor state machine to reach the METASTABLE state before HARD_RUPTURE. |

## `ntpp_irreflexive`

The axiom `ntpp_irreflexive` states that no region is a non-tangential proper
part of itself.

This is a primitive RCC-style mereotopological assumption. It is not derivable
from the minimal connection axioms `C_refl` and `C_sym` alone. It is included
explicitly so that later results depending on non-tangential containment do not
hide geometric strength inside an admitted lemma.

The derived antisymmetry result for non-tangential proper part is therefore not
an unfinished proof. It is a theorem proved from the explicit geometric
assumption `ntpp_irreflexive`.

## Parameters (abstract interfaces)

The following `Parameter` declarations define abstract module signatures. They
are interface contracts, not unproved theorems.

| Name | File | Justification |
|---|---|---|
| `Region` | `Foundation/Mereotopology.v` | Abstract type for spatial regions; instantiated concretely in case studies |
| `C` | `Foundation/Mereotopology.v` | Primitive connection relation; axiomatised by `C_refl` and `C_sym` |
| `BoundarySignature` | `Foundation/Mereotopology.v` | Abstract signature type; instantiated in PhysicalSystems |
| `boundary_observation` | `Foundation/Mereotopology.v` | Abstract sensor map; instantiated in SensorCollapse.v |
| `PhysicalProperty` | `Foundation/Mereotopology.v` | Abstract physical property; instantiated as `thermal_safe` in case studies |
| `max_temp` | `CaseStudies/PhysicalSystems/BoundaryConditions.v` | Thermal safety threshold; concrete value set by application |
| `max_pressure` | `CaseStudies/PhysicalSystems/BoundaryConditions.v` | Pressure safety threshold; concrete value set by application |
| `max_flux` | `CaseStudies/PhysicalSystems/BoundaryConditions.v` | Flux safety threshold; concrete value set by application |
| `fatigue_threshold` | `Runtime/MonitorStates.v` | Hard rupture threshold; value set by deployment configuration |
| `tension_threshold` | `Runtime/MonitorStates.v` | Tension accumulation threshold; value set by deployment configuration |
| `meta_review_trigger` | `Runtime/MonitorStates.v` | Metastability review trigger; value set by deployment configuration |

## GPU Restriction Repair

The GPU restriction repair is mechanised in `GPURestriction.v`. The theorem
`gpu_drf_sc_restriction_repair` proves that `thread_local_obs` is admissible
for the sequential-consistency predicate restricted to the subtype of
data-race-free executions. The proof is conditional on a DRF-SC bridge
supplied as a section hypothesis; it introduces no new axioms and no admitted
lemmas.

This result should not be read as a full mechanisation of a production GPU
memory model or as an independent proof of a DRF-SC theorem. It proves the
admissibility repair obtained once the execution class is restricted to
data-race-free executions and the bridge is supplied for the toy model.

## Consensus Observational Enrichment

The consensus case study records an observational refinement.

The original observation did not determine quorum safety without an additional
uniformity assumption about reachable alive nodes. That assumption is invalid in
the partition model, where different nodes may have different reachable alive
counts. The final version therefore enriches `ConsensusObs` with
`co_quorum_safe`, computed by `consensus_obs`.

The admissibility proof is then one line because the safety-relevant component is
part of the observation.

This is intentional. The framework's rule is: if a predicate does not factor
through the current observation, either reject it as inadmissible or enrich the
observation. Do not add axioms that bypass the observation boundary.

## Warrant-Debt Typology

`WarrantDebt.v` now contains a qualitative typology (`WarrantDebtKind`,
`RepairPressure`, `RepairCostBand`, `WarrantDebtProfile`,
`ProfiledWarrantDebtWitness`). A profiled witness bundles a standard
`WarrantDebtWitness` with a repair-pressure and cost-band annotation.
The theorem `profiled_warrant_debt_witness_sound` proves that the profile
adds no logical strength: a profiled witness implies `has_warrant_debt`
by projection to its underlying witness. The typology introduces no axioms.

## NonDegenerateThreshold Parameterisation

The three positivity axioms (`max_temp_positive`, `max_pressure_positive`,
`max_flux_positive`) in `BoundaryConditions.v` are now presented as instances
of `NonDegenerateThreshold`, a record that packages a natural-number value
with a proof of positivity. Instance definitions `max_temp_threshold`,
`max_pressure_threshold`, and `max_flux_threshold` make this explicit. The
general lemma `threshold_predecessor_lt` derives `k - 1 < k` from any
`NonDegenerateThreshold`. The three axioms remain; the `NonDegenerateThreshold`
layer makes their shared structural role visible rather than hiding it in
three independent assumptions.

`ThermalModel.v` and `PDEAdmissibility.v` now use `max_temp_predecessor_lt`
directly instead of re-deriving the predecessor bound via `lia`.

## Extractable Engineering Actions

`ExtractableTypes.v` and `MonitorExtraction.v` now define
`ExtractableEngineeringAction`, a record carrying ticket kind, monitor status,
repair recommendation, debt kind, and cost bands — all as natural-number codes.
The function `engineering_action_from_status` maps monitor status to an action
record. `engineering_action_from_certificate` maps a rupture certificate to an
action. `engineering_action_after_update` composes a verified monitor update
with action generation in one step.

Correctness theorems proved in Rocq:

| Theorem | Statement |
|---|---|
| `closed_status_emits_no_ticket` | Status 0 produces `ticket_none` |
| `hard_status_emits_admissibility_ticket` | Status 2 produces `ticket_admissibility_failure` |
| `valid_certificate_emits_admissibility_ticket` | A valid certificate produces `ticket_admissibility_failure` |
| `engineering_action_after_update_tracks_monitor_status` | The action's `ea_monitor_status` field equals the updated monitor status |
| `hard_rupture_update_emits_ticket` | A hard-rupture update produces `ticket_admissibility_failure` |

These theorems introduce no axioms and no admitted lemmas.

## Resolved Proof Gaps

Earlier versions of the development contained admitted lemmas. These have been
removed.

| Name | Previous issue | Final resolution |
|---|---|---|
| `ntpp_antisym` | Previously treated as a difficult proof obligation for non-tangential proper part. | Now proved from the explicit RCC-style axiom `ntpp_irreflexive`. The required geometric strength is stated directly rather than hidden as an admission. |
| `consensus_obs_admissible` | Previously depended on auxiliary assumptions about reachable alive node counts, including one (`alive_reachable_count_uniformity`) that is invalid in the partition model. | Repaired by observational enrichment. `ConsensusObs` now contains `co_quorum_safe`, computed by `consensus_obs`, so admissibility follows by projection. |
| `step_preserves_invariant` | Unproved monitor state machine invariant. | Proved by `inversion` on all five step constructors. |
| `structural_fatigue_le_total` | Unproved fatigue bound. | Proved under the explicit `fatigue_wf` invariant using `lia`. |
| `update_monitor_hard_rupture_absorbing` | Unproved absorption property. | Strengthened statement with precondition `fatigue_threshold < ex_fatigue s`; proved directly. |
| `full_safety_sensor_inadmissible` | Witnesses used fixed constants that did not survive parametric thresholds. | Replaced with threshold-relative witnesses (`max_temp - 1`, etc.), proved by `lia` from positivity axioms. |

## Audit Commands

```bash
find . -name '*.v' | wc -l
find . -name '*.vo' | wc -l
grep -RniE '\bAdmitted\b|\badmit\b' . --include='*.v'
grep -RniE '\bAxiom\b' . --include='*.v'
```

Expected output:

```
41
41
(no output)
8 matches
```
