# Structural Admissibility Library

A Rocq mechanisation of **structural admissibility**: the property that a
safety predicate factors through an observation map. If factorisation fails,
no downstream classifier, monitor, or post-processor can recover the lost
distinction. The development proves this, identifies the two principled
repairs, and extracts a verified monitor and certificate checker to OCaml.

## Core idea

A safety predicate Φ is **admissible** relative to an observation map M when
Φ is constant on the fibres of M — that is, states that look identical to M
must agree on Φ. If two concrete states have the same observation but
different predicate values, the observation does not support the claim. The
development calls the concrete evidence of this failure a **witnessed warrant
debt**.

The two principled repairs are:

- **Restriction** — weaken or restrict Φ to a predicate that factors through
  the existing M.
- **Refinement** — enrich M to a finer observation through which Φ does
  factor.

Both repairs are mechanised in all three case-study domains.

## Formal status

| Item | Count |
|---|---|
| Rocq source files | 41 |
| Compiled `.vo` files | 41 |
| Admitted lemmas | 0 |
| Named axioms | 8 |

All axioms are documented in [ASSUMPTIONS.md](ASSUMPTIONS.md). To verify:

```bash
find . -name '*.v'  | wc -l          # 41
find . -name '*.vo' | wc -l          # 41
grep -RniE '\bAdmitted\b' . --include='*.v'   # no output
grep -RnE  '\bAxiom\b'    . --include='*.v'   # 8 matches
```

## Building

### Prerequisites

- [Rocq](https://rocq-prover.org) 9.x (tested with 9.1.0)
- OCaml 4.14+ with [dune](https://dune.build) 3.0+

The recommended way to install Rocq is via opam. If your opam switch has
`rocq` in PATH, the build script finds it automatically.

### Build everything

From the repository root:

```bash
scripts/build_all.sh
```

Or from this directory:

```bash
scripts/build_all.sh
```

The script compiles all Rocq proofs with `make`, then builds and tests the
OCaml components with `dune`.

### Rocq only

```bash
make
```

### OCaml only

```bash
cd ocaml && dune build
cd ocaml && dune test
```

## Repository structure

```
structural-admissibility-library/
├── coq/
│   ├── Foundation/
│   │   ├── Relations.v          Kernel equivalences, fibre structure
│   │   ├── Orders.v             Refinement preorder
│   │   ├── Lattices.v           Lattice structure on observations
│   │   ├── Quotients.v          Factorisation through quotients
│   │   ├── TopologyCore.v       Topological support
│   │   ├── Mereotopology.v      RCC-style region connection (3 axioms)
│   │   └── MetricResolution.v   Finite-precision indistinguishability
│   ├── Admissibility/
│   │   ├── ObservationMaps.v    Observation maps and fibres
│   │   ├── Factorisation.v      Backbone theorem
│   │   ├── KernelPairs.v        Categorical formulation
│   │   ├── AdmissibilityBase.v  Non-recoverability
│   │   ├── Refinement.v         Refinement monotonicity
│   │   ├── Collapse.v           Collapse witnesses
│   │   ├── WarrantDebt.v        Witnessed and profiled warrant debt
│   │   ├── TimelyAdmissibility.v  Temporal extension
│   │   └── HorizonDebt.v        Horizon-bounded debt
│   ├── Runtime/
│   │   ├── MonitorStates.v      State machine and axiom ordering
│   │   ├── StructuralFatigue.v  Fatigue monotonicity
│   │   ├── MetastableClosure.v  Metastable closure ≠ safety
│   │   ├── RuptureCertificates.v  Certificate soundness
│   │   ├── Recovery.v           Reclosure ≠ recovery
│   │   └── RuntimeSoundness.v   Full pipeline soundness
│   ├── Automation/
│   │   ├── AdmissibilityTactics.v
│   │   ├── RefinementTactics.v
│   │   ├── CollapseTactics.v
│   │   └── CertificateTactics.v
│   ├── CaseStudies/
│   │   ├── Consensus/
│   │   │   ├── NetworkModel.v           Nodes, partitions, quorum
│   │   │   ├── PartitionCollapse.v      Local view collapses global quorum
│   │   │   ├── ConsensusAdmissibility.v Refinement repair
│   │   │   └── ConsensusRestriction.v   Restriction repair
│   │   ├── GPU/
│   │   │   ├── MemoryModel.v            Executions and thread-local traces
│   │   │   ├── GPUAdmissibility.v       Refinement repair
│   │   │   └── GPURestriction.v         DRF restriction repair
│   │   └── PhysicalSystems/
│   │       ├── BoundaryConditions.v     Thresholds and NonDegenerateThreshold
│   │       ├── ThermalModel.v           Thermal safety predicate
│   │       ├── SensorCollapse.v         Sensor inadmissibility witness
│   │       └── PDEAdmissibility.v       Both repairs for physical case
│   └── Extraction/
│       ├── ExtractableTypes.v           Types, engineering actions, correctness
│       ├── MonitorExtraction.v          Verified monitor update and actions
│       ├── CertificateExtraction.v      Certificate checker extraction
│       └── ExtractionCorrectness.v      Round-trip faithfulness
├── ocaml/
│   ├── lib/
│   │   ├── monitor_kernel.ml    Monitor state machine
│   │   ├── rupture_cert.ml      Certificate types and validation
│   │   ├── cert_parser.ml       JSON certificate parsing
│   │   ├── sensor_adapter.ml    Sensor data ingestion
│   │   └── fatigue_trace.ml     Fatigue trace replay
│   ├── bin/
│   │   ├── monitor_cli.ml       Command-line monitor runner
│   │   └── replay_trace.ml      Trace replay tool
│   └── test/                    Unit tests for all OCaml components
├── scripts/
│   ├── build_all.sh             Full build (Rocq + OCaml)
│   ├── check_no_admitted.sh     Audit for admitted lemmas
│   ├── count_loc.sh             Line-count summary
│   └── extract_monitor.sh       Re-run Rocq extraction
├── docs/                        Theory documentation
├── ASSUMPTIONS.md               All axioms, documented and auditable
├── _CoqProject                  Rocq build configuration
├── dune-project                 OCaml dune project
└── dune-workspace               Pins dune workspace to this directory
```

## Key theorems

### Admissibility

| Theorem | File | Statement |
|---|---|---|
| `admissible_iff_constant_on_kernel` | `Admissibility/Factorisation.v` | Φ admissible ↔ Φ constant on fibres of M |
| `safety_relevant_collapse_iff_inadmissible` | `Admissibility/Collapse.v` | Collapse ↔ inadmissibility |
| `postcompose_preserves_collapse` | `Admissibility/Collapse.v` | Post-processing cannot undo a collapse |
| `warrant_debt_witness_sound` | `Admissibility/WarrantDebt.v` | Witnessed debt implies inadmissibility |
| `profiled_warrant_debt_witness_sound` | `Admissibility/WarrantDebt.v` | Profile adds no proof strength |
| `admissibility_monotone_under_refinement` | `Admissibility/Refinement.v` | Finer observation preserves admissibility |

### Runtime monitor

| Theorem | File | Statement |
|---|---|---|
| `update_monitor_preserves_invariants` | `Extraction/MonitorExtraction.v` | Invariant maintained across every step |
| `update_monitor_hard_rupture_absorbing` | `Extraction/MonitorExtraction.v` | HARD\_RUPTURE is absorbing |
| `hard_rupture_implies_certificate` | `Runtime/RuntimeSoundness.v` | Hard rupture produces a valid certificate |
| `monitor_soundness` | `Runtime/RuntimeSoundness.v` | Monitor states track admissibility |
| `full_monitor_pipeline_sound` | `Runtime/RuntimeSoundness.v` | End-to-end pipeline soundness |

### Engineering actions (extraction layer)

| Theorem | File | Statement |
|---|---|---|
| `valid_certificate_emits_admissibility_ticket` | `Extraction/ExtractableTypes.v` | Valid certificate → admissibility-failure ticket |
| `engineering_action_after_update_tracks_monitor_status` | `Extraction/MonitorExtraction.v` | Action record mirrors monitor status |
| `hard_rupture_update_emits_ticket` | `Extraction/MonitorExtraction.v` | Hard-rupture update → admissibility-failure ticket |

### Case studies

| Theorem | File | Statement |
|---|---|---|
| `boundary_sensor_inadmissible_for_interior_safety` | `PhysicalSystems/PDEAdmissibility.v` | Boundary-only sensor cannot warrant interior safety |
| `full_field_sensor_admissible` | `PhysicalSystems/PDEAdmissibility.v` | Full-field sensor restores admissibility |
| `partition_is_structural_admissibility_failure` | `Consensus/PartitionCollapse.v` | Network partition = admissibility failure |
| `local_quorum_belief_admissible` | `Consensus/ConsensusRestriction.v` | Local quorum belief is admissible (restriction) |
| `restriction_is_genuinely_weaker` | `Consensus/ConsensusRestriction.v` | Local belief and global quorum can disagree |
| `both_repairs_are_available` | `Consensus/ConsensusRestriction.v` | Both restriction and refinement mechanised |
| `thread_local_obs_inadmissible_for_sc` | `GPU/GPUAdmissibility.v` | Thread-local traces cannot determine SC |
| `gpu_drf_sc_restriction_repair` | `GPU/GPURestriction.v` | SC admissible on DRF executions (conditional on DRF-SC bridge) |

## Warrant debt typology

The development classifies admissibility failures by kind, repair pressure,
and expected repair burden. This is not a quantitative risk metric. It
prevents the category error of treating all admissibility failures as equally
cheap to discharge.

| Debt kind | Collapsed distinction | Repair pressure | Burden |
|---|---|---|---|
| Quorum debt | Global quorum structure | Either restriction or refinement | Moderate |
| Trace debt | Global ordering / visibility | Either restriction or refinement | Low to moderate |
| Boundary debt | Boundary or inter-sample behaviour | Prefer refinement | High |
| Threshold debt | Non-degenerate threshold condition | Carry explicitly | Low, proof-critical |
| Runtime debt | Fatigue or rupture-state information | Emit action | Operational |

## Extracted OCaml interface

Rocq extraction produces two OCaml files:

- **`monitor_extracted.ml`** — `update_monitor`, `update_monitor_preserves_invariants`, `update_monitor_hard_rupture_absorbing`, and the engineering-action functions `engineering_action_from_status`, `engineering_action_after_update`.
- **`cert_extracted.ml`** — `extracted_cert_valid`, `build_extractable_cert`, `engineering_action_from_certificate`.

The extracted `ExtractableEngineeringAction` record maps monitor status and
certificate validity to a typed repair obligation:

| Monitor output | Engineering action |
|---|---|
| Closed | No action required |
| Meta Review | Review observation boundary |
| Hard Rupture | Reject, restrict, or refine |
| Certificate witness | Open admissibility obligation |

This is not a dashboard implementation. It is the verified core that a
dashboard, issue tracker, or safety-case tool would consume.

## Axioms

The eight axioms are background principles, not incomplete proofs.

| Axiom | Role |
|---|---|
| `C_refl` | Every region connects to itself (RCC base) |
| `C_sym` | Connection is symmetric (RCC base) |
| `ntpp_irreflexive` | No region is an NTPP of itself (boundary discipline) |
| `boundary_obs_respects_signature` | Same boundary signature → same observation |
| `max_temp_positive` | Thermal threshold is non-degenerate |
| `max_pressure_positive` | Pressure threshold is non-degenerate |
| `max_flux_positive` | Flux threshold is non-degenerate |
| `meta_review_trigger_lt_fatigue_threshold` | Review trigger fires before hard rupture |

The three positivity axioms are instances of one structural obligation: a
threshold-based witness of the form `k - 1` vs `k` requires `0 < k` in
Rocq's natural-number arithmetic. The development packages this as
`NonDegenerateThreshold` in `BoundaryConditions.v`.

Full justification for each axiom is in [ASSUMPTIONS.md](ASSUMPTIONS.md).

## Documentation

The `docs/` directory contains theory notes on each major component:

- `theory_overview.md` — factorisation criterion and backbone theorem
- `admissibility_identity.md` — admissibility as identity condition
- `warrant_debt.md` — warrant debt, profiles, and repair typology
- `no_recovery_lemma.md` — non-recoverability proof
- `runtime_certificates.md` — monitor state machine and rupture certificates
- `case_study_consensus.md` — consensus partition collapse
- `case_study_gpu.md` — GPU thread-local trace inadmissibility
- `case_study_physical_systems.md` — boundary sensing and PDE safety
- `critique_implementation_plan.md` — engineering action and typology extensions
