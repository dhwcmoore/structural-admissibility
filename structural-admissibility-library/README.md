# Structural Admissibility Verification Library

A Rocq/Coq library mechanising **structural admissibility** — the formal property that a safety predicate can be computed from the available observation map.

## Central Thesis

> A system is structurally safe only when its safety predicate is admissible with respect to the available observational structure.  If the observation map collapses distinctions needed by the predicate, no downstream optimiser, monitor, classifier, or controller can recover the lost warrant.

## The Verification Chain

```
observation map
  → kernel collapse
    → factorisation failure
      → inadmissibility
        → warrant debt
          → metastable closure
            → structural fatigue
              → rupture certificate
                → extracted monitor
                  → industrial case study
```

## Repository Structure

```
structural-admissibility-library/
├── coq/
│   ├── Foundation/          Relations, Orders, Lattices, Quotients, Topology, Mereotopology, Metric
│   ├── Admissibility/       ObservationMaps, Factorisation, KernelPairs, Refinement, Collapse, WarrantDebt
│   ├── Runtime/             MonitorStates, Fatigue, MetastableClosure, RuptureCertificates, Soundness
│   ├── Automation/          AdmissibilityTactics, RefinementTactics, CollapseTactics, CertificateTactics
│   ├── CaseStudies/
│   │   ├── PhysicalSystems/ Sensor boundary collapse
│   │   ├── Consensus/       Partition-induced local view collapse
│   │   └── GPU/             Thread-local trace inadmissibility for SC
│   └── Extraction/          Verified extraction bridge to OCaml
├── ocaml/
│   ├── lib/                 monitor_kernel, cert_parser, sensor_adapter, fatigue_trace
│   ├── bin/                 monitor_cli, replay_trace
│   └── test/                Unit tests
├── scripts/
│   ├── check_no_admitted.sh
│   ├── build_all.sh
│   ├── count_loc.sh
│   └── extract_monitor.sh
└── docs/                    Theory documentation
```

## Key Theorems

### Foundation
| Theorem | File | Statement |
|---------|------|-----------|
| `kernel_equivalence` | Foundation/Relations.v | The kernel of any map is an equivalence relation |
| `refines_refl`, `refines_trans` | Foundation/Orders.v | Refinement is a preorder |
| `factorisation_iff_kernel_bool` | Foundation/Quotients.v | Factorisation iff constant on fibres |
| `eps_indistinguishable_not_transitive` | Foundation/MetricResolution.v | Finite-precision indistinguishability is not transitive |

### Admissibility
| Theorem | File | Statement |
|---------|------|-----------|
| `admissible_iff_constant_on_kernel` | Admissibility/Factorisation.v | **The backbone theorem** |
| `factorisation_iff_kernel_pair_descent` | Admissibility/KernelPairs.v | Categorical formulation |
| `no_recovery` | Admissibility/AdmissibilityBase.v | Post-processing cannot recover collapsed information |
| `inadmissibility_not_repaired_by_postprocessing` | Admissibility/AdmissibilityBase.v | Stronger no-recovery |
| `admissibility_monotone_under_refinement` | Admissibility/Refinement.v | Finer observation preserves admissibility |
| `admissibility_not_antitone` | Admissibility/Refinement.v | Counterexample: reverse does not hold |
| `safety_relevant_collapse_iff_inadmissible` | Admissibility/Collapse.v | Collapse ↔ inadmissibility |
| `warrant_debt_witness_sound` | Admissibility/WarrantDebt.v | Witnessed debt implies inadmissibility |

### Runtime
| Theorem | File | Statement |
|---------|------|-----------|
| `hard_rupture_absorbing` | Runtime/MonitorStates.v | HARD_RUPTURE is absorbing |
| `fatigue_monotone` | Runtime/StructuralFatigue.v | Fatigue never decreases |
| `operational_closure_not_structural_safety` | Runtime/MetastableClosure.v | CLOSED ≠ safe |
| `metastable_closure_has_warrant_debt` | Runtime/MetastableClosure.v | Metastable → warrant debt |
| `reclosure_not_recovery` | Runtime/Recovery.v | Metastable reclosure ≠ genuine recovery |
| `rupture_certificate_sound` | Runtime/RuptureCertificates.v | **Key publishable theorem** |

### Case Studies
| Theorem | File | Statement |
|---------|------|-----------|
| `sensor_observation_inadmissible` | CaseStudies/PhysicalSystems/SensorCollapse.v | Boundary-only sensor cannot warrant thermal safety |
| `enriched_sensor_restores_admissibility` | CaseStudies/PhysicalSystems/SensorCollapse.v | Adding temperature restores admissibility |
| `partition_is_structural_admissibility_failure` | CaseStudies/Consensus/PartitionCollapse.v | Network partition = admissibility failure |
| `thread_local_obs_inadmissible_for_sc` | CaseStudies/GPU/GPUAdmissibility.v | Thread-local traces cannot determine SC |

## Building

### Coq proofs

```bash
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```

### OCaml components

```bash
cd ocaml && dune build
cd ocaml && dune test
```

### All at once

```bash
scripts/build_all.sh
```

## Formal Status

The Rocq development contains 39 source files, all of which compile to `.vo`
files. It contains no admitted lemmas. The remaining logical assumptions are
confined to eight named axioms, each documented in [ASSUMPTIONS.md](ASSUMPTIONS.md).

The consensus case study demonstrates observational enrichment. An earlier
formulation attempted to prove quorum safety admissible relative to an
observation that did not determine quorum safety. That proof required a
uniformity principle falsified by the partition model. The final development
therefore refines `ConsensusObs` with `co_quorum_safe`, computed by
`consensus_obs`. The admissibility proof is immediate because the
safety-relevant component is now observable.

This is the intended discipline of the framework: if a predicate does not factor
through the current observation map, one must either reject it as inadmissible or
refine the observation. One must not rescue the proof with an assumption that
bypasses the observation boundary.

To verify:

```bash
scripts/check_no_admitted.sh
```
