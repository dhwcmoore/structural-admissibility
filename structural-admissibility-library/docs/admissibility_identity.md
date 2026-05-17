# Theorem: admissible_iff_constant_on_kernel

## Informal Statement

A boolean predicate Φ is admissible with respect to observation map M exactly
when Φ is constant on all states identified by M (i.e., constant on M-fibres).

## Formal Statement

```coq
Theorem admissible_iff_constant_on_kernel :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    boolean_admissible Phi M
    <->
    forall x y, M x = M y -> Phi x = Phi y.
```

## Why It Matters

This theorem is the formal backbone of the entire project.  It says:
- Admissibility is NOT a property of Φ alone — it is relative to M.
- The observation map M determines which distinctions are available.
- If M collapses x and y, then Φ cannot (and must not) distinguish them.

## File Location

`coq/Admissibility/Factorisation.v`

## Dependencies

- `Foundation/Relations.v` (kernel definition)
- `Foundation/Quotients.v` (factorisation_iff_kernel_bool)

## Used By

- `Admissibility/Collapse.v` (safety_relevant_collapse_iff_inadmissible)
- `Admissibility/WarrantDebt.v` (warrant debt witness completeness)
- `Admissibility/Refinement.v` (monotonicity under refinement)
- `Runtime/RuptureCertificates.v` (soundness)
- `CaseStudies/PhysicalSystems/SensorCollapse.v`
- `CaseStudies/Consensus/PartitionCollapse.v`
- `CaseStudies/GPU/GPUAdmissibility.v`
