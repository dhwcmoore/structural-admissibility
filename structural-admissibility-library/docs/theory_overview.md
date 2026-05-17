# Theory Overview

## The Central Chain

```
1. Observation map M : X → O
   Maps physical/computational states to observable values.

2. Kernel collapse
   ker(M) = {(x,y) | M x = M y}
   Two distinct states x ≠ y with M x = M y are indistinguishable.

3. Factorisation failure
   Φ : X → bool fails to factor through M when Φ is NOT constant on ker(M).
   Equivalently: ∃ x y, M x = M y ∧ Φ x ≠ Φ y.

4. Inadmissibility
   boolean_inadmissible Φ M ↔ ¬(∃ Φ̂, ∀ x, Φ x = Φ̂(M x))
   ↔ safety_relevant_collapse Φ M   [the central theorem]

5. Warrant debt
   has_warrant_debt Φ M ↔ boolean_inadmissible Φ M
   A witnessed WarrantDebtWitness (x, y, M x = M y, Φ x ≠ Φ y) is evidence.

6. Metastable closure
   Operational closure (monitor says CLOSED) with structural debt (inadmissible)
   and positive fatigue. The system APPEARS safe but IS NOT.

7. Structural fatigue
   Accumulated from kernel oscillations and widenings.
   fatigue_monotone: F never decreases.

8. Rupture certificate
   A machine-checkable record proving inadmissibility:
   (left, right, M left = M right, Φ left ≠ Φ right, fatigue > 0)
   rupture_certificate_sound: certificate → ¬ boolean_admissible Φ M

9. Extracted monitor
   The update_monitor function extracted from Coq to OCaml.
   Certified by ExtractionCorrectness.v.

10. Industrial case studies
    - Physical systems: sensor at boundary cannot see interior temperature.
    - Distributed consensus: local view cannot determine global quorum.
    - GPU memory: thread-local trace cannot determine sequential consistency.
```

## Key Distinctions

### Admissibility vs Admissibility-in-principle
A predicate may be admissible w.r.t. a finer observation (admissible-in-principle)
while being inadmissible w.r.t. the deployed observation (inadmissible-in-operation).

### Operational closure vs Structural safety
The monitor returning CLOSED does not imply structural safety unless the
observation map is admissible for the safety predicate. Metastable closure
formalises the gap.

### Reclosure vs Recovery
Genuine recovery requires BOTH re-entering CLOSED AND achieving structural
admissibility. Returning to CLOSED without a structural fix is metastable reclosure.
