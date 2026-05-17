# Theorem: no_recovery

## Informal Statement

Once an observation map M collapses two states x and y (M x = M y), no
downstream function from observations to any type can recover the distinction.

## Formal Statement

```coq
Theorem no_recovery :
  forall {X O Y : Type} (M : X -> O) (f : O -> Y) (x y : X),
    M x = M y -> f (M x) = f (M y).
```

Stronger version:

```coq
Theorem inadmissibility_not_repaired_by_postprocessing :
  forall {X O Y : Type} (M : X -> O) (Phi : X -> bool),
    (exists x y, M x = M y /\ Phi x <> Phi y) ->
    forall (f : O -> Y),
      exists x y, M x = M y /\ Phi x <> Phi y.
```

## Why It Matters

This theorem is philosophically powerful and practically critical:
- The inadmissibility witness is independent of any post-processing function.
- No amount of signal processing, ML inference, or optimisation can recover
  a distinction that the observation map collapsed.
- This justifies the claim that structural admissibility must be fixed at
  the observation layer, not the processing layer.

## File Location

`coq/Admissibility/AdmissibilityBase.v`

## Used By

- All case studies (as motivation for observation enrichment)
- `CaseStudies/Consensus/PartitionCollapse.v` (no_local_recovery_of_global_safety)
