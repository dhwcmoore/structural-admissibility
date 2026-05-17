# Warrant Debt

## Concept

Warrant debt is the gap between what a system claims about its safety status
and what its observational structure can actually warrant.

A system has warrant debt when its safety predicate Φ is inadmissible with
respect to its deployed observation map M.

## Types of Warrant Debt

### Qualitative
```coq
Definition has_warrant_debt {X O} (Phi : X -> bool) (M : X -> O) : Prop :=
  ~ boolean_admissible Phi M.
```

### Witnessed
```coq
Record WarrantDebtWitness {X O} (Phi : X -> bool) (M : X -> O) := {
  wd_left      : X;
  wd_right     : X;
  wd_collapsed : M wd_left = M wd_right;
  wd_disagrees : Phi wd_left <> Phi wd_right
}.
```

### Temporal (Horizon Debt)
```coq
Definition horizon_debt (lag horizon : nat) : nat := lag - horizon.
```

## Key Theorems

```coq
(* Witness implies debt *)
Theorem warrant_debt_witness_sound :
  WarrantDebtWitness Phi M -> has_warrant_debt Phi M.

(* Coarsening increases debt *)
Theorem warrant_debt_monotone_under_degradation :
  refines M1 M2 -> (* M1 coarser *)
  has_warrant_debt Phi M2 ->
  has_warrant_debt Phi M1.

(* Refinement can eliminate debt *)
Theorem refinement_can_eliminate_warrant_debt :
  exists M2, refines M2 M1 /\ has_warrant_debt Phi M1 /\ ~ has_warrant_debt Phi M2.

(* Zero horizon debt iff timely *)
Theorem zero_horizon_debt_iff_timely :
  horizon_debt lag horizon = 0 <-> lag <= horizon.
```

## File Locations

- `coq/Admissibility/WarrantDebt.v`
- `coq/Admissibility/HorizonDebt.v`
- `coq/Admissibility/TimelyAdmissibility.v`
