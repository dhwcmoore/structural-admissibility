# Critique Implementation Plan

This note records the three code-level changes made in response to the critique dialogue.

## 1. Operational engineering on-ramp

The extraction layer now contains `ExtractableEngineeringAction`, `engineering_action_from_status`, `engineering_action_from_certificate`, and `engineering_action_after_update`. These functions turn monitor status or rupture-certificate validity into a dashboard/ticket-oriented action record. The record does not pretend to automate engineering judgement. It states the repair obligation: no ticket, structural review, or admissibility-failure ticket, together with a repair recommendation and cost bands.

## 2. Physical axioms as parameterised threshold obligations

`BoundaryConditions.v` now packages the three positivity axioms into `NonDegenerateThreshold`. The temperature, pressure, and flux assumptions are therefore visible as three instances of one structural obligation: threshold witnesses of the form `k - 1` versus `k` require `0 < k` in natural-number arithmetic.

## 3. Warrant debt as a typological tool

`WarrantDebt.v` now defines `WarrantDebtKind`, `RepairPressure`, `RepairCostBand`, `WarrantDebtProfile`, and `ProfiledWarrantDebtWitness`. The typology separates quorum debt, trace debt, boundary debt, and threshold debt. The profile does not increase proof strength. It attaches repair information to an already sound warrant-debt witness.
