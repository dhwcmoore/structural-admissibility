# Case Study: Physical Sensor Boundary Collapse

## Setting

A physical system (e.g., a reactor) with temperature, pressure, and boundary flux.
A sensor deployed at the physical boundary measures flux and pressure but NOT temperature.

## The Collapse

```
s1 = {temperature = max_temp - 1, pressure = 5, flux = 3}   (* thermally safe *)
s2 = {temperature = max_temp,     pressure = 5, flux = 3}   (* thermally unsafe *)

sensor_obs s1 = sensor_obs s2 = {flux = 3, pressure = 5}
thermal_safe s1 = true ≠ false = thermal_safe s2
```

## Main Theorems

```coq
(* Basic sensor cannot determine thermal safety *)
Theorem sensor_observation_inadmissible :
  ~ boolean_admissible thermal_safe sensor_obs.

(* Enriched sensor (with temperature) restores admissibility *)
Theorem enriched_sensor_restores_admissibility :
  boolean_admissible thermal_safe enriched_sensor_obs.

(* Refinement: enriched refines basic *)
Theorem enriched_sensor_refines_basic :
  refines enriched_sensor_obs sensor_obs.
```

## Files

- `coq/CaseStudies/PhysicalSystems/BoundaryConditions.v`
- `coq/CaseStudies/PhysicalSystems/SensorCollapse.v`
- `coq/CaseStudies/PhysicalSystems/ThermalModel.v`
- `coq/CaseStudies/PhysicalSystems/PDEAdmissibility.v`
