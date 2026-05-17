Structural Admissibility Verification Library
Working title
Structural Admissibility: A Verified Library for Observational Quotients, Warrant Debt, and Runtime Rupture Certificates
Possible repository name:
structural-admissibility-library
or, if you want continuity with the current paper:
structural-admissibility-in-rocq
The second is safer if the current repo already has history, but the first better signals that this is no longer merely a paper artefact.

0. Central Thesis of the Library
The library should mechanise the following claim:
A system is structurally safe only when its safety predicate is admissible with respect to the available observational structure. If the observation map collapses distinctions needed by the predicate, no downstream optimiser, monitor, classifier, or controller can recover the lost warrant.
That gives the whole project a coherent spine.
Everything else should serve this thesis:
    1. observation maps,
    2. quotient collapse,
    3. admissibility by factorisation,
    4. refinement of observation,
    5. warrant debt,
    6. runtime fatigue,
    7. rupture certificates,
    8. extracted monitor logic,
    9. industrial case studies.
The key is that the project should not look like fifteen unrelated Coq files. It should look like one verified theory unfolding through increasingly concrete layers.

1. Repository-Level Architecture
A serious formal methods submission should have a structure closer to this:
structural-admissibility-library/
│
├── README.md
├── _CoqProject
├── dune-project
├── coq/
│   ├── Foundation/
│   │   ├── Relations.v
│   │   ├── Orders.v
│   │   ├── Lattices.v
│   │   ├── Quotients.v
│   │   ├── TopologyCore.v
│   │   ├── Mereotopology.v
│   │   └── MetricResolution.v
│   │
│   ├── Admissibility/
│   │   ├── ObservationMaps.v
│   │   ├── Factorisation.v
│   │   ├── KernelPairs.v
│   │   ├── AdmissibilityBase.v
│   │   ├── Refinement.v
│   │   ├── Collapse.v
│   │   ├── WarrantDebt.v
│   │   ├── TimelyAdmissibility.v
│   │   └── HorizonDebt.v
│   │
│   ├── Runtime/
│   │   ├── MonitorStates.v
│   │   ├── StructuralFatigue.v
│   │   ├── MetastableClosure.v
│   │   ├── RuptureCertificates.v
│   │   ├── Recovery.v
│   │   └── RuntimeSoundness.v
│   │
│   ├── Automation/
│   │   ├── AdmissibilityTactics.v
│   │   ├── RefinementTactics.v
│   │   ├── CollapseTactics.v
│   │   └── CertificateTactics.v
│   │
│   ├── CaseStudies/
│   │   ├── GPU/
│   │   │   ├── MemoryModel.v
│   │   │   ├── RelaxedConsistency.v
│   │   │   └── GPUAdmissibility.v
│   │   │
│   │   ├── Consensus/
│   │   │   ├── NetworkModel.v
│   │   │   ├── PaxosSkeleton.v
│   │   │   ├── PartitionCollapse.v
│   │   │   └── ConsensusAdmissibility.v
│   │   │
│   │   └── PhysicalSystems/
│   │       ├── BoundaryConditions.v
│   │       ├── ThermalModel.v
│   │       ├── SensorCollapse.v
│   │       └── PDEAdmissibility.v
│   │
│   └── Extraction/
│       ├── ExtractableTypes.v
│       ├── MonitorExtraction.v
│       ├── CertificateExtraction.v
│       └── ExtractionCorrectness.v
│
├── ocaml/
│   ├── lib/
│   │   ├── monitor_kernel.ml
│   │   ├── cert_parser.ml
│   │   ├── rupture_cert.ml
│   │   ├── fatigue_trace.ml
│   │   └── sensor_adapter.ml
│   │
│   ├── bin/
│   │   ├── monitor_cli.ml
│   │   └── replay_trace.ml
│   │
│   └── test/
│       ├── test_cert_parser.ml
│       ├── test_monitor_kernel.ml
│       └── test_extracted_equivalence.ml
│
├── examples/
│   ├── gpu_memory/
│   ├── distributed_consensus/
│   └── physical_boundary/
│
├── paper/
│   ├── structural_admissibility_library.tex
│   ├── refs.bib
│   └── figs/
│
└── scripts/
    ├── check_no_admitted.sh
    ├── count_loc.sh
    ├── build_all.sh
    └── extract_monitor.sh
This structure matters because it tells a reviewer immediately:
this is a library, not a toy proof.

2. Foundational Layer
The foundational layer should not try to reprove all of mathematics. It should mechanise only the structures needed for admissibility.
The danger here is overreach. A full lattice theory, full topology, full metric space library, and full mereotopology can become a bottomless pit. The goal should be a minimal verified foundation sufficient for the later admissibility theorems.
2.1 Relations.v
Purpose:
Define the relational substrate.
Core objects:
Class ReflexiveRel (A : Type) := {
  R : A -> A -> Prop;
  R_refl : forall x, R x x
}.

Class EquivalenceRel (A : Type) := {
  equiv : A -> A -> Prop;
  equiv_refl : forall x, equiv x x;
  equiv_sym : forall x y, equiv x y -> equiv y x;
  equiv_trans : forall x y z, equiv x y -> equiv y z -> equiv x z
}.
Key definitions:
Definition kernel {X O : Type} (M : X -> O) : X -> X -> Prop :=
  fun x y => M x = M y.
Main lemmas:
Lemma kernel_equivalence :
  forall {X O : Type} (M : X -> O),
    Equivalence (kernel M).
Why this matters:
The kernel of the observation map is the basic formal object behind observational collapse. If two states are identified by M, then no predicate downstream of M can distinguish them.
Expected size:
300-500 lines

2.2 Orders.v
Purpose:
Define preorders, partial orders, and refinement orders.
Core idea:
Observation map M2 refines M1 if whenever M2 identifies two states, M1 also identifies them.
Formally:
Definition refines {X O1 O2 : Type}
  (M2 : X -> O2) (M1 : X -> O1) : Prop :=
  forall x y, M2 x = M2 y -> M1 x = M1 y.
Interpretation:
M2 is at least as informative as M1.
Key lemmas:
Lemma refines_refl :
  forall {X O : Type} (M : X -> O),
    refines M M.

Lemma refines_trans :
  forall {X O1 O2 O3 : Type}
    (M3 : X -> O3) (M2 : X -> O2) (M1 : X -> O1),
    refines M3 M2 ->
    refines M2 M1 ->
    refines M3 M1.
Important correction:
The original outline says:
refinement preserves safety predicates without exception.
That is too strong as stated.
The precise claim should be:
if a predicate is admissible with respect to a coarser observation map, then it remains admissible with respect to any finer observation map.
That direction is valid.
The reverse is false.
A finer observation can support predicates that a coarser observation cannot.
Expected size:
400-700 lines

2.3 Lattices.v
Purpose:
Formalise observation structures as ordered objects.
You do not need a full complete lattice theory unless the later proof genuinely uses arbitrary joins and meets.
A better first version:
Class JoinSemiLattice (A : Type) := {
  leq : A -> A -> Prop;
  join : A -> A -> A;
  leq_refl : forall x, leq x x;
  leq_trans : forall x y z, leq x y -> leq y z -> leq x z;
  join_upper_l : forall x y, leq x (join x y);
  join_upper_r : forall x y, leq y (join x y);
  join_least : forall x y z, leq x z -> leq y z -> leq (join x y) z
}.
What it should support:
    1. combining observations,
    2. comparing observation maps,
    3. defining minimal sufficient observation,
    4. proving monotonicity of admissibility under refinement.
Possible later extension:
Class CompleteLattice (A : Type) := {
  leq : A -> A -> Prop;
  sup : (A -> Prop) -> A;
  inf : (A -> Prop) -> A;
  ...
}.
But do not start with complete lattices unless needed. Reviewers will punish pointless abstraction.
Expected size:
700-1,200 lines

2.4 Quotients.v
Purpose:
Mechanise observational quotients without relying on unsafe quotient assumptions.
In Coq/Rocq, quotients are awkward. You can avoid heavy quotient machinery by working with kernel equivalence relations directly.
Core definitions:
Definition collapsed_by {X O : Type}
  (M : X -> O) (x y : X) : Prop :=
  M x = M y.
Instead of defining X / kernel M as a true quotient type, define functions that respect the kernel:
Definition respects_kernel {X O Y : Type}
  (M : X -> O) (f : X -> Y) : Prop :=
  forall x y, M x = M y -> f x = f y.
This is enough for admissibility.
Main theorem:
Theorem factorisation_iff_kernel_respect :
  forall {X O Y : Type} (M : X -> O) (Phi : X -> Y),
    (exists Phi_hat : O -> Y, forall x, Phi x = Phi_hat (M x)) <->
    respects_kernel M Phi.
This is the central theorem of the whole project.
Expected size:
700-1,000 lines

2.5 Mereotopology.v
Purpose:
Mechanise boundary and region logic.
This is where your regional structure logic belongs.
Primitive relation:
Parameter Region : Type.
Parameter C : Region -> Region -> Prop.
Read C x y as connection.
Derived relations:
Definition disconnected x y := ~ C x y.

Definition part_of x y :=
  forall z, C z x -> C z y.

Definition overlaps x y :=
  exists z, part_of z x /\ part_of z y.

Definition external_connection x y :=
  C x y /\ ~ overlaps x y.
You can then recover RCC-like relations:
Inductive RCC8Rel :=
| DC
| EC
| PO
| EQ
| TPP
| NTPP
| TPPI
| NTPPI.
Main purpose:
Use boundary relations as a source of observation maps.
For example:
Definition boundary_observation
  (r : Region) : BoundarySignature := ...
Then prove:
Theorem boundary_collapse_induces_admissibility_failure :
  ...
This becomes highly relevant for the PDE and sensor case studies.
Expected size:
1,200-1,800 lines

2.6 MetricResolution.v
Purpose:
Formalise epsilon-resolution and observational collapse.
Core idea:
At resolution ε, two states may become observationally indistinguishable.
Definitions:
Class PseudoMetric (X : Type) := {
  dist : X -> X -> R;
  dist_nonneg : forall x y, 0 <= dist x y;
  dist_sym : forall x y, dist x y = dist y x;
  dist_triangle : forall x y z, dist x z <= dist x y + dist y z
}.
Resolution equivalence:
Definition eps_indistinguishable
  {X : Type} `{PseudoMetric X}
  (eps : R) (x y : X) : Prop :=
  dist x y <= eps.
Important nuance:
eps_indistinguishable is not generally transitive. That means it is not automatically an equivalence relation.
This is a good place for a real theorem:
Theorem eps_indistinguishable_not_transitive :
  exists X `{PseudoMetric X} eps x y z,
    eps_indistinguishable eps x y /\
    eps_indistinguishable eps y z /\
    ~ eps_indistinguishable eps x z.
Then define closure:
Definition eps_chain_connected eps x y :=
  exists path : list X, ...
That gives a genuine quotient-like collapse relation.
Expected size:
800-1,300 lines

3. Core Admissibility Theory
This is the heart of the project.
The existing 500-line proof file should become a modular theory.
3.1 ObservationMaps.v
Purpose:
Define observation maps, observation signatures, and observational kernels.
Core structure:
Record ObservationMap (X O : Type) := {
  observe : X -> O
}.
Potentially richer version:
Record ObservationStructure := {
  State : Type;
  Obs : Type;
  obs : State -> Obs
}.
Useful definitions:
Definition obs_equiv (S : ObservationStructure)
  (x y : State S) : Prop :=
  obs S x = obs S y.
Main lemmas:
    1. observation equivalence is reflexive,
    2. observation equivalence is symmetric,
    3. observation equivalence is transitive,
    4. every observation map induces a kernel pair,
    5. observation equality is the maximal information downstream functions may use.
Expected size:
600-900 lines

3.2 Factorisation.v
Purpose:
Mechanise the central admissibility criterion.
Definition:
Definition factors_through
  {X O Y : Type}
  (Phi : X -> Y)
  (M : X -> O) : Prop :=
  exists Phi_hat : O -> Y,
    forall x, Phi x = Phi_hat (M x).
Predicate version:
Definition predicate_admissible
  {X O : Type}
  (Phi : X -> Prop)
  (M : X -> O) : Prop :=
  exists Phi_hat : O -> Prop,
    forall x, Phi x <-> Phi_hat (M x).
The distinction matters.
For computational extraction, Prop may be inconvenient. You may need a Boolean version:
Definition boolean_admissible
  {X O : Type}
  (Phi : X -> bool)
  (M : X -> O) : Prop :=
  exists Phi_hat : O -> bool,
    forall x, Phi x = Phi_hat (M x).
Main theorem:
Theorem admissible_iff_constant_on_kernel :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    boolean_admissible Phi M <->
    forall x y, M x = M y -> Phi x = Phi y.
This theorem is the formal backbone of the project.
Expected size:
900-1,300 lines

3.3 KernelPairs.v
Purpose:
Give the categorical formulation without overburdening the whole development.
Define the kernel pair:
Record KernelPair {X O : Type} (M : X -> O) := {
  left : X;
  right : X;
  kernel_eq : M left = M right
}.
Projections:
Definition kp_left ...
Definition kp_right ...
Predicate descent condition:
Definition descends_along_kernel_pair
  {X O : Type}
  (M : X -> O)
  (Phi : X -> bool) : Prop :=
  forall kp : KernelPair M,
    Phi (left kp) = Phi (right kp).
Main theorem:
Theorem factorisation_iff_kernel_pair_descent :
  boolean_admissible Phi M <->
  descends_along_kernel_pair M Phi.
This gives you the bridge to category theory, but in a way that is directly checkable.
Expected size:
700-1,000 lines

3.4 AdmissibilityBase.v
Purpose:
Collect the central definitions and results under the library’s public interface.
Exports:
Require Export ObservationMaps.
Require Export Factorisation.
Require Export KernelPairs.
Main public definitions:
Definition Admissible := boolean_admissible.
Definition Inadmissible Phi M := ~ Admissible Phi M.
Core theorem names:
Theorem admissibility_identity :
  ...
Theorem no_recovery :
  forall {X O Y Z : Type}
    (M : X -> O)
    (Phi : X -> Y)
    (post : O -> Z),
    ...
The no-recovery lemma should be stated carefully:
if two states are collapsed by M, then every post-processing function from observations assigns them the same downstream value.
Formal version:
Theorem no_recovery :
  forall {X O Y : Type}
    (M : X -> O)
    (f : O -> Y)
    (x y : X),
    M x = M y ->
    f (M x) = f (M y).
Then the stronger version:
Theorem inadmissibility_not_repaired_by_postprocessing :
  forall {X O Y : Type}
    (M : X -> O)
    (Phi : X -> bool),
    (exists x y, M x = M y /\ Phi x <> Phi y) ->
    forall (f : O -> Y),
      exists x y, M x = M y /\ Phi x <> Phi y.
This theorem is simple but philosophically powerful.
Expected size:
800-1,200 lines

3.5 Refinement.v
Purpose:
Mechanise refinement of observations.
Definition:
Definition refines
  {X O1 O2 : Type}
  (M2 : X -> O2)
  (M1 : X -> O1) : Prop :=
  forall x y, M2 x = M2 y -> M1 x = M1 y.
Main theorem:
Theorem admissibility_monotone_under_refinement :
  forall {X O1 O2 : Type}
    (Phi : X -> bool)
    (M1 : X -> O1)
    (M2 : X -> O2),
    refines M2 M1 ->
    boolean_admissible Phi M1 ->
    boolean_admissible Phi M2.
This is one of the most important results in the library.
Also prove the counterexample:
Theorem admissibility_not_antitone :
  exists X O1 O2 Phi M1 M2,
    refines M2 M1 /\
    boolean_admissible Phi M2 /\
    ~ boolean_admissible Phi M1.
That counterexample is worth including. It prevents reviewers from thinking the theory is trivial.
Expected size:
900-1,300 lines

3.6 Collapse.v
Purpose:
Formalise observational collapse.
Definition:
Definition collapses_pair
  {X O : Type}
  (M : X -> O)
  (x y : X) : Prop :=
  x <> y /\ M x = M y.
Safety-relevant collapse:
Definition safety_relevant_collapse
  {X O : Type}
  (Phi : X -> bool)
  (M : X -> O) : Prop :=
  exists x y,
    M x = M y /\
    Phi x <> Phi y.
Main theorem:
Theorem safety_relevant_collapse_iff_inadmissible :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    safety_relevant_collapse Phi M <->
    ~ boolean_admissible Phi M.
This theorem should be a centrepiece.
Expected size:
800-1,200 lines

3.7 WarrantDebt.v
Purpose:
Formalise the gap between what the system claims and what its observational structure warrants.
You need both qualitative and quantitative versions.
Qualitative warrant debt:
Definition has_warrant_debt
  {X O : Type}
  (Phi : X -> bool)
  (M : X -> O) : Prop :=
  ~ boolean_admissible Phi M.
Witnessed warrant debt:
Record WarrantDebtWitness
  {X O : Type}
  (Phi : X -> bool)
  (M : X -> O) := {
  wd_left : X;
  wd_right : X;
  wd_collapsed : M wd_left = M wd_right;
  wd_disagrees : Phi wd_left <> Phi wd_right
}.
Main theorem:
Theorem warrant_debt_witness_complete :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    WarrantDebtWitness Phi M ->
    ~ boolean_admissible Phi M.
If X is finite, you can prove the converse constructively:
Theorem finite_inadmissibility_has_witness :
  ...
This finite witness theorem matters for computation and extraction.
Expected size:
900-1,400 lines

3.8 TimelyAdmissibility.v
Purpose:
Connect admissibility to intervention timing.
Definitions:
Record Intervention := {
  latency : nat;
  gain : nat;
  cost : nat
}.
Timely admissibility:
Definition timely_admissible
  (lag horizon : nat) : Prop :=
  lag <= horizon.
No-forced-lag principle:
Definition no_forced_lag
  (required_lag horizon : nat) : Prop :=
  required_lag <= horizon.
The important theorem:
Theorem untimely_refinement_cannot_restore_safety :
  ...
Meaning:
Even if a refinement would make a predicate admissible in principle, it is not operationally sufficient if it arrives after the rupture horizon.
Expected size:
600-1,000 lines

3.9 HorizonDebt.v
Purpose:
Formalise the temporal version of warrant debt.
Core idea:
HorizonDebt = admissibility_lag - time_to_threshold
Use naturals first:
Definition horizon_debt (lag horizon : nat) : nat :=
  lag - horizon.
Main lemmas:
Theorem zero_horizon_debt_iff_timely :
  forall lag horizon,
    horizon_debt lag horizon = 0 <-> lag <= horizon.
This can later be extended to rationals or reals.
Expected size:
500-800 lines

4. Runtime Layer
This layer connects the static admissibility theory to your runtime monitor paper.
The key claim:
metastable closure is operational closure in the presence of unresolved structural fatigue or warrant debt.
4.1 MonitorStates.v
Define states:
Inductive MonitorStatus :=
| CLOSED
| META_REVIEW
| HARD_RUPTURE.
Define transitions:
Record MonitorSnapshot := {
  fatigue : nat;
  tension : nat;
  horizon : nat;
  lag : nat;
  status : MonitorStatus
}.
Transition relation:
Inductive step : MonitorSnapshot -> MonitorSnapshot -> Prop :=
| StepClosedStable : ...
| StepClosedToMetaReview : ...
| StepMetaReviewToClosed : ...
| StepMetaReviewToRupture : ...
| StepHardRuptureAbsorbing : ...
Main theorem:
Theorem hard_rupture_absorbing :
  forall s s',
    status s = HARD_RUPTURE ->
    step s s' ->
    status s' = HARD_RUPTURE.
Expected size:
700-1,000 lines

4.2 StructuralFatigue.v
Purpose:
Formalise fatigue accumulation.
Definition:
Record FatigueState := {
  F : nat;
  oscillations : nat;
  widenings : nat
}.
Update function:
Definition update_fatigue
  (f : FatigueState)
  (strain : nat)
  (osc : bool)
  (widened : bool) : FatigueState := ...
Main lemmas:
Theorem fatigue_monotone :
  forall f strain osc widened,
    F f <= F (update_fatigue f strain osc widened).
Theorem fatigue_zero_preserved_under_zero_strain :
  ...
Expected size:
700-1,100 lines

4.3 MetastableClosure.v
Purpose:
Formalise the distinction between operational closure and structural safety.
Definitions:
Definition operationally_closed (s : MonitorSnapshot) : Prop :=
  status s = CLOSED.

Definition structurally_safe
  {X O : Type}
  (Phi : X -> bool)
  (M : X -> O) : Prop :=
  boolean_admissible Phi M.

Definition metastable_closure
  {X O : Type}
  (Phi : X -> bool)
  (M : X -> O)
  (s : MonitorSnapshot) : Prop :=
  operationally_closed s /\
  ~ structurally_safe Phi M /\
  fatigue s > 0.
Main theorem:
Theorem operational_closure_not_structural_safety :
  exists X O Phi M s,
    operationally_closed s /\
    ~ structurally_safe Phi M.
Stronger theorem:
Theorem metastable_closure_has_warrant_debt :
  forall X O Phi M s,
    metastable_closure Phi M s ->
    has_warrant_debt Phi M.
Expected size:
800-1,200 lines

4.4 RuptureCertificates.v
Purpose:
Define machine-checkable rupture evidence.
Certificate type:
Record RuptureCertificate
  {X O : Type}
  (Phi : X -> bool)
  (M : X -> O) := {
  cert_left : X;
  cert_right : X;
  cert_same_observation : M cert_left = M cert_right;
  cert_predicate_disagreement : Phi cert_left <> Phi cert_right;
  cert_fatigue : nat;
  cert_fatigue_positive : cert_fatigue > 0
}.
Soundness theorem:
Theorem rupture_certificate_sound :
  forall X O Phi M,
    RuptureCertificate Phi M ->
    ~ boolean_admissible Phi M.
This is one of the key publishable theorems.
Expected size:
800-1,200 lines

4.5 Recovery.v
Purpose:
Formalise the difference between genuine recovery and metastable reclosure.
Definitions:
Definition genuine_recovery ... := ...
Definition metastable_reclosure ... := ...
Main theorem:
Theorem reclosure_not_recovery :
  ...
This theorem is important because it distinguishes your work from ordinary runtime threshold monitoring.
Expected size:
600-1,000 lines

4.6 RuntimeSoundness.v
Purpose:
Prove the runtime monitor’s main soundness theorem.
Target theorem:
Theorem monitor_soundness :
  forall trace cert,
    monitor_emits cert trace ->
    rupture_certificate_valid cert.
or:
Theorem hard_rupture_implies_certificate :
  forall trace s,
    reaches_hard_rupture trace s ->
    exists cert, valid_rupture_certificate cert.
This is the theorem that makes the OCaml monitor and the Coq/Rocq theory feel like one system.
Expected size:
1,000-1,500 lines

5. Automation Layer
Do not call the file admit_tactics.v.
That name is a problem.
It looks like it is related to Admitted, which is exactly what you want to avoid.
Use:
AdmissibilityTactics.v
or:
StructuralTactics.v
5.1 AdmissibilityTactics.v
Purpose:
Automate common proof patterns.
Example tactic:
Ltac solve_kernel :=
  unfold kernel, respects_kernel in *;
  intros;
  subst;
  reflexivity.
Example:
Ltac solve_admissible :=
  unfold boolean_admissible;
  eexists;
  intros;
  reflexivity.
But be careful: serious automation should not just hide weak proof scripts. It should solve recurring algebraic proof obligations.
Useful tactics:
solve_kernel
solve_factorisation
solve_refinement
discharge_collapse
extract_warrant_witness
Expected size:
500-900 lines

5.2 RefinementTactics.v
Purpose:
Automate monotonicity and refinement chains.
Example:
Ltac solve_refinement :=
  unfold refines;
  intros;
  try assumption;
  try congruence.
More valuable:
A tactic that composes refinement facts:
Hint Resolve refines_refl refines_trans : refinement.
Then:
Ltac refinement_chain :=
  eauto with refinement.
Expected size:
300-600 lines

5.3 CollapseTactics.v
Purpose:
Automate safety-relevant collapse proofs.
Example proof pattern:
    1. exhibit two states,
    2. prove same observation,
    3. prove predicate disagreement,
    4. invoke collapse theorem.
Expected size:
400-700 lines

5.4 CertificateTactics.v
Purpose:
Build rupture certificates from witnesses.
This is useful for case studies.
Expected size:
300-600 lines

6. Case Study Layer
This is where the project becomes credible to formal methods reviewers.
But you should be strategic.
The three case studies in the original outline are ambitious. I would not attempt all three at full depth immediately.
A better plan:
    1. one small but complete case study,
    2. one medium industrial case study,
    3. one larger aspirational case study.
For JAR, depth matters more than superficial breadth.

6.1 Case Study A: Sensor Boundary Collapse
This is the best first case study because it connects directly to your existing work.
Directory:
coq/CaseStudies/PhysicalSystems/
Files:
BoundaryConditions.v
SensorCollapse.v
ThermalSafety.v
PDEAdmissibility.v
Core model:
Record PhysicalState := {
  temperature : nat;
  pressure : nat;
  boundary_flux : nat
}.
Observation map:
Definition sensor_obs (s : PhysicalState) : SensorReading := ...
Safety predicate:
Definition thermal_safe (s : PhysicalState) : bool :=
  temperature s <? max_temp.
Collapse example:
Two physical states have the same sensor reading but different safety status.
Example sensor_collapse_witness :
  exists s1 s2,
    sensor_obs s1 = sensor_obs s2 /\
    thermal_safe s1 <> thermal_safe s2.
Then:
Theorem sensor_observation_inadmissible :
  ~ boolean_admissible thermal_safe sensor_obs.
Then refinement:
Definition enriched_sensor_obs ... := ...
Prove:
Theorem enriched_sensor_restores_admissibility :
  boolean_admissible thermal_safe enriched_sensor_obs.
This case study is clean and directly aligned with your theory.
Expected size:
1,000-1,800 lines

6.2 Case Study B: Distributed Consensus Under Partition
This is attractive, but more dangerous. Paxos and Raft are large topics.
Do not mechanise full Paxos.
Instead mechanise a structural skeleton:
Inductive NodeStatus :=
| Alive
| Failed
| Partitioned.

Record NetworkState := {
  nodes : list Node;
  messages : list Message;
  partition_relation : Node -> Node -> bool
}.
Observation map:
Definition local_node_obs
  (n : Node)
  (s : NetworkState) : LocalView := ...
Safety predicate:
Definition quorum_safe (s : NetworkState) : bool := ...
Main result:
Theorem local_view_inadmissible_under_partition :
  exists s1 s2,
    local_node_obs n s1 = local_node_obs n s2 /\
    quorum_safe s1 <> quorum_safe s2.
Then:
Theorem partition_is_structural_admissibility_failure :
  ~ boolean_admissible quorum_safe (local_node_obs n).
This is much better than claiming to verify Paxos itself.
Expected size:
1,200-2,000 lines

6.3 Case Study C: GPU Memory Consistency
This is powerful but risky.
You need to avoid overclaiming.
Do not say:
relaxed consistency is a form of observational collapse.
Say:
certain relaxed-memory observations induce quotient collapses relative to stronger safety predicates.
That is precise.
Basic model:
Inductive Op :=
| Read
| Write
| Fence.

Record Event := {
  thread_id : nat;
  location : nat;
  op : Op;
  value : nat;
  time : nat
}.
Executions:
Definition Execution := list Event.
Observation map:
Definition thread_local_obs
  (tid : nat)
  (e : Execution) : ThreadTrace := ...
Predicate:
Definition sequentially_consistent (e : Execution) : bool := ...
Main theorem:
Theorem local_trace_not_admissible_for_sc :
  exists e1 e2,
    thread_local_obs tid e1 = thread_local_obs tid e2 /\
    sequentially_consistent e1 <> sequentially_consistent e2.
This is enough. You do not need a full GPU memory model at first.
Expected size:
1,200-2,200 lines

7. Extraction and OCaml Bridge
This is where the project becomes more than a Coq exercise.
7.1 ExtractableTypes.v
Purpose:
Define Coq/Rocq types that can be extracted safely.
Avoid using Prop in extractable computational paths.
Use bool, nat, finite lists, and decidable equality.
Example:
Record ExtractableSnapshot := {
  ex_fatigue : nat;
  ex_tension : nat;
  ex_status : nat
}.
Expected size:
300-600 lines

7.2 MonitorExtraction.v
Purpose:
Define the verified monitor update function.
Example:
Definition update_monitor
  (s : ExtractableSnapshot)
  (input : MonitorInput) : ExtractableSnapshot := ...
Prove:
Theorem update_monitor_preserves_invariants :
  forall s input,
    monitor_invariant s ->
    monitor_invariant (update_monitor s input).
Expected size:
700-1,100 lines

7.3 CertificateExtraction.v
Purpose:
Define extractable rupture certificates.
Record ExtractableCert := {
  left_id : nat;
  right_id : nat;
  observation_hash : nat;
  predicate_left : bool;
  predicate_right : bool;
  cert_fatigue : nat
}.
Soundness theorem:
Theorem extracted_certificate_sound :
  forall cert,
    extracted_cert_valid cert = true ->
    rupture_certificate_semantically_valid cert.
Expected size:
700-1,200 lines

7.4 ExtractionCorrectness.v
Purpose:
Prove that the OCaml-extracted functions preserve the Coq/Rocq semantics.
This is where the submission gains force.
Expected theorem:
Theorem extracted_monitor_correct :
  forall input s,
    extracted_update s input = update_monitor s input.
Depending on extraction setup, the exact theorem may be stated before extraction, then tested against the extracted OCaml.
Expected size:
500-900 lines

8. OCaml Runtime Components
The OCaml layer should not contain the trusted theory. It should be the operational shell around the extracted trusted kernel.
8.1 monitor_kernel.ml
Role:
Runs extracted monitor logic.
Responsibilities:
    1. accept typed monitor snapshots,
    2. update fatigue,
    3. update status,
    4. emit rupture certificate when required,
    5. serialise result.
This file should be mostly extracted or thinly wrapped around extracted code.
Expected size:
800-1,200 lines

8.2 cert_parser.ml
Role:
Parse JSON certificates and convert them into typed OCaml values.
Important:
The parser itself is usually not fully verified unless you extract it from Coq/Rocq. If it is handwritten, then it is part of the trusted computing base unless checked afterward.
Better architecture:
    1. handwritten parser parses JSON into untrusted raw data,
    2. extracted verifier checks semantic validity,
    3. only verified certificates are accepted.
Expected size:
500-900 lines

8.3 sensor_adapter.ml
Role:
Convert external sensor traces into formal monitor inputs.
Important:
This should carry explicit uncertainty.
Example:
type raw_sensor_reading = {
  sensor_id : string;
  value : float;
  timestamp : int;
  confidence : float;
}
Then map into formal types:
type monitor_input = {
  tension : int;
  horizon : int;
  lag : int;
}
Expected size:
400-800 lines

8.4 replay_trace.ml
Role:
Replay historical traces and check whether certificates are emitted.
This is useful for examples and the paper.
Expected size:
300-600 lines

9. Proof Automation Strategy
The automation layer should be justified as follows:
The library introduces repeated proof obligations concerning kernel preservation, factorisation, refinement monotonicity, collapse witnesses, and certificate construction. These obligations are structurally uniform, so we provide domain-specific tactics that discharge routine cases while leaving case-specific semantic obligations explicit.
That is a strong formal-methods justification.
The tactics should never make the project look less transparent.
Good tactic names:
solve_kernel_equiv
solve_factorisation
solve_refinement_chain
derive_collapse
build_warrant_witness
build_rupture_certificate
Bad tactic names:
admit_tactics
magic
crush_everything
auto_all
The automation should reduce proof pain, not hide proof content.

10. No-Admitted Discipline
This must be enforced mechanically.
Add a script:
#!/usr/bin/env bash
set -e

if grep -R "Admitted\|admit" coq/; then
  echo "Forbidden admitted proof found."
  exit 1
fi

echo "No admitted proofs found."
File:
scripts/check_no_admitted.sh
Also check for:
Axiom
Parameter
Conjecture
But be careful. Some parameters are legitimate in abstract developments. You should distinguish between:
    1. declared abstract interfaces,
    2. unproved assumptions pretending to be theorems.
Better script:
grep -R "Admitted\|admit\|Conjecture" coq/
And separately:
grep -R "Axiom\|Parameter" coq/
Then maintain:
ASSUMPTIONS.md
Every axiom or parameter must be listed there with justification.
For a JAR-style submission, the ideal is:
Admitted: 0
Conjecture: 0
Axiom: 0 or explicitly isolated interface assumptions
Parameter: allowed only for abstract module signatures

11. Documentation Layer
A heavyweight library needs documentation.
Add:
docs/
├── theory_overview.md
├── admissibility_identity.md
├── no_recovery_lemma.md
├── warrant_debt.md
├── runtime_certificates.md
├── case_study_gpu.md
├── case_study_consensus.md
└── case_study_physical_systems.md
Each major theorem should have:
    1. informal statement,
    2. formal statement,
    3. why it matters,
    4. file location,
    5. dependencies,
    6. case-study use.
Example:
Theorem: admissibility_iff_constant_on_kernel

Informal:
A predicate is admissible with respect to an observation map exactly when it is constant on all states identified by that observation map.

Formal location:
coq/Admissibility/Factorisation.v

Used by:
Collapse.v
WarrantDebt.v
RuptureCertificates.v
SensorCollapse.v
GPUAdmissibility.v
This makes the project much easier to review.

12. Suggested Theorem Inventory
A serious library should advertise its theorem inventory.
Here is a plausible core list.
Foundation
kernel_equivalence
refinement_preorder
kernel_inclusion_refinement_equiv
join_observation_upper_bound
metric_resolution_chain_equivalence
boundary_connection_reflexive
part_of_preorder
overlap_symmetric
Admissibility
admissible_iff_constant_on_kernel
factorisation_iff_kernel_pair_descent
admissibility_monotone_under_refinement
inadmissibility_witness_complete
safety_relevant_collapse_iff_inadmissible
no_recovery
postprocessing_preserves_collapse
minimal_sufficient_observation_exists_finite
Warrant Debt
warrant_debt_implies_inadmissibility
warrant_debt_witness_sound
finite_inadmissibility_has_warrant_witness
warrant_debt_monotone_under_degradation
refinement_reduces_warrant_debt
Runtime
fatigue_monotone
hard_rupture_absorbing
operational_closure_not_structural_safety
metastable_closure_has_warrant_debt
reclosure_not_recovery
rupture_certificate_sound
hard_rupture_implies_certificate
monitor_soundness
Case Studies
sensor_observation_inadmissible
sensor_refinement_restores_admissibility
partition_induces_local_view_collapse
local_view_inadmissible_for_quorum_safety
thread_local_trace_inadmissible_for_sc
boundary_sensor_collapse_violates_thermal_safety

13. Revised LOC Estimate
A more realistic version:
Layer
Files
Expected LOC
Foundation
7
4,000-5,500
Core admissibility
9
5,000-6,500
Runtime theory
6
4,000-6,000
Automation
4
1,500-2,800
Case studies
8-12
5,000-8,000
Extraction and OCaml
6-8
3,000-5,000
Tests and examples
8-15
2,000-4,000
Total
48-61
24,500-37,800
That sounds large, but that is the point.
The JAR feedback cited 5,000-20,000 lines. A genuinely mature version of this project can exceed that without looking padded, because the runtime, extraction, and case-study material naturally add mass.

14. Development Roadmap
Phase 1: Stabilise the Existing Core
Goal:
Turn the current 500-line proved file into a clean admissibility core.
Deliverables:
ObservationMaps.v
Factorisation.v
KernelPairs.v
AdmissibilityBase.v
Collapse.v
Required theorems:
admissible_iff_constant_on_kernel
factorisation_iff_kernel_pair_descent
safety_relevant_collapse_iff_inadmissible
no_recovery
Exit criterion:
0 Admitted
0 Conjecture
compiles from clean checkout
Estimated size:
2,500-4,000 lines

Phase 2: Add Refinement and Warrant Debt
Deliverables:
Refinement.v
WarrantDebt.v
TimelyAdmissibility.v
HorizonDebt.v
Required theorems:
admissibility_monotone_under_refinement
admissibility_not_antitone
warrant_debt_witness_sound
zero_horizon_debt_iff_timely
Exit criterion:
The static theory can express the difference between:
    1. inadmissibility,
    2. witnessed warrant debt,
    3. untimely admissibility repair,
    4. horizon debt.
Estimated size:
3,000-5,000 additional lines

Phase 3: Runtime Monitor Theory
Deliverables:
MonitorStates.v
StructuralFatigue.v
MetastableClosure.v
RuptureCertificates.v
Recovery.v
RuntimeSoundness.v
Required theorems:
fatigue_monotone
hard_rupture_absorbing
metastable_closure_has_warrant_debt
rupture_certificate_sound
reclosure_not_recovery
monitor_soundness
Exit criterion:
The project can formally support the runtime monitoring paper.
Estimated size:
4,000-6,000 additional lines

Phase 4: First Case Study
Start with the physical sensor boundary case.
Deliverables:
BoundaryConditions.v
SensorCollapse.v
ThermalSafety.v
PDEAdmissibility.v
Required theorem:
sensor_observation_inadmissible
Then:
enriched_sensor_restores_admissibility
Exit criterion:
One complete industrially motivated case study with collapse witness, inadmissibility theorem, refinement theorem, and certificate generation.
Estimated size:
2,000-3,500 additional lines

Phase 5: Extraction Bridge
Deliverables:
ExtractableTypes.v
MonitorExtraction.v
CertificateExtraction.v
ExtractionCorrectness.v
monitor_kernel.ml
cert_parser.ml
replay_trace.ml
Exit criterion:
A runtime trace can produce a certificate that corresponds to a proved Coq/Rocq certificate structure.
Estimated size:
3,000-5,000 additional lines

Phase 6: Second and Third Case Studies
Only after the first case study is solid.
Add:
Consensus/
GPU/
Exit criterion:
At least two independent domains show the same admissibility mechanism.
Estimated size:
4,000-8,000 additional lines

15. What the Paper Should Eventually Claim
A mature JAR-style paper should not say:
We present an idea about structural admissibility.
It should say:
We present a Rocq library for structural admissibility, consisting of approximately N lines of machine-checked proof and M lines of extracted OCaml support. The library mechanises observational kernels, factorisation-based admissibility, refinement, warrant debt, runtime structural fatigue, metastable closure, and rupture certificates. We prove soundness theorems connecting static inadmissibility witnesses to runtime certificates, and we validate the framework across three case studies.
That is the difference between a rejected theory sketch and a serious formal methods artefact.

16. Most Important Corrections to the Original Outline
Correction 1: Do not expand proofs merely to increase line count
This is bad strategy:
Replace opaque auto or simpl calls with detailed, step-by-step tactical derivations.
Sometimes that is appropriate. But if you replace clean proof automation with verbose proof scripts only to increase LOC, reviewers will see through it.
Better:
Replace opaque proof scripts with named intermediate lemmas, explicit theorem structure, and reusable automation.
That gives genuine substance.

Correction 2: Rename admit_tactics.v
Use:
AdmissibilityTactics.v
The name admit_tactics.v is poison for this project.

Correction 3: Be careful with GPU and Paxos claims
Do not claim to mechanise full GPU memory consistency or full Paxos unless you actually do it.
Safer claims:
A structural model of local observations in relaxed-memory executions.
A structural model of local-view collapse under network partition.
These are still valuable, but they are honest.

Correction 4: Prefer finite computational models for extraction
General theorems can use arbitrary types.
Extractable runtime tools should use finite, decidable structures.
That means:
Phi : X -> bool
is extraction-friendly.
Phi : X -> Prop
is mathematically elegant but operationally weaker.
You probably need both.

Correction 5: Keep assumptions visible
Create:
ASSUMPTIONS.md
and list every abstract assumption.
That is how you avoid another reviewer saying the development is not really complete.

17. Minimum Viable Heavyweight Version
The smallest version worth aiming for before another JAR-style submission is:
10,000+ lines total
0 Admitted
1 complete case study
1 extracted OCaml monitor path
1 certificate soundness theorem
clear theorem dependency graph
clear build instructions
A better target:
15,000-20,000 lines
0 Admitted
2 complete case studies
runtime certificate extraction
custom tactics
paper + artefact evaluation
The strongest target:
25,000+ lines
0 Admitted
3 case studies
verified extraction bridge
CI
documentation
reproducible benchmarks

18. The Real Core of the Project
The deepest contribution is not the line count.
The real contribution is this chain:
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
That chain is the project.
Every file should support one part of that chain.
If the project is built that way, it stops looking like a rejected 500-line theorem sketch and starts looking like a serious formal verification framework.

