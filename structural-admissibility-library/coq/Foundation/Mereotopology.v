(** * Mereotopology.v

    Boundary and region logic for physical system modelling.
    Provides the RCC8 relation hierarchy and its connection to observation maps.

    Regions and connection are the primitive notions; all other spatial
    relations are defined from them.  Boundary-based observations are
    formalised as maps from regions to boundary signatures, and boundary
    collapse is shown to induce admissibility failures.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Classes.RelationClasses.
Require Import Foundation.Relations.
Require Import Foundation.Orders.

(* ================================================================= *)
(** ** 1. Primitive mereotopological vocabulary                       *)
(* ================================================================= *)

Parameter Region : Type.
Parameter C : Region -> Region -> Prop.

(** Connection is reflexive and symmetric. *)
Axiom C_refl : forall x, C x x.
Axiom C_sym  : forall x y, C x y -> C y x.

(* ================================================================= *)
(** ** 2. Derived mereotopological relations                          *)
(* ================================================================= *)

Definition disconnected (x y : Region) : Prop := ~ C x y.

Definition part_of (x y : Region) : Prop :=
  forall z, C z x -> C z y.

Definition proper_part_of (x y : Region) : Prop :=
  part_of x y /\ ~ part_of y x.

Definition overlaps (x y : Region) : Prop :=
  exists z, part_of z x /\ part_of z y.

Definition external_connection (x y : Region) : Prop :=
  C x y /\ ~ overlaps x y.

Definition tangential_part (x y : Region) : Prop :=
  part_of x y /\
  exists z, external_connection z y /\ C z x.

Definition non_tangential_part (x y : Region) : Prop :=
  part_of x y /\
  forall z, external_connection z y -> ~ C z x.

(* ================================================================= *)
(** ** 3. RCC8 relations                                              *)
(* ================================================================= *)

Inductive RCC8Rel : Region -> Region -> Prop :=
| RCC_DC   : forall x y, disconnected x y ->
               RCC8Rel x y
| RCC_EC   : forall x y, external_connection x y ->
               RCC8Rel x y
| RCC_PO   : forall x y, overlaps x y /\
               ~ part_of x y /\ ~ part_of y x ->
               RCC8Rel x y
| RCC_EQ   : forall x y, part_of x y /\ part_of y x ->
               RCC8Rel x y
| RCC_TPP  : forall x y, tangential_part x y /\
               ~ tangential_part y x ->
               RCC8Rel x y
| RCC_NTPP : forall x y, non_tangential_part x y ->
               RCC8Rel x y
| RCC_TPPI : forall x y, tangential_part y x /\
               ~ tangential_part x y ->
               RCC8Rel x y
| RCC_NTPPI: forall x y, non_tangential_part y x ->
               RCC8Rel x y.

(* ================================================================= *)
(** ** 4. Part-of is a preorder                                       *)
(* ================================================================= *)

Lemma part_of_refl : forall x, part_of x x.
Proof.
  intro x. unfold part_of. intros. assumption.
Qed.

Lemma part_of_trans : forall x y z,
    part_of x y -> part_of y z -> part_of x z.
Proof.
  intros x y z Hxy Hyz.
  unfold part_of in *. intros w HCwx.
  apply Hyz. apply Hxy. assumption.
Qed.

(* ================================================================= *)
(** ** 5. Overlap is symmetric                                        *)
(* ================================================================= *)

Lemma overlap_sym : forall x y, overlaps x y -> overlaps y x.
Proof.
  intros x y [z [Hzx Hzy]]. exists z. split; assumption.
Qed.

(* ================================================================= *)
(** ** 6. Connection reflexivity implies part-of reflex               *)
(* ================================================================= *)

Lemma C_refl_implies_part_of_self : forall x, part_of x x.
Proof. apply part_of_refl. Qed.

(* ================================================================= *)
(** ** 7. Boundary signatures as observation maps                     *)
(* ================================================================= *)

(** A boundary signature captures topological information about a region's
    boundaries — specifically, which other regions it is externally connected to. *)

Definition boundary_connected_regions (r : Region) : Region -> Prop :=
  fun s => external_connection s r.

(** Two regions have the same boundary signature if they are externally
    connected to exactly the same set of regions. *)
Definition same_boundary_signature (r s : Region) : Prop :=
  forall t, external_connection t r <-> external_connection t s.

Lemma same_boundary_signature_equiv : Equivalence same_boundary_signature.
Proof.
  constructor.
  - intro r. unfold same_boundary_signature. tauto.
  - intros r s H. unfold same_boundary_signature in *.
    intro t. symmetry. apply H.
  - intros r s t Hrs Hst. unfold same_boundary_signature in *.
    intro u. rewrite Hrs. apply Hst.
Qed.

(** A boundary observation map assigns a representative signature to each region. *)
Parameter BoundarySignature : Type.
Parameter boundary_observation : Region -> BoundarySignature.
Axiom boundary_obs_respects_signature :
  forall r s,
    same_boundary_signature r s ->
    boundary_observation r = boundary_observation s.

(* ================================================================= *)
(** ** 8. Boundary collapse induces admissibility failure             *)
(* ================================================================= *)

(** A physical state predicate (e.g., thermal safety) that depends on
    boundary conditions but whose observation is the boundary signature
    can suffer admissibility failure if distinct safety-relevant states
    share a boundary signature. *)

Parameter PhysicalProperty : Region -> Prop.

(** Boundary collapse: two regions share a signature but differ in physical property. *)
Definition boundary_collapse_witness (r s : Region) : Prop :=
  same_boundary_signature r s /\
  (PhysicalProperty r /\ ~ PhysicalProperty s \/
   ~ PhysicalProperty r /\ PhysicalProperty s).

Theorem boundary_collapse_induces_admissibility_failure :
  forall r s,
    boundary_collapse_witness r s ->
    ~ (exists P_hat : BoundarySignature -> Prop,
          forall t, PhysicalProperty t <-> P_hat (boundary_observation t)).
Proof.
  intros r s [Hsig Hdiff] [P_hat HP].
  pose proof (HP r) as Hr.
  pose proof (HP s) as Hs.
  rewrite (boundary_obs_respects_signature Hsig) in Hr.
  destruct Hdiff as [[HPr HnPs] | [HnPr HPs]].
  - exact (HnPs (proj2 Hs (proj1 Hr HPr))).
  - exact (HnPr (proj2 Hr (proj1 Hs HPs))).
Qed.

(* ================================================================= *)
(** ** 9. Non-tangential containment and interior                     *)
(* ================================================================= *)

Definition interior_of (y : Region) : Region -> Prop :=
  fun x => non_tangential_part x y.

Axiom ntpp_irreflexive : forall x, ~ non_tangential_part x x.

Lemma ntpp_antisym :
  forall x y, non_tangential_part x y -> non_tangential_part y x -> False.
Proof.
  intros x y [Hpx Hnx] [Hpy Hny].
  apply ntpp_irreflexive with (x := x).
  split.
  - apply part_of_refl.
  - intros z Hz.
    apply Hnx.
    unfold external_connection in *.
    destruct Hz as [HC Hno].
    split.
    + unfold part_of in Hpx. apply Hpx. auto.
    + intro Hc. apply Hno.
      unfold overlaps in *. destruct Hc as [w [Hwz Hwy]].
      exists w. split; auto.
      apply part_of_trans with y; auto.
Qed.

(* ================================================================= *)
(** ** 10. Mereotopological refinement of observations               *)
(* ================================================================= *)

(** An enriched observation uses both boundary signature and interior
    information. *)
Parameter InteriorSignature : Type.
Parameter interior_observation : Region -> InteriorSignature.

Definition enriched_obs (r : Region) : (BoundarySignature * InteriorSignature) :=
  (boundary_observation r, interior_observation r).

Lemma enriched_obs_refines_boundary :
    refines enriched_obs boundary_observation.
Proof.
  unfold refines, enriched_obs. intros x y Heq.
  exact (f_equal fst Heq).
Qed.

