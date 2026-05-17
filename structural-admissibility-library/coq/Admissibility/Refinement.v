(** * Refinement.v

    Monotonicity and anti-monotonicity of admissibility under observation refinement.

    Central theorem (admissibility_monotone_under_refinement):
        refines M2 M1 -> boolean_admissible Phi M1 -> boolean_admissible Phi M2.

    Counterexample theorem (admissibility_not_antitone):
        There exist M1, M2, Phi such that refines M2 M1 but Phi is admissible
        w.r.t. M2 yet NOT w.r.t. M1.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Logic.Classical_Prop.

Require Import Foundation.Relations.
Require Import Foundation.Orders.
Require Import Admissibility.ObservationMaps.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.

(* ================================================================= *)
(** ** 1. Refinement definition (restated for this module)            *)
(* ================================================================= *)

(** M2 refines M1: M2 x = M2 y -> M1 x = M1 y. *)
(** Definition imported from Foundation.Orders. *)

(* ================================================================= *)
(** ** 2. Admissibility is monotone under refinement                  *)
(* ================================================================= *)

(** If Phi is admissible w.r.t. the coarser M1, it remains admissible
    w.r.t. the finer M2, because M2 never collapses more than M1. *)
Theorem admissibility_monotone_under_refinement :
  forall {X O1 O2 : Type}
    (Phi : X -> bool)
    (M1 : X -> O1)
    (M2 : X -> O2),
    refines M2 M1 ->
    boolean_admissible Phi M1 ->
    boolean_admissible Phi M2.
Proof.
  intros X O1 O2 Phi M1 M2 Href Hadm.
  apply constant_on_kernel_implies_admissible.
  intros x y H2.
  apply (admissible_implies_constant_on_kernel Hadm).
  apply Href. assumption.
Qed.

(** Intuition: M2 refines M1 means kernel(M2) ⊆ kernel(M1).
    If Phi is constant on kernel(M1), it is a fortiori constant on kernel(M2). *)

(* ================================================================= *)
(** ** 3. Admissibility is NOT antitone                               *)
(* ================================================================= *)

(** Counterexample: there exist M1, M2, Phi such that M2 refines M1,
    Phi is admissible w.r.t. M2, but NOT admissible w.r.t. M1.

    Concrete construction:
      X = {0, 1, 2, 3}  (approximated by nat with elements 0, 1, 2, 3)
      M1 x = x mod 2     (collapses {0,2} and {1,3})
      M2 x = x           (identity, finest possible)
      Phi x = (x =? 0 || x =? 1)  (true for 0, 1; false for 2, 3)

    Phi is NOT admissible w.r.t. M1 because M1 collapses 0 and 2
    (both map to 0) but Phi 0 = true ≠ false = Phi 2.

    Phi IS admissible w.r.t. M2 (identity) trivially.
    M2 refines M1 (identity refines everything).
*)

Theorem admissibility_not_antitone :
  exists (X : Type) (O1 O2 : Type)
    (Phi : X -> bool) (M1 : X -> O1) (M2 : X -> O2),
    refines M2 M1 /\
    boolean_admissible Phi M2 /\
    ~ boolean_admissible Phi M1.
Proof.
  (** X = nat (we use 4 elements: 0, 1, 2, 3) *)
  exists nat.
  exists nat.  (** O1 = nat *)
  exists nat.  (** O2 = nat (identity codom) *)
  exists (fun x => if Nat.leb x 1 then true else false).
  exists (fun x => Nat.modulo x 2).
  exists (fun x => x).               (** M2 = identity *)
  split; [| split].
  - (** M2 refines M1: M2 x = M2 y -> M1 x = M1 y, i.e., x = y -> x mod 2 = y mod 2. *)
    unfold refines. intros x y Heq. rewrite Heq. reflexivity.
  - (** Phi admissible w.r.t. M2 = identity. *)
    apply admissible_identity_obs.
  - (** Phi not admissible w.r.t. M1 = mod 2. *)
    intros [Phi_hat Hfact].
    (** M1 0 = 0, M1 2 = 0, but Phi 0 = true ≠ false = Phi 2. *)
    assert (H0 : Phi_hat (Nat.modulo 0 2) = true).
    { rewrite <- Hfact. simpl. reflexivity. }
    assert (H2 : Phi_hat (Nat.modulo 2 2) = false).
    { rewrite <- Hfact. simpl. reflexivity. }
    simpl in H0, H2.
    rewrite H0 in H2. discriminate.
Qed.

(** This counterexample is worth including because it prevents reviewers
    from thinking the theory is trivial in the reverse direction. *)

(* ================================================================= *)
(** ** 4. Refinement chains preserve admissibility                    *)
(* ================================================================= *)

Theorem admissibility_preserved_by_refinement_chain :
  forall {X O1 O2 : Type}
    (Phi : X -> bool)
    (M2 : X -> O2)
    (M1 : X -> O1),
    refines M2 M1 ->
    boolean_admissible Phi M1 ->
    boolean_admissible Phi M2.
Proof.
  intros X O1 O2 Phi M2 M1 Hchain Hadm.
  apply admissibility_monotone_under_refinement with (M1 := M1).
  - assumption.
  - assumption.
Qed.

(* ================================================================= *)
(** ** 5. Minimal sufficient refinement                               *)
(* ================================================================= *)

(** A refinement M2 is minimally sufficient for Phi if:
    1. Phi is admissible w.r.t. M2.
    2. No coarser map M' (i.e., M2 refines M' but M' does not refine M2)
       makes Phi admissible. *)
Definition minimally_sufficient_for {X O : Type}
    (M : X -> O) (Phi : X -> bool) : Prop :=
  boolean_admissible Phi M /\
  forall (O' : Type) (M' : X -> O'),
    refines M M' ->
    ~ refines M' M ->
    ~ boolean_admissible Phi M'.

(** The identity map is not minimally sufficient in general (it is maximal). *)

(* ================================================================= *)
(** ** 6. Refinement and inadmissibility                              *)
(* ================================================================= *)

(** If Phi is inadmissible w.r.t. M2 (finer), it is also inadmissible
    w.r.t. any M1 that M2 refines (coarser). *)
Theorem inadmissibility_antimonotone :
  forall {X O1 O2 : Type}
    (Phi : X -> bool)
    (M1 : X -> O1)
    (M2 : X -> O2),
    refines M2 M1 ->
    boolean_inadmissible Phi M2 ->
    boolean_inadmissible Phi M1.
Proof.
  intros X O1 O2 Phi M1 M2 Href Hinadm2 Hadm1.
  apply Hinadm2.
  apply admissibility_monotone_under_refinement with (M1 := M1); assumption.
Qed.

(** Contrapositive: admissibility of the finer map implies admissibility of the coarser. *)
(** Wait — that is admissibility_monotone_under_refinement above. *)

(* ================================================================= *)
(** ** 7. Refinement gap: the warrant debt structure                  *)
(* ================================================================= *)

(** If M2 refines M1 and Phi is inadmissible w.r.t. M1, then replacing
    M1 by M2 might restore admissibility.  The gap between M1 and the
    finest admissible coarsening of M2 is the refinement gap. *)

Definition refinement_gap {X O1 O2 : Type}
    (M1 : X -> O1) (M2 : X -> O2) (Phi : X -> bool) : Prop :=
  refines M2 M1 /\
  boolean_inadmissible Phi M1 /\
  boolean_admissible Phi M2.

(** Refinement_gap witnesses a situation where upgrading the observation
    map would restore admissibility. *)
Theorem refinement_gap_implies_strict_refinement :
  forall {X O1 O2 : Type}
    (M1 : X -> O1) (M2 : X -> O2) (Phi : X -> bool),
    refinement_gap M1 M2 Phi ->
    strictly_refines M2 M1.
Proof.
  intros X O1 O2 M1 M2 Phi [Href [Hinadm Hadm]].
  unfold strictly_refines. split.
  - assumption.
  - intro HM1refM2.
    apply Hinadm.
    apply admissibility_monotone_under_refinement with (M1 := M2); assumption.
Qed.

