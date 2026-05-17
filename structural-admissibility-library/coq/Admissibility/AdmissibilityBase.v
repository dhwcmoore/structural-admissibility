(** * AdmissibilityBase.v

    Public interface of the admissibility theory.
    Re-exports the core definitions and collects the central theorems
    under canonical names.

    Key theorems:
    - admissibility_identity: the identity observation makes every predicate admissible.
    - no_recovery: kernel-collapsed states cannot be separated by any downstream function.
    - inadmissibility_not_repaired_by_postprocessing: the stronger version.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Logic.Classical_Prop.

Require Export Foundation.Relations.
Require Export Foundation.Orders.
Require Export Foundation.Quotients.
Require Export Admissibility.ObservationMaps.
Require Export Admissibility.Factorisation.
Require Export Admissibility.KernelPairs.

(* ================================================================= *)
(** ** 1. Canonical names                                             *)
(* ================================================================= *)

Definition Admissible {X O : Type} :=
  @boolean_admissible X O.

Definition Inadmissible {X O : Type}
    (Phi : X -> bool) (M : X -> O) : Prop :=
  ~ Admissible Phi M.

(* ================================================================= *)
(** ** 2. Admissibility under identity observation                    *)
(* ================================================================= *)

Theorem admissibility_identity :
  forall {X : Type} (Phi : X -> bool),
    Admissible Phi (@identity_obs X).
Proof.
  intros X Phi. apply admissible_identity_obs.
Qed.

(** Any predicate is admissible w.r.t. the identity because the identity
    makes every state distinguishable — the kernel is trivial. *)

(* ================================================================= *)
(** ** 3. No-recovery theorem                                         *)
(* ================================================================= *)

(** Simple version: kernel-equal states yield equal downstream outputs. *)
Theorem no_recovery :
  forall {X O Y : Type}
    (M : X -> O)
    (f : O -> Y)
    (x y : X),
    M x = M y ->
    f (M x) = f (M y).
Proof.
  intros X O Y M f x y Heq.
  rewrite Heq. reflexivity.
Qed.

(** This is philosophically important: once M collapses x and y,
    no post-processing function f can recover the distinction. *)

(** Contrapositive: if f distinguishes M x from M y, then x and y are not collapsed. *)
Corollary no_recovery_contrapositive :
  forall {X O Y : Type}
    (M : X -> O)
    (f : O -> Y)
    (x y : X),
    f (M x) <> f (M y) ->
    M x <> M y.
Proof.
  intros X O Y M f x y Hdiff Heq.
  apply Hdiff. rewrite Heq. reflexivity.
Qed.

(* ================================================================= *)
(** ** 4. Inadmissibility not repaired by post-processing             *)
(* ================================================================= *)

(** The witness-level version: if Phi disagrees on some collapsed pair,
    every post-processing step on observations inherits that disagreement. *)
Theorem inadmissibility_not_repaired_by_postprocessing :
  forall {X O Y : Type}
    (M : X -> O)
    (Phi : X -> bool),
    (exists x y, M x = M y /\ Phi x <> Phi y) ->
    forall (f : O -> Y),
      exists x y, M x = M y /\ Phi x <> Phi y.
Proof.
  intros X O Y M Phi Hwit f.
  exact Hwit.
Qed.

(** Note: This theorem is simple but philosophically powerful.
    The witness is already present regardless of f.
    No function f : O -> Y can remove the witness because the witness
    only refers to x, y, and M — not to f. *)

(** Stronger version: any attempt to reroute Phi through f ∘ M fails. *)
Theorem postprocessing_cannot_restore_admissibility :
  forall {X O Y : Type}
    (M : X -> O)
    (Phi : X -> bool)
    (f : O -> Y),
    boolean_inadmissible Phi M ->
    boolean_inadmissible (fun x => Phi x) (fun x => f (M x)).
Proof.
  intros X O Y M Phi f Hinadm.
  unfold boolean_inadmissible, boolean_admissible in *.
  intros [Phi_hat Hfact].
  apply Hinadm.
  exists (fun o => Phi_hat (f o)).
  intro x. rewrite Hfact. reflexivity.
Qed.

(* ================================================================= *)
(** ** 5. Admissibility composition lemmas                            *)
(* ================================================================= *)

(** If Phi is admissible w.r.t. M, and N refines M, then Phi is admissible w.r.t. N.
    (Full proof is in Refinement.v; we record the statement here.) *)
Theorem admissibility_preserved_by_refinement :
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
  intros x y Heq.
  apply (admissible_implies_constant_on_kernel Hadm).
  apply Href. assumption.
Qed.

(* ================================================================= *)
(** ** 6. Kernel-pair descent is equivalent to admissibility          *)
(* ================================================================= *)

(** Canonical statement under AdmissibilityBase names. *)
Theorem admissibility_iff_kernel_pair_descent :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    Admissible Phi M
    <->
    descends_along_kernel_pair M Phi.
Proof.
  exact @factorisation_iff_kernel_pair_descent.
Qed.

(* ================================================================= *)
(** ** 7. Interplay between Admissible and Inadmissible               *)
(* ================================================================= *)

Lemma admissible_or_inadmissible :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    Admissible Phi M \/ Inadmissible Phi M.
Proof.
  intros. unfold Inadmissible. apply Classical_Prop.classic.
Qed.

Lemma not_both_admissible_inadmissible :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    ~ (Admissible Phi M /\ Inadmissible Phi M).
Proof.
  intros. unfold Inadmissible. tauto.
Qed.

(* ================================================================= *)
(** ** 8. Admissibility under coarser and finer maps                  *)
(* ================================================================= *)

(** The trivial observation makes only the trivially constant predicates admissible. *)
Corollary only_trivial_predicates_trivially_admissible :
  forall {X : Type} (Phi : X -> bool),
    boolean_admissible Phi (@trivial_obs X) ->
    forall x y : X, Phi x = Phi y.
Proof.
  intros X Phi Hadm x y.
  apply (admissible_implies_constant_on_kernel Hadm).
  unfold trivial_obs. reflexivity.
Qed.

