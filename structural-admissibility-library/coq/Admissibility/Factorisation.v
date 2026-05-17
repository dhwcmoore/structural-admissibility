(** * Factorisation.v

    The central admissibility criterion via factorisation.

    A predicate Phi is admissible with respect to observation map M when
    Phi factors through M: there exists Phi_hat s.t. Phi = Phi_hat ∘ M.

    This is the formal backbone of the entire project.

    Main theorem (admissible_iff_constant_on_kernel):
        boolean_admissible Phi M
        <->
        forall x y, M x = M y -> Phi x = Phi y.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.ClassicalDescription.

Require Import Foundation.Relations.
Require Import Foundation.Orders.
Require Import Foundation.Quotients.
Require Import Admissibility.ObservationMaps.

(* ================================================================= *)
(** ** 1. Core factorisation definitions                              *)
(* ================================================================= *)

(** A function Phi : X -> Y factors through M : X -> O. *)
Definition factors_through {X O Y : Type}
    (Phi : X -> Y) (M : X -> O) : Prop :=
  exists Phi_hat : O -> Y,
    forall x, Phi x = Phi_hat (M x).

(** Predicate (Prop) version. *)
Definition predicate_admissible {X O : Type}
    (Phi : X -> Prop) (M : X -> O) : Prop :=
  exists Phi_hat : O -> Prop,
    forall x, Phi x <-> Phi_hat (M x).

(** Boolean version — extraction-friendly. *)
Definition boolean_admissible {X O : Type}
    (Phi : X -> bool) (M : X -> O) : Prop :=
  exists Phi_hat : O -> bool,
    forall x, Phi x = Phi_hat (M x).

(** Shorthand: inadmissible. *)
Definition boolean_inadmissible {X O : Type}
    (Phi : X -> bool) (M : X -> O) : Prop :=
  ~ boolean_admissible Phi M.

(* ================================================================= *)
(** ** 2. The main equivalence theorem                                *)
(* ================================================================= *)

(** Half 1: factorisation implies constant on fibres. *)
Lemma admissible_implies_constant_on_kernel :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    boolean_admissible Phi M ->
    forall x y, M x = M y -> Phi x = Phi y.
Proof.
  intros X O Phi M [Phi_hat Hfact] x y Heq.
  rewrite Hfact, Hfact, Heq. reflexivity.
Qed.

(** Half 2: constant on fibres implies factorisation.
    Delegates to constant_on_kernel_implies_factorisation_bool (Quotients.v). *)
Lemma constant_on_kernel_implies_admissible :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    (forall x y, M x = M y -> Phi x = Phi y) ->
    boolean_admissible Phi M.
Proof.
  intros X O Phi M Hconst.
  exact (constant_on_kernel_implies_factorisation_bool Hconst).
Qed.

(** THE MAIN THEOREM: the formal backbone of the project. *)
Theorem admissible_iff_constant_on_kernel :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    boolean_admissible Phi M
    <->
    forall x y, M x = M y -> Phi x = Phi y.
Proof.
  intros X O Phi M. split.
  - apply admissible_implies_constant_on_kernel.
  - apply constant_on_kernel_implies_admissible.
Qed.

(* ================================================================= *)
(** ** 3. Prop version of the main theorem                            *)
(* ================================================================= *)

Theorem predicate_admissible_iff_iff_on_kernel :
  forall {X O : Type} (Phi : X -> Prop) (M : X -> O),
    predicate_admissible Phi M
    <->
    forall x y, M x = M y -> (Phi x <-> Phi y).
Proof.
  intros X O Phi M. exact (factorisation_iff_kernel_prop M Phi).
Qed.

(* ================================================================= *)
(** ** 4. Consequences                                                *)
(* ================================================================= *)

(** Admissibility is closed under boolean negation. *)
Lemma admissible_neg :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    boolean_admissible Phi M ->
    boolean_admissible (fun x => negb (Phi x)) M.
Proof.
  intros X O Phi M [Phi_hat Hfact].
  exists (fun o => negb (Phi_hat o)).
  intro x. rewrite Hfact. reflexivity.
Qed.

(** Admissibility is closed under boolean conjunction. *)
Lemma admissible_and :
  forall {X O : Type} (Phi Psi : X -> bool) (M : X -> O),
    boolean_admissible Phi M ->
    boolean_admissible Psi M ->
    boolean_admissible (fun x => andb (Phi x) (Psi x)) M.
Proof.
  intros X O Phi Psi M [PhiH HfP] [PsiH HfQ].
  exists (fun o => andb (PhiH o) (PsiH o)).
  intro x. rewrite HfP, HfQ. reflexivity.
Qed.

(** Admissibility is closed under boolean disjunction. *)
Lemma admissible_or :
  forall {X O : Type} (Phi Psi : X -> bool) (M : X -> O),
    boolean_admissible Phi M ->
    boolean_admissible Psi M ->
    boolean_admissible (fun x => orb (Phi x) (Psi x)) M.
Proof.
  intros X O Phi Psi M [PhiH HfP] [PsiH HfQ].
  exists (fun o => orb (PhiH o) (PsiH o)).
  intro x. rewrite HfP, HfQ. reflexivity.
Qed.

(** The constant-true and constant-false predicates are always admissible. *)
Lemma admissible_const_true :
  forall {X O : Type} (M : X -> O),
    boolean_admissible (fun _ => true) M.
Proof.
  intros. exists (fun _ => true). intros. reflexivity.
Qed.

Lemma admissible_const_false :
  forall {X O : Type} (M : X -> O),
    boolean_admissible (fun _ => false) M.
Proof.
  intros. exists (fun _ => false). intros. reflexivity.
Qed.

(** Any predicate is admissible w.r.t. the identity observation. *)
Lemma admissible_identity_obs :
  forall {X : Type} (Phi : X -> bool),
    boolean_admissible Phi (@identity_obs X).
Proof.
  intros. exists Phi. intros. unfold identity_obs. reflexivity.
Qed.

(** No non-trivial predicate is admissible w.r.t. the trivial observation. *)
Lemma inadmissible_trivial_obs :
  forall {X : Type} (Phi : X -> bool),
    (exists x y : X, Phi x <> Phi y) ->
    ~ boolean_admissible Phi (@trivial_obs X).
Proof.
  intros X Phi [x [y Hne]] [Phi_hat Hfact].
  apply Hne.
  rewrite Hfact, Hfact. unfold trivial_obs. reflexivity.
Qed.

(* ================================================================= *)
(** ** 5. Inadmissibility witnesses                                   *)
(* ================================================================= *)

(** An explicit inadmissibility witness. *)
Record InadmissibilityWitness {X O : Type}
    (Phi : X -> bool) (M : X -> O) := {
  iw_left   : X;
  iw_right  : X;
  iw_same_obs   : M iw_left = M iw_right;
  iw_diff_pred  : Phi iw_left <> Phi iw_right
}.

Theorem inadmissibility_witness_implies_inadmissible :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    InadmissibilityWitness Phi M ->
    boolean_inadmissible Phi M.
Proof.
  intros X O Phi M [l r Hobs Hpred].
  unfold boolean_inadmissible.
  intro Hadm.
  apply Hpred.
  apply (admissible_implies_constant_on_kernel Hadm).
  assumption.
Qed.

(** Conversely, inadmissibility gives rise to a witness (classically). *)
Theorem inadmissible_implies_witness :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    boolean_inadmissible Phi M ->
    exists x y, M x = M y /\ Phi x <> Phi y.
Proof.
  intros X O Phi M Hinadm.
  unfold boolean_inadmissible in Hinadm.
  apply Classical_Prop.NNPP. intro H.
  apply Hinadm.
  apply constant_on_kernel_implies_admissible.
  intros x y Heq.
  apply Classical_Prop.NNPP. intro Hne.
  apply H. exists x. exists y. split; assumption.
Qed.

(* ================================================================= *)
(** ** 6. Factorisation uniqueness                                    *)
(* ================================================================= *)

(** When M is surjective, the factor Phi_hat is unique. *)
Theorem admissible_factor_unique :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    surjective M ->
    boolean_admissible Phi M ->
    exists! Phi_hat : O -> bool, forall x, Phi x = Phi_hat (M x).
Proof.
  intros X O Phi M Hsurj [Phi_hat Hfact].
  exists Phi_hat. split.
  - assumption.
  - intros Psi_hat Hfact2.
    apply functional_extensionality. intro o.
    destruct (Hsurj o) as [x Hx].
    rewrite <- Hx.
    rewrite <- Hfact, <- Hfact2. reflexivity.
Qed.

