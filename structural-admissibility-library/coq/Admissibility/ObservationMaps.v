(** * ObservationMaps.v

    Observation maps, observation structures, and observational kernels.
*)

Unset Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import Logic.IndefiniteDescription.
From Stdlib Require Import Classes.RelationClasses.

Require Import Foundation.Relations.
Require Import Foundation.Orders.

(* ================================================================= *)
(** ** 1. Basic observation map record                                *)
(* ================================================================= *)

Record ObservationMap (X O : Type) := {
  observe : X -> O
}.

(* ================================================================= *)
(** ** 2. Observation structure                                       *)
(* ================================================================= *)

Record ObservationStructure := {
  State  : Type;
  Obs    : Type;
  obs    : State -> Obs
}.

(** Observation equivalence: two states yield the same observation. *)
Definition obs_equiv (S : ObservationStructure)
    (x y : State S) : Prop :=
  obs S x = obs S y.

Lemma obs_equiv_refl : forall (S : ObservationStructure) (x : State S),
    obs_equiv S x x.
Proof. intros. unfold obs_equiv. reflexivity. Qed.

Lemma obs_equiv_sym : forall (S : ObservationStructure) (x y : State S),
    obs_equiv S x y -> obs_equiv S y x.
Proof. intros. unfold obs_equiv in *. symmetry. assumption. Qed.

Lemma obs_equiv_trans : forall (S : ObservationStructure) (x y z : State S),
    obs_equiv S x y -> obs_equiv S y z -> obs_equiv S x z.
Proof. intros. unfold obs_equiv in *. congruence. Qed.

Theorem obs_equiv_equivalence : forall (S : ObservationStructure),
    Equivalence (obs_equiv S).
Proof.
  intro S. constructor.
  - intro x. apply obs_equiv_refl.
  - intros x y. apply obs_equiv_sym.
  - intros x y z. apply obs_equiv_trans.
Qed.

Instance obs_equiv_Equivalence (S : ObservationStructure)
  : Equivalence (obs_equiv S) := obs_equiv_equivalence S.

(* ================================================================= *)
(** ** 3. Kernel pair induced by an observation map                   *)
(* ================================================================= *)

Record KernelPairPoint {X O : Type} (M : X -> O) := {
  kp_left  : X;
  kp_right : X;
  kp_eq    : M kp_left = M kp_right
}.
Arguments kp_left  {X O M}.
Arguments kp_right {X O M}.
Arguments kp_eq    {X O M}.

Definition obs_kernel_pair (S : ObservationStructure)
  : KernelPairPoint (obs S) -> Prop :=
  fun _ => True.

Lemma obs_induces_kernel_pair : forall (S : ObservationStructure) (x y : State S),
    obs_equiv S x y ->
    exists kp : KernelPairPoint (obs S),
      kp_left kp = x /\ kp_right kp = y.
Proof.
  intros S x y Heq.
  exists {| kp_left := x; kp_right := y; kp_eq := Heq |}.
  simpl. split; reflexivity.
Qed.

(* ================================================================= *)
(** ** 4. Computable-from-obs and maximal information principle       *)
(* ================================================================= *)

Definition computable_from_obs (S : ObservationStructure) (Y : Type)
    (f : State S -> Y) : Prop :=
  exists f_hat : Obs S -> Y,
    forall x, f x = f_hat (obs S x).

Lemma computable_from_obs_constant_on_fibres :
  forall (S : ObservationStructure) (Y : Type) (f : State S -> Y),
    computable_from_obs S Y f ->
    forall x y, obs_equiv S x y -> f x = f y.
Proof.
  intros S Y f [f_hat Hf] x y Heq.
  unfold obs_equiv in Heq.
  rewrite Hf, Hf, Heq. reflexivity.
Qed.

(** Maximal information principle: f factors through obs iff f is constant
    on fibres.  The <- direction requires inhabited Y and classical choice. *)
Theorem maximal_information_principle :
  forall (S : ObservationStructure) (Y : Type) (iY : inhabited Y)
    (f : State S -> Y),
    computable_from_obs S Y f <->
    (forall x y, obs_equiv S x y -> f x = f y).
Proof.
  intros S Y [y0] f. split.
  - apply computable_from_obs_constant_on_fibres.
  - intro Hconst.
    unfold computable_from_obs, obs_equiv in *.
    assert (Htot : forall o : Obs S,
        exists v : Y, forall x : State S, obs S x = o -> f x = v).
    { intro o.
      destruct (excluded_middle_informative (exists x : State S, obs S x = o))
        as [[x Hx] | Hnone].
      - exists (f x). intros y Hy. apply Hconst. congruence.
      - exists y0. intros x Hx. exfalso. apply Hnone. exists x. assumption.
    }
    apply functional_choice in Htot.
    destruct Htot as [f_hat Hf_hat].
    exists f_hat.
    intro x. apply (Hf_hat (obs S x)). reflexivity.
Qed.

(* ================================================================= *)
(** ** 5. Observation map composition                                 *)
(* ================================================================= *)

Definition compose_obs (S1 S2 : ObservationStructure)
    (bridge : State S2 -> State S1) : ObservationStructure :=
  {| State := State S2;
     Obs   := Obs S1;
     obs   := fun x => obs S1 (bridge x) |}.

Lemma compose_obs_coarser :
  forall (S1 S2 : ObservationStructure) (bridge : State S2 -> State S1),
    refines (obs S2) (obs (compose_obs S1 S2 bridge)) ->
    forall x y,
      obs_equiv S2 x y ->
      obs_equiv (compose_obs S1 S2 bridge) x y.
Proof.
  intros S1 S2 bridge Href x y Heq.
  unfold obs_equiv, compose_obs in *. simpl.
  apply Href. assumption.
Qed.

(* ================================================================= *)
(** ** 6. Observation map distinguishability                          *)
(* ================================================================= *)

Definition distinguishes (X O : Type) (M : X -> O) (x y : X) : Prop :=
  M x <> M y.

Definition M_separates (X O : Type) (M : X -> O) : Prop :=
  forall x y, x <> y -> distinguishes X O M x y.

Lemma M_separates_trivial_kernel :
  forall (X O : Type) (M : X -> O),
    M_separates X O M -> forall x y, kernel M x y -> x = y.
Proof.
  intros X O M Hsep x y Hk.
  unfold kernel in Hk.
  apply NNPP. intro Hne.
  exact (Hsep x y Hne Hk).
Qed.

(* ================================================================= *)
(** ** 7. Observable predicates                                       *)
(* ================================================================= *)

Definition observable_through (X O : Type) (M : X -> O) (Phi : X -> bool) : Prop :=
  exists Phi_hat : O -> bool, forall x, Phi x = Phi_hat (M x).

Lemma observable_neg :
  forall (X O : Type) (M : X -> O) (Phi : X -> bool),
    observable_through X O M Phi ->
    observable_through X O M (fun x => negb (Phi x)).
Proof.
  intros X O M Phi [Phi_hat Hfact].
  exists (fun o => negb (Phi_hat o)).
  intro x. rewrite Hfact. reflexivity.
Qed.

Lemma observable_and :
  forall (X O : Type) (M : X -> O) (Phi Psi : X -> bool),
    observable_through X O M Phi ->
    observable_through X O M Psi ->
    observable_through X O M (fun x => andb (Phi x) (Psi x)).
Proof.
  intros X O M Phi Psi [PH Hfp] [PsH Hfq].
  exists (fun o => andb (PH o) (PsH o)).
  intro x. rewrite Hfp, Hfq. reflexivity.
Qed.

Lemma observable_or :
  forall (X O : Type) (M : X -> O) (Phi Psi : X -> bool),
    observable_through X O M Phi ->
    observable_through X O M Psi ->
    observable_through X O M (fun x => orb (Phi x) (Psi x)).
Proof.
  intros X O M Phi Psi [PH Hfp] [PsH Hfq].
  exists (fun o => orb (PH o) (PsH o)).
  intro x. rewrite Hfp, Hfq. reflexivity.
Qed.
