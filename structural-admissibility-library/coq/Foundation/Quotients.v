(** * Quotients.v

    Observational quotients without heavy quotient machinery.

    Rather than defining a genuine quotient type X / kernel(M), we work
    with kernel-respecting functions directly.  A function f : X -> Y
    respects the kernel of M exactly when it factors through M:
        exists f_hat : O -> Y, forall x, f x = f_hat (M x).

    Central theorem (factorisation_iff_kernel_bool):
        (exists Phi_hat, forall x, Phi x = Phi_hat (M x))
        <->
        forall x y, M x = M y -> Phi x = Phi y.

    This avoids all quotient-type issues in Coq/Rocq.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import Logic.Classical_Prop.

Require Import Foundation.Relations.
Require Import Foundation.Orders.

(* ================================================================= *)
(** ** 1. Collapsed-by relation (synonym for kernel)                  *)
(* ================================================================= *)

Definition collapsed_by {X O : Type}
    (M : X -> O) (x y : X) : Prop :=
  M x = M y.

Lemma collapsed_by_eq_kernel :
  forall {X O : Type} (M : X -> O) (x y : X),
    collapsed_by M x y <-> kernel M x y.
Proof.
  intros. unfold collapsed_by, kernel. tauto.
Qed.

(* ================================================================= *)
(** ** 2. Factorisation                                               *)
(* ================================================================= *)

(** f factors through M: there exists f_hat : O -> Y with f = f_hat ∘ M. *)
Definition factors_through {X O Y : Type}
    (f : X -> Y) (M : X -> O) : Prop :=
  exists f_hat : O -> Y, forall x, f x = f_hat (M x).

(** If f factors through M, then M x = M y implies f x = f y. *)
Lemma factors_through_respects_kernel :
  forall {X O Y : Type} (M : X -> O) (f : X -> Y),
    factors_through f M -> respects_kernel M f.
Proof.
  intros X O Y M f [f_hat Hfact].
  unfold respects_kernel.
  intros x y Heq.
  rewrite Hfact, Hfact, Heq. reflexivity.
Qed.

Theorem factorisation_implies_constant_on_kernel :
  forall {X O Y : Type} (M : X -> O) (Phi : X -> Y),
    (exists Phi_hat : O -> Y, forall x, Phi x = Phi_hat (M x)) ->
    forall x y, M x = M y -> Phi x = Phi y.
Proof.
  intros X O Y M Phi [Phi_hat Hfact] x y Heq.
  rewrite Hfact, Hfact, Heq. reflexivity.
Qed.

(** For the boolean case we use excluded_middle_informative to construct
    a decidable witness without requiring X to be inhabited. *)

Theorem constant_on_kernel_implies_factorisation_bool :
  forall {X O : Type} (M : X -> O) (Phi : X -> bool),
    (forall x y, M x = M y -> Phi x = Phi y) ->
    exists Phi_hat : O -> bool, forall x, Phi x = Phi_hat (M x).
Proof.
  intros X O M Phi Hconst.
  exists (fun o =>
    if excluded_middle_informative (exists x : X, M x = o /\ Phi x = true)
    then true
    else false).
  intro x.
  destruct (excluded_middle_informative (exists z : X, M z = M x /\ Phi z = true))
    as [[z [Hz HPz]] | Hnone].
  - rewrite <- (Hconst z x Hz). exact HPz.
  - destruct (Phi x) eqn:Hpx.
    + exfalso. apply Hnone. exists x. split; [reflexivity | exact Hpx].
    + reflexivity.
Qed.

(* ================================================================= *)
(** ** 3. Main theorem of the quotient layer                          *)
(* ================================================================= *)

Theorem factorisation_iff_kernel_bool :
  forall {X O : Type} (M : X -> O) (Phi : X -> bool),
    (exists Phi_hat : O -> bool, forall x, Phi x = Phi_hat (M x))
    <->
    (forall x y, M x = M y -> Phi x = Phi y).
Proof.
  intros X O M Phi. split.
  - apply factorisation_implies_constant_on_kernel.
  - apply constant_on_kernel_implies_factorisation_bool.
Qed.

(* ================================================================= *)
(** ** 4. Predicate (Prop) version                                    *)
(* ================================================================= *)

Theorem factorisation_iff_kernel_prop :
  forall {X O : Type} (M : X -> O) (Phi : X -> Prop),
    (exists Phi_hat : O -> Prop, forall x, Phi x <-> Phi_hat (M x))
    <->
    (forall x y, M x = M y -> (Phi x <-> Phi y)).
Proof.
  intros X O M Phi. split.
  - intros [Phi_hat Hfact] x y Heq.
    split; intro H.
    + apply (proj2 (Hfact y)). rewrite <- Heq. exact (proj1 (Hfact x) H).
    + apply (proj2 (Hfact x)). rewrite Heq. exact (proj1 (Hfact y) H).
  - intro Hconst.
    exists (fun o => exists x, M x = o /\ Phi x).
    intro x. split.
    + intro HPx. exists x. split; [reflexivity | assumption].
    + intros [y [HMy HPy]].
      exact (proj1 (Hconst y x HMy) HPy).
Qed.

(* ================================================================= *)
(** ** 5. Uniqueness of factorisation                                  *)
(* ================================================================= *)

Theorem factorisation_unique :
  forall {X O Y : Type} (M : X -> O) (f : X -> Y)
    (f_hat g_hat : O -> Y),
    surjective M ->
    (forall x, f x = f_hat (M x)) ->
    (forall x, f x = g_hat (M x)) ->
    f_hat = g_hat.
Proof.
  intros X O Y M f f_hat g_hat Hsurj Hf Hg.
  apply functional_extensionality. intro o.
  destruct (Hsurj o) as [x Hx].
  rewrite <- Hx.
  rewrite <- Hf, <- Hg. reflexivity.
Qed.

(* ================================================================= *)
(** ** 6. Induced predicate on the quotient                           *)
(* ================================================================= *)

Definition induced_pred {X O : Type}
    (M : X -> O) (Phi : X -> bool)
    (_Hconst : forall x y, M x = M y -> Phi x = Phi y)
    : O -> bool :=
  fun o =>
    if excluded_middle_informative (exists x : X, M x = o /\ Phi x = true)
    then true
    else false.
Arguments induced_pred {X O} M Phi _Hconst.

Lemma induced_pred_correct :
  forall {X O : Type} (M : X -> O) (Phi : X -> bool)
    (Hconst : forall x y, M x = M y -> Phi x = Phi y)
    (x : X),
    Phi x = induced_pred M Phi Hconst (M x).
Proof.
  intros X O M Phi Hconst x.
  unfold induced_pred.
  destruct (excluded_middle_informative (exists z : X, M z = M x /\ Phi z = true))
    as [[z [Hz HPz]] | Hnone].
  - rewrite <- (Hconst z x Hz). exact HPz.
  - destruct (Phi x) eqn:Hpx.
    + exfalso. apply Hnone. exists x. split; [reflexivity | exact Hpx].
    + reflexivity.
Qed.

(* ================================================================= *)
(** ** 7. Quotient lift                                               *)
(* ================================================================= *)

Lemma kernel_constant_eq :
  forall {X O Y : Type} (M : X -> O) (f g : X -> Y),
    respects_kernel M f ->
    respects_kernel M g ->
    (forall x, f x = g x) ->
    forall x, f x = g x.
Proof.
  intros. apply H1.
Qed.
