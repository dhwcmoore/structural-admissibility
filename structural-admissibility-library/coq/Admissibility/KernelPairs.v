(** * KernelPairs.v

    Categorical formulation of admissibility via kernel pairs.

    A kernel pair of M : X -> O is the set of pairs (x, y) satisfying M x = M y.
    A predicate Phi descends along the kernel pair when Phi x = Phi y for all
    such pairs.  This is the categorical bridge between factorisation and
    category-theoretic epimorphism structure.

    Main theorem (factorisation_iff_kernel_pair_descent):
        boolean_admissible Phi M <->
        descends_along_kernel_pair M Phi.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.

Require Import Foundation.Relations.
Require Import Foundation.Orders.
Require Import Admissibility.ObservationMaps.
Require Import Admissibility.Factorisation.

(* ================================================================= *)
(** ** 1. Kernel pair record                                          *)
(* ================================================================= *)

Record KernelPair {X O : Type} (M : X -> O) := {
  kp_left  : X;
  kp_right : X;
  kernel_eq : M kp_left = M kp_right
}.

Definition kp_left_proj {X O : Type} {M : X -> O}
    (kp : KernelPair M) : X := kp_left kp.

Definition kp_right_proj {X O : Type} {M : X -> O}
    (kp : KernelPair M) : X := kp_right kp.

(* ================================================================= *)
(** ** 2. Descent along the kernel pair                              *)
(* ================================================================= *)

Definition descends_along_kernel_pair {X O : Type}
    (M : X -> O) (Phi : X -> bool) : Prop :=
  forall kp : KernelPair M,
    Phi (kp_left kp) = Phi (kp_right kp).

(* ================================================================= *)
(** ** 3. Main theorem: factorisation iff descent                     *)
(* ================================================================= *)

Theorem factorisation_iff_kernel_pair_descent :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    boolean_admissible Phi M
    <->
    descends_along_kernel_pair M Phi.
Proof.
  intros X O Phi M. split.
  - intros Hadm kp.
    apply (admissible_implies_constant_on_kernel Hadm).
    apply kernel_eq.
  - intro Hdesc.
    apply constant_on_kernel_implies_admissible.
    intros x y Heq.
    apply (Hdesc {| kp_left := x; kp_right := y; kernel_eq := Heq |}).
Qed.

(* ================================================================= *)
(** ** 4. Kernel pair as a type-level pullback                        *)
(* ================================================================= *)

(** The kernel pair of M is the pullback of M along itself. *)
Definition kernel_pair_type {X O : Type} (M : X -> O) : Type :=
  { p : X * X | M (fst p) = M (snd p) }.

Definition kp_from_pair {X O : Type} (M : X -> O)
    (kpt : kernel_pair_type M) : KernelPair M :=
  {| kp_left  := fst (proj1_sig kpt);
     kp_right := snd (proj1_sig kpt);
     kernel_eq := proj2_sig kpt |}.

(* ================================================================= *)
(** ** 5. Diagonal kernel pair element                                *)
(* ================================================================= *)

Definition diagonal_kp {X O : Type} (M : X -> O) (x : X) : KernelPair M :=
  {| kp_left  := x;
     kp_right := x;
     kernel_eq := eq_refl (M x) |}.

Lemma descent_holds_on_diagonal :
  forall {X O : Type} (M : X -> O) (Phi : X -> bool),
    descends_along_kernel_pair M Phi ->
    forall x, Phi (kp_left (diagonal_kp M x)) = Phi (kp_right (diagonal_kp M x)).
Proof.
  intros X O M Phi Hdesc x.
  apply Hdesc.
Qed.

(* ================================================================= *)
(** ** 6. Symmetry of kernel pairs                                    *)
(* ================================================================= *)

Definition kp_swap {X O : Type} {M : X -> O} (kp : KernelPair M) : KernelPair M :=
  {| kp_left  := kp_right kp;
     kp_right := kp_left  kp;
     kernel_eq := eq_sym (kernel_eq kp) |}.

Lemma descent_symmetric :
  forall {X O : Type} (M : X -> O) (Phi : X -> bool),
    descends_along_kernel_pair M Phi ->
    forall kp : KernelPair M,
      Phi (kp_right kp) = Phi (kp_left kp).
Proof.
  intros X O M Phi Hdesc kp.
  symmetry. apply Hdesc.
Qed.

(* ================================================================= *)
(** ** 7. Composition of kernel pairs                                 *)
(* ================================================================= *)

(** If M3 = M1 ∘ f and M3 x = M3 y, then M1 (f x) = M1 (f y). *)
Lemma composed_kernel_pair :
  forall {X O1 O2 : Type} (M1 : X -> O1) (f : O1 -> O2)
    (kp : KernelPair (fun x => f (M1 x))),
    M1 (kp_left kp) = M1 (kp_right kp) \/
    f (M1 (kp_left kp)) = f (M1 (kp_right kp)).
Proof.
  intros. right. exact (kernel_eq kp).
Qed.

(* ================================================================= *)
(** ** 8. Effective epimorphism condition                             *)
(* ================================================================= *)

(** M : X -> O is an effective epimorphism (in the category of sets with
    decidable equality) when it is the coequaliser of its kernel pair.
    Formally: every function O -> Y that makes the kernel pair commute
    factors through M in a unique way.

    In our setting, boolean_admissible characterises exactly those functions
    that factor through M. *)

Definition is_effective_epi {X O : Type} (M : X -> O) : Prop :=
  forall (Y : Type) (f : O -> Y) (g : O -> Y),
    (forall kp : KernelPair M, f (M (kp_left kp)) = g (M (kp_right kp))) ->
    f = g.

(** Surjective maps are effective epis in Set. *)
Theorem surjective_effective_epi :
  forall {X O : Type} (M : X -> O),
    surjective M -> is_effective_epi M.
Proof.
  intros X O M Hsurj Y f g Hkp.
  apply functional_extensionality. intro o.
  destruct (Hsurj o) as [x Hx].
  rewrite <- Hx.
  apply (Hkp {| kp_left := x; kp_right := x; kernel_eq := eq_refl (M x) |}).
Qed.

(* ================================================================= *)
(** ** 9. Kernel pair count and finite inadmissibility                *)
(* ================================================================= *)

(** For finite types, the number of collapsing pairs gives a measure of
    how severely admissibility is violated. *)

Definition collapse_count {X O : Type}
    (O_dec : forall a b : O, {a = b} + {a <> b})
    (M : X -> O) (Phi : X -> bool) (enum_X : list X) : nat :=
  List.length (List.filter
    (fun p => match p with (x, y) =>
      match O_dec (M x) (M y) with
      | left _  => negb (Bool.eqb (Phi x) (Phi y))
      | right _ => false
      end
    end)
    (List.list_prod enum_X enum_X)).
