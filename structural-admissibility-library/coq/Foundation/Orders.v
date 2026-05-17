(** * Orders.v

    Preorders, partial orders, and the refinement order on observation maps.

    Central notion: observation map M2 refines M1 when M2 is at least as
    informative — whenever M2 collapses two states, M1 also collapses them.
    Formally:   refines M2 M1  :=  forall x y, M2 x = M2 y -> M1 x = M1 y.

    The direction is deliberate: refinement is sub-collapse, not extension.
    A finer map has a smaller kernel, hence refines a coarser one.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Relations.Relations.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Logic.Classical_Prop.

Require Import Foundation.Relations.

(* ================================================================= *)
(** ** 1. Preorder class                                              *)
(* ================================================================= *)

Class Preorder (A : Type) := {
  leq        : A -> A -> Prop;
  leq_refl   : forall x, leq x x;
  leq_trans  : forall x y z, leq x y -> leq y z -> leq x z
}.

Class PartialOrder (A : Type) := {
  po_leq      : A -> A -> Prop;
  po_refl     : forall x, po_leq x x;
  po_trans    : forall x y z, po_leq x y -> po_leq y z -> po_leq x z;
  po_antisym  : forall x y, po_leq x y -> po_leq y x -> x = y
}.

(* ================================================================= *)
(** ** 2. Refinement order on observation maps                        *)
(* ================================================================= *)

(** M2 refines M1: M2 is at least as informative as M1.
    Equivalently: kernel M2 ⊆ kernel M1. *)
Definition refines {X O1 O2 : Type}
    (M2 : X -> O2) (M1 : X -> O1) : Prop :=
  forall x y, M2 x = M2 y -> M1 x = M1 y.

(** Refinement is equivalent to kernel inclusion. *)
Theorem refines_iff_kernel_included :
  forall {X O1 O2 : Type} (M2 : X -> O2) (M1 : X -> O1),
    refines M2 M1 <-> kernel_included M2 M1.
Proof.
  intros. unfold refines, kernel_included, kernel. tauto.
Qed.

(* ================================================================= *)
(** ** 3. Refinement is a preorder                                    *)
(* ================================================================= *)

Lemma refines_refl : forall {X O : Type} (M : X -> O),
    refines M M.
Proof.
  intros. unfold refines. intros. assumption.
Qed.

Lemma refines_trans :
  forall {X O1 O2 O3 : Type}
    (M3 : X -> O3) (M2 : X -> O2) (M1 : X -> O1),
    refines M3 M2 ->
    refines M2 M1 ->
    refines M3 M1.
Proof.
  intros X O1 O2 O3 M3 M2 M1 H32 H21.
  unfold refines in *.
  intros x y H. apply H21. apply H32. assumption.
Qed.

(** Refinement is not antisymmetric in general (different codomain types). *)

(* ================================================================= *)
(** ** 4. Strict refinement                                           *)
(* ================================================================= *)

(** M2 strictly refines M1 if M2 refines M1 but M1 does not refine M2. *)
Definition strictly_refines {X O1 O2 : Type}
    (M2 : X -> O2) (M1 : X -> O1) : Prop :=
  refines M2 M1 /\ ~ refines M1 M2.

(* ================================================================= *)
(** ** 5. The coarsest observation: constant map                      *)
(* ================================================================= *)

Lemma trivial_obs_coarsest :
  forall {X O : Type} (M : X -> O),
    refines M (@trivial_obs X).
Proof.
  intros. unfold refines, trivial_obs. intros. reflexivity.
Qed.

(* ================================================================= *)
(** ** 6. The finest observation: identity map                        *)
(* ================================================================= *)

Lemma identity_obs_finest :
  forall {X O : Type} (M : X -> O),
    refines (@identity_obs X) M.
Proof.
  intros. unfold refines, identity_obs.
  intros x y H. subst. reflexivity.
Qed.

(** The identity observation has a trivial kernel. *)
Lemma identity_obs_trivial_kernel :
  forall {X : Type} (x y : X),
    kernel (@identity_obs X) x y -> x = y.
Proof.
  intros. unfold kernel, identity_obs in H. assumption.
Qed.

(* ================================================================= *)
(** ** 7. Observation map composition and refinement                  *)
(* ================================================================= *)

(** Composing with a further function can only coarsen. *)
Lemma postcompose_coarsens :
  forall {X O1 O2 : Type} (M : X -> O1) (f : O1 -> O2),
    refines M (fun x => f (M x)).
Proof.
  intros. unfold refines. intros x y H. rewrite H. reflexivity.
Qed.

(** A composed observation refines either component if the composition
    also refines the individual map. *)
Lemma refines_product_left :
  forall {X O1 O2 : Type} (M1 : X -> O1) (M2 : X -> O2),
    refines (product_obs M1 M2) M1.
Proof.
  intros. unfold refines, product_obs.
  intros x y H. injection H as H1 H2. exact H1.
Qed.

Lemma refines_product_right :
  forall {X O1 O2 : Type} (M1 : X -> O1) (M2 : X -> O2),
    refines (product_obs M1 M2) M2.
Proof.
  intros. unfold refines, product_obs.
  intros x y H. injection H as H1 H2. exact H2.
Qed.

(** The product map refines any map that both components refine to. *)
Lemma refines_product_universal :
  forall {X O O1 O2 : Type}
    (M : X -> O) (M1 : X -> O1) (M2 : X -> O2),
    refines M M1 ->
    refines M M2 ->
    refines M (product_obs M1 M2).
Proof.
  intros X O O1 O2 M M1 M2 H1 H2.
  unfold refines, product_obs in *.
  intros x y H.
  rewrite (H1 x y H), (H2 x y H). reflexivity.
Qed.

(* ================================================================= *)
(** ** 8. Refinement chains                                           *)
(* ================================================================= *)

(** A finite chain of refinements: M_n refines M_{n-1} refines ... refines M_0. *)
Inductive RefinesChain {X : Type} : forall {O1 O2 : Type},
    (X -> O1) -> (X -> O2) -> Prop :=
| RefChain_base : forall {O} (M : X -> O), RefinesChain M M
| RefChain_step : forall {O1 O2 O3 : Type}
    (M3 : X -> O3) (M2 : X -> O2) (M1 : X -> O1),
    refines M3 M2 ->
    RefinesChain M2 M1 ->
    RefinesChain M3 M1.

Lemma refines_chain_composition :
  forall {X O1 O2 : Type} (M2 : X -> O2) (M1 : X -> O1),
    RefinesChain M2 M1 -> refines M2 M1.
Proof.
  intros X O1 O2 M2 M1 Hchain.
  induction Hchain.
  - apply refines_refl.
  - eapply refines_trans; eassumption.
Qed.

(* ================================================================= *)
(** ** 9. Correction: refinement and admissibility monotonicity       *)
(* ================================================================= *)

(** IMPORTANT NOTE (from spec section 2.2):
    The claim "refinement preserves safety predicates without exception"
    is too strong as stated. The precise claim is:

    If a predicate is admissible w.r.t. a coarser observation map, then it
    remains admissible w.r.t. any finer map.  (This direction is valid.)
    The reverse is false: a finer observation can support predicates that a
    coarser one cannot.

    The formal proof of this monotonicity lives in Admissibility/Refinement.v.
    Here we record only the structural order lemmas. *)

(** Kernel coarsening: if M2 refines M1 then every M1-fibre is a union of
    M2-fibres. *)
Lemma refines_fibre_coarsening :
  forall {X O1 O2 : Type} (M2 : X -> O2) (M1 : X -> O1) (x y : X),
    refines M2 M1 ->
    kernel M2 x y ->
    kernel M1 x y.
Proof.
  intros. apply H. assumption.
Qed.

(* ================================================================= *)
(** ** 10. Restriction of a refinement                                *)
(* ================================================================= *)

(** Given a subset S ⊆ X (as a predicate), the refinement relationship is
    preserved when restricting attention to S. *)
Definition refines_on {X O1 O2 : Type}
    (S : X -> Prop) (M2 : X -> O2) (M1 : X -> O1) : Prop :=
  forall x y, S x -> S y -> M2 x = M2 y -> M1 x = M1 y.

Lemma refines_implies_refines_on :
  forall {X O1 O2 : Type} (S : X -> Prop) (M2 : X -> O2) (M1 : X -> O1),
    refines M2 M1 -> refines_on S M2 M1.
Proof.
  intros. unfold refines_on. intros. apply H. assumption.
Qed.

