(** * Relations.v

    Foundational relational substrate for the Structural Admissibility Library.
    Defines reflexive relations, equivalence relations, kernels of functions,
    and the central connection between observational collapse and kernel equality.

    The kernel of an observation map is the primary formal object behind
    observational collapse: if two states x, y satisfy M x = M y, then no
    predicate downstream of M can distinguish them.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Relations.Relations.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import Setoids.Setoid.

(* ================================================================= *)
(** ** 1. Type-class definitions for relational structures            *)
(* ================================================================= *)

Class ReflexiveRel (A : Type) := {
  rr_R    : A -> A -> Prop;
  rr_refl : forall x, rr_R x x
}.

Class SymmetricRel (A : Type) := {
  sr_R   : A -> A -> Prop;
  sr_sym : forall x y, sr_R x y -> sr_R y x
}.

Class TransitiveRel (A : Type) := {
  tr_R     : A -> A -> Prop;
  tr_trans : forall x y z, tr_R x y -> tr_R y z -> tr_R x z
}.

Class EquivalenceRel (A : Type) := {
  equiv       : A -> A -> Prop;
  equiv_refl  : forall x,     equiv x x;
  equiv_sym   : forall x y,   equiv x y -> equiv y x;
  equiv_trans : forall x y z, equiv x y -> equiv y z -> equiv x z
}.

(** Every EquivalenceRel yields a Coq Equivalence. *)
Instance EquivalenceRel_Equivalence {A : Type} (E : EquivalenceRel A)
  : Equivalence (@equiv A E).
Proof.
  constructor.
  - intro x. apply equiv_refl.
  - intros x y. apply equiv_sym.
  - intros x y z. apply equiv_trans.
Qed.

(* ================================================================= *)
(** ** 2. Kernel of a function                                        *)
(* ================================================================= *)

(** The kernel identifies all pairs of states that M cannot separate. *)
Definition kernel {X O : Type} (M : X -> O) : X -> X -> Prop :=
  fun x y => M x = M y.

Lemma kernel_refl : forall {X O : Type} (M : X -> O) (x : X),
    kernel M x x.
Proof. intros. unfold kernel. reflexivity. Qed.

Lemma kernel_sym : forall {X O : Type} (M : X -> O) (x y : X),
    kernel M x y -> kernel M y x.
Proof. intros. unfold kernel in *. symmetry. assumption. Qed.

Lemma kernel_trans : forall {X O : Type} (M : X -> O) (x y z : X),
    kernel M x y -> kernel M y z -> kernel M x z.
Proof. intros. unfold kernel in *. congruence. Qed.

Theorem kernel_equivalence : forall {X O : Type} (M : X -> O),
    Equivalence (kernel M).
Proof.
  intros. constructor.
  - intro x. apply kernel_refl.
  - intros x y. apply kernel_sym.
  - intros x y z. apply kernel_trans.
Qed.

Instance kernel_Equivalence {X O : Type} (M : X -> O) : Equivalence (kernel M) :=
  kernel_equivalence M.

Definition kernel_equiv_rel {X O : Type} (M : X -> O) : EquivalenceRel X.
Proof.
  refine {| equiv := kernel M |}.
  - intro x. apply kernel_refl.
  - intros x y. apply kernel_sym.
  - intros x y z. apply kernel_trans.
Defined.

(* ================================================================= *)
(** ** 3. Setoid rewriting support                                    *)
(* ================================================================= *)

Add Parametric Relation (X O : Type) (M : X -> O) : X (kernel M)
  reflexivity  proved by (@kernel_refl  X O M)
  symmetry     proved by (@kernel_sym   X O M)
  transitivity proved by (@kernel_trans X O M)
  as kernel_setoid.

(* ================================================================= *)
(** ** 4. Kernel inclusions and comparisons                           *)
(* ================================================================= *)

Definition kernel_included {X O1 O2 : Type}
    (M1 : X -> O1) (M2 : X -> O2) : Prop :=
  forall x y, kernel M1 x y -> kernel M2 x y.

Lemma kernel_included_refl : forall {X O : Type} (M : X -> O),
    kernel_included M M.
Proof. unfold kernel_included. intros. assumption. Qed.

Lemma kernel_included_trans :
  forall {X O1 O2 O3 : Type}
    (M1 : X -> O1) (M2 : X -> O2) (M3 : X -> O3),
    kernel_included M1 M2 ->
    kernel_included M2 M3 ->
    kernel_included M1 M3.
Proof. unfold kernel_included. intros. auto. Qed.

(* ================================================================= *)
(** ** 5. Congruence: respecting the kernel                          *)
(* ================================================================= *)

Definition respects_kernel {X O Y : Type}
    (M : X -> O) (f : X -> Y) : Prop :=
  forall x y, M x = M y -> f x = f y.

Definition pred_respects_kernel {X O : Type}
    (M : X -> O) (P : X -> Prop) : Prop :=
  forall x y, M x = M y -> (P x <-> P y).

Lemma compose_respects_kernel :
  forall {X O Y Z : Type} (M : X -> O) (f : X -> Y) (g : Y -> Z),
    respects_kernel M f ->
    respects_kernel M (fun x => g (f x)).
Proof.
  intros. unfold respects_kernel in *.
  intros x y Heq. f_equal. apply H. assumption.
Qed.

(* ================================================================= *)
(** ** 6. Kernel equality implies downstream equality                 *)
(* ================================================================= *)

Theorem kernel_eq_downstream :
  forall {X O Y : Type} (M : X -> O) (f : O -> Y) (x y : X),
    kernel M x y ->
    f (M x) = f (M y).
Proof.
  intros X O Y M f x y Hk. unfold kernel in Hk. rewrite Hk. reflexivity.
Qed.

Corollary downstream_distinction_implies_kernel_apart :
  forall {X O Y : Type} (M : X -> O) (f : O -> Y) (x y : X),
    f (M x) <> f (M y) ->
    ~ kernel M x y.
Proof.
  intros X O Y M f x y Hdist Hk. apply Hdist. apply kernel_eq_downstream. assumption.
Qed.

(* ================================================================= *)
(** ** 7. Product kernel                                              *)
(* ================================================================= *)

Definition product_obs {X O1 O2 : Type}
    (M1 : X -> O1) (M2 : X -> O2) : X -> (O1 * O2) :=
  fun x => (M1 x, M2 x).

Lemma product_kernel_intersection :
  forall {X O1 O2 : Type} (M1 : X -> O1) (M2 : X -> O2) (x y : X),
    kernel (product_obs M1 M2) x y <->
    kernel M1 x y /\ kernel M2 x y.
Proof.
  intros. unfold kernel, product_obs.
  split.
  - intro H. injection H as H1 H2. split; assumption.
  - intro H. destruct H as [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

(* ================================================================= *)
(** ** 8. Kernel-based quotient predicates                            *)
(* ================================================================= *)

Definition kernel_constant {X O : Type} (M : X -> O) (P : X -> Prop) : Prop :=
  forall x y, kernel M x y -> (P x <-> P y).

Lemma kernel_constant_neg :
  forall {X O : Type} (M : X -> O) (P : X -> Prop),
    kernel_constant M P -> kernel_constant M (fun x => ~ P x).
Proof.
  unfold kernel_constant. intros. specialize (H x y H0). tauto.
Qed.

Lemma kernel_constant_and :
  forall {X O : Type} (M : X -> O) (P Q : X -> Prop),
    kernel_constant M P ->
    kernel_constant M Q ->
    kernel_constant M (fun x => P x /\ Q x).
Proof.
  unfold kernel_constant. intros.
  specialize (H x y H1). specialize (H0 x y H1). tauto.
Qed.

(* ================================================================= *)
(** ** 9. Decidable kernel pairs                                      *)
(* ================================================================= *)

Definition kernel_dec {X O : Type}
    (O_dec : forall a b : O, {a = b} + {a <> b})
    (M : X -> O) (x y : X) : {kernel M x y} + {~ kernel M x y} :=
  O_dec (M x) (M y).

(* ================================================================= *)
(** ** 10. Boolean kernel                                             *)
(* ================================================================= *)

Definition kernel_bool_constant {X O : Type} (M : X -> O)
    (Phi : X -> bool) : Prop :=
  forall x y, M x = M y -> Phi x = Phi y.

Lemma kernel_bool_constant_iff_respects :
  forall {X O : Type} (M : X -> O) (Phi : X -> bool),
    kernel_bool_constant M Phi <-> respects_kernel M Phi.
Proof.
  split; intros H x y Heq; apply H; assumption.
Qed.

(** Trivial and identity observations. *)
Definition trivial_obs {X : Type} (x : X) : unit := tt.
Definition identity_obs {X : Type} : X -> X := fun x => x.

Definition surjective {X O : Type} (M : X -> O) : Prop :=
  forall o : O, exists x : X, M x = o.
