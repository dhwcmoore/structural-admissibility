(** * MetricResolution.v

    Epsilon-resolution and observational collapse under finite precision.

    At resolution ε, two states within distance ε become observationally
    indistinguishable.  This is NOT generally transitive, so it is not
    an equivalence relation.  The epsilon-chain connected closure is.

    Key theorem: eps_indistinguishable_not_transitive demonstrates that
    finite-precision observation is fundamentally different from equivalence.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.ROrderedType.
From Stdlib Require Import micromega.Lra.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import Classes.RelationClasses.

Open Scope R_scope.

Require Import Foundation.Relations.
Require Import Foundation.Orders.

(* ================================================================= *)
(** ** 1. Pseudo-metric                                               *)
(* ================================================================= *)

Class PseudoMetric (X : Type) := {
  dist          : X -> X -> R;
  dist_nonneg   : forall x y, 0 <= dist x y;
  dist_self     : forall x, dist x x = 0;
  dist_sym      : forall x y, dist x y = dist y x;
  dist_triangle : forall x y z, dist x z <= dist x y + dist y z
}.

(** A metric additionally requires dist x y = 0 -> x = y. *)
Class Metric (X : Type) := {
  #[global] metric_pm :: PseudoMetric X;
  dist_zero     : forall x y, dist x y = 0 -> x = y
}.

(** Every metric is a pseudo-metric. *)

(* ================================================================= *)
(** ** 2. Epsilon-indistinguishability                                *)
(* ================================================================= *)

Definition eps_indistinguishable
    {X : Type} `{PseudoMetric X}
    (eps : R) (x y : X) : Prop :=
  dist x y <= eps.

Lemma eps_indist_refl :
  forall {X : Type} `{PseudoMetric X} (eps : R) (x : X),
    0 <= eps -> eps_indistinguishable eps x x.
Proof.
  intros X PM eps x Heps. unfold eps_indistinguishable.
  rewrite dist_self. exact Heps.
Qed.

Lemma eps_indist_sym :
  forall {X : Type} `{PseudoMetric X} (eps : R) (x y : X),
    eps_indistinguishable eps x y -> eps_indistinguishable eps y x.
Proof.
  intros. unfold eps_indistinguishable in *.
  rewrite dist_sym. assumption.
Qed.

(** The key negative result: eps-indistinguishability is NOT transitive. *)
Theorem eps_indistinguishable_not_transitive :
  exists (X : Type) (pm : PseudoMetric X) (eps : R) (x y z : X),
    eps_indistinguishable eps x y /\
    eps_indistinguishable eps y z /\
    ~ eps_indistinguishable eps x z.
Proof.
  (** Concrete example: X = R with standard metric, eps = 1, x = 0, y = 0.8, z = 1.6. *)
  exists R.
  exists {|
    dist         := fun a b => Rabs (a - b);
    dist_nonneg  := fun a b => Rabs_pos _;
    dist_self    := ltac:(intro a; change (Rabs (a - a) = 0);
                          replace (a - a) with (0 : R) by ring; apply Rabs_R0);
    dist_sym     := fun a b => (Rabs_minus_sym a b);
    dist_triangle := ltac:(intros a b c;
                            change (Rabs (a - c) <= Rabs (a - b) + Rabs (b - c));
                            replace (a - c) with ((a - b) + (b - c)) by ring;
                            apply Rabs_triang)
  |}.
  exists 1. exists 0. exists 0.8. exists 1.6.
  unfold eps_indistinguishable. simpl.
  split; [| split].
  - apply Rabs_le; lra.
  - apply Rabs_le; lra.
  - intro H. rewrite Rabs_left in H by lra. lra.
Qed.

(* ================================================================= *)
(** ** 3. Epsilon-chain connected closure                             *)
(* ================================================================= *)

(** An epsilon-path from x to y is a finite sequence of points,
    each consecutive pair within eps. *)
Definition eps_path {X : Type} `{PseudoMetric X}
    (eps : R) (x y : X) : Prop :=
  exists path : list X,
    (match path with [] => False | p :: _ => p = x end) /\
    last path x = y /\
    forall (i : nat),
      (i + 1 < length path)%nat ->
      dist (nth i path x) (nth (i+1) path x) <= eps.

(** Epsilon-chain connectedness. *)
Inductive eps_chain_connected {X : Type} `{PseudoMetric X} (eps : R)
  : X -> X -> Prop :=
| EpsChain_base : forall x, eps_chain_connected eps x x
| EpsChain_step : forall x y z,
    eps_indistinguishable eps x y ->
    eps_chain_connected eps y z ->
    eps_chain_connected eps x z.

(** Chain connectedness is an equivalence relation. *)
Lemma eps_chain_refl :
  forall {X : Type} `{PseudoMetric X} (eps : R) x,
    eps_chain_connected eps x x.
Proof. intros. constructor. Qed.

Lemma eps_chain_connected_trans :
  forall {X : Type} `{PseudoMetric X} (eps : R) x y z,
    eps_chain_connected eps x y ->
    eps_chain_connected eps y z ->
    eps_chain_connected eps x z.
Proof.
  intros X PM eps x y z H1 H2.
  induction H1 as [x0 | x0 m z0 Hindist Hchain IH].
  - assumption.
  - apply EpsChain_step with (y := m). assumption. apply IH. assumption.
Qed.

Lemma eps_chain_sym :
  forall {X : Type} `{PseudoMetric X} (eps : R) x y,
    eps_chain_connected eps x y ->
    eps_chain_connected eps y x.
Proof.
  intros X PM eps x y H.
  induction H.
  - constructor.
  - apply eps_chain_connected_trans with (y := y).
    + assumption.
    + apply EpsChain_step with (y := x).
      * apply eps_indist_sym. assumption.
      * constructor.
Qed.

Theorem eps_chain_equivalence :
  forall {X : Type} `{PseudoMetric X} (eps : R),
    Equivalence (eps_chain_connected eps).
Proof.
  intros. constructor.
  - intro x. constructor.
  - intros x y. apply eps_chain_sym.
  - intros x y z. apply eps_chain_connected_trans.
Qed.

(* ================================================================= *)
(** ** 4. Resolution-induced observation map                          *)
(* ================================================================= *)

(** At resolution eps, two states are observationally indistinguishable
    if they are eps-chain connected.  This induces a quotient observation. *)

(** The resolution-collapse relation: being chain connected at resolution eps. *)
Definition resolution_collapsed {X : Type} `{PseudoMetric X}
    (eps : R) : X -> X -> Prop :=
  eps_chain_connected eps.

(** Monotonicity: coarser resolution means more collapse. *)
Lemma resolution_monotone :
  forall {X : Type} `{PseudoMetric X} (eps1 eps2 : R) (x y : X),
    eps1 <= eps2 ->
    eps_chain_connected eps1 x y ->
    eps_chain_connected eps2 x y.
Proof.
  intros X PM eps1 eps2 x y Hle H.
  induction H.
  - constructor.
  - apply EpsChain_step with (y := y).
    + unfold eps_indistinguishable in *. lra.
    + assumption.
Qed.

(* ================================================================= *)
(** ** 5. Resolution and safety predicates                            *)
(* ================================================================= *)

(** A boolean safety predicate is resolution-admissible at eps if it is
    constant on eps-chain-connected components. *)
Definition resolution_admissible {X : Type} `{PseudoMetric X}
    (eps : R) (Phi : X -> bool) : Prop :=
  forall x y, eps_chain_connected eps x y -> Phi x = Phi y.

(** Correct statement: coarser resolution (larger eps) is harder to be admissible for. *)
Lemma resolution_admissible_antitone :
  forall {X : Type} `{PseudoMetric X} (eps1 eps2 : R) (Phi : X -> bool),
    eps1 <= eps2 ->
    resolution_admissible eps2 Phi ->
    resolution_admissible eps1 Phi.
Proof.
  intros X PM eps1 eps2 Phi Hle Hadm2.
  unfold resolution_admissible in *.
  intros x y Hchain1.
  apply Hadm2.
  apply resolution_monotone with (eps1 := eps1); assumption.
Qed.

(* ================================================================= *)
(** ** 6. Discrete metric: all non-equal states separated             *)
(* ================================================================= *)

Definition discrete_metric {X : Type} (x y : X) : R :=
  if excluded_middle_informative (x = y) then 0 else 1.

(** Under the discrete metric at epsilon < 1, only identical states collapse. *)
(** Under epsilon >= 1, all states can chain-connect. *)
