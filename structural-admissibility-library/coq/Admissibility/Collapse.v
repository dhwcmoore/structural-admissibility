(** * Collapse.v

    Formalisation of observational collapse and its connection to inadmissibility.

    Central theorem (safety_relevant_collapse_iff_inadmissible):
        safety_relevant_collapse Phi M
        <->
        ~ boolean_admissible Phi M.

    This theorem is a centrepiece of the library.
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
(** ** 1. Collapse definitions                                        *)
(* ================================================================= *)

(** Two distinct states are collapsed by M. *)
Definition collapses_pair {X O : Type}
    (M : X -> O) (x y : X) : Prop :=
  x <> y /\ M x = M y.

(** M collapses some pair. *)
Definition has_collapse {X O : Type} (M : X -> O) : Prop :=
  exists x y, collapses_pair M x y.

(** M collapses a safety-relevant pair: same observation, different predicate value. *)
Definition safety_relevant_collapse {X O : Type}
    (Phi : X -> bool) (M : X -> O) : Prop :=
  exists x y,
    M x = M y /\
    Phi x <> Phi y.

(* ================================================================= *)
(** ** 2. Central theorem                                             *)
(* ================================================================= *)

(** Safety-relevant collapse is equivalent to inadmissibility. *)
Theorem safety_relevant_collapse_iff_inadmissible :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    safety_relevant_collapse Phi M
    <->
    ~ boolean_admissible Phi M.
Proof.
  intros X O Phi M. split.
  - intros [x [y [Hobs Hpred]]] [Phi_hat Hfact].
    apply Hpred.
    rewrite Hfact, Hfact, Hobs. reflexivity.
  - intro Hinadm.
    apply inadmissible_implies_witness. assumption.
Qed.

(* ================================================================= *)
(** ** 3. Collapse degrees                                            *)
(* ================================================================= *)

(** Number of collapsing observation equivalence classes that contain
    safety-relevant pairs. *)

Definition collapse_witnessed {X O : Type}
    (Phi : X -> bool) (M : X -> O) : Prop :=
  exists x y,
    M x = M y /\
    Phi x = true /\
    Phi y = false.

Lemma collapse_witnessed_implies_safety_relevant_collapse :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    collapse_witnessed Phi M ->
    safety_relevant_collapse Phi M.
Proof.
  intros X O Phi M [x [y [Hobs [HPx HPy]]]].
  exists x. exists y. split.
  - assumption.
  - rewrite HPx, HPy. discriminate.
Qed.

Lemma safety_relevant_collapse_implies_witnessed :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    safety_relevant_collapse Phi M ->
    collapse_witnessed Phi M \/ collapse_witnessed (fun x => negb (Phi x)) M.
Proof.
  intros X O Phi M [x [y [Hobs Hne]]].
  destruct (Bool.bool_dec (Phi x) true) as [Htx | Hfx];
  destruct (Bool.bool_dec (Phi y) true) as [Hty | Hfy].
  - exfalso. apply Hne. rewrite Htx, Hty. reflexivity.
  - left. exists x. exists y.
    split. assumption.
    split. assumption.
    destruct (Phi y); [exfalso; apply Hfy; reflexivity | reflexivity].
  - right. exists x. exists y.
    split. assumption. split.
    + destruct (Phi x); [exfalso; apply Hfx; reflexivity | reflexivity].
    + rewrite Hty. reflexivity.
  - exfalso. apply Hne.
    destruct (Phi x); [contradiction | ].
    destruct (Phi y); [contradiction | reflexivity].
Qed.

(* ================================================================= *)
(** ** 4. Collapse under composition                                  *)
(* ================================================================= *)

(** Post-composing M with any f does not remove safety-relevant collapse. *)
Theorem postcompose_preserves_collapse :
  forall {X O Y : Type}
    (M : X -> O)
    (f : O -> Y)
    (Phi : X -> bool),
    safety_relevant_collapse Phi M ->
    safety_relevant_collapse Phi (fun x => f (M x)).
Proof.
  intros X O Y M f Phi [x [y [Hobs Hne]]].
  exists x. exists y. split.
  - rewrite Hobs. reflexivity.
  - assumption.
Qed.

(** Therefore: post-processing the observation cannot repair inadmissibility. *)
Corollary postprocessing_preserves_inadmissibility :
  forall {X O Y : Type}
    (M : X -> O)
    (f : O -> Y)
    (Phi : X -> bool),
    boolean_inadmissible Phi M ->
    boolean_inadmissible Phi (fun x => f (M x)).
Proof.
  intros X O Y M f Phi Hinadm.
  apply safety_relevant_collapse_iff_inadmissible.
  apply postcompose_preserves_collapse.
  apply safety_relevant_collapse_iff_inadmissible.
  assumption.
Qed.

(* ================================================================= *)
(** ** 5. Collapse under coarsening                                   *)
(* ================================================================= *)

(** If M1 collapses a safety-relevant pair and M2 refines M1, then M1
    still collapses the pair — but M2 might not.  Coarsening can create
    new safety-relevant collapses. *)

Lemma coarsening_can_create_collapse :
  exists (X : Type) (O1 O2 : Type)
    (M1 : X -> O1) (M2 : X -> O2) (Phi : X -> bool),
    refines M2 M1 /\   (* M2 refines M1, i.e., M2 is finer *)
    safety_relevant_collapse Phi M1 /\
    ~ safety_relevant_collapse Phi M2.
Proof.
  (** Same construction as admissibility_not_antitone in Refinement.v. *)
  exists nat. exists nat. exists nat.
  exists (fun x => Nat.modulo x 2).
  exists (fun x => x).
  exists (fun x => if Nat.leb x 1 then true else false).
  split; [| split].
  - unfold refines. intros x y Heq. rewrite Heq. reflexivity.
  - exists 0. exists 2. split. simpl. reflexivity. simpl. discriminate.
  - intros [x [y [Hobs Hne]]].
    apply Hne.
    simpl in Hobs. rewrite Hobs. reflexivity.
Qed.

(* ================================================================= *)
(** ** 6. Safe collapse: structural collapse vs safety collapse       *)
(* ================================================================= *)

(** A collapse is safe when the collapsed states agree on the safety predicate. *)
Definition safe_collapse {X O : Type}
    (Phi : X -> bool) (M : X -> O) (x y : X) : Prop :=
  M x = M y /\ Phi x = Phi y.

(** A map has only safe collapses iff Phi is admissible. *)
Theorem only_safe_collapses_iff_admissible :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    (forall x y, M x = M y -> safe_collapse Phi M x y)
    <->
    boolean_admissible Phi M.
Proof.
  intros X O Phi M. split.
  - intro Hall.
    apply constant_on_kernel_implies_admissible.
    intros x y Heq.
    exact (proj2 (Hall x y Heq)).
  - intros Hadm x y Heq.
    unfold safe_collapse. split.
    + assumption.
    + apply (admissible_implies_constant_on_kernel Hadm). assumption.
Qed.
