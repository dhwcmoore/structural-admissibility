(** * TopologyCore.v

    Minimal topological structures needed for admissibility theory:
    open sets, continuity, and the connection between topological separation
    and observational collapse.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Logic.Classical_Prop.
Require Import Foundation.Relations.
Require Import Foundation.Orders.

(* ================================================================= *)
(** ** 1. Topology via open sets                                      *)
(* ================================================================= *)

Record Topology (X : Type) := {
  is_open     : (X -> Prop) -> Prop;
  open_empty  : is_open (fun _ => False);
  open_full   : is_open (fun _ => True);
  open_inter  : forall U V, is_open U -> is_open V ->
                  is_open (fun x => U x /\ V x);
  open_union  : forall (F : (X -> Prop) -> Prop),
                  (forall U, F U -> is_open U) ->
                  is_open (fun x => exists U, F U /\ U x)
}.

(* ================================================================= *)
(** ** 2. Continuous maps                                             *)
(* ================================================================= *)

Definition continuous {X Y : Type}
    (TX : Topology X) (TY : Topology Y)
    (f : X -> Y) : Prop :=
  forall V, is_open TY V -> is_open TX (fun x => V (f x)).

(* ================================================================= *)
(** ** 3. Topological separation (T0, T1, T2)                        *)
(* ================================================================= *)

Definition T0_sep {X : Type} (TX : Topology X) : Prop :=
  forall x y, x <> y ->
    exists U, is_open TX U /\ (U x /\ ~ U y \/ ~ U x /\ U y).

Definition T1_sep {X : Type} (TX : Topology X) : Prop :=
  forall x y, x <> y ->
    exists U, is_open TX U /\ U x /\ ~ U y.

Definition T2_sep {X : Type} (TX : Topology X) : Prop :=
  forall x y, x <> y ->
    exists U V, is_open TX U /\ is_open TX V /\
      U x /\ V y /\ (forall z, ~ (U z /\ V z)).

(* ================================================================= *)
(** ** 4. Topology induced by an observation map                      *)
(* ================================================================= *)

(** The coarsest topology on X making M continuous. *)
Definition induced_topology {X O : Type}
    (TO : Topology O) (M : X -> O) : Topology X.
Proof.
  refine {|
    is_open := fun U => exists V, is_open TO V /\ forall x, U x <-> V (M x)
  |}.
  - exists (fun _ => False). split.
    + apply open_empty.
    + intro x. tauto.
  - exists (fun _ => True). split.
    + apply open_full.
    + intro x. tauto.
  - intros U V [VU [HoU HU]] [VV [HoV HV]].
    exists (fun o => VU o /\ VV o). split.
    + apply open_inter; assumption.
    + intro x. rewrite HU, HV. tauto.
  - intros F HF.
    exists (fun o => exists V : O -> Prop,
        (is_open TO V /\ (exists U : X -> Prop, F U /\ (forall x, U x <-> V (M x)))) /\ V o).
    split.
    + apply open_union.
      intros V [HoV _]. exact HoV.
    + intro x. split.
      * intros [U [HFU HUx]].
        destruct (HF U HFU) as [V [HoV HV]].
        exists V. split.
        -- split. exact HoV. exists U. split. assumption. assumption.
        -- apply HV. assumption.
      * intros [V [[HoV [U [HFU HUV]]] HVMx]].
        exists U. split. assumption. apply HUV. assumption.
Defined.

(** The induced topology is the coarsest making M continuous. *)
Theorem induced_topology_continuous :
  forall {X O : Type} (TO : Topology O) (M : X -> O),
    continuous (induced_topology TO M) TO M.
Proof.
  intros X O TO M V HoV.
  unfold continuous. simpl.
  exists V. split. assumption. intro x. tauto.
Qed.

(* ================================================================= *)
(** ** 5. Topological collapse and admissibility                      *)
(* ================================================================= *)

(** Two points are topologically indistinguishable when every open set
    containing one contains the other. *)
Definition topo_indistinguishable {X : Type} (TX : Topology X) (x y : X) : Prop :=
  forall U, is_open TX U -> (U x <-> U y).

(** Topological indistinguishability is an equivalence relation. *)
Lemma topo_indist_refl : forall {X : Type} (TX : Topology X) x,
    topo_indistinguishable TX x x.
Proof. intros. unfold topo_indistinguishable. tauto. Qed.

Lemma topo_indist_sym : forall {X : Type} (TX : Topology X) x y,
    topo_indistinguishable TX x y -> topo_indistinguishable TX y x.
Proof.
  unfold topo_indistinguishable. intros. symmetry. apply H. assumption.
Qed.

Lemma topo_indist_trans : forall {X : Type} (TX : Topology X) x y z,
    topo_indistinguishable TX x y ->
    topo_indistinguishable TX y z ->
    topo_indistinguishable TX x z.
Proof.
  unfold topo_indistinguishable. intros.
  rewrite H; auto.
Qed.

(** In a T0 space, topological indistinguishability implies equality. *)
Theorem T0_indist_implies_eq :
  forall {X : Type} (TX : Topology X),
    T0_sep TX ->
    forall x y, topo_indistinguishable TX x y -> x = y.
Proof.
  intros X TX HT0 x y Hindist.
  apply Classical_Prop.NNPP. intro Hne.
  destruct (HT0 x y Hne) as [U [HoU HsepU]].
  specialize (Hindist U HoU).
  tauto.
Qed.

(* ================================================================= *)
(** ** 6. Open-set image: admissible open sets                        *)
(* ================================================================= *)

(** An open set U in X is M-admissible if it is a pullback of an open
    set in O along M. *)
Definition M_admissible_open {X O : Type}
    (TO : Topology O) (M : X -> O)
    (U : X -> Prop) : Prop :=
  exists V, is_open TO V /\ forall x, U x <-> V (M x).

Lemma M_admissible_open_kernel_constant :
  forall {X O : Type} (TO : Topology O) (M : X -> O) (U : X -> Prop),
    M_admissible_open TO M U ->
    forall x y, M x = M y -> (U x <-> U y).
Proof.
  intros X O TO M U [V [_ HV]] x y Heq.
  rewrite HV, HV, Heq. tauto.
Qed.

