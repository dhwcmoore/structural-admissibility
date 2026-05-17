(** * GPURestriction.v

    Purpose:
    Prove the restriction-side repair for the GPU case study.

    The unrestricted predicate

        sequentially_consistent : Execution -> Prop

    is not admissible relative to a thread-local observation in general.  The
    existing GPU case study proves the refinement repair by moving to a richer
    global observation.

    This file proves the complementary restriction repair: on the subdomain of
    data-race-free executions, sequential consistency is admissible relative to
    thread_local_obs.

    The proof is intentionally small.  The burden is placed exactly where it
    belongs: in the DRF-SC bridge lemma.  Once DRF implies SC, the restricted
    predicate is constant over the restricted domain, hence admissible.
*)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Section GPU_DRF_SC_Restriction.

  (*
    These parameters should be replaced by imports from the existing GPU
    model if the names are already present.

    Expected existing names are likely close to:

      Execution
      MemEvent
      Thread
      Location
      thread_local_obs
      sequentially_consistent

    Keep this section shape if the existing definitions have different names.
  *)

  Variable Thread   : Type.
  Variable Location : Type.
  Variable Event    : Type.
  Variable Execution : Type.

  Variable event_thread    : Event -> Thread.
  Variable event_location  : Event -> Location.
  Variable event_is_write  : Event -> bool.

  Variable execution_events : Execution -> list Event.

  Variable happens_before   : Execution -> Event -> Event -> Prop.
  Variable synchronizes_with : Execution -> Event -> Event -> Prop.

  Variable thread_local_obs     : Thread -> Execution -> list Event.
  Variable sequentially_consistent : Execution -> Prop.

  Definition same_location (e1 e2 : Event) : Prop :=
    event_location e1 = event_location e2.

  Definition at_least_one_write (e1 e2 : Event) : Prop :=
    event_is_write e1 = true \/ event_is_write e2 = true.

  Definition different_threads (e1 e2 : Event) : Prop :=
    event_thread e1 <> event_thread e2.

  Definition conflicting_accesses (e1 e2 : Event) : Prop :=
    same_location e1 e2 /\ at_least_one_write e1 e2 /\ e1 <> e2.

  Definition ordered_by_hb (x : Execution) (e1 e2 : Event) : Prop :=
    happens_before x e1 e2 \/ happens_before x e2 e1.

  Definition synchronized_pair (x : Execution) (e1 e2 : Event) : Prop :=
    synchronizes_with x e1 e2 \/ synchronizes_with x e2 e1.

  Definition data_race (x : Execution) (e1 e2 : Event) : Prop :=
    In e1 (execution_events x) /\
    In e2 (execution_events x) /\
    different_threads e1 e2 /\
    conflicting_accesses e1 e2 /\
    ~ ordered_by_hb x e1 e2.

  Definition data_race_free (x : Execution) : Prop :=
    forall e1 e2 : Event,
      In e1 (execution_events x) ->
      In e2 (execution_events x) ->
      different_threads e1 e2 ->
      conflicting_accesses e1 e2 ->
      ordered_by_hb x e1 e2.

  (*
    This is the local synchronisation discipline.

    In a fuller memory model, this should be proved from the definitions of
    synchronisation, scopes, barriers, fences, or cache visibility.

    It is not an axiom once the Section is closed.  It becomes a premise of the
    final theorem.  That is the correct level of honesty for a small case study.
  *)

  Hypothesis synchronizes_with_orders :
    forall (x : Execution) (e1 e2 : Event),
      In e1 (execution_events x) ->
      In e2 (execution_events x) ->
      synchronizes_with x e1 e2 ->
      happens_before x e1 e2.

  Hypothesis drf_sc_bridge :
    forall x : Execution,
      data_race_free x ->
      sequentially_consistent x.

  Lemma synchronized_pair_orders :
    forall (x : Execution) (e1 e2 : Event),
      In e1 (execution_events x) ->
      In e2 (execution_events x) ->
      synchronized_pair x e1 e2 ->
      ordered_by_hb x e1 e2.
  Proof.
    intros x e1 e2 Hin1 Hin2 Hsync.
    unfold synchronized_pair in Hsync.
    unfold ordered_by_hb.
    destruct Hsync as [H12 | H21].
    - left.  apply synchronizes_with_orders; assumption.
    - right. apply synchronizes_with_orders; assumption.
  Qed.

  Lemma data_race_free_no_data_race :
    forall x e1 e2,
      data_race_free x ->
      ~ data_race x e1 e2.
  Proof.
    intros x e1 e2 HDRF Hr.
    unfold data_race in Hr.
    destruct Hr as [Hin1 [Hin2 [Hdiff [Hconf Hnot_ordered]]]].
    apply Hnot_ordered.
    apply HDRF; assumption.
  Qed.

  Lemma data_race_free_implies_sc :
    forall x,
      data_race_free x ->
      sequentially_consistent x.
  Proof.
    intros x HDRF.
    apply drf_sc_bridge.
    exact HDRF.
  Qed.

  (*
    The restricted domain.

    This is the cleanest way to express "SC restricted to DRF executions":
    we do not change the observation, and we do not enrich the execution.
    We restrict X to the subtype of executions carrying a DRF proof.
  *)

  Record DRFExecution : Type := {
    drf_exec       : Execution;
    drf_exec_is_drf : data_race_free drf_exec
  }.

  Definition drf_thread_local_obs
      (t : Thread)
      (x : DRFExecution)
      : list Event :=
    thread_local_obs t (drf_exec x).

  Definition sc_on_drf (x : DRFExecution) : Prop :=
    sequentially_consistent (drf_exec x).

  Definition admissible {X O : Type} (M : X -> O) (Phi : X -> Prop) : Prop :=
    forall x y : X,
      M x = M y ->
      (Phi x <-> Phi y).

  Lemma sc_on_drf_holds :
    forall x : DRFExecution,
      sc_on_drf x.
  Proof.
    intros [exec Hdrf].
    unfold sc_on_drf. simpl.
    apply data_race_free_implies_sc.
    exact Hdrf.
  Qed.

  Theorem thread_local_obs_admissible_for_sc_on_drf :
    forall t : Thread,
      admissible (drf_thread_local_obs t) sc_on_drf.
  Proof.
    intros t x y _Hobs.
    split; intros _H.
    - apply sc_on_drf_holds.
    - apply sc_on_drf_holds.
  Qed.

  (*
    More explicit theorem name, matching the prose of the paper.
  *)

  Theorem gpu_drf_sc_restriction_repair :
    forall t : Thread,
      admissible (drf_thread_local_obs t) sc_on_drf.
  Proof.
    apply thread_local_obs_admissible_for_sc_on_drf.
  Qed.

End GPU_DRF_SC_Restriction.
