(** * RuptureCertificates.v

    Machine-checkable rupture certificates.

    A rupture certificate is a record containing:
    - two states that are kernel-equal,
    - a proof that their predicate values differ,
    - a positive fatigue level.

    Key theorem (rupture_certificate_sound):
        RuptureCertificate Phi M -> ~ boolean_admissible Phi M.

    This is one of the key publishable theorems.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Logic.Classical_Prop.

Require Import Foundation.Relations.
Require Import Admissibility.ObservationMaps.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.Collapse.
Require Import Admissibility.WarrantDebt.
Require Import Runtime.MonitorStates.

(* ================================================================= *)
(** ** 1. Rupture certificate record                                  *)
(* ================================================================= *)

Record RuptureCertificate {X O : Type}
    (Phi : X -> bool)
    (M   : X -> O) := {
  cert_left              : X;
  cert_right             : X;
  cert_same_observation  : M cert_left = M cert_right;
  cert_predicate_disagreement : Phi cert_left <> Phi cert_right;
  cert_fatigue           : nat;
  cert_fatigue_positive  : cert_fatigue > 0
}.

(* ================================================================= *)
(** ** 2. Certificate soundness                                       *)
(* ================================================================= *)

Theorem rupture_certificate_sound :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    RuptureCertificate Phi M ->
    ~ boolean_admissible Phi M.
Proof.
  intros X O Phi M cert.
  intros [Phi_hat Hfact].
  destruct cert as [l r Hcol Hne fat Hfat].
  apply Hne.
  rewrite (Hfact l), (Hfact r), Hcol. reflexivity.
Qed.

(** The certificate also witnesses structural inadmissibility. *)
Corollary certificate_implies_warrant_debt :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    RuptureCertificate Phi M ->
    has_warrant_debt Phi M.
Proof.
  intros X O Phi M cert.
  apply rupture_certificate_sound in cert.
  unfold has_warrant_debt. assumption.
Qed.

(** The certificate implies safety-relevant collapse. *)
Corollary certificate_implies_collapse :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O),
    RuptureCertificate Phi M ->
    safety_relevant_collapse Phi M.
Proof.
  intros X O Phi M cert.
  apply safety_relevant_collapse_iff_inadmissible.
  apply rupture_certificate_sound. assumption.
Qed.

(* ================================================================= *)
(** ** 3. Certificate construction from collapse witness              *)
(* ================================================================= *)

Definition cert_from_witness {X O : Type}
    (Phi : X -> bool) (M : X -> O)
    (w   : WarrantDebtWitness Phi M)
    (fat : nat)
    (Hf  : fat > 0) : RuptureCertificate Phi M :=
  match w with
  | {| wd_left := l; wd_right := r;
       wd_collapsed := Hcol; wd_disagrees := Hne |} =>
    {| cert_left                  := l;
       cert_right                 := r;
       cert_same_observation      := Hcol;
       cert_predicate_disagreement := Hne;
       cert_fatigue               := fat;
       cert_fatigue_positive      := Hf |}
  end.

Theorem cert_from_witness_sound :
  forall {X O : Type} (Phi : X -> bool) (M : X -> O)
    (w : WarrantDebtWitness Phi M) (fat : nat) (Hf : fat > 0),
    ~ boolean_admissible Phi M.
Proof.
  intros X O Phi M w fat Hf.
  apply rupture_certificate_sound.
  exact (cert_from_witness w Hf).
Qed.

(* ================================================================= *)
(** ** 4. Certificate serialisation record                            *)
(* ================================================================= *)

(** Extractable certificate: uses nat identifiers and boolean values
    instead of type-polymorphic state. *)
Record ExtractableRuptureCert := {
  ec_left_id    : nat;
  ec_right_id   : nat;
  ec_obs_hash   : nat;   (** hash of the shared observation value *)
  ec_pred_left  : bool;
  ec_pred_right : bool;
  ec_fatigue    : nat;
  ec_valid      : ec_pred_left <> ec_pred_right /\
                  ec_fatigue > 0
}.

(** Semantic validity of an extractable certificate. *)
Definition extractable_cert_semantically_valid
    (cert : ExtractableRuptureCert) : Prop :=
  ec_pred_left cert <> ec_pred_right cert /\
  ec_fatigue cert > 0.

Theorem extractable_cert_sound :
  forall cert : ExtractableRuptureCert,
    extractable_cert_semantically_valid cert.
Proof.
  intro cert. apply ec_valid.
Qed.

(* ================================================================= *)
(** ** 5. Certificate validity checking function                      *)
(* ================================================================= *)

Definition extracted_cert_valid (cert : ExtractableRuptureCert) : bool :=
  negb (Bool.eqb (ec_pred_left cert) (ec_pred_right cert)) &&
  Nat.ltb 0 (ec_fatigue cert).

Theorem extracted_cert_valid_correct :
  forall cert,
    extracted_cert_valid cert = true <->
    extractable_cert_semantically_valid cert.
Proof.
  intro cert.
  unfold extracted_cert_valid, extractable_cert_semantically_valid.
  split.
  - intro H.
    apply Bool.andb_true_iff in H. destruct H as [Hneq Hfat].
    split.
    + destruct (ec_pred_left cert), (ec_pred_right cert);
        simpl in Hneq; try discriminate; try congruence.
    + apply Nat.ltb_lt in Hfat. assumption.
  - intros [Hneq Hfat].
    apply Bool.andb_true_iff. split.
    + destruct (ec_pred_left cert), (ec_pred_right cert);
        simpl; try reflexivity; try (exfalso; apply Hneq; reflexivity).
    + apply Nat.ltb_lt. assumption.
Qed.

(* ================================================================= *)
(** ** 6. Hard rupture implies certificate                            *)
(* ================================================================= *)

(** If a trace reaches HARD_RUPTURE and there was a collapse event,
    a rupture certificate can be extracted. *)

Definition rupture_trace_has_cert {X O : Type}
    (Phi : X -> bool) (M : X -> O)
    (trace : Trace)
    (s : MonitorSnapshot) : Prop :=
  reaches_hard_rupture trace s ->
  exists cert : RuptureCertificate Phi M,
    cert_fatigue cert = fatigue s.

(** This is the key linking theorem between the runtime monitor and the
    static admissibility theory.  Full proof requires connecting the monitor
    state machine to the admissibility witness — see RuntimeSoundness.v. *)

