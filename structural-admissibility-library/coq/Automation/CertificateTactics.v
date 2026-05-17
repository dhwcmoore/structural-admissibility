(** * CertificateTactics.v

    Tactics for building rupture certificates from witnesses.
    Useful for case studies and extraction.
*)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.

Require Import Foundation.Relations.
Require Import Admissibility.Factorisation.
Require Import Admissibility.AdmissibilityBase.
Require Import Admissibility.WarrantDebt.
Require Import Runtime.RuptureCertificates.

(* ================================================================= *)
(** ** 1. Certificate construction                                    *)
(* ================================================================= *)

Ltac build_rupture_certificate l r fat :=
  refine {| cert_left                   := l;
            cert_right                  := r;
            cert_same_observation       := _;
            cert_predicate_disagreement := _;
            cert_fatigue                := fat;
            cert_fatigue_positive       := _ |};
  [simpl; try reflexivity | try discriminate | lia].

Ltac build_extractable_cert pl pr fat :=
  refine {| ec_left_id   := 0;
            ec_right_id  := 1;
            ec_obs_hash  := 0;
            ec_pred_left  := pl;
            ec_pred_right := pr;
            ec_fatigue    := fat;
            ec_valid      := _ |};
  split; [try discriminate | lia].

(* ================================================================= *)
(** ** 2. Certificate soundness discharge                             *)
(* ================================================================= *)

Ltac discharge_certificate_soundness :=
  apply rupture_certificate_sound; assumption.

Hint Resolve rupture_certificate_sound : certificates.
Hint Resolve certificate_implies_warrant_debt : certificates.
Hint Resolve certificate_implies_collapse : certificates.

