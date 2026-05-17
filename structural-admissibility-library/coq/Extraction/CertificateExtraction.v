(** * CertificateExtraction.v

    Extractable rupture certificates and their soundness.
*)

Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.

Require Import Runtime.RuptureCertificates.
Require Import Extraction.ExtractableTypes.

(* ================================================================= *)
(** ** 1. Certificate soundness for extractable certs                 *)
(* ================================================================= *)

Theorem extracted_certificate_sound :
  forall cert : ExtractableRuptureCert,
    extracted_cert_valid cert = true ->
    extractable_cert_semantically_valid cert.
Proof.
  intro cert. apply extracted_cert_valid_correct.
Qed.

(* ================================================================= *)
(** ** 2. Certificate builder                                         *)
(* ================================================================= *)

Definition build_extractable_cert
    (pl pr : bool) (fat : nat)
    (Hne : pl <> pr) (Hf : fat > 0) : ExtractableRuptureCert :=
  {| ec_left_id   := 0;
     ec_right_id  := 1;
     ec_obs_hash  := 0;
     ec_pred_left  := pl;
     ec_pred_right := pr;
     ec_fatigue    := fat;
     ec_valid      := conj Hne Hf |}.

Extraction Language OCaml.

Extraction "cert_extracted.ml"
  extracted_cert_valid
  engineering_action_from_certificate
  extractable_cert_semantically_valid
  build_extractable_cert.

