# Runtime Rupture Certificates

## Concept

A rupture certificate is a machine-checkable record proving structural
inadmissibility at runtime.  It connects the static theory (Factorisation.v)
to the runtime monitor (MonitorStates.v).

## Certificate Structure

```coq
Record RuptureCertificate {X O} (Phi : X -> bool) (M : X -> O) := {
  cert_left                   : X;
  cert_right                  : X;
  cert_same_observation       : M cert_left = M cert_right;
  cert_predicate_disagreement : Phi cert_left <> Phi cert_right;
  cert_fatigue                : nat;
  cert_fatigue_positive       : cert_fatigue > 0
}.
```

## Soundness Theorem

```coq
Theorem rupture_certificate_sound :
  forall {X O} (Phi : X -> bool) (M : X -> O),
    RuptureCertificate Phi M ->
    ~ boolean_admissible Phi M.
```

## Extractable Version

```coq
Record ExtractableRuptureCert := {
  ec_left_id    : nat;
  ec_right_id   : nat;
  ec_obs_hash   : nat;
  ec_pred_left  : bool;
  ec_pred_right : bool;
  ec_fatigue    : nat;
  ec_valid      : ec_pred_left <> ec_pred_right /\ ec_fatigue > 0
}.
```

Checked by:
```coq
Definition extracted_cert_valid (cert : ExtractableRuptureCert) : bool :=
  negb (Bool.eqb (ec_pred_left cert) (ec_pred_right cert)) &&
  Nat.ltb 0 (ec_fatigue cert).

Theorem extracted_cert_valid_correct :
  forall cert, extracted_cert_valid cert = true <->
               extractable_cert_semantically_valid cert.
```

## File Locations

- `coq/Runtime/RuptureCertificates.v`
- `coq/Extraction/CertificateExtraction.v`
- `ocaml/lib/rupture_cert.ml`
- `ocaml/lib/cert_parser.ml`
