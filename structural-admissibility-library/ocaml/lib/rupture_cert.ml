(** rupture_cert.ml

    Rupture certificate types, validation, and construction.
*)

open Monitor_kernel

(* ================================================================= *)
(** 1. Certificate validation                                         *)
(* ================================================================= *)

let validate (cert : rupture_certificate) : (unit, string) result =
  if cert.cert_pred_left = cert.cert_pred_right then
    Error "certificate invalid: predicate values agree"
  else if cert.cert_fatigue <= 0 then
    Error "certificate invalid: fatigue must be positive"
  else
    Ok ()

(* ================================================================= *)
(** 2. Certificate comparison                                         *)
(* ================================================================= *)

let equal (c1 : rupture_certificate) (c2 : rupture_certificate) : bool =
  c1.cert_left_id    = c2.cert_left_id    &&
  c1.cert_right_id   = c2.cert_right_id   &&
  c1.cert_obs_hash   = c2.cert_obs_hash   &&
  c1.cert_pred_left  = c2.cert_pred_left  &&
  c1.cert_pred_right = c2.cert_pred_right &&
  c1.cert_fatigue    = c2.cert_fatigue

(* ================================================================= *)
(** 3. Certificate from collapse pair                                 *)
(* ================================================================= *)

let of_collapse_pair
    ~left_id ~right_id ~obs_hash ~pred_left ~pred_right ~fatigue
    : (rupture_certificate, string) result =
  if pred_left = pred_right then
    Error "not a collapse: predicates agree"
  else if fatigue <= 0 then
    Error "fatigue must be positive"
  else
    Ok {
      cert_left_id    = left_id;
      cert_right_id   = right_id;
      cert_obs_hash   = obs_hash;
      cert_pred_left  = pred_left;
      cert_pred_right = pred_right;
      cert_fatigue    = fatigue;
    }

(* ================================================================= *)
(** 4. Pretty printing                                                *)
(* ================================================================= *)

let pp (c : rupture_certificate) : string =
  Printf.sprintf
    "RuptureCert{left=%d, right=%d, obs_hash=%d, pred_l=%b, pred_r=%b, fatigue=%d}"
    c.cert_left_id c.cert_right_id c.cert_obs_hash
    c.cert_pred_left c.cert_pred_right c.cert_fatigue
