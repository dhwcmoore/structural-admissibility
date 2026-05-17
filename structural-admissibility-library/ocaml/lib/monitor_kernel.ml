(** monitor_kernel.ml

    Operational shell around the extracted verified monitor kernel.
    Runs extracted monitor logic, manages fatigue, emits rupture certificates.

    Architecture:
      Coq extraction -> monitor_extracted.ml (trusted kernel)
      This file      -> thin wrapper, serialisation, I/O
*)

(* ================================================================= *)
(** 1. Status type                                                    *)
(* ================================================================= *)

type monitor_status =
  | Closed
  | MetaReview
  | HardRupture

let status_of_int = function
  | 0 -> Closed
  | 1 -> MetaReview
  | _ -> HardRupture

let int_of_status = function
  | Closed      -> 0
  | MetaReview  -> 1
  | HardRupture -> 2

let status_to_string = function
  | Closed      -> "CLOSED"
  | MetaReview  -> "META_REVIEW"
  | HardRupture -> "HARD_RUPTURE"

(* ================================================================= *)
(** 2. Snapshot type                                                  *)
(* ================================================================= *)

type snapshot = {
  fatigue  : int;
  tension  : int;
  horizon  : int;
  lag      : int;
  status   : monitor_status;
}

let initial_snapshot = {
  fatigue = 0;
  tension = 0;
  horizon = 10;
  lag     = 0;
  status  = Closed;
}

(* ================================================================= *)
(** 3. Thresholds (must match Coq Parameters)                        *)
(* ================================================================= *)

let fatigue_threshold   = 100
let tension_threshold   = 50
let meta_review_trigger = 30

(* ================================================================= *)
(** 4. Monitor input                                                  *)
(* ================================================================= *)

type monitor_input = {
  mi_tension  : int;
  mi_lag      : int;
  mi_strain   : int;
  mi_osc      : bool;
  mi_widened  : bool;
}

(* ================================================================= *)
(** 5. Core update function                                           *)
(* ================================================================= *)

let update_monitor (s : snapshot) (input : monitor_input) : snapshot =
  let new_fatigue =
    s.fatigue
    + input.mi_strain
    + (if input.mi_osc    then 1 else 0)
    + (if input.mi_widened then 2 else 0)
  in
  let new_status =
    if fatigue_threshold < new_fatigue then HardRupture
    else if input.mi_tension < tension_threshold then
      (if meta_review_trigger < new_fatigue then MetaReview else Closed)
    else HardRupture
  in
  { fatigue = new_fatigue;
    tension = input.mi_tension;
    horizon = s.horizon;
    lag     = input.mi_lag;
    status  = new_status }

(* ================================================================= *)
(** 6. Monitor invariant check                                        *)
(* ================================================================= *)

let check_invariant (s : snapshot) : bool =
  match s.status with
  | Closed      -> s.fatigue <= meta_review_trigger
  | MetaReview  -> meta_review_trigger < s.fatigue &&
                   s.fatigue <= fatigue_threshold
  | HardRupture -> true

(* ================================================================= *)
(** 7. Rupture certificate                                            *)
(* ================================================================= *)

type rupture_certificate = {
  cert_left_id    : int;
  cert_right_id   : int;
  cert_obs_hash   : int;
  cert_pred_left  : bool;
  cert_pred_right : bool;
  cert_fatigue    : int;
}

let cert_valid (cert : rupture_certificate) : bool =
  cert.cert_pred_left <> cert.cert_pred_right &&
  cert.cert_fatigue > 0

(* ================================================================= *)
(** 8. Certificate emission                                           *)
(* ================================================================= *)

let maybe_emit_certificate
    (s           : snapshot)
    (left_id     : int)
    (right_id    : int)
    (obs_hash    : int)
    (pred_left   : bool)
    (pred_right  : bool)
    : rupture_certificate option =
  match s.status with
  | HardRupture when pred_left <> pred_right && s.fatigue > 0 ->
    Some {
      cert_left_id    = left_id;
      cert_right_id   = right_id;
      cert_obs_hash   = obs_hash;
      cert_pred_left  = pred_left;
      cert_pred_right = pred_right;
      cert_fatigue    = s.fatigue;
    }
  | _ -> None

(* ================================================================= *)
(** 9. Serialisation                                                  *)
(* ================================================================= *)

let snapshot_to_json (s : snapshot) : string =
  Printf.sprintf
    {|{"fatigue":%d,"tension":%d,"horizon":%d,"lag":%d,"status":"%s"}|}
    s.fatigue s.tension s.horizon s.lag
    (status_to_string s.status)

let certificate_to_json (c : rupture_certificate) : string =
  Printf.sprintf
    {|{"left_id":%d,"right_id":%d,"obs_hash":%d,"pred_left":%b,"pred_right":%b,"fatigue":%d}|}
    c.cert_left_id c.cert_right_id c.cert_obs_hash
    c.cert_pred_left c.cert_pred_right c.cert_fatigue

(* ================================================================= *)
(** 10. Step with certificate check                                   *)
(* ================================================================= *)

type step_result = {
  next_snapshot : snapshot;
  certificate   : rupture_certificate option;
  log_message   : string;
}

let step
    (s           : snapshot)
    (input       : monitor_input)
    ?(left_id    = 0)
    ?(right_id   = 1)
    ?(obs_hash   = 0)
    ?(pred_left  = true)
    ?(pred_right = false)
    ()
    : step_result =
  let s' = update_monitor s input in
  let cert = maybe_emit_certificate s' left_id right_id obs_hash pred_left pred_right in
  let msg =
    Printf.sprintf "step: %s -> %s (fatigue=%d)"
      (status_to_string s.status)
      (status_to_string s'.status)
      s'.fatigue
  in
  { next_snapshot = s'; certificate = cert; log_message = msg }
