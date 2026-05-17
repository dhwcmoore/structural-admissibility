(** sensor_adapter.ml

    Convert external sensor traces into formal monitor inputs.
    Carries explicit uncertainty about the mapping from raw readings
    to formal types.
*)

open Monitor_kernel

(* ================================================================= *)
(** 1. Raw sensor reading                                             *)
(* ================================================================= *)

type raw_sensor_reading = {
  sensor_id  : string;
  value      : float;
  timestamp  : int;
  confidence : float;   (** 0.0 to 1.0: confidence in the reading *)
}

(* ================================================================= *)
(** 2. Conversion parameters                                         *)
(* ================================================================= *)

type adapter_config = {
  tension_scale    : float;   (** multiplier: raw -> tension *)
  lag_base         : int;     (** base latency in timesteps *)
  strain_per_unit  : float;   (** raw delta -> strain *)
  oscillation_threshold : float;  (** delta above which oscillation is counted *)
  widening_threshold    : float;  (** broadening above which widening is counted *)
  min_confidence   : float;   (** readings below this are discarded *)
}

let default_config = {
  tension_scale         = 10.0;
  lag_base              = 1;
  strain_per_unit       = 1.0;
  oscillation_threshold = 5.0;
  widening_threshold    = 3.0;
  min_confidence        = 0.7;
}

(* ================================================================= *)
(** 3. Adapter state (tracks previous reading for delta)             *)
(* ================================================================= *)

type adapter_state = {
  prev_value      : float;
  prev_timestamp  : int;
}

let initial_adapter_state = {
  prev_value     = 0.0;
  prev_timestamp = 0;
}

(* ================================================================= *)
(** 4. Conversion function                                           *)
(* ================================================================= *)

let convert
    (cfg   : adapter_config)
    (state : adapter_state)
    (r     : raw_sensor_reading)
    : (monitor_input * adapter_state) option =
  if r.confidence < cfg.min_confidence then None
  else begin
    let delta = abs_float (r.value -. state.prev_value) in
    let strain  = int_of_float (delta *. cfg.strain_per_unit) in
    let osc     = delta > cfg.oscillation_threshold in
    let widened = delta > cfg.widening_threshold in
    let tension = int_of_float (r.value *. cfg.tension_scale) in
    let lag     = cfg.lag_base + (r.timestamp - state.prev_timestamp) in
    let input = {
      mi_tension  = tension;
      mi_lag      = max 0 lag;
      mi_strain   = strain;
      mi_osc      = osc;
      mi_widened  = widened;
    } in
    let new_state = {
      prev_value     = r.value;
      prev_timestamp = r.timestamp;
    } in
    Some (input, new_state)
  end

(* ================================================================= *)
(** 5. Batch conversion                                              *)
(* ================================================================= *)

let convert_trace
    (cfg    : adapter_config)
    (readings : raw_sensor_reading list)
    : monitor_input list =
  let _, inputs =
    List.fold_left
      (fun (state, acc) r ->
         match convert cfg state r with
         | None -> (state, acc)
         | Some (input, state') -> (state', input :: acc))
      (initial_adapter_state, [])
      readings
  in
  List.rev inputs

(* ================================================================= *)
(** 6. Uncertainty annotation                                        *)
(* ================================================================= *)

type uncertain_input = {
  input       : monitor_input;
  confidence  : float;
  source_id   : string;
}

let with_uncertainty
    (cfg   : adapter_config)
    (state : adapter_state)
    (r     : raw_sensor_reading)
    : (uncertain_input * adapter_state) option =
  match convert cfg state r with
  | None -> None
  | Some (input, state') ->
    Some ({ input; confidence = r.confidence; source_id = r.sensor_id }, state')
