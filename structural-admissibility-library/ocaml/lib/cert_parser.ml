(** cert_parser.ml

    Parse JSON certificate strings into typed OCaml values.

    Architecture (from spec):
    1. Handwritten parser converts JSON into untrusted raw data.
    2. Extracted verifier (cert_valid) checks semantic validity.
    3. Only verified certificates are accepted.

    This parser is part of the TRUSTED COMPUTING BASE only if used
    in a verified context.  Untrusted input goes through validate.
*)

open Monitor_kernel

(* ================================================================= *)
(** 1. Raw parsed record (unverified)                                 *)
(* ================================================================= *)

type raw_cert = {
  raw_left_id    : int option;
  raw_right_id   : int option;
  raw_obs_hash   : int option;
  raw_pred_left  : bool option;
  raw_pred_right : bool option;
  raw_fatigue    : int option;
}

let empty_raw = {
  raw_left_id    = None;
  raw_right_id   = None;
  raw_obs_hash   = None;
  raw_pred_left  = None;
  raw_pred_right = None;
  raw_fatigue    = None;
}

(* ================================================================= *)
(** 2. Minimal JSON parser (no dependencies)                         *)
(* ================================================================= *)

let trim s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n && s.[!i] = ' ' do incr i done;
  let j = ref (n - 1) in
  while !j >= 0 && s.[!j] = ' ' do decr j done;
  if !i > !j then "" else String.sub s !i (!j - !i + 1)

let parse_int_field (s : string) : int option =
  try Some (int_of_string (trim s)) with _ -> None

let parse_bool_field (s : string) : bool option =
  match trim s with
  | "true"  -> Some true
  | "false" -> Some false
  | _ -> None

let split_on_char c s =
  let n = String.length s in
  let acc = ref [] in
  let buf = Buffer.create 16 in
  for i = 0 to n - 1 do
    if s.[i] = c then begin
      acc := Buffer.contents buf :: !acc;
      Buffer.clear buf
    end else
      Buffer.add_char buf s.[i]
  done;
  acc := Buffer.contents buf :: !acc;
  List.rev !acc

let strip_quotes s =
  let s = trim s in
  let n = String.length s in
  if n >= 2 && s.[0] = '"' && s.[n-1] = '"'
  then String.sub s 1 (n - 2)
  else s

let parse_kv_pair (s : string) : (string * string) option =
  match split_on_char ':' s with
  | [k; v] -> Some (strip_quotes k, trim v)
  | k :: rest ->
    Some (strip_quotes k, trim (String.concat ":" rest))
  | _ -> None

let parse_json_object (json : string) : (string * string) list =
  let n = String.length json in
  let content =
    if n >= 2 && json.[0] = '{' && json.[n-1] = '}'
    then String.sub json 1 (n - 2)
    else json
  in
  List.filter_map parse_kv_pair (split_on_char ',' content)

(* ================================================================= *)
(** 3. Parse JSON string into raw_cert                               *)
(* ================================================================= *)

let parse_raw (json : string) : raw_cert =
  List.fold_left
    (fun acc (k, v) ->
       match k with
       | "left_id"    -> { acc with raw_left_id    = parse_int_field v }
       | "right_id"   -> { acc with raw_right_id   = parse_int_field v }
       | "obs_hash"   -> { acc with raw_obs_hash   = parse_int_field v }
       | "pred_left"  -> { acc with raw_pred_left  = parse_bool_field v }
       | "pred_right" -> { acc with raw_pred_right = parse_bool_field v }
       | "fatigue"    -> { acc with raw_fatigue    = parse_int_field v }
       | _ -> acc)
    empty_raw
    (parse_json_object json)

(* ================================================================= *)
(** 4. Validate and convert raw cert                                  *)
(* ================================================================= *)

let of_json (json : string) : (rupture_certificate, string) result =
  let raw = parse_raw json in
  match raw.raw_left_id, raw.raw_right_id, raw.raw_obs_hash,
        raw.raw_pred_left, raw.raw_pred_right, raw.raw_fatigue with
  | Some li, Some ri, Some oh, Some pl, Some pr, Some fat ->
    let cert = {
      cert_left_id    = li;
      cert_right_id   = ri;
      cert_obs_hash   = oh;
      cert_pred_left  = pl;
      cert_pred_right = pr;
      cert_fatigue    = fat;
    } in
    (* Step 2: semantic validation via the extracted verifier *)
    if cert_valid cert then Ok cert
    else Error "certificate fails semantic validation"
  | _ ->
    Error "missing required fields in certificate JSON"

(* ================================================================= *)
(** 5. Parse snapshot JSON                                            *)
(* ================================================================= *)

let snapshot_of_json (json : string) : (snapshot, string) result =
  let kvs = parse_json_object json in
  let get k =
    match List.assoc_opt k kvs with
    | Some v -> parse_int_field v
    | None   -> None
  in
  let status_of_str s =
    match strip_quotes (trim s) with
    | "CLOSED"       -> Some Closed
    | "META_REVIEW"  -> Some MetaReview
    | "HARD_RUPTURE" -> Some HardRupture
    | _ -> None
  in
  match get "fatigue", get "tension", get "horizon", get "lag",
        (List.assoc_opt "status" kvs |> Option.map status_of_str |> Option.join) with
  | Some f, Some t, Some h, Some l, Some st ->
    Ok { fatigue = f; tension = t; horizon = h; lag = l; status = st }
  | _ ->
    Error "missing required fields in snapshot JSON"
