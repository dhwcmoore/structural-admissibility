(** monitor_cli.ml

    Command-line interface for the structural admissibility monitor.
    Reads JSON monitor inputs from stdin, emits snapshots and certificates.
*)

open Monitor_kernel
open Cert_parser

let usage () =
  Printf.eprintf "Usage: monitor_cli [--json] [--verbose]\n";
  Printf.eprintf "  Reads newline-delimited JSON monitor inputs from stdin.\n";
  Printf.eprintf "  Emits JSON snapshots and rupture certificates to stdout.\n";
  exit 1

let parse_input_json json =
  let kvs = parse_json_object json in
  let get k = match List.assoc_opt k kvs with
    | Some v -> (match int_of_string_opt (String.trim v) with
                 | Some n -> n
                 | None   -> 0)
    | None -> 0
  in
  let get_bool k = match List.assoc_opt k kvs with
    | Some "true" -> true
    | _ -> false
  in
  { mi_tension  = get "tension";
    mi_lag      = get "lag";
    mi_strain   = get "strain";
    mi_osc      = get_bool "osc";
    mi_widened  = get_bool "widened"; }

let run_monitor () =
  let verbose = Array.mem "--verbose" Sys.argv in
  let snapshot = ref initial_snapshot in
  try
    while true do
      let line = input_line stdin in
      let line = String.trim line in
      if String.length line > 0 && line.[0] = '{' then begin
        let input = parse_input_json line in
        let result = step !snapshot input () in
        snapshot := result.next_snapshot;
        Printf.printf "%s\n%!" (snapshot_to_json !snapshot);
        (match result.certificate with
         | Some cert ->
           Printf.printf "CERTIFICATE: %s\n%!" (certificate_to_json cert)
         | None -> ());
        if verbose then
          Printf.eprintf "[monitor] %s\n%!" result.log_message
      end
    done
  with End_of_file -> ()

let () =
  if Array.mem "--help" Sys.argv || Array.mem "-h" Sys.argv
  then usage ()
  else run_monitor ()
