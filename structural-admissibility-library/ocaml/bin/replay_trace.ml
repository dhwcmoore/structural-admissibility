(** replay_trace.ml

    Replay historical traces and check whether certificates are emitted.
    Useful for examples and the paper.
*)

open Monitor_kernel
open Fatigue_trace

let sensor_example () : monitor_input list =
  [{ mi_tension = 10; mi_lag = 1; mi_strain = 0;  mi_osc = false; mi_widened = false };
   { mi_tension = 15; mi_lag = 1; mi_strain = 5;  mi_osc = false; mi_widened = false };
   { mi_tension = 20; mi_lag = 2; mi_strain = 10; mi_osc = true;  mi_widened = false };
   { mi_tension = 18; mi_lag = 2; mi_strain = 3;  mi_osc = true;  mi_widened = true  };
   { mi_tension = 25; mi_lag = 3; mi_strain = 8;  mi_osc = false; mi_widened = true  };
   { mi_tension = 30; mi_lag = 3; mi_strain = 15; mi_osc = true;  mi_widened = true  }]

let print_trace (t : fatigue_trace) =
  Printf.printf "=== Trace Replay ===\n";
  Printf.printf "Start: %s\n" (snapshot_to_json t.ft_start);
  List.iter (fun ev ->
    Printf.printf "  t=%d: %s"
      ev.te_time
      (snapshot_to_json ev.te_snapshot);
    (match ev.te_cert with
     | Some c -> Printf.printf "  >> CERTIFICATE: %s" (certificate_to_json c)
     | None   -> ());
    Printf.printf "\n"
  ) t.ft_events;
  Printf.printf "Total fatigue accumulated: %d\n"
    (total_fatigue_accumulated t);
  Printf.printf "Rupture events: %d\n"
    (List.length (rupture_events t))

let () =
  let trace = replay_trace initial_snapshot (sensor_example ()) in
  print_trace trace
