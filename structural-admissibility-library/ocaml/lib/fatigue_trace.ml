(** fatigue_trace.ml

    Fatigue accumulation trace recording and analysis.
*)

open Monitor_kernel

(* ================================================================= *)
(** 1. Trace event                                                   *)
(* ================================================================= *)

type trace_event = {
  te_input    : monitor_input;
  te_snapshot : snapshot;
  te_cert     : rupture_certificate option;
  te_time     : int;
}

(* ================================================================= *)
(** 2. Trace accumulator                                             *)
(* ================================================================= *)

type fatigue_trace = {
  ft_events : trace_event list;
  ft_start  : snapshot;
}

let empty_trace s = { ft_events = []; ft_start = s }

let add_event (t : fatigue_trace) (ev : trace_event) : fatigue_trace =
  { t with ft_events = t.ft_events @ [ev] }

(* ================================================================= *)
(** 3. Trace statistics                                              *)
(* ================================================================= *)

let total_fatigue_accumulated (t : fatigue_trace) : int =
  match t.ft_events with
  | [] -> 0
  | events ->
    let last = List.nth events (List.length events - 1) in
    last.te_snapshot.fatigue - t.ft_start.fatigue

let rupture_events (t : fatigue_trace) : trace_event list =
  List.filter (fun ev -> ev.te_cert <> None) t.ft_events

let transition_to_meta_review (t : fatigue_trace) : trace_event list =
  List.filter
    (fun ev -> ev.te_snapshot.status = MetaReview)
    t.ft_events

(* ================================================================= *)
(** 4. Trace replay                                                  *)
(* ================================================================= *)

let replay_trace
    (init   : snapshot)
    (inputs : monitor_input list)
    : fatigue_trace =
  let trace = empty_trace init in
  let _, trace =
    List.fold_left
      (fun (s, t) (i, input) ->
         let result = step s input () in
         let ev = {
           te_input    = input;
           te_snapshot = result.next_snapshot;
           te_cert     = result.certificate;
           te_time     = i;
         } in
         (result.next_snapshot, add_event t ev))
      (init, trace)
      (List.mapi (fun i x -> (i, x)) inputs)
  in
  trace
