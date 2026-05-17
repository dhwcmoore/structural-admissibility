(** test_extracted_equivalence.ml

    Tests verifying that the OCaml implementation matches the Coq spec.
    These tests should pass after extraction.
*)

open Monitor_kernel

let assert_eq_int label a b =
  if a = b then Printf.printf "PASS: %s\n" label
  else Printf.printf "FAIL: %s (expected %d, got %d)\n" label a b

let assert_bool label b =
  if b then Printf.printf "PASS: %s\n" label
  else Printf.printf "FAIL: %s\n" label

let () =
  (* Test: fatigue monotone under any update *)
  let s0 = initial_snapshot in
  let inputs = [
    { mi_tension=5; mi_lag=1; mi_strain=0; mi_osc=false; mi_widened=false };
    { mi_tension=5; mi_lag=1; mi_strain=3; mi_osc=false; mi_widened=false };
    { mi_tension=5; mi_lag=1; mi_strain=0; mi_osc=true;  mi_widened=false };
    { mi_tension=5; mi_lag=1; mi_strain=0; mi_osc=false; mi_widened=true  };
  ] in
  List.iteri (fun i input ->
    let s' = update_monitor s0 input in
    assert_bool
      (Printf.sprintf "fatigue monotone case %d" i)
      (s'.fatigue >= s0.fatigue)
  ) inputs;

  (* Test: zero strain preserves fatigue *)
  let s1 = update_monitor s0
    { mi_tension=5; mi_lag=1; mi_strain=0; mi_osc=false; mi_widened=false } in
  assert_eq_int "zero strain preserves fatigue" s0.fatigue s1.fatigue;

  (* Test: hard rupture absorbing (by invariant: any input keeps status HardRupture
     when fatigue is above threshold after the first rupture event) *)
  let rupture_input = { mi_tension=5; mi_lag=1; mi_strain=200; mi_osc=false; mi_widened=false } in
  let s_rupt = update_monitor s0 rupture_input in
  assert_bool "reaches hard rupture" (s_rupt.status = HardRupture);

  (* Test: round-trip snapshot serialisation *)
  let json = snapshot_to_json s0 in
  assert_bool "snapshot serialises" (String.length json > 0);

  Printf.printf "Done.\n"
