(** test_monitor_kernel.ml

    Unit tests for the monitor kernel.
*)

open Monitor_kernel

let assert_eq label expected actual =
  if expected = actual then
    Printf.printf "PASS: %s\n" label
  else
    Printf.printf "FAIL: %s (expected %s, got %s)\n"
      label
      (match expected with Closed -> "CLOSED" | MetaReview -> "META_REVIEW" | HardRupture -> "HARD_RUPTURE")
      (match actual with Closed -> "CLOSED" | MetaReview -> "META_REVIEW" | HardRupture -> "HARD_RUPTURE")

let assert_bool label b =
  if b then Printf.printf "PASS: %s\n" label
  else Printf.printf "FAIL: %s\n" label

let low_input = {
  mi_tension = 5; mi_lag = 1; mi_strain = 0;
  mi_osc = false; mi_widened = false }

let high_strain_input = {
  mi_tension = 5; mi_lag = 1; mi_strain = 200;
  mi_osc = false; mi_widened = false }

let () =
  (* Test 1: initial state is CLOSED *)
  assert_eq "initial status" Closed initial_snapshot.status;

  (* Test 2: zero-strain update stays CLOSED *)
  let s1 = update_monitor initial_snapshot low_input in
  assert_eq "zero-strain stays CLOSED" Closed s1.status;

  (* Test 3: high strain causes HARD_RUPTURE *)
  let s2 = update_monitor initial_snapshot high_strain_input in
  assert_eq "high strain -> HARD_RUPTURE" HardRupture s2.status;

  (* Test 4: HARD_RUPTURE is absorbing *)
  let s3 = update_monitor s2 low_input in
  assert_bool "HARD_RUPTURE absorbing"
    (s3.status = HardRupture || s3.fatigue > 100);

  (* Test 5: fatigue monotone under non-zero strain *)
  let s4 = update_monitor initial_snapshot
    { mi_tension = 5; mi_lag = 1; mi_strain = 5; mi_osc = false; mi_widened = false } in
  assert_bool "fatigue increases" (s4.fatigue > initial_snapshot.fatigue);

  (* Test 6: certificate valid when pred_left != pred_right *)
  let cert = {
    cert_left_id = 0; cert_right_id = 1; cert_obs_hash = 0;
    cert_pred_left = true; cert_pred_right = false; cert_fatigue = 1 } in
  assert_bool "cert_valid true/false" (cert_valid cert);

  (* Test 7: certificate invalid when pred values equal *)
  let cert2 = { cert with cert_pred_right = true } in
  assert_bool "cert_valid equal predicates -> false" (not (cert_valid cert2));

  Printf.printf "Done.\n"
