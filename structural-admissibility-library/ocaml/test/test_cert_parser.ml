(** test_cert_parser.ml

    Unit tests for the certificate JSON parser.
*)

open Cert_parser

let assert_ok label = function
  | Ok _    -> Printf.printf "PASS: %s\n" label
  | Error e -> Printf.printf "FAIL: %s (%s)\n" label e

let assert_error label = function
  | Ok _    -> Printf.printf "FAIL: %s (expected error)\n" label
  | Error _ -> Printf.printf "PASS: %s\n" label

let () =
  (* Test 1: parse valid certificate *)
  let json = {|{"left_id":0,"right_id":1,"obs_hash":42,"pred_left":true,"pred_right":false,"fatigue":5}|} in
  assert_ok "valid cert" (of_json json);

  (* Test 2: reject cert with equal predicates *)
  let json2 = {|{"left_id":0,"right_id":1,"obs_hash":42,"pred_left":true,"pred_right":true,"fatigue":5}|} in
  assert_error "equal predicates rejected" (of_json json2);

  (* Test 3: reject cert with zero fatigue *)
  let json3 = {|{"left_id":0,"right_id":1,"obs_hash":42,"pred_left":true,"pred_right":false,"fatigue":0}|} in
  assert_error "zero fatigue rejected" (of_json json3);

  (* Test 4: reject incomplete JSON *)
  let json4 = {|{"left_id":0,"right_id":1}|} in
  assert_error "incomplete json rejected" (of_json json4);

  (* Test 5: parse valid snapshot *)
  let json5 = {|{"fatigue":10,"tension":5,"horizon":20,"lag":2,"status":"CLOSED"}|} in
  assert_ok "valid snapshot" (snapshot_of_json json5);

  Printf.printf "Done.\n"
