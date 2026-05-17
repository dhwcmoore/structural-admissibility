
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true



(** val add : int -> int -> int **)

let rec add n m =
  (fun fO fS n -> if n = 0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun p -> succ (add p m))
    n

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
  (** val eqb : int -> int -> bool **)

  let rec eqb = (fun n m -> n = m)

  (** val leb : int -> int -> bool **)

  let rec leb = (fun n m -> n <= m)

  (** val ltb : int -> int -> bool **)

  let ltb = (fun n m -> n < m)
 end

type monitorStatus =
| CLOSED
| META_REVIEW
| HARD_RUPTURE

type monitorSnapshot = { fatigue : int; tension : int; horizon : int;
                         lag : int; status : monitorStatus }

(** val fatigue_threshold : int **)

let fatigue_threshold =
  failwith "AXIOM TO BE REALIZED (StructuralAdmissibility.Runtime.MonitorStates.fatigue_threshold)"

(** val tension_threshold : int **)

let tension_threshold =
  failwith "AXIOM TO BE REALIZED (StructuralAdmissibility.Runtime.MonitorStates.tension_threshold)"

(** val meta_review_trigger : int **)

let meta_review_trigger =
  failwith "AXIOM TO BE REALIZED (StructuralAdmissibility.Runtime.MonitorStates.meta_review_trigger)"

type extractableRuptureCert = { ec_left_id : int; ec_right_id : int;
                                ec_obs_hash : int; ec_pred_left : bool;
                                ec_pred_right : bool; ec_fatigue : int }

(** val extracted_cert_valid : extractableRuptureCert -> bool **)

let extracted_cert_valid cert =
  if negb (eqb cert.ec_pred_left cert.ec_pred_right)
  then Nat.ltb 0 cert.ec_fatigue
  else false

(** val status_to_nat : monitorStatus -> int **)

let status_to_nat = function
| CLOSED -> 0
| META_REVIEW -> succ 0
| HARD_RUPTURE -> succ (succ 0)

(** val nat_to_status : int -> monitorStatus **)

let nat_to_status n =
  (fun fO fS n -> if n = 0 then fO () else fS (n-1))
    (fun _ -> CLOSED)
    (fun n0 ->
    (fun fO fS n -> if n = 0 then fO () else fS (n-1))
      (fun _ -> META_REVIEW)
      (fun _ -> HARD_RUPTURE)
      n0)
    n

type extractableSnapshot = { ex_fatigue : int; ex_tension : int;
                             ex_horizon : int; ex_lag : int; ex_status : 
                             int }

(** val snapshot_to_extractable : monitorSnapshot -> extractableSnapshot **)

let snapshot_to_extractable s =
  { ex_fatigue = s.fatigue; ex_tension = s.tension; ex_horizon = s.horizon;
    ex_lag = s.lag; ex_status = (status_to_nat s.status) }

(** val extractable_to_snapshot : extractableSnapshot -> monitorSnapshot **)

let extractable_to_snapshot e =
  { fatigue = e.ex_fatigue; tension = e.ex_tension; horizon = e.ex_horizon;
    lag = e.ex_lag; status = (nat_to_status e.ex_status) }

type extractableInput = { ei_tension : int; ei_lag : int; ei_strain : 
                          int; ei_osc : bool; ei_widened : bool }

(** val ticket_none : int **)

let ticket_none =
  0

(** val ticket_admissibility_failure : int **)

let ticket_admissibility_failure =
  succ 0

(** val ticket_structural_review : int **)

let ticket_structural_review =
  succ (succ 0)

(** val repair_no_action : int **)

let repair_no_action =
  0

(** val repair_refine_observation : int **)

let repair_refine_observation =
  succ (succ 0)

(** val repair_choose_by_cost : int **)

let repair_choose_by_cost =
  succ (succ (succ 0))

(** val repair_carry_explicit_debt : int **)

let repair_carry_explicit_debt =
  succ (succ (succ (succ 0)))

(** val debt_boundary : int **)

let debt_boundary =
  succ (succ (succ 0))

(** val debt_threshold : int **)

let debt_threshold =
  succ (succ (succ (succ 0)))

type extractableEngineeringAction = { ea_ticket_kind : int;
                                      ea_monitor_status : int;
                                      ea_repair_recommendation : int;
                                      ea_debt_kind : int;
                                      ea_restriction_cost : int;
                                      ea_refinement_cost : int }

(** val recommended_repair_for_debt_kind : int -> int **)

let recommended_repair_for_debt_kind debt_kind =
  if Nat.eqb debt_kind debt_threshold
  then repair_carry_explicit_debt
  else if Nat.eqb debt_kind debt_boundary
       then repair_refine_observation
       else repair_choose_by_cost

(** val engineering_action_from_status :
    int -> int -> int -> int -> extractableEngineeringAction **)

let engineering_action_from_status status0 restriction_cost refinement_cost debt_kind =
  (fun fO fS n -> if n = 0 then fO () else fS (n-1))
    (fun _ -> { ea_ticket_kind = ticket_none; ea_monitor_status = 0;
    ea_repair_recommendation = repair_no_action; ea_debt_kind = debt_kind;
    ea_restriction_cost = restriction_cost; ea_refinement_cost =
    refinement_cost })
    (fun n ->
    (fun fO fS n -> if n = 0 then fO () else fS (n-1))
      (fun _ -> { ea_ticket_kind = ticket_structural_review;
      ea_monitor_status = (succ 0); ea_repair_recommendation =
      (recommended_repair_for_debt_kind debt_kind); ea_debt_kind = debt_kind;
      ea_restriction_cost = restriction_cost; ea_refinement_cost =
      refinement_cost })
      (fun _ -> { ea_ticket_kind = ticket_admissibility_failure;
      ea_monitor_status = status0; ea_repair_recommendation =
      (recommended_repair_for_debt_kind debt_kind); ea_debt_kind = debt_kind;
      ea_restriction_cost = restriction_cost; ea_refinement_cost =
      refinement_cost })
      n)
    status0

(** val engineering_action_from_certificate :
    extractableRuptureCert -> int -> int -> int ->
    extractableEngineeringAction **)

let engineering_action_from_certificate cert restriction_cost refinement_cost debt_kind =
  if extracted_cert_valid cert
  then engineering_action_from_status (succ (succ 0)) restriction_cost
         refinement_cost debt_kind
  else engineering_action_from_status 0 restriction_cost refinement_cost
         debt_kind

(** val update_monitor :
    extractableSnapshot -> extractableInput -> extractableSnapshot **)

let update_monitor s input =
  let new_fatigue =
    add
      (add (add s.ex_fatigue input.ei_strain)
        (if input.ei_osc then succ 0 else 0))
      (if input.ei_widened then succ (succ 0) else 0)
  in
  let new_status =
    if Nat.ltb fatigue_threshold new_fatigue
    then succ (succ 0)
    else if Nat.ltb input.ei_tension tension_threshold
         then if Nat.ltb meta_review_trigger new_fatigue then succ 0 else 0
         else succ (succ 0)
  in
  { ex_fatigue = new_fatigue; ex_tension = input.ei_tension; ex_horizon =
  s.ex_horizon; ex_lag = input.ei_lag; ex_status = new_status }

(** val update_monitor_preserves_invariants : __ **)

let update_monitor_preserves_invariants =
  __

(** val engineering_action_after_update :
    extractableSnapshot -> extractableInput -> int -> int -> int ->
    extractableEngineeringAction **)

let engineering_action_after_update s input restriction_cost refinement_cost debt_kind =
  engineering_action_from_status (update_monitor s input).ex_status
    restriction_cost refinement_cost debt_kind
