
type __ = Obj.t

val negb : bool -> bool



val add : int -> int -> int

val eqb : bool -> bool -> bool

module Nat :
 sig
  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val ltb : int -> int -> bool
 end

type monitorStatus =
| CLOSED
| META_REVIEW
| HARD_RUPTURE

type monitorSnapshot = { fatigue : int; tension : int; horizon : int;
                         lag : int; status : monitorStatus }

val fatigue_threshold : int

val tension_threshold : int

val meta_review_trigger : int

type extractableRuptureCert = { ec_left_id : int; ec_right_id : int;
                                ec_obs_hash : int; ec_pred_left : bool;
                                ec_pred_right : bool; ec_fatigue : int }

val extracted_cert_valid : extractableRuptureCert -> bool

val status_to_nat : monitorStatus -> int

val nat_to_status : int -> monitorStatus

type extractableSnapshot = { ex_fatigue : int; ex_tension : int;
                             ex_horizon : int; ex_lag : int; ex_status : 
                             int }

val snapshot_to_extractable : monitorSnapshot -> extractableSnapshot

val extractable_to_snapshot : extractableSnapshot -> monitorSnapshot

type extractableInput = { ei_tension : int; ei_lag : int; ei_strain : 
                          int; ei_osc : bool; ei_widened : bool }

val ticket_none : int

val ticket_admissibility_failure : int

val ticket_structural_review : int

val repair_no_action : int

val repair_refine_observation : int

val repair_choose_by_cost : int

val repair_carry_explicit_debt : int

val debt_boundary : int

val debt_threshold : int

type extractableEngineeringAction = { ea_ticket_kind : int;
                                      ea_monitor_status : int;
                                      ea_repair_recommendation : int;
                                      ea_debt_kind : int;
                                      ea_restriction_cost : int;
                                      ea_refinement_cost : int }

val recommended_repair_for_debt_kind : int -> int

val engineering_action_from_status :
  int -> int -> int -> int -> extractableEngineeringAction

val engineering_action_from_certificate :
  extractableRuptureCert -> int -> int -> int -> extractableEngineeringAction

val update_monitor :
  extractableSnapshot -> extractableInput -> extractableSnapshot

val update_monitor_preserves_invariants : __

val engineering_action_after_update :
  extractableSnapshot -> extractableInput -> int -> int -> int ->
  extractableEngineeringAction
