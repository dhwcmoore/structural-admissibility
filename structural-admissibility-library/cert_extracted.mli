
type __ = Obj.t

val negb : bool -> bool



val eqb : bool -> bool -> bool

module Nat :
 sig
  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val ltb : int -> int -> bool
 end

type extractableRuptureCert = { ec_left_id : int; ec_right_id : int;
                                ec_obs_hash : int; ec_pred_left : bool;
                                ec_pred_right : bool; ec_fatigue : int }

type extractable_cert_semantically_valid = __

val extracted_cert_valid : extractableRuptureCert -> bool

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

val build_extractable_cert : bool -> bool -> int -> extractableRuptureCert
