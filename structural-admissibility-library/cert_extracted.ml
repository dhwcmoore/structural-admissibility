
type __ = Obj.t

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true



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

type extractableRuptureCert = { ec_left_id : int; ec_right_id : int;
                                ec_obs_hash : int; ec_pred_left : bool;
                                ec_pred_right : bool; ec_fatigue : int }

type extractable_cert_semantically_valid = __

(** val extracted_cert_valid : extractableRuptureCert -> bool **)

let extracted_cert_valid cert =
  if negb (eqb cert.ec_pred_left cert.ec_pred_right)
  then Nat.ltb 0 cert.ec_fatigue
  else false

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

let engineering_action_from_status status restriction_cost refinement_cost debt_kind =
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
      ea_monitor_status = status; ea_repair_recommendation =
      (recommended_repair_for_debt_kind debt_kind); ea_debt_kind = debt_kind;
      ea_restriction_cost = restriction_cost; ea_refinement_cost =
      refinement_cost })
      n)
    status

(** val engineering_action_from_certificate :
    extractableRuptureCert -> int -> int -> int ->
    extractableEngineeringAction **)

let engineering_action_from_certificate cert restriction_cost refinement_cost debt_kind =
  if extracted_cert_valid cert
  then engineering_action_from_status (succ (succ 0)) restriction_cost
         refinement_cost debt_kind
  else engineering_action_from_status 0 restriction_cost refinement_cost
         debt_kind

(** val build_extractable_cert :
    bool -> bool -> int -> extractableRuptureCert **)

let build_extractable_cert pl pr fat =
  { ec_left_id = 0; ec_right_id = (succ 0); ec_obs_hash = 0; ec_pred_left =
    pl; ec_pred_right = pr; ec_fatigue = fat }
