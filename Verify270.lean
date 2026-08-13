import Mathlib.Util.AssertNoSorry
import stoch_to_det.Ledger270

/-! Kernel audit for the unconditional `270` endpoint. -/

#check stoch_to_det.diag_context_quarter_arith
#check stoch_to_det.exists_raceQuantitiesQuarter
#check stoch_to_det.seedLeak_bound_270
#check stoch_to_det.hellingerSq_eq_two_contactSecantEnergy_sub_two_cross
#check stoch_to_det.rho_le_rhoHGR_of_contacts_param_l2
#check stoch_to_det.assembly_cap_270
#check stoch_to_det.infoFloor270_le_Ixy_of_contact
#check stoch_to_det.Cdagger270_lt_270
#check stoch_to_det.T_le_270

assert_no_sorry stoch_to_det.diag_context_quarter_arith
assert_no_sorry stoch_to_det.exists_raceQuantitiesQuarter
assert_no_sorry stoch_to_det.seedLeak_bound_270
assert_no_sorry stoch_to_det.hellingerSq_eq_two_contactSecantEnergy_sub_two_cross
assert_no_sorry stoch_to_det.rho_le_rhoHGR_of_contacts_param_l2
assert_no_sorry stoch_to_det.assembly_cap_270
assert_no_sorry stoch_to_det.infoFloor270_le_Ixy_of_contact
assert_no_sorry stoch_to_det.Cdagger270_lt_270
assert_no_sorry stoch_to_det.T_le_270

/--
info: 'stoch_to_det.diag_context_quarter_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.diag_context_quarter_arith

/--
info: 'stoch_to_det.exists_raceQuantitiesQuarter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.exists_raceQuantitiesQuarter

/--
info: 'stoch_to_det.seedLeak_bound_270' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.seedLeak_bound_270

/--
info: 'stoch_to_det.hellingerSq_eq_two_contactSecantEnergy_sub_two_cross' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.hellingerSq_eq_two_contactSecantEnergy_sub_two_cross

/--
info: 'stoch_to_det.rho_le_rhoHGR_of_contacts_param_l2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.rho_le_rhoHGR_of_contacts_param_l2

/--
info: 'stoch_to_det.assembly_cap_270' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.assembly_cap_270

/--
info: 'stoch_to_det.infoFloor270_le_Ixy_of_contact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.infoFloor270_le_Ixy_of_contact

/--
info: 'stoch_to_det.Cdagger270_lt_270' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.Cdagger270_lt_270

/--
info: 'stoch_to_det.T_le_270' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.T_le_270
