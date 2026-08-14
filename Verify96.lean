import Mathlib.Util.AssertNoSorry
import stoch_to_det.SharedRace

/-! Kernel audit for the exact joint-charge closure at `C < 96`. -/

#check stoch_to_det.M_add_Bq_eq_bZ_add_jointCharge
#check stoch_to_det.bZ_le_tau
#check stoch_to_det.Cdagger96_lt_96
#check stoch_to_det.mismatch_charge_96
#check stoch_to_det.winnerEntropy_bound_96
#check stoch_to_det.Dwdefect_le_96
#check stoch_to_det.T_le_96_of_joint_seed_bound
#check stoch_to_det.hasJointSeedBound_of_sharedRaceBound
#check stoch_to_det.T_le_96_of_sharedRaceBound
#check stoch_to_det.T_le_96_of_universalClockCoordinateBound
#check stoch_to_det.SharedRace.clockCoordinateIntegral_le
#check stoch_to_det.SharedRace.clockSharedRaceEntropy_le
#check stoch_to_det.SharedRace.universalClockCoordinateBound
#check stoch_to_det.SharedRace.hasSharedRaceBound
#check stoch_to_det.T_le_96

assert_no_sorry stoch_to_det.M_add_Bq_eq_bZ_add_jointCharge
assert_no_sorry stoch_to_det.bZ_le_tau
assert_no_sorry stoch_to_det.Cdagger96_lt_96
assert_no_sorry stoch_to_det.mismatch_charge_96
assert_no_sorry stoch_to_det.winnerEntropy_bound_96
assert_no_sorry stoch_to_det.Dwdefect_le_96
assert_no_sorry stoch_to_det.T_le_96_of_joint_seed_bound
assert_no_sorry stoch_to_det.hasJointSeedBound_of_sharedRaceBound
assert_no_sorry stoch_to_det.T_le_96_of_sharedRaceBound
assert_no_sorry stoch_to_det.T_le_96_of_universalClockCoordinateBound
assert_no_sorry stoch_to_det.SharedRace.clockCoordinateIntegral_le
assert_no_sorry stoch_to_det.SharedRace.clockSharedRaceEntropy_le
assert_no_sorry stoch_to_det.SharedRace.universalClockCoordinateBound
assert_no_sorry stoch_to_det.SharedRace.hasSharedRaceBound
assert_no_sorry stoch_to_det.T_le_96

/--
info: 'stoch_to_det.M_add_Bq_eq_bZ_add_jointCharge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.M_add_Bq_eq_bZ_add_jointCharge

/--
info: 'stoch_to_det.Cdagger96_lt_96' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.Cdagger96_lt_96

/--
info: 'stoch_to_det.T_le_96_of_joint_seed_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.T_le_96_of_joint_seed_bound

/--
info: 'stoch_to_det.T_le_96' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.T_le_96
