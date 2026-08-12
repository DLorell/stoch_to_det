import Mathlib.Util.AssertNoSorry
import stoch_to_det.MainTheorems
import stoch_to_det.Final1336

/-!
This file is both a compact index of the public results and a kernel-level
audit of their transitive dependencies.
-/

#check stoch_to_det.generalized_stoch_to_det_Cdagger1771_joint
#check stoch_to_det.Cdagger1771_lt_1771
#check stoch_to_det.LW_sum_1771_joint
#check stoch_to_det.T_le_698

assert_no_sorry stoch_to_det.generalized_stoch_to_det_Cdagger1771_joint
assert_no_sorry stoch_to_det.Cdagger1771_lt_1771
assert_no_sorry stoch_to_det.LW_sum_1771_joint
assert_no_sorry stoch_to_det.T_le_698

/--
info: 'stoch_to_det.T_le_698' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.T_le_698

/--
info: 'stoch_to_det.generalized_stoch_to_det_Cdagger1771_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.generalized_stoch_to_det_Cdagger1771_joint

/--
info: 'stoch_to_det.Cdagger1771_lt_1771' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.Cdagger1771_lt_1771

/--
info: 'stoch_to_det.LW_sum_1771_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.LW_sum_1771_joint
