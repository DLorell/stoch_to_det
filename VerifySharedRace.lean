import Mathlib.Util.AssertNoSorry
import stoch_to_det.SharedRace.ReferenceLoss
import stoch_to_det.SharedRace.ClockLaw
import stoch_to_det.SharedRace.CoordinateBound
import stoch_to_det.SharedRace.EntropyAssembly
import stoch_to_det.SharedRace.Information
import stoch_to_det.SharedRace.PairClockLaw

/-! Kernel audit for the independent all-label analytic tranches. -/

#check stoch_to_det.SharedRace.coordinateContribution_le
#check stoch_to_det.SharedRace.winnerBetaExpMoment_le
#check stoch_to_det.SharedRace.loserBetaExpMoment_le
#check stoch_to_det.SharedRace.integratedLoserBetaExpMoment_le
#check stoch_to_det.SharedRace.integratedLoserDegenerateExpMoment_le
#check stoch_to_det.SharedRace.betaCoordinateContribution_le_of_mem_Icc
#check stoch_to_det.SharedRace.twoCoordinateContribution_le_of_mem_Icc
#check stoch_to_det.SharedRace.clockLaw_scaledNormClock_map_eq_scaledBetaOneLaw
#check stoch_to_det.SharedRace.clockLaw_pairShareRatio_map_eq
#check stoch_to_det.SharedRace.clockLaw_pairShareRatio_map_eq_two
#check stoch_to_det.SharedRace.clockLaw_scaledNormClock_expMoment_le
#check stoch_to_det.SharedRace.normalizedRaceLogIntegral_le
#check stoch_to_det.SharedRace.referenceLossIntegral_le
#check stoch_to_det.SharedRace.posteriorMI_mul_logTwo_eq_expectedKL
#check stoch_to_det.SharedRace.clockSharedRaceEntropy_le_of_referenceLoss

assert_no_sorry stoch_to_det.SharedRace.coordinateContribution_le
assert_no_sorry stoch_to_det.SharedRace.winnerBetaExpMoment_le
assert_no_sorry stoch_to_det.SharedRace.loserBetaExpMoment_le
assert_no_sorry stoch_to_det.SharedRace.integratedLoserBetaExpMoment_le
assert_no_sorry stoch_to_det.SharedRace.integratedLoserDegenerateExpMoment_le
assert_no_sorry stoch_to_det.SharedRace.betaCoordinateContribution_le_of_mem_Icc
assert_no_sorry stoch_to_det.SharedRace.twoCoordinateContribution_le_of_mem_Icc
assert_no_sorry stoch_to_det.SharedRace.clockLaw_scaledNormClock_map_eq_scaledBetaOneLaw
assert_no_sorry stoch_to_det.SharedRace.clockLaw_pairShareRatio_map_eq
assert_no_sorry stoch_to_det.SharedRace.clockLaw_pairShareRatio_map_eq_two
assert_no_sorry stoch_to_det.SharedRace.clockLaw_scaledNormClock_expMoment_le
assert_no_sorry stoch_to_det.SharedRace.normalizedRaceLogIntegral_le
assert_no_sorry stoch_to_det.SharedRace.referenceLossIntegral_le
assert_no_sorry stoch_to_det.SharedRace.posteriorMI_mul_logTwo_eq_expectedKL
assert_no_sorry stoch_to_det.SharedRace.clockSharedRaceEntropy_le_of_referenceLoss

/--
info: 'stoch_to_det.SharedRace.normalizedRaceLogIntegral_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.SharedRace.normalizedRaceLogIntegral_le

/--
info: 'stoch_to_det.SharedRace.referenceLossIntegral_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.SharedRace.referenceLossIntegral_le

/--
info: 'stoch_to_det.SharedRace.clockLaw_scaledNormClock_expMoment_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.SharedRace.clockLaw_scaledNormClock_expMoment_le

/--
info: 'stoch_to_det.SharedRace.clockSharedRaceEntropy_le_of_referenceLoss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.SharedRace.clockSharedRaceEntropy_le_of_referenceLoss
