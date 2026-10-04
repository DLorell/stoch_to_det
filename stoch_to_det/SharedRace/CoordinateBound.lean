import stoch_to_det.SharedRace.Mobius

/-!
# One-coordinate winner/loser assembly

This file combines the literal winner and loser exponential-moment bounds
with the scalar allocation inequality.  The nondegenerate `k ≥ 3` and
degenerate `k = 2` loser branches are kept separate.
-/

namespace stoch_to_det
namespace SharedRace

open MeasureTheory
open scoped Interval

local notation "L" => SharedRace.logTwo

/-- One-coordinate contribution for the nondegenerate shape-two loser law. -/
theorem betaCoordinateContribution_le (k : ℕ) (hk : 3 ≤ k) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    p * SharedRace.betaOneExpMoment k (-L * (1 - p)) +
        (1 - p) *
          (∫ v : ℝ in 0..1,
            SharedRace.loserBetaIntegrand k p
              (SharedRace.mobius p v)) ≤
      p := by
  have hlam : -L * (1 - p) < 1 := by
    have hL := SharedRace.L_pos
    nlinarith
  have hwinner := SharedRace.winnerBetaExpMoment_le k
    (by omega : 2 ≤ k) hlam
  have hwinner' : SharedRace.betaOneExpMoment k (-L * (1 - p)) ≤
      1 / (1 + L * (1 - p)) := by
    simpa [one_div] using hwinner
  have hloser := SharedRace.integratedLoserBetaExpMoment_le
    k hk hp0 hp1
  exact SharedRace.coordinateContribution_le hp0.le hp1.le
    hwinner' hloser

/-- One-coordinate contribution for the degenerate `k = 2` loser law. -/
theorem twoCoordinateContribution_le {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    p * SharedRace.betaOneExpMoment 2 (-L * (1 - p)) +
        (1 - p) *
          (∫ v : ℝ in 0..1,
            SharedRace.loserDegenerateIntegrand p
              (SharedRace.mobius p v)) ≤
      p := by
  have hlam : -L * (1 - p) < 1 := by
    have hL := SharedRace.L_pos
    nlinarith
  have hwinner := SharedRace.winnerBetaExpMoment_le 2
    (by omega : 2 ≤ 2) hlam
  have hwinner' : SharedRace.betaOneExpMoment 2 (-L * (1 - p)) ≤
      1 / (1 + L * (1 - p)) := by
    simpa [one_div] using hwinner
  have hloser := SharedRace.integratedLoserDegenerateExpMoment_le
    hp0 hp1
  exact SharedRace.coordinateContribution_le hp0.le hp1.le
    hwinner' hloser

/-- Closed-interval form of `betaCoordinateContribution_le`, including the
two deterministic coordinate endpoints. -/
theorem betaCoordinateContribution_le_of_mem_Icc (k : ℕ) (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    p * SharedRace.betaOneExpMoment k (-L * (1 - p)) +
        (1 - p) *
          (∫ v : ℝ in 0..1,
            SharedRace.loserBetaIntegrand k p
              (SharedRace.mobius p v)) ≤
      p := by
  by_cases hpzero : p = 0
  · subst p
    simp [SharedRace.mobius,
      SharedRace.loserBetaIntegrand]
  by_cases hpone : p = 1
  · subst p
    have hwinner := SharedRace.winnerBetaExpMoment_le k
      (by omega : 2 ≤ k) (by norm_num : (0 : ℝ) < 1)
    simpa using hwinner
  exact betaCoordinateContribution_le k hk
    (lt_of_le_of_ne hp.1 (Ne.symm hpzero))
    (lt_of_le_of_ne hp.2 hpone)

/-- Closed-interval form of `twoCoordinateContribution_le`, including the
two deterministic coordinate endpoints. -/
theorem twoCoordinateContribution_le_of_mem_Icc {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    p * SharedRace.betaOneExpMoment 2 (-L * (1 - p)) +
        (1 - p) *
          (∫ v : ℝ in 0..1,
            SharedRace.loserDegenerateIntegrand p
              (SharedRace.mobius p v)) ≤
      p := by
  by_cases hpzero : p = 0
  · subst p
    simp [SharedRace.mobius,
      SharedRace.loserDegenerateIntegrand]
  by_cases hpone : p = 1
  · subst p
    have hwinner := SharedRace.winnerBetaExpMoment_le 2
      (by omega : 2 ≤ 2) (by norm_num : (0 : ℝ) < 1)
    simpa using hwinner
  exact twoCoordinateContribution_le
    (lt_of_le_of_ne hp.1 (Ne.symm hpzero))
    (lt_of_le_of_ne hp.2 hpone)

end SharedRace
end stoch_to_det
