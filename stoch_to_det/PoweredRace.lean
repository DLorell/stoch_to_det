import stoch_to_det.PoweredRaceNormalization
import stoch_to_det.PoweredRaceEntropy
import stoch_to_det.PoweredRaceDispersion

/-! The unconditional fourth-power shared-race estimate and its concrete
seed-leak consequence. -/

namespace stoch_to_det

namespace SharedRace

universe u

/-- Fourth-power shared clocks satisfy the sharpened entropy estimate for
any finite supported family of strictly positive posterior laws. -/
theorem sharedRaceEntropy_le_powered
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) :
    sharedRaceEntropy μ r ≤
      (4 + poweredRaceJ4Upper) * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        poweredRaceJ4Upper / Real.log 2 * categoricalMismatch μ r := by
  apply sharedRaceEntropy_le_powered_of_dispersion hμ hr hrpos
    (by norm_num [poweredRaceJ4Upper])
  · intro π hπ hπpos
    exact integral_log_poweredRaceZ_le π hπpos hπ.total
  · exact posteriorMean_mismatch_le hμ hr hrpos

end SharedRace

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- The actual calibrated race satisfies the improved seed-leak estimate. -/
theorem powered_race_seedLeak_bound
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D) :
    (concreteRaceQuantities D K).seedLeak ≤
      (3 + poweredRaceJ4Upper) * bZ D +
        poweredRaceJ4Upper / Real.log 2 * K.dMis := by
  have hw := raceWinnerEntropy_le_of_uniform_entropy_bound D K
    (4 + poweredRaceJ4Upper) (poweredRaceJ4Upper / Real.log 2)
    (fun _ _ hμ hr hrpos => SharedRace.sharedRaceEntropy_le_powered hμ hr hrpos)
  have hid := (concreteRaceQuantities D K).winner_entropy_identity
  change raceWinnerEntropy D = K.Sinfo + (concreteRaceQuantities D K).seedLeak at hid
  rw [K.Sinfo_eq_bZ] at hw hid
  nlinarith only [hw, hid]

end stoch_to_det
