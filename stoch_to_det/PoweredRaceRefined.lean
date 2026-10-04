import stoch_to_det.PoweredRace
import stoch_to_det.PoweredRaceIntegralRefined

/-! The powered shared race with the corrected normalization constant. -/

namespace stoch_to_det
namespace SharedRace

open Finset MeasureTheory

universe u

theorem integral_log_poweredRaceZ_le_refined
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1) :
    (∫ E : κ → ℝ, Real.log (poweredRaceZ π E) ∂clockLaw κ) ≤
      poweredRaceJ4Refined * (1 - ∑ i, π i ^ 2) :=
  integral_log_poweredRaceZ_le_of_loser_integral poweredRaceJ4Refined
    (fun _ hp0 hp1 => powered_loser_mobius_integral_le_refined hp0 hp1) π hπ hπtotal

/-- Corrected fourth-power entropy estimate for arbitrary finite sources. -/
theorem sharedRaceEntropy_le_powered_refined
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) :
    sharedRaceEntropy μ r ≤
      (4 + poweredRaceJ4Refined) * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        poweredRaceJ4Refined / Real.log 2 * categoricalMismatch μ r := by
  apply sharedRaceEntropy_le_powered_of_dispersion hμ hr hrpos
    (by norm_num [poweredRaceJ4Refined, poweredRaceJ4Upper])
  · intro π hπ hπpos
    exact integral_log_poweredRaceZ_le_refined π hπpos hπ.total
  · exact posteriorMean_mismatch_le hμ hr hrpos

end SharedRace

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- The concrete race uses the corrected rational seed-leak bound. -/
theorem powered_race_seedLeak_bound_refined
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D) :
    (concreteRaceQuantities D K).seedLeak ≤
      (3 + poweredRaceJ4Refined) * bZ D +
        poweredRaceJ4Refined / Real.log 2 * K.dMis := by
  have hw := raceWinnerEntropy_le_of_uniform_entropy_bound D K
    (4 + poweredRaceJ4Refined) (poweredRaceJ4Refined / Real.log 2)
    (fun _ _ hμ hr hrpos => SharedRace.sharedRaceEntropy_le_powered_refined hμ hr hrpos)
  have hid := (concreteRaceQuantities D K).winner_entropy_identity
  change raceWinnerEntropy D = K.Sinfo + (concreteRaceQuantities D K).seedLeak at hid
  rw [K.Sinfo_eq_bZ] at hw hid
  nlinarith only [hw, hid]

end stoch_to_det
