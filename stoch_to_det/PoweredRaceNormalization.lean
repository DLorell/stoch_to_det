import stoch_to_det.PoweredRaceWinner
import stoch_to_det.PoweredRaceIntegral

/-! The fourth-power partition function is charged once to each ordered
winner/loser pair. The exponential residual law makes the losing ratio a
Möbius transform of a uniform coordinate. -/

namespace stoch_to_det
namespace SharedRace

open Finset MeasureTheory Set
open scoped Interval

variable {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]

lemma integral_fresh_powered_loser_eq (p : ℝ) (hp : 0 < p)
    (a i : κ) (hai : a ≠ i) :
    (∫ W : κ → ℝ, Real.log (1 + (p * W a / (p * W a + W i)) ^ 4)
      ∂clockLaw κ) =
      ∫ v : ℝ in 0..1, Real.log (1 + (mobius p v) ^ 4) := by
  let F : ℝ → ℝ := fun v => Real.log (1 + (mobius p v) ^ 4)
  have hF : Measurable F := by unfold F mobius; fun_prop
  have hratio : Measurable (fun W : κ → ℝ => W a / (W a + W i)) := by fun_prop
  calc
    _ = ∫ W : κ → ℝ, F (W a / (W a + W i)) ∂clockLaw κ := by
      apply integral_congr_ae
      filter_upwards [ae_clockLaw_pos (κ := κ)] with W hW
      simp only [F, mobius_pairRatio hp (hW a) (hW i)]
    _ = ∫ v : ℝ, F v ∂uniformUnitLaw := by
      rw [← clockLaw_pairRatio_map_eq_uniformUnitLaw a i hai]
      exact (integral_map hratio.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by
      unfold uniformUnitLaw
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le zero_le_one]

lemma integral_powered_loser_on_cell_eq
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (a i : κ) (hia : i ≠ a) :
    (∫ E : κ → ℝ, Real.log (1 + raceRatio π E i ^ 4)
      ∂(clockLaw κ).restrict {E | strictClockWin π a E}) =
      π a * ∫ v : ℝ in 0..1, Real.log (1 + (mobius (π i) v) ^ 4) := by
  let f : (κ → ℝ) → ℝ := fun W =>
    Real.log (1 + (π i * W a / (π i * W a + W i)) ^ 4)
  have hf : Measurable f := by unfold f; fun_prop
  calc
    _ = ∫ E : κ → ℝ, f (winnerResidualClock π a E)
        ∂(clockLaw κ).restrict {E | strictClockWin π a E} := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictClockWin_measurableSet π a)] with E hE
      simp only [f, raceRatio_loser_eq_residual π hπ a i hia E hE]
    _ = π a * ∫ W : κ → ℝ, f W ∂clockLaw κ :=
      integral_comp_winnerResidualClock π hπ hπtotal a f hf
    _ = _ := by rw [integral_fresh_powered_loser_eq (π i) (hπ i) a i hia.symm]

/-- A scalar Möbius integral bound controls the full partition function.
The factor is the categorical variance of the reference marginal. -/
theorem integral_log_poweredRaceZ_le_of_loser_integral
    (J : ℝ)
    (hJ : ∀ p : ℝ, 0 < p → p < 1 →
      (∫ v : ℝ in 0..1, Real.log (1 + (mobius p v) ^ 4)) ≤ p * J)
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1) :
    (∫ E : κ → ℝ, Real.log (poweredRaceZ π E) ∂clockLaw κ) ≤
      J * (1 - ∑ i, π i ^ 2) := by
  have hcell (a : κ) :
      (∫ E : κ → ℝ, Real.log (poweredRaceZ π E)
        ∂(clockLaw κ).restrict {E | strictClockWin π a E}) ≤
      ∑ i ∈ univ.erase a, π a * (π i * J) := by
    have hs : Integrable
        (fun E : κ → ℝ => ∑ i ∈ univ.erase a, Real.log (1 + raceRatio π E i ^ 4))
        ((clockLaw κ).restrict {E | strictClockWin π a E}) := by
      apply integrable_finsetSum
      intro i _
      exact (integrable_log_one_add_raceRatio_four π hπ i).restrict
    calc
      _ ≤ ∫ E : κ → ℝ, ∑ i ∈ univ.erase a, Real.log (1 + raceRatio π E i ^ 4)
          ∂(clockLaw κ).restrict {E | strictClockWin π a E} := by
        apply integral_mono_ae (integrable_log_poweredRaceZ π hπ).restrict hs
        filter_upwards [(ae_clockLaw_pos (κ := κ)).filter_mono ae_restrict_le,
          ae_restrict_mem (strictClockWin_measurableSet π a)] with E hE ha
        have hb := log_poweredRaceZ_le_sum_loser π E hπ hE
        rwa [clockArgmin_eq_of_strictClockWin π E a ha] at hb
      _ = ∑ i ∈ univ.erase a,
          ∫ E : κ → ℝ, Real.log (1 + raceRatio π E i ^ 4)
            ∂(clockLaw κ).restrict {E | strictClockWin π a E} := by
        rw [integral_finsetSum]
        intro i _
        exact (integrable_log_one_add_raceRatio_four π hπ i).restrict
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hia : i ≠ a := (Finset.mem_erase.mp hi).1
        rw [integral_powered_loser_on_cell_eq π hπ hπtotal a i hia]
        apply mul_le_mul_of_nonneg_left _ (hπ a).le
        exact hJ (π i) (hπ i) (pmf_coordinate_lt_one_of_ne π hπ hπtotal i a hia.symm)
  calc
    _ = ∑ a, ∫ E : κ → ℝ, Real.log (poweredRaceZ π E)
        ∂(clockLaw κ).restrict {E | strictClockWin π a E} :=
      integral_clock_eq_sum_strictClockWin π hπ hπtotal _ (integrable_log_poweredRaceZ π hπ)
    _ ≤ ∑ a, ∑ i ∈ univ.erase a, π a * (π i * J) :=
      Finset.sum_le_sum fun a _ => hcell a
    _ = J * (1 - ∑ i, π i ^ 2) := by
      have hsum (a : κ) : ∑ i ∈ univ.erase a, π i = 1 - π a := by
        have h := Finset.sum_erase_add (s := (univ : Finset κ))
          (f := π) (mem_univ a)
        rw [hπtotal] at h
        linarith
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, hsum]
      calc
        (∑ a, π a * ((1 - π a) * J)) =
            J * ((∑ a, π a) - ∑ a, π a ^ 2) := by
          rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = _ := by rw [hπtotal]

/-- The fourth-power normalization cost is at most the certified scalar
bound times categorical variance. -/
theorem integral_log_poweredRaceZ_le
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1) :
    (∫ E : κ → ℝ, Real.log (poweredRaceZ π E) ∂clockLaw κ) ≤
      poweredRaceJ4Upper * (1 - ∑ i, π i ^ 2) :=
  integral_log_poweredRaceZ_le_of_loser_integral poweredRaceJ4Upper
    (fun _ hp0 hp1 => powered_loser_mobius_integral_le hp0 hp1) π hπ hπtotal

end SharedRace
end stoch_to_det
