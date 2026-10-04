import stoch_to_det.PoweredRaceWinner

/-! Finite-source entropy assembly for the powered clock reference. -/
namespace stoch_to_det.SharedRace

open Finset MeasureTheory

universe u

variable {Ω : Type u} {κ : Type}
  [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]

/-- Averaging the powered reference loss bounds shared-race entropy. -/
theorem clockSharedRaceEntropy_le_powered_reference
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i)
    (hk : 2 ≤ Fintype.card κ) :
    logTwo * clockSharedRaceEntropy μ r ≤
      4 * logTwo * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        ∫ E : κ → ℝ, Real.log (poweredRaceZ (posteriorMean μ r) E) ∂clockLaw κ := by
  let π : κ → ℝ := posteriorMean μ r
  let A : (κ → ℝ) → Ω → κ := fun E z => clockArgmin (r z) E
  let loss : Ω → (κ → ℝ) → ℝ :=
    fun z E => Real.log (1 / poweredReferencePMF π E (A E z))
  let C : ℝ := ∫ E : κ → ℝ, Real.log (poweredRaceZ π E) ∂clockLaw κ
  have hπpos : ∀ i, 0 < π i := posteriorMean_pos_of_support hμ hrpos
  have hπ : IsPMF π := posteriorMean_isPMF_of_support hμ hr
  have hπtotal : ∑ i, π i = 1 := hπ.total
  have hloss (z : Ω) (hz : μ z ≠ 0) : Integrable (loss z) (clockLaw κ) :=
    integrable_log_inv_poweredReferencePMF_clockArgmin π (r z) hπpos hπtotal
      (hrpos z hz) (hr z hz).total hk
  have hwloss (z : Ω) : Integrable (fun E => μ z * loss z E) (clockLaw κ) := by
    by_cases hz : μ z = 0
    · simp [hz]
    · exact (hloss z hz).const_mul (μ z)
  have hsumloss : Integrable (fun E => ∑ z, μ z * loss z E) (clockLaw κ) :=
    integrable_finsetSum univ fun z _ => hwloss z
  have hH : Integrable (fun E => H (push (A E) μ)) (clockLaw κ) :=
    integrable_clockSharedRaceEntropy_integrand hμ r
  have hpoint : ∀ᵐ E ∂clockLaw κ,
      logTwo * H (push (A E) μ) ≤ ∑ z, μ z * loss z E := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
    have hc := H_push_le_expected_crossEntropy hμ (A E)
      (poweredReferencePMF_isPMF π E hπpos hE)
      (poweredReferencePMF_pos π E hπpos hE)
    have hm := mul_le_mul_of_nonneg_left hc L_pos.le
    convert hm using 1 <;> try rfl
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    dsimp [loss]
    rw [lg_eq_log_div]
    change μ z * Real.log (1 / poweredReferencePMF π E (A E z)) =
      Real.log 2 * (μ z * (Real.log (1 / poweredReferencePMF π E (A E z)) / Real.log 2))
    field_simp
  have hint := integral_mono_ae (hH.const_mul logTwo) hsumloss hpoint
  rw [integral_const_mul, integral_finsetSum univ (fun z _ => hwloss z)] at hint
  simp_rw [integral_const_mul] at hint
  have hrow (z : Ω) : μ z * (∫ E, loss z E ∂clockLaw κ) =
      μ z * (4 * (∑ i, r z i * Real.log (r z i / π i)) + C) := by
    by_cases hz : μ z = 0
    · simp [hz]
    · rw [show (∫ E, loss z E ∂clockLaw κ) = _ from
        integral_log_inv_poweredReferencePMF_clockArgmin_eq π (r z)
          hπpos hπtotal (hrpos z hz) (hr z hz).total hk]
  simp_rw [hrow] at hint
  have hsum : (∑ z, μ z * (4 * (∑ i, r z i * Real.log (r z i / π i)) + C)) =
      4 * logTwo * MI Prod.fst Prod.snd (posteriorJoint μ r) + C := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, show (∑ z, μ z) = 1 from hμ.total, one_mul]
    have hm := posteriorMI_mul_logTwo_eq_expectedKL hμ hr hrpos
    calc
      (∑ z, μ z * (4 * ∑ i, r z i * Real.log (r z i / π i))) + C =
          4 * (∑ z, μ z * ∑ i, r z i * Real.log (r z i / π i)) + C := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by rw [← hm]; ring
  rw [hsum] at hint
  exact hint

/-- A normalization bound and a posterior-variance estimate give the powered
shared-race entropy bound, including singleton output alphabets. -/
theorem sharedRaceEntropy_le_powered_of_dispersion
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i)
    {J : ℝ} (hJ : 0 ≤ J)
    (hZ : ∀ (π : κ → ℝ), IsPMF π → (∀ i, 0 < π i) →
      (∫ E : κ → ℝ, Real.log (poweredRaceZ π E) ∂clockLaw κ) ≤
        J * (1 - ∑ i, π i ^ 2))
    (hdisp : 1 - ∑ i, (posteriorMean μ r i)^2 ≤
      categoricalMismatch μ r + logTwo * MI Prod.fst Prod.snd (posteriorJoint μ r)) :
    sharedRaceEntropy μ r ≤ (4 + J) * MI Prod.fst Prod.snd (posteriorJoint μ r) +
      J / logTwo * categoricalMismatch μ r := by
  classical
  by_cases hk : 2 ≤ Fintype.card κ
  · rw [sharedRaceEntropy_eq_clockSharedRaceEntropy hrpos]
    have he := clockSharedRaceEntropy_le_powered_reference hμ hr hrpos hk
    have hnorm := hZ (posteriorMean μ r) (posteriorMean_isPMF_of_support hμ hr)
      (posteriorMean_pos_of_support hμ hrpos)
    have hv := mul_le_mul_of_nonneg_left hdisp hJ
    have hcancel : logTwo * (J / logTwo * categoricalMismatch μ r) =
        J * categoricalMismatch μ r := by field_simp [L_pos.ne']
    apply le_of_mul_le_mul_left (a := logTwo) _ L_pos
    nlinarith only [he, hnorm, hv, hcancel]
  · have hcard : Fintype.card κ = 1 := by
      have hpos := Fintype.card_pos (α := κ)
      omega
    have hzero (G : κ → ℝ) : H (push (sharedWinner r G) μ) = 0 := by
      have hp := isPMF_push (f := sharedWinner r G) hμ
      apply le_antisymm
      · have hle := H_le_card hp
        simpa [hcard] using hle
      · exact H_nonneg_of_isPMF hp
    have he : sharedRaceEntropy μ r = 0 := by
      unfold sharedRaceEntropy
      simp_rw [hzero]
      simp
    rw [he]
    exact add_nonneg
      (mul_nonneg (by linarith) (MI_nonneg (posteriorJoint_isPMF_of_support hμ hr)
        Prod.fst Prod.snd))
      (mul_nonneg (div_nonneg hJ L_pos.le) (categoricalMismatch_nonneg_of_support hμ hr))

end stoch_to_det.SharedRace
