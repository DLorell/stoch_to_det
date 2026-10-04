import stoch_to_det.PoweredRaceSixth

/-! A bounded-interval correction to the five-term logarithm majorant. -/

namespace stoch_to_det

/-- The corrected sixth-power normalization constant. -/
noncomputable def poweredRaceJ6Refined : ℝ := poweredRaceJ6Upper - 1 / 420

namespace SharedRace.Sixth

open Set MeasureTheory
open scoped Interval

/-- On the unit interval, half the next alternating term improves the
five-term logarithm majorant. -/
theorem log_one_add_le_five_terms_refined {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.log (1 + x) ≤ logTaylor5 x - x ^ 6 / 12 := by
  let F : ℝ → ℝ := fun x => logTaylor5 x - x ^ 6 / 12 - Real.log (1 + x)
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivAt F (x ^ 5 * (1 - x) / (2 * (1 + x))) x := by
    have hxne : 1 + x ≠ 0 := ne_of_gt (by linarith [hx.1])
    have hp := ((((((((hasDerivAt_id x).pow 1).div_const 1).sub
      (((hasDerivAt_id x).pow 2).div_const 2)).add
      (((hasDerivAt_id x).pow 3).div_const 3)).sub
      (((hasDerivAt_id x).pow 4).div_const 4)).add
      (((hasDerivAt_id x).pow 5).div_const 5)).sub
      (((hasDerivAt_id x).pow 6).div_const 12)).sub
      (((hasDerivAt_id x).const_add 1).log hxne)
    apply hp.congr_deriv
    norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, pow_zero]
    field_simp [hxne]
    ring
  have hmono : MonotoneOn F (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' : y ∈ Icc (0 : ℝ) 1 := interior_subset hy
      rw [(hd y hy').deriv]
      exact div_nonneg
        (mul_nonneg (pow_nonneg hy'.1 _) (sub_nonneg.mpr hy'.2))
        (by linarith [hy'.1])
  have h := hmono (by norm_num) ⟨hx0, hx1⟩ hx0
  norm_num [F, logTaylor5] at h
  simpa [logTaylor5] using h

noncomputable def loserLogPolynomialRefined (x : ℝ) : ℝ :=
  loserLogPolynomial x - x ^ 34 / 12

private lemma loserLogPolynomialRefined_identity (x : ℝ) :
    logTaylor5 (x ^ 6) - (x ^ 6) ^ 6 / 12 =
      x ^ 2 * loserLogPolynomialRefined x := by
  rw [loserLogPolynomial_identity]
  unfold loserLogPolynomialRefined
  ring

theorem integral_loserLogPolynomial_refined :
    (∫ x : ℝ in 0..1, loserLogPolynomialRefined x) = poweredRaceJ6Refined := by
  have hP : IntervalIntegrable loserLogPolynomial volume 0 1 :=
    (by unfold loserLogPolynomial; fun_prop : Continuous loserLogPolynomial).intervalIntegrable _ _
  have hQ : IntervalIntegrable (fun x : ℝ => x ^ 34 / 12) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 34 / 12)).intervalIntegrable _ _
  unfold loserLogPolynomialRefined
  rw [intervalIntegral.integral_sub hP hQ, integral_loserLogPolynomial,
    intervalIntegral.integral_div, integral_pow]
  norm_num [poweredRaceJ6Refined]

/-- The corrected scalar integral bound used by the powered race. -/
theorem powered_loser_mobius_integral_le_refined {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ v : ℝ in 0..1, Real.log (1 + (mobius p v) ^ 6)) ≤ p * poweredRaceJ6Refined := by
  have hlogcont : Continuous (fun x : ℝ => Real.log (1 + x ^ 6)) := by
    apply Continuous.log (by fun_prop)
    intro x
    positivity
  rw [integral_comp_mobius hp0 hp1 hlogcont.continuousOn]
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < p + (1 - p) * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1.le) hx.1]
  have hdens : ContinuousOn (mobiusDensity p) (Icc (0 : ℝ) 1) := by
    unfold mobiusDensity
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    exact pow_ne_zero _ (hd x hx).ne'
  have hi1 : IntervalIntegrable
      (fun x : ℝ => mobiusDensity p x * Real.log (1 + x ^ 6)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro x hx
    exact (hdens x hx).mul hlogcont.continuousAt.continuousWithinAt
  have hi2 : IntervalIntegrable (fun x : ℝ => p * loserLogPolynomialRefined x) volume 0 1 :=
    (by unfold loserLogPolynomialRefined loserLogPolynomial; fun_prop :
      Continuous (fun x : ℝ => p * loserLogPolynomialRefined x)).intervalIntegrable _ _
  have hbound :
      (∫ x : ℝ in 0..1, mobiusDensity p x * Real.log (1 + x ^ 6)) ≤
        ∫ x : ℝ in 0..1, p * loserLogPolynomialRefined x := by
    apply intervalIntegral.integral_mono_on (by norm_num) hi1 hi2
    intro x hx
    by_cases hxzero : x = 0
    · subst x
      norm_num [loserLogPolynomialRefined, loserLogPolynomial]
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxzero)
    have hpoly := log_one_add_le_five_terms_refined
      (show 0 ≤ x ^ 6 by positivity) (pow_le_one₀ hx.1 hx.2)
    rw [loserLogPolynomialRefined_identity] at hpoly
    have hlog0 : 0 ≤ Real.log (1 + x ^ 6) :=
      Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    have hP0 : 0 ≤ loserLogPolynomialRefined x :=
      nonneg_of_mul_nonneg_right (hlog0.trans hpoly) (sq_pos_of_pos hxpos)
    have hd0 : 0 ≤ mobiusDensity p x := by unfold mobiusDensity; positivity
    have hdenx : x ≤ p + (1 - p) * x := by
      nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hx.2)]
    have hdx : mobiusDensity p x * x ^ 2 ≤ p := by
      unfold mobiusDensity
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (sq_pos_of_pos (hd x hx))).2
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hdenx 2) hp0.le
    calc
      mobiusDensity p x * Real.log (1 + x ^ 6) ≤
          mobiusDensity p x * (x ^ 2 * loserLogPolynomialRefined x) :=
        mul_le_mul_of_nonneg_left hpoly hd0
      _ = (mobiusDensity p x * x ^ 2) * loserLogPolynomialRefined x := by ring
      _ ≤ p * loserLogPolynomialRefined x := mul_le_mul_of_nonneg_right hdx hP0
  rw [intervalIntegral.integral_const_mul, integral_loserLogPolynomial_refined] at hbound
  exact hbound


/-- The refined sixth-power normalization bound retains prior dispersion. -/
theorem integral_log_poweredRaceZ_le_refined
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1) :
    (∫ E : κ → ℝ, Real.log (poweredRaceZ π E) ∂clockLaw κ) ≤
      poweredRaceJ6Refined * (1 - ∑ i, π i ^ 2) :=
  integral_log_poweredRaceZ_le_of_loser_integral poweredRaceJ6Refined
    (fun _ hp0 hp1 => powered_loser_mobius_integral_le_refined hp0 hp1) π hπ hπtotal

end SharedRace.Sixth

namespace SharedRace

universe u

/-- Refined sixth-power entropy estimate for arbitrary finite sources. -/
theorem sharedRaceEntropy_le_sixth_refined
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) :
    sharedRaceEntropy μ r ≤
      (6 + poweredRaceJ6Refined) * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        poweredRaceJ6Refined / Real.log 2 * categoricalMismatch μ r := by
  apply Sixth.sharedRaceEntropy_le_powered_of_dispersion hμ hr hrpos
    (by norm_num [poweredRaceJ6Refined, poweredRaceJ6Upper])
  · intro π hπ hπpos
    exact Sixth.integral_log_poweredRaceZ_le_refined π hπpos hπ.total
  · exact posteriorMean_mismatch_le hμ hr hrpos

end SharedRace
end stoch_to_det
