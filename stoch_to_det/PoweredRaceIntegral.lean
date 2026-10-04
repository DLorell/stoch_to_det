import stoch_to_det.PairChargeScalar
import stoch_to_det.SharedRace.Mobius
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A rational upper bound on the fourth-power race normalization integral. -/
namespace stoch_to_det
namespace SharedRace

open Set MeasureTheory
open scoped Interval

noncomputable def logTaylor9 (x : ℝ) : ℝ :=
  x ^ 1 / 1 - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 + x ^ 5 / 5 - x ^ 6 / 6 + x ^ 7 / 7 - x ^ 8 / 8 + x ^ 9 / 9

/-- Nine alternating terms give a global upper bound on the positive axis. -/
theorem log_one_add_le_nine_terms {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1+x) ≤ logTaylor9 x := by
  let F : ℝ → ℝ := fun x => logTaylor9 x - Real.log (1+x)
  have hd (x : ℝ) (hx : 0 ≤ x) : HasDerivAt F (x^9/(1+x)) x := by
    have hx1 : 1+x ≠ 0 := ne_of_gt (by linarith)
    have hp := (((((((((((hasDerivAt_id x).pow 1).div_const 1).sub (((hasDerivAt_id x).pow 2).div_const 2)).add (((hasDerivAt_id x).pow 3).div_const 3)).sub (((hasDerivAt_id x).pow 4).div_const 4)).add (((hasDerivAt_id x).pow 5).div_const 5)).sub (((hasDerivAt_id x).pow 6).div_const 6)).add (((hasDerivAt_id x).pow 7).div_const 7)).sub (((hasDerivAt_id x).pow 8).div_const 8)).add (((hasDerivAt_id x).pow 9).div_const 9)).sub
      (((hasDerivAt_id x).const_add 1).log hx1)
    apply hp.congr_deriv
    norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, pow_zero]
    field_simp [hx1]
    ring
  have hmono : MonotoneOn F (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := (interior_subset hy : y ∈ Set.Ici 0)
      exact (hd y hy0).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := (interior_subset hy : y ∈ Set.Ici 0)
      rw [(hd y hy0).deriv]
      exact div_nonneg (pow_nonneg hy0 9) (by linarith)
  have h := hmono (by simp) hx hx
  norm_num [F, logTaylor9] at h
  simpa [logTaylor9] using h

/-- Integrability of the scalar fourth-power normalizer on the positive tail. -/
theorem integrable_log_one_add_rpow_neg_four :
    IntegrableOn (fun x : ℝ => Real.log (1 + x ^ (-4 : ℝ))) (Ioi 1) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)
  apply hi.mono' (Real.measurable_log.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hp : 0 ≤ x ^ (-4 : ℝ) := Real.rpow_nonneg hx0.le _
  have hlog : 0 ≤ Real.log (1 + x ^ (-4 : ℝ)) := Real.log_nonneg (by linarith)
  simp only [Function.comp_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg hlog]
  have hh := Real.log_le_sub_one_of_pos (show 0 < 1+x^(-4:ℝ) by linarith)
  linarith

/-- Exact integration of the nine-term majorant gives the rational race constant. -/
theorem integral_log_one_add_rpow_neg_four_le :
    (∫ x : ℝ in Ioi 1, Real.log (1 + x ^ (-4 : ℝ))) ≤ poweredRaceJ4Upper := by
  have h1 : IntegrableOn (fun x : ℝ => x ^ (-4 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h2 : IntegrableOn (fun x : ℝ => x ^ (-8 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h3 : IntegrableOn (fun x : ℝ => x ^ (-12 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h4 : IntegrableOn (fun x : ℝ => x ^ (-16 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h5 : IntegrableOn (fun x : ℝ => x ^ (-20 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h6 : IntegrableOn (fun x : ℝ => x ^ (-24 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h7 : IntegrableOn (fun x : ℝ => x ^ (-28 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h8 : IntegrableOn (fun x : ℝ => x ^ (-32 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h9 : IntegrableOn (fun x : ℝ => x ^ (-36 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  let P : ℝ → ℝ := fun x => x ^ (-4 : ℝ) / 1 - x ^ (-8 : ℝ) / 2 + x ^ (-12 : ℝ) / 3 - x ^ (-16 : ℝ) / 4 + x ^ (-20 : ℝ) / 5 - x ^ (-24 : ℝ) / 6 + x ^ (-28 : ℝ) / 7 - x ^ (-32 : ℝ) / 8 + x ^ (-36 : ℝ) / 9
  have hP : IntegrableOn P (Ioi 1) := ((((((((h1.div_const 1).sub (h2.div_const 2)).add (h3.div_const 3)).sub (h4.div_const 4)).add (h5.div_const 5)).sub (h6.div_const 6)).add (h7.div_const 7)).sub (h8.div_const 8)).add (h9.div_const 9)
  have hpoint (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      Real.log (1+x^(-4:ℝ)) ≤ P x := by
    have hx0 : 0 ≤ x := (lt_trans zero_lt_one hx).le
    have h := log_one_add_le_nine_terms (Real.rpow_nonneg hx0 (-4))
    have hp (n : ℕ) : (x ^ (-4 : ℝ)) ^ n = x ^ (-4 * (n : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num [logTaylor9, hp, ← pow_mul] at h
    simpa [P] using h
  have hle := integral_mono_ae integrable_log_one_add_rpow_neg_four hP
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; exact hpoint x hx)
  have hPi : (∫ x : ℝ in Ioi 1, P x) = poweredRaceJ4Upper := by
    dsimp only [P]
    rw [integral_add (f := fun x : ℝ => x ^ (-4 : ℝ) / 1 - x ^ (-8 : ℝ) / 2 + x ^ (-12 : ℝ) / 3 - x ^ (-16 : ℝ) / 4 + x ^ (-20 : ℝ) / 5 - x ^ (-24 : ℝ) / 6 + x ^ (-28 : ℝ) / 7 - x ^ (-32 : ℝ) / 8) (g := fun x : ℝ => x ^ (-36 : ℝ) / 9) ((((((((h1.div_const 1).sub (h2.div_const 2)).add (h3.div_const 3)).sub (h4.div_const 4)).add (h5.div_const 5)).sub (h6.div_const 6)).add (h7.div_const 7)).sub (h8.div_const 8)) (h9.div_const 9)]
    rw [integral_sub (f := fun x : ℝ => x ^ (-4 : ℝ) / 1 - x ^ (-8 : ℝ) / 2 + x ^ (-12 : ℝ) / 3 - x ^ (-16 : ℝ) / 4 + x ^ (-20 : ℝ) / 5 - x ^ (-24 : ℝ) / 6 + x ^ (-28 : ℝ) / 7) (g := fun x : ℝ => x ^ (-32 : ℝ) / 8) (((((((h1.div_const 1).sub (h2.div_const 2)).add (h3.div_const 3)).sub (h4.div_const 4)).add (h5.div_const 5)).sub (h6.div_const 6)).add (h7.div_const 7)) (h8.div_const 8)]
    rw [integral_add (f := fun x : ℝ => x ^ (-4 : ℝ) / 1 - x ^ (-8 : ℝ) / 2 + x ^ (-12 : ℝ) / 3 - x ^ (-16 : ℝ) / 4 + x ^ (-20 : ℝ) / 5 - x ^ (-24 : ℝ) / 6) (g := fun x : ℝ => x ^ (-28 : ℝ) / 7) ((((((h1.div_const 1).sub (h2.div_const 2)).add (h3.div_const 3)).sub (h4.div_const 4)).add (h5.div_const 5)).sub (h6.div_const 6)) (h7.div_const 7)]
    rw [integral_sub (f := fun x : ℝ => x ^ (-4 : ℝ) / 1 - x ^ (-8 : ℝ) / 2 + x ^ (-12 : ℝ) / 3 - x ^ (-16 : ℝ) / 4 + x ^ (-20 : ℝ) / 5) (g := fun x : ℝ => x ^ (-24 : ℝ) / 6) (((((h1.div_const 1).sub (h2.div_const 2)).add (h3.div_const 3)).sub (h4.div_const 4)).add (h5.div_const 5)) (h6.div_const 6)]
    rw [integral_add (f := fun x : ℝ => x ^ (-4 : ℝ) / 1 - x ^ (-8 : ℝ) / 2 + x ^ (-12 : ℝ) / 3 - x ^ (-16 : ℝ) / 4) (g := fun x : ℝ => x ^ (-20 : ℝ) / 5) ((((h1.div_const 1).sub (h2.div_const 2)).add (h3.div_const 3)).sub (h4.div_const 4)) (h5.div_const 5)]
    rw [integral_sub (f := fun x : ℝ => x ^ (-4 : ℝ) / 1 - x ^ (-8 : ℝ) / 2 + x ^ (-12 : ℝ) / 3) (g := fun x : ℝ => x ^ (-16 : ℝ) / 4) (((h1.div_const 1).sub (h2.div_const 2)).add (h3.div_const 3)) (h4.div_const 4)]
    rw [integral_add (f := fun x : ℝ => x ^ (-4 : ℝ) / 1 - x ^ (-8 : ℝ) / 2) (g := fun x : ℝ => x ^ (-12 : ℝ) / 3) ((h1.div_const 1).sub (h2.div_const 2)) (h3.div_const 3)]
    rw [integral_sub (f := fun x : ℝ => x ^ (-4 : ℝ) / 1) (g := fun x : ℝ => x ^ (-8 : ℝ) / 2) (h1.div_const 1) (h2.div_const 2)]
    simp_rw [integral_div]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-8 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-12 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-16 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-20 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-24 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-28 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-32 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-36 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
    norm_num [poweredRaceJ4Upper]
  rwa [hPi] at hle

noncomputable def loserLogPolynomial (x : ℝ) : ℝ :=
  x ^ 2 / 1 - x ^ 6 / 2 + x ^ 10 / 3 - x ^ 14 / 4 + x ^ 18 / 5 - x ^ 22 / 6 + x ^ 26 / 7 - x ^ 30 / 8 + x ^ 34 / 9

theorem loserLogPolynomial_identity (x : ℝ) :
    logTaylor9 (x^4) = x^2*loserLogPolynomial x := by
  unfold logTaylor9 loserLogPolynomial
  ring

theorem integral_loserLogPolynomial :
    (∫ x : ℝ in 0..1, loserLogPolynomial x) = poweredRaceJ4Upper := by
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ 2 / 1) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 2 / 1)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ => x ^ 6 / 2) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 6 / 2)).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun x : ℝ => x ^ 10 / 3) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 10 / 3)).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun x : ℝ => x ^ 14 / 4) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 14 / 4)).intervalIntegrable _ _
  have h5 : IntervalIntegrable (fun x : ℝ => x ^ 18 / 5) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 18 / 5)).intervalIntegrable _ _
  have h6 : IntervalIntegrable (fun x : ℝ => x ^ 22 / 6) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 22 / 6)).intervalIntegrable _ _
  have h7 : IntervalIntegrable (fun x : ℝ => x ^ 26 / 7) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 26 / 7)).intervalIntegrable _ _
  have h8 : IntervalIntegrable (fun x : ℝ => x ^ 30 / 8) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 30 / 8)).intervalIntegrable _ _
  have h9 : IntervalIntegrable (fun x : ℝ => x ^ 34 / 9) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 34 / 9)).intervalIntegrable _ _
  unfold loserLogPolynomial
  rw [intervalIntegral.integral_add (f := fun x : ℝ => x ^ 2 / 1 - x ^ 6 / 2 + x ^ 10 / 3 - x ^ 14 / 4 + x ^ 18 / 5 - x ^ 22 / 6 + x ^ 26 / 7 - x ^ 30 / 8) (g := fun x : ℝ => x ^ 34 / 9) ((((((((h1).sub h2).add h3).sub h4).add h5).sub h6).add h7).sub h8) h9]
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x ^ 2 / 1 - x ^ 6 / 2 + x ^ 10 / 3 - x ^ 14 / 4 + x ^ 18 / 5 - x ^ 22 / 6 + x ^ 26 / 7) (g := fun x : ℝ => x ^ 30 / 8) (((((((h1).sub h2).add h3).sub h4).add h5).sub h6).add h7) h8]
  rw [intervalIntegral.integral_add (f := fun x : ℝ => x ^ 2 / 1 - x ^ 6 / 2 + x ^ 10 / 3 - x ^ 14 / 4 + x ^ 18 / 5 - x ^ 22 / 6) (g := fun x : ℝ => x ^ 26 / 7) ((((((h1).sub h2).add h3).sub h4).add h5).sub h6) h7]
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x ^ 2 / 1 - x ^ 6 / 2 + x ^ 10 / 3 - x ^ 14 / 4 + x ^ 18 / 5) (g := fun x : ℝ => x ^ 22 / 6) (((((h1).sub h2).add h3).sub h4).add h5) h6]
  rw [intervalIntegral.integral_add (f := fun x : ℝ => x ^ 2 / 1 - x ^ 6 / 2 + x ^ 10 / 3 - x ^ 14 / 4) (g := fun x : ℝ => x ^ 18 / 5) ((((h1).sub h2).add h3).sub h4) h5]
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x ^ 2 / 1 - x ^ 6 / 2 + x ^ 10 / 3) (g := fun x : ℝ => x ^ 14 / 4) (((h1).sub h2).add h3) h4]
  rw [intervalIntegral.integral_add (f := fun x : ℝ => x ^ 2 / 1 - x ^ 6 / 2) (g := fun x : ℝ => x ^ 10 / 3) ((h1).sub h2) h3]
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x ^ 2 / 1) (g := fun x : ℝ => x ^ 6 / 2) (h1) h2]
  simp_rw [intervalIntegral.integral_div, integral_pow]
  norm_num [poweredRaceJ4Upper]

/-- The normalized fourth-power loser contributes at most its prior mass
 times the universal rational normalization constant. -/
theorem powered_loser_mobius_integral_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ v : ℝ in 0..1, Real.log (1+(mobius p v)^4)) ≤ p*poweredRaceJ4Upper := by
  have hlogcont : Continuous (fun x : ℝ => Real.log (1+x^4)) := by
    apply Continuous.log (by fun_prop)
    intro x
    positivity
  rw [integral_comp_mobius hp0 hp1 hlogcont.continuousOn]
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < p+(1-p)*x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1.le) hx.1]
  have hdens : ContinuousOn (mobiusDensity p) (Icc (0 : ℝ) 1) := by
    unfold mobiusDensity
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    exact pow_ne_zero _ (hd x hx).ne'
  have hi1 : IntervalIntegrable
      (fun x : ℝ => mobiusDensity p x * Real.log (1+x^4)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro x hx
    exact (hdens x hx).mul hlogcont.continuousAt.continuousWithinAt
  have hi2 : IntervalIntegrable (fun x : ℝ => p*loserLogPolynomial x) volume 0 1 :=
    (by unfold loserLogPolynomial; fun_prop : Continuous (fun x : ℝ => p*loserLogPolynomial x)).intervalIntegrable _ _
  have hbound : (∫ x : ℝ in 0..1, mobiusDensity p x * Real.log (1+x^4)) ≤
      ∫ x : ℝ in 0..1, p*loserLogPolynomial x := by
    apply intervalIntegral.integral_mono_on (by norm_num) hi1 hi2
    intro x hx
    by_cases hxzero : x = 0
    · subst x
      norm_num [loserLogPolynomial]
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxzero)
    have hpoly := log_one_add_le_nine_terms (show 0 ≤ x^4 by positivity)
    rw [loserLogPolynomial_identity] at hpoly
    have hlog0 : 0 ≤ Real.log (1+x^4) :=
      Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    have hP0 : 0 ≤ loserLogPolynomial x :=
      nonneg_of_mul_nonneg_right (hlog0.trans hpoly) (sq_pos_of_pos hxpos)
    have hd0 : 0 ≤ mobiusDensity p x := by unfold mobiusDensity; positivity
    have hdenx : x ≤ p+(1-p)*x := by
      nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hx.2)]
    have hdx : mobiusDensity p x * x^2 ≤ p := by
      unfold mobiusDensity
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (sq_pos_of_pos (hd x hx))).2
      have hxpow : x^2 ≤ (p+(1-p)*x)^2 := pow_le_pow_left₀ hx.1 hdenx 2
      exact mul_le_mul_of_nonneg_left hxpow hp0.le
    calc
      mobiusDensity p x * Real.log (1+x^4) ≤
          mobiusDensity p x * (x^2*loserLogPolynomial x) :=
        mul_le_mul_of_nonneg_left hpoly hd0
      _ = (mobiusDensity p x*x^2)*loserLogPolynomial x := by ring
      _ ≤ p*loserLogPolynomial x := mul_le_mul_of_nonneg_right hdx hP0
  rw [intervalIntegral.integral_const_mul, integral_loserLogPolynomial] at hbound
  exact hbound

end SharedRace
end stoch_to_det
