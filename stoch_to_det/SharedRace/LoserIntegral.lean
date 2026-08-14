import stoch_to_det.SharedRace.Scalar

/-!
# The loser-coordinate integral

After the scaled Beta(2, k-2) exponential moment is compared with a
Gamma(2,1) moment, the losing-coordinate contribution reduces to the single
rational integral proved here.  Keeping this algebra separate makes the
clock-law module responsible only for distributional identities.
-/

namespace stoch_to_det
namespace SharedRace

open Set MeasureTheory
open scoped Interval

local notation "L" => SharedRace.logTwo

/-- The simplified losing-coordinate integral produced by the Möbius change
of variables is bounded by the scalar expression used in
`coordinateContribution_le`. -/
theorem loserRationalIntegral_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ x : ℝ in 0..1,
      p * x ^ 2 /
        (p * (1 - L) + ((1 - p) + L) * x) ^ 2) ≤
      p /
        ((1 + L * (1 - p)) ^ 2 *
          (1 + 2 * (p * (1 - L) / (1 + L * (1 - p))))) := by
  let D : ℝ := 1 + L * (1 - p)
  let r : ℝ := p * (1 - L) / D
  have hL0 : 0 < L := SharedRace.L_pos
  have hL1 : L < 1 := SharedRace.L_lt_one
  have hp1' : p ≤ 1 := hp1.le
  have hD : 0 < D := by
    dsimp [D]
    nlinarith
  have hr0 : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r ≤ 1 := by
    apply (div_le_one hD).2
    dsimp [D]
    nlinarith
  have hden (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      0 < r + (1 - r) * x := by
    have hxr : 0 ≤ (1 - r) * x :=
      mul_nonneg (sub_nonneg.mpr hr1) hx.1
    linarith
  have hfactor (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      p * x ^ 2 /
          (p * (1 - L) + ((1 - p) + L) * x) ^ 2 =
        (p / D ^ 2) * (x / (r + (1 - r) * x)) ^ 2 := by
    have hDr : D * r = p * (1 - L) := by
      dsimp [r]
      field_simp [hD.ne']
    have hDone : D * (1 - r) = (1 - p) + L := by
      calc
        D * (1 - r) = D - D * r := by ring
        _ = D - p * (1 - L) := by rw [hDr]
        _ = (1 - p) + L := by
          dsimp [D]
          ring
    have hlinear :
        p * (1 - L) + ((1 - p) + L) * x =
          D * (r + (1 - r) * x) := by
      rw [mul_add, hDr, ← mul_assoc, hDone]
    rw [hlinear]
    field_simp [hD.ne', (hden x hx).ne']
  have hEq :
      (∫ x : ℝ in 0..1,
        p * x ^ 2 /
          (p * (1 - L) + ((1 - p) + L) * x) ^ 2) =
        (p / D ^ 2) *
          ∫ x : ℝ in 0..1, (x / (r + (1 - r) * x)) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    exact hfactor x hx'
  rw [hEq]
  have hbase := SharedRace.integral_sq_div_affine_le hr0 hr1
  have hcoeff : 0 ≤ p / D ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbase hcoeff
  calc
    (p / D ^ 2) *
        (∫ x : ℝ in 0..1, (x / (r + (1 - r) * x)) ^ 2) ≤
        (p / D ^ 2) * (1 / (1 + 2 * r)) := hmul
    _ = p / (D ^ 2 * (1 + 2 * r)) := by
      have hlast : 0 < 1 + 2 * r := by positivity
      field_simp [hD.ne', hlast.ne']
    _ = _ := by rfl

/-- Algebraic cancellation of the Möbius density against the Gamma(2,1)
moment denominator. -/
lemma mobiusGamma_integrand_eq {p x : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hx0 : 0 ≤ x) :
    p / (p + (1 - p) * x) ^ 2 * x ^ 2 *
        (1 - L * ((p - x) / (p + (1 - p) * x)))⁻¹ ^ 2 =
      p * x ^ 2 /
        (p * (1 - L) + ((1 - p) + L) * x) ^ 2 := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1.le
  have hbase : 0 < p + (1 - p) * x := by
    nlinarith [mul_nonneg hq hx0]
  have hL : L < 1 := SharedRace.L_lt_one
  have hnum : 0 < p * (1 - L) + ((1 - p) + L) * x := by
    have hfirst : 0 < p * (1 - L) := mul_pos hp0 (sub_pos.mpr hL)
    have hsecond : 0 ≤ ((1 - p) + L) * x := by
      exact mul_nonneg (add_nonneg hq SharedRace.L_pos.le) hx0
    linarith
  have hone :
      1 - L * ((p - x) / (p + (1 - p) * x)) =
        (p * (1 - L) + ((1 - p) + L) * x) /
          (p + (1 - p) * x) := by
    field_simp [hbase.ne']
    ring
  rw [hone]
  field_simp [hbase.ne', hnum.ne']

/-- The complete rational integral after both the Möbius density and the
Gamma(2,1) moment have been inserted. -/
theorem loserMobiusGammaIntegral_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ x : ℝ in 0..1,
      p / (p + (1 - p) * x) ^ 2 * x ^ 2 *
        (1 - L * ((p - x) / (p + (1 - p) * x)))⁻¹ ^ 2) ≤
      p /
        ((1 + L * (1 - p)) ^ 2 *
          (1 + 2 * (p * (1 - L) / (1 + L * (1 - p))))) := by
  calc
    (∫ x : ℝ in 0..1,
      p / (p + (1 - p) * x) ^ 2 * x ^ 2 *
        (1 - L * ((p - x) / (p + (1 - p) * x)))⁻¹ ^ 2) =
      ∫ x : ℝ in 0..1,
        p * x ^ 2 /
          (p * (1 - L) + ((1 - p) + L) * x) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
        exact mobiusGamma_integrand_eq hp0 hp1 hx'.1
    _ ≤ _ := loserRationalIntegral_le hp0 hp1

end SharedRace
end stoch_to_det
