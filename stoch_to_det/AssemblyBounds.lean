import stoch_to_det.Prelude

/-! Elementary tangent bounds used by the calibrated information floor. -/

namespace stoch_to_det

/-- The tangent-line bound for the square root at the positive point `s`. -/
theorem sqrt_tangent (t s : ℝ) (ht : 0 ≤ t) (hs : 0 < s) :
    Real.sqrt t ≤ (t + s ^ 2) / (2 * s) := by
  apply (le_div_iff₀ (by positivity : 0 < 2 * s)).2
  have hsqrt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hsqrt_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  have hsq : 0 ≤ (Real.sqrt t - s) ^ 2 := sq_nonneg _
  nlinarith

/-- The tangent-line bound for the fourth root at the positive point `b`. -/
theorem qrt_tangent (t b : ℝ) (ht : 0 ≤ t) (hb : 0 < b) :
    t ^ ((1 : ℝ) / 4) ≤ (t + 3 * b ^ 4) / (4 * b ^ 3) := by
  let u : ℝ := t ^ ((1 : ℝ) / 4)
  have hu : 0 ≤ u := Real.rpow_nonneg ht _
  have hu4 : u ^ 4 = t := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    norm_num
  have hquad : 0 ≤ u ^ 2 + 2 * u * b + 3 * b ^ 2 := by positivity
  have hfactor : 0 ≤ (u - b) ^ 2 * (u ^ 2 + 2 * u * b + 3 * b ^ 2) :=
    mul_nonneg (sq_nonneg _) hquad
  have hid :
      (u - b) ^ 2 * (u ^ 2 + 2 * u * b + 3 * b ^ 2) =
        u ^ 4 - 4 * u * b ^ 3 + 3 * b ^ 4 := by
    ring
  rw [hid, hu4] at hfactor
  change u ≤ (t + 3 * b ^ 4) / (4 * b ^ 3)
  apply (le_div_iff₀ (by positivity : 0 < 4 * b ^ 3)).2
  nlinarith

end stoch_to_det
