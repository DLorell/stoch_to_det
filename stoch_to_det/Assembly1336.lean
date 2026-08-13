import stoch_to_det.Constants1336

/-!
# Elementary assembly bounds for the calibrated `1336` ledger

Tangent-line estimates for the square-root and fourth-root terms, followed by
an exact rational cap for their sum.
-/

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

/-- Exact rational cap for the square-root plus fourth-root assembly term. -/
theorem assembly_cap (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ (116 : ℝ) / 10000) :
    Real.sqrt (((259 : ℝ) / 100) * x) +
        (((5062 : ℝ) / 10000) * y) ^ ((1 : ℝ) / 4) ≤
      (3565 : ℝ) / 10000 := by
  have ht₁ : 0 ≤ ((259 : ℝ) / 100) * x := by positivity
  have ht₂ : 0 ≤ ((5062 : ℝ) / 10000) * y := by positivity
  have hsqrt := sqrt_tangent (((259 : ℝ) / 100) * x)
    ((1247 : ℝ) / 10000) ht₁ (by norm_num)
  have hqrt := qrt_tangent (((5062 : ℝ) / 10000) * y)
    ((2301 : ℝ) / 10000) ht₂ (by norm_num)
  have hlin₁ :
      ((((259 : ℝ) / 100) * x + ((1247 : ℝ) / 10000) ^ 2) /
          (2 * ((1247 : ℝ) / 10000))) ≤
        ((1039 : ℝ) / 100) * x + (1247 : ℝ) / 20000 := by
    norm_num
    nlinarith
  have hlin₂ :
      ((((5062 : ℝ) / 10000) * y + 3 * ((2301 : ℝ) / 10000) ^ 4) /
          (4 * ((2301 : ℝ) / 10000) ^ 3)) ≤
        ((1039 : ℝ) / 100) * y + 3 * (2301 : ℝ) / 40000 := by
    norm_num
    nlinarith
  calc
    Real.sqrt (((259 : ℝ) / 100) * x) +
          (((5062 : ℝ) / 10000) * y) ^ ((1 : ℝ) / 4) ≤
        ((((259 : ℝ) / 100) * x + ((1247 : ℝ) / 10000) ^ 2) /
            (2 * ((1247 : ℝ) / 10000))) +
          ((((5062 : ℝ) / 10000) * y + 3 * ((2301 : ℝ) / 10000) ^ 4) /
            (4 * ((2301 : ℝ) / 10000) ^ 3)) := add_le_add hsqrt hqrt
    _ ≤ (((1039 : ℝ) / 100) * x + (1247 : ℝ) / 20000) +
          (((1039 : ℝ) / 100) * y + 3 * (2301 : ℝ) / 40000) :=
      add_le_add hlin₁ hlin₂
    _ ≤ (3565 : ℝ) / 10000 := by
      norm_num at hxy ⊢
      nlinarith

/-- The assembly cap lies strictly below the calibrated HGR threshold. -/
theorem cap_lt_rho1336 : (3565 : ℝ) / 10000 < 479 / 1296 := by
  norm_num

end stoch_to_det
