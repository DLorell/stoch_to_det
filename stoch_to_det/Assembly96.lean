import stoch_to_det.AssemblyBounds
import stoch_to_det.Constants96

/-! Exact two-tangent assembly at the information budget used by `T_le_96`. -/

namespace stoch_to_det

theorem assembly_cap_96 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ (231 : ℝ) / 10000) :
    Real.sqrt (((259 : ℝ) / 100) * x) +
        (((5062 : ℝ) / 10000) * y) ^ ((1 : ℝ) / 4) ≤
          (4511 : ℝ) / 10000 := by
  have ht₁ : 0 ≤ ((259 : ℝ) / 100) * x := by positivity
  have ht₂ : 0 ≤ ((5062 : ℝ) / 10000) * y := by positivity
  have hsqrt := sqrt_tangent (((259 : ℝ) / 100) * x)
    ((937 : ℝ) / 5000) ht₁ (by norm_num)
  have hqrt := qrt_tangent (((5062 : ℝ) / 10000) * y)
    ((659 : ℝ) / 2500) ht₂ (by norm_num)
  have hslope :
      (1977343750 : ℝ) / 286191179 < (6475 : ℝ) / 937 := by
    norm_num
  have hlin₁ :
      ((((259 : ℝ) / 100) * x + ((937 : ℝ) / 5000) ^ 2) /
          (2 * ((937 : ℝ) / 5000))) =
        ((6475 : ℝ) / 937) * x + (937 : ℝ) / 10000 := by
    ring
  have hlin₂ :
      ((((5062 : ℝ) / 10000) * y + 3 * ((659 : ℝ) / 2500) ^ 4) /
          (4 * ((659 : ℝ) / 2500) ^ 3)) =
        ((1977343750 : ℝ) / 286191179) * y +
          (1977 : ℝ) / 10000 := by
    ring
  calc
    Real.sqrt (((259 : ℝ) / 100) * x) +
          (((5062 : ℝ) / 10000) * y) ^ ((1 : ℝ) / 4) ≤
        ((((259 : ℝ) / 100) * x + ((937 : ℝ) / 5000) ^ 2) /
            (2 * ((937 : ℝ) / 5000))) +
          ((((5062 : ℝ) / 10000) * y + 3 * ((659 : ℝ) / 2500) ^ 4) /
            (4 * ((659 : ℝ) / 2500) ^ 3)) := add_le_add hsqrt hqrt
    _ = (((6475 : ℝ) / 937) * x + (937 : ℝ) / 10000) +
          (((1977343750 : ℝ) / 286191179) * y +
            (1977 : ℝ) / 10000) := by
      rw [hlin₁, hlin₂]
    _ ≤ (((6475 : ℝ) / 937) * x + (937 : ℝ) / 10000) +
          (((6475 : ℝ) / 937) * y + (1977 : ℝ) / 10000) := by
      gcongr
    _ ≤ (4511 : ℝ) / 10000 := by
      norm_num at hxy ⊢
      nlinarith

theorem assembly_cap_96_lt_rho : (4511 : ℝ) / 10000 < rho96 := by
  rw [rho96_eq_value]
  norm_num

end stoch_to_det
