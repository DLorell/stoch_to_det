import stoch_to_det.CoContact

/-!
# Quartic bilinear moment bound

A feasible kernel controls a bilinear form with a quartic coefficient moment.
The proof factors each summand into the `3/4` power of a feasible `Lambda`
summand and the `1/4` power of the quartic moment, then realizes the resulting
Hölder estimate by two finite Cauchy--Schwarz inequalities.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
/-- **Quartic bilinear bound.** For nonnegative unit `ℓ²` vectors, every
nonnegative coefficient field on a subset of a feasible support satisfies

`(∑ w^{3/2} c φ ψ)^4 ≤ ∑ w^3 c^4`.

The statement is division-free and remains valid when some vector or
coefficient entries vanish. -/
theorem quartic_bilinear {S T : Finset (α × β)} (hTS : T ⊆ S)
    {w c : α × β → ℝ} (hw : Feasible S w) (hc : ∀ z ∈ T, 0 ≤ c z)
    {φ : α → ℝ} {ψ : β → ℝ} (hφ0 : ∀ x, 0 ≤ φ x) (hψ0 : ∀ y, 0 ≤ ψ y)
    (hφ2 : ∑ x, φ x ^ 2 = 1) (hψ2 : ∑ y, ψ y ^ 2 = 1) :
    (∑ z ∈ T, w z ^ ((3 : ℝ) / 2) * c z * (φ z.1 * ψ z.2)) ^ 4 ≤
      ∑ z ∈ T, (w z) ^ 3 * (c z) ^ 4 := by
  let u : α → ℝ := fun x => φ x ^ 2
  let v : β → ℝ := fun y => ψ y ^ 2
  have hu : IsPMF u := by
    constructor
    · intro x
      exact sq_nonneg (φ x)
    · simpa [mass, u] using hφ2
  have hv : IsPMF v := by
    constructor
    · intro y
      exact sq_nonneg (ψ y)
    · simpa [mass, v] using hψ2
  let A : α × β → ℝ := fun z =>
    w z * u z.1 ^ ((2 : ℝ) / 3) * v z.2 ^ ((2 : ℝ) / 3)
  let B : α × β → ℝ := fun z => (w z) ^ 3 * (c z) ^ 4
  have hA0S : ∀ z ∈ S, 0 ≤ A z := by
    intro z hz
    exact mul_nonneg
      (mul_nonneg (hw.1 z hz).le (Real.rpow_nonneg (hu.nonneg z.1) _))
      (Real.rpow_nonneg (hv.nonneg z.2) _)
  have hA0T : ∀ z ∈ T, 0 ≤ A z := fun z hz => hA0S z (hTS hz)
  have hB0 : ∀ z ∈ T, 0 ≤ B z := by
    intro z hz
    exact mul_nonneg (pow_nonneg (hw.1 z (hTS hz)).le _) (pow_nonneg (hc z hz) _)
  have hsq_rpow (a : ℝ) (ha : 0 ≤ a) :
      ((a ^ 2) ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 4) = a := by
    rw [← Real.rpow_mul (sq_nonneg a)]
    norm_num
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq ha]
  have hcube_quarter (a : ℝ) (ha : 0 ≤ a) :
      (a ^ (3 : ℕ)) ^ ((1 : ℝ) / 4) = a ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have hfourth_quarter (a : ℝ) (ha : 0 ≤ a) :
      (a ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have hterm : ∀ z ∈ T,
      w z ^ ((3 : ℝ) / 2) * c z * (φ z.1 * ψ z.2) =
        A z ^ ((3 : ℝ) / 4) * B z ^ ((1 : ℝ) / 4) := by
    intro z hz
    have hzS : z ∈ S := hTS hz
    have hwz : 0 < w z := hw.1 z hzS
    have hcz : 0 ≤ c z := hc z hz
    have hA34 :
        A z ^ ((3 : ℝ) / 4) =
          w z ^ ((3 : ℝ) / 4) * φ z.1 * ψ z.2 := by
      dsimp [A, u, v]
      rw [Real.mul_rpow
          (mul_nonneg hwz.le (Real.rpow_nonneg (sq_nonneg (φ z.1)) _))
          (Real.rpow_nonneg (sq_nonneg (ψ z.2)) _),
        Real.mul_rpow hwz.le (Real.rpow_nonneg (sq_nonneg (φ z.1)) _),
        hsq_rpow (φ z.1) (hφ0 z.1), hsq_rpow (ψ z.2) (hψ0 z.2)]
    have hB14 :
        B z ^ ((1 : ℝ) / 4) = w z ^ ((3 : ℝ) / 4) * c z := by
      dsimp [B]
      rw [Real.mul_rpow (pow_nonneg hwz.le _) (pow_nonneg hcz _),
        hcube_quarter (w z) hwz.le, hfourth_quarter (c z) hcz]
    rw [hA34, hB14]
    symm
    calc
      w z ^ ((3 : ℝ) / 4) * φ z.1 * ψ z.2 *
          (w z ^ ((3 : ℝ) / 4) * c z) =
          (w z ^ ((3 : ℝ) / 4) * w z ^ ((3 : ℝ) / 4)) *
            c z * (φ z.1 * ψ z.2) := by ring
      _ = w z ^ ((3 : ℝ) / 2) * c z * (φ z.1 * ψ z.2) := by
        rw [← Real.rpow_add hwz]
        norm_num
  have hAthree_sq : ∀ z ∈ T,
      (A z ^ ((3 : ℝ) / 4)) ^ 2 = A z * Real.sqrt (A z) := by
    intro z hz
    have hAz := hA0T z hz
    calc
      (A z ^ ((3 : ℝ) / 4)) ^ 2 = A z ^ (((3 : ℝ) / 4) * (2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hAz]
        norm_num
      _ = A z ^ ((3 : ℝ) / 2) := by norm_num
      _ = A z ^ (1 : ℝ) * A z ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add' hAz (by norm_num)]
        norm_num
      _ = A z * Real.sqrt (A z) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have hBquarter_sq : ∀ z ∈ T,
      (B z ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt (B z) := by
    intro z hz
    have hBz := hB0 z hz
    calc
      (B z ^ ((1 : ℝ) / 4)) ^ 2 = B z ^ (((1 : ℝ) / 4) * (2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hBz]
        norm_num
      _ = B z ^ ((1 : ℝ) / 2) := by norm_num
      _ = Real.sqrt (B z) := by rw [Real.sqrt_eq_rpow]
  have hcsA :
      (∑ z ∈ T, A z ^ ((3 : ℝ) / 4) * B z ^ ((1 : ℝ) / 4)) ^ 2 ≤
        (∑ z ∈ T, A z) *
          ∑ z ∈ T, Real.sqrt (A z) * Real.sqrt (B z) := by
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul T hA0T
      (fun z hz => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (fun z hz => by
        rw [mul_pow, hAthree_sq z hz, hBquarter_sq z hz]
        apply le_of_eq
        ring)
  have hcsB :
      (∑ z ∈ T, Real.sqrt (A z) * Real.sqrt (B z)) ^ 2 ≤
        (∑ z ∈ T, A z) * ∑ z ∈ T, B z := by
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul T hA0T hB0
      (fun z hz => by
        rw [mul_pow, Real.sq_sqrt (hA0T z hz), Real.sq_sqrt (hB0 z hz)])
  have hAsum0 : 0 ≤ ∑ z ∈ T, A z := Finset.sum_nonneg hA0T
  have hBsum0 : 0 ≤ ∑ z ∈ T, B z := Finset.sum_nonneg hB0
  have hholder :
      (∑ z ∈ T, A z ^ ((3 : ℝ) / 4) * B z ^ ((1 : ℝ) / 4)) ^ 4 ≤
        (∑ z ∈ T, A z) ^ 3 * ∑ z ∈ T, B z := by
    have hfirst :
        (∑ z ∈ T, A z ^ ((3 : ℝ) / 4) * B z ^ ((1 : ℝ) / 4)) ^ 4 ≤
          ((∑ z ∈ T, A z) *
            ∑ z ∈ T, Real.sqrt (A z) * Real.sqrt (B z)) ^ 2 := by
      calc
        (∑ z ∈ T, A z ^ ((3 : ℝ) / 4) * B z ^ ((1 : ℝ) / 4)) ^ 4 =
            ((∑ z ∈ T, A z ^ ((3 : ℝ) / 4) * B z ^ ((1 : ℝ) / 4)) ^ 2) ^ 2 := by
          ring
        _ ≤ ((∑ z ∈ T, A z) *
            ∑ z ∈ T, Real.sqrt (A z) * Real.sqrt (B z)) ^ 2 :=
          pow_le_pow_left₀ (sq_nonneg _) hcsA 2
    calc
      (∑ z ∈ T, A z ^ ((3 : ℝ) / 4) * B z ^ ((1 : ℝ) / 4)) ^ 4 ≤
          ((∑ z ∈ T, A z) *
            ∑ z ∈ T, Real.sqrt (A z) * Real.sqrt (B z)) ^ 2 := hfirst
      _ = (∑ z ∈ T, A z) ^ 2 *
          (∑ z ∈ T, Real.sqrt (A z) * Real.sqrt (B z)) ^ 2 := by ring
      _ ≤ (∑ z ∈ T, A z) ^ 2 *
          ((∑ z ∈ T, A z) * ∑ z ∈ T, B z) :=
        mul_le_mul_of_nonneg_left hcsB (sq_nonneg _)
      _ = (∑ z ∈ T, A z) ^ 3 * ∑ z ∈ T, B z := by ring
  have hAsum_le : (∑ z ∈ T, A z) ≤ 1 := by
    calc
      (∑ z ∈ T, A z) ≤ ∑ z ∈ S, A z := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hTS
        intro z hzS hzT
        exact hA0S z hzS
      _ = Lambda S w u v := by rfl
      _ ≤ 1 := hw.2 u v hu hv
  have hApow_le : (∑ z ∈ T, A z) ^ 3 ≤ 1 :=
    pow_le_one₀ hAsum0 hAsum_le
  calc
    (∑ z ∈ T, w z ^ ((3 : ℝ) / 2) * c z * (φ z.1 * ψ z.2)) ^ 4 =
        (∑ z ∈ T, A z ^ ((3 : ℝ) / 4) * B z ^ ((1 : ℝ) / 4)) ^ 4 := by
      congr 1
      exact Finset.sum_congr rfl hterm
    _ ≤ (∑ z ∈ T, A z) ^ 3 * ∑ z ∈ T, B z := hholder
    _ ≤ ∑ z ∈ T, B z := mul_le_of_le_one_left hBsum0 hApow_le
    _ = ∑ z ∈ T, (w z) ^ 3 * (c z) ^ 4 := rfl

end stoch_to_det
