import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A scalar exponential majorant for the contact entropy estimate.

The polynomial certificates below are exact rational identities in the
Bernstein basis on the indicated intervals. -/

namespace stoch_to_det

private def entropyPolyPlus (t : ℝ) : ℝ :=
  6200 - 6150 * t ^ 2 + 6200 * t ^ 3 - 4425 * t ^ 5 + 1829 * t ^ 6

private def entropyPolyMinus (t : ℝ) : ℝ :=
  6200 - 6150 * t ^ 2 - 6200 * t ^ 3 + 4425 * t ^ 5 + 1829 * t ^ 6

private lemma entropyPolyPlus_interval0 {t : ℝ}
    (ha : 0 ≤ t) (hb : t ≤ 1) : 0 ≤ entropyPolyPlus t := by
  have hleft : 0 ≤ t - (0) := by linarith
  have hright : 0 ≤ (1) - t := by linarith
  have hid : entropyPolyPlus t =
      (6200 : ℝ) * (t - (0)) ^ 0 * ((1) - t) ^ 6 +
      (37200 : ℝ) * (t - (0)) ^ 1 * ((1) - t) ^ 5 +
      (86850 : ℝ) * (t - (0)) ^ 2 * ((1) - t) ^ 4 +
      (105600 : ℝ) * (t - (0)) ^ 3 * ((1) - t) ^ 3 +
      (74700 : ℝ) * (t - (0)) ^ 4 * ((1) - t) ^ 2 +
      (26775 : ℝ) * (t - (0)) ^ 5 * ((1) - t) ^ 1 +
      (3654 : ℝ) * (t - (0)) ^ 6 * ((1) - t) ^ 0 := by unfold entropyPolyPlus; ring
  rw [hid]
  positivity

private lemma entropyPolyPlus_interval1 {t : ℝ}
    (ha : 1 ≤ t) (hb : t ≤ 3 / 2) : 0 ≤ entropyPolyPlus t := by
  have hleft : 0 ≤ t - (1) := by linarith
  have hright : 0 ≤ (3 / 2) - t := by linarith
  have hid : entropyPolyPlus t =
      (233856 : ℝ) * (t - (1)) ^ 0 * ((3 / 2) - t) ^ 6 +
      (1247904 : ℝ) * (t - (1)) ^ 1 * ((3 / 2) - t) ^ 5 +
      (2661840 : ℝ) * (t - (1)) ^ 2 * ((3 / 2) - t) ^ 4 +
      (2833680 : ℝ) * (t - (1)) ^ 3 * ((3 / 2) - t) ^ 3 +
      (1522440 : ℝ) * (t - (1)) ^ 4 * ((3 / 2) - t) ^ 2 +
      (367914 : ℝ) * (t - (1)) ^ 5 * ((3 / 2) - t) ^ 1 +
      (33191 : ℝ) * (t - (1)) ^ 6 * ((3 / 2) - t) ^ 0 := by unfold entropyPolyPlus; ring
  rw [hid]
  positivity

private lemma entropyPolyPlus_interval2 {t : ℝ}
    (ha : 3 / 2 ≤ t) (hb : t ≤ 7 / 4) : 0 ≤ entropyPolyPlus t := by
  have hleft : 0 ≤ t - (3 / 2) := by linarith
  have hright : 0 ≤ (7 / 4) - t := by linarith
  have hid : entropyPolyPlus t =
      (2124224 : ℝ) * (t - (3 / 2)) ^ 0 * ((7 / 4) - t) ^ 6 +
      (7344768 : ℝ) * (t - (3 / 2)) ^ 1 * ((7 / 4) - t) ^ 5 +
      (7752240 : ℝ) * (t - (3 / 2)) ^ 2 * ((7 / 4) - t) ^ 4 +
      (1971840 : ℝ) * (t - (3 / 2)) ^ 3 * ((7 / 4) - t) ^ 3 +
      (1443060 : ℝ) * (t - (3 / 2)) ^ 4 * ((7 / 4) - t) ^ 2 +
      (4049208 : ℝ) * (t - (3 / 2)) ^ 5 * ((7 / 4) - t) ^ 1 +
      (2048121 : ℝ) * (t - (3 / 2)) ^ 6 * ((7 / 4) - t) ^ 0 := by unfold entropyPolyPlus; ring
  rw [hid]
  positivity

private lemma entropyPolyPlus_interval3 {t : ℝ}
    (ha : 7 / 4 ≤ t) (hb : t ≤ 2) : 0 ≤ entropyPolyPlus t := by
  have hleft : 0 ≤ t - (7 / 4) := by linarith
  have hright : 0 ≤ (2) - t := by linarith
  have hid : entropyPolyPlus t =
      (2048121 : ℝ) * (t - (7 / 4)) ^ 0 * ((2) - t) ^ 6 +
      (20528244 : ℝ) * (t - (7 / 4)) ^ 1 * ((2) - t) ^ 5 +
      (83838240 : ℝ) * (t - (7 / 4)) ^ 2 * ((2) - t) ^ 4 +
      (175303680 : ℝ) * (t - (7 / 4)) ^ 3 * ((2) - t) ^ 3 +
      (198167040 : ℝ) * (t - (7 / 4)) ^ 4 * ((2) - t) ^ 2 +
      (115482624 : ℝ) * (t - (7 / 4)) ^ 5 * ((2) - t) ^ 1 +
      (27262976 : ℝ) * (t - (7 / 4)) ^ 6 * ((2) - t) ^ 0 := by unfold entropyPolyPlus; ring
  rw [hid]
  positivity

private lemma entropyPolyPlus_tail {t : ℝ}
    (ht : 2 ≤ t) : 0 ≤ entropyPolyPlus t := by
  have hshift : 0 ≤ t - 2 := by linarith
  have hid : entropyPolyPlus t =
      6656 * (t - 2) ^ 0 +
      46968 * (t - 2) ^ 1 +
      116010 * (t - 2) ^ 2 +
      121840 * (t - 2) ^ 3 +
      65490 * (t - 2) ^ 4 +
      17523 * (t - 2) ^ 5 +
      1829 * (t - 2) ^ 6 := by unfold entropyPolyPlus; ring
  rw [hid]
  positivity

private lemma entropyPolyPlus_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ entropyPolyPlus t := by
  by_cases h0 : t ≤ 1
  · exact entropyPolyPlus_interval0 (by linarith) h0
  by_cases h1 : t ≤ 3 / 2
  · exact entropyPolyPlus_interval1 (by linarith) h1
  by_cases h2 : t ≤ 7 / 4
  · exact entropyPolyPlus_interval2 (by linarith) h2
  by_cases h3 : t ≤ 2
  · exact entropyPolyPlus_interval3 (by linarith) h3
  exact entropyPolyPlus_tail (by linarith)

private lemma entropyPolyMinus_interval0 {t : ℝ}
    (ha : 0 ≤ t) (hb : t ≤ 3 / 4) : 0 ≤ entropyPolyMinus t := by
  have hleft : 0 ≤ t - (0) := by linarith
  have hright : 0 ≤ (3 / 4) - t := by linarith
  have hid : entropyPolyMinus t =
      (25395200 / 729 : ℝ) * (t - (0)) ^ 0 * ((3 / 4) - t) ^ 6 +
      (50790400 / 243 : ℝ) * (t - (0)) ^ 1 * ((3 / 4) - t) ^ 5 +
      (122252800 / 243 : ℝ) * (t - (0)) ^ 2 * ((3 / 4) - t) ^ 4 +
      (440512000 / 729 : ℝ) * (t - (0)) ^ 3 * ((3 / 4) - t) ^ 3 +
      (87923200 / 243 : ℝ) * (t - (0)) ^ 4 * ((3 / 4) - t) ^ 2 +
      (22617700 / 243 : ℝ) * (t - (0)) ^ 5 * ((3 / 4) - t) ^ 1 +
      (6146441 / 729 : ℝ) * (t - (0)) ^ 6 * ((3 / 4) - t) ^ 0 := by unfold entropyPolyMinus; ring
  rw [hid]
  positivity

private lemma entropyPolyMinus_interval1 {t : ℝ}
    (ha : 3 / 4 ≤ t) (hb : t ≤ 1) : 0 ≤ entropyPolyMinus t := by
  have hleft : 0 ≤ t - (3 / 4) := by linarith
  have hright : 0 ≤ (1) - t := by linarith
  have hid : entropyPolyMinus t =
      (6146441 : ℝ) * (t - (3 / 4)) ^ 0 * ((1) - t) ^ 6 +
      (26553828 : ℝ) * (t - (3 / 4)) ^ 1 * ((1) - t) ^ 5 +
      (42428160 : ℝ) * (t - (3 / 4)) ^ 2 * ((1) - t) ^ 4 +
      (29287040 : ℝ) * (t - (3 / 4)) ^ 3 * ((1) - t) ^ 3 +
      (7146240 : ℝ) * (t - (3 / 4)) ^ 4 * ((1) - t) ^ 2 +
      (304128 : ℝ) * (t - (3 / 4)) ^ 5 * ((1) - t) ^ 1 +
      (425984 : ℝ) * (t - (3 / 4)) ^ 6 * ((1) - t) ^ 0 := by unfold entropyPolyMinus; ring
  rw [hid]
  positivity

private lemma entropyPolyMinus_tail {t : ℝ}
    (ht : 1 ≤ t) : 0 ≤ entropyPolyMinus t := by
  have hshift : 0 ≤ t - 1 := by linarith
  have hid : entropyPolyMinus t =
      104 * (t - 1) ^ 0 +
      2199 * (t - 1) ^ 1 +
      46935 * (t - 1) ^ 2 +
      74630 * (t - 1) ^ 3 +
      49560 * (t - 1) ^ 4 +
      15399 * (t - 1) ^ 5 +
      1829 * (t - 1) ^ 6 := by unfold entropyPolyMinus; ring
  rw [hid]
  positivity

private lemma entropyPolyMinus_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ entropyPolyMinus t := by
  by_cases h0 : t ≤ 3 / 4
  · exact entropyPolyMinus_interval0 (by linarith) h0
  by_cases h1 : t ≤ 1
  · exact entropyPolyMinus_interval1 (by linarith) h1
  exact entropyPolyMinus_tail (by linarith)

private lemma entropyQuadratic_pos {ε z : ℝ} (hε : ε ^ 2 = 1) :
    0 < 1 + ε * z + (59 : ℝ) / 200 * z ^ 2 := by
  nlinarith [sq_nonneg (59 * z + 100 * ε)]

private lemma entropyCubic_log_deriv {ε : ℝ} (hε : ε ^ 2 = 1) (t : ℝ) :
    HasDerivAt
      (fun t : ℝ => Real.log (1 + ε * t ^ 3 + (59 : ℝ) / 200 * t ^ 6) -
        ε * t ^ 3 + (31 : ℝ) / 100 * t ^ 4)
      (t ^ 3 * (6200 - 6150 * t ^ 2 + ε * 6200 * t ^ 3 -
        ε * 4425 * t ^ 5 + 1829 * t ^ 6) /
          (5000 * (1 + ε * t ^ 3 + (59 : ℝ) / 200 * t ^ 6))) t := by
  have hp : 0 < 1 + ε * t ^ 3 + (59 : ℝ) / 200 * t ^ 6 := by
    convert entropyQuadratic_pos (z := t ^ 3) hε using 1; ring
  have hbase := (((hasDerivAt_const t (1 : ℝ)).add
    ((hasDerivAt_pow 3 t).const_mul ε)).add
    ((hasDerivAt_pow 6 t).const_mul ((59 : ℝ) / 200))).log hp.ne'
  convert (hbase.sub ((hasDerivAt_pow 3 t).const_mul ε)).add
    ((hasDerivAt_pow 4 t).const_mul ((31 : ℝ) / 100)) using 1 <;> try rfl
  dsimp only [Pi.add_apply, Pi.sub_apply]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub]
  field_simp (discharger := nlinarith)
  ring_nf
  rw [hε]
  ring

private lemma entropyCubic_log_nonneg {ε t : ℝ}
    (hε : ε = 1 ∨ ε = -1) (ht : 0 ≤ t) :
    0 ≤ Real.log (1 + ε * t ^ 3 + (59 : ℝ) / 200 * t ^ 6) -
      ε * t ^ 3 + (31 : ℝ) / 100 * t ^ 4 := by
  have hεsq : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  let F : ℝ → ℝ := fun t => Real.log (1 + ε * t ^ 3 + (59 : ℝ) / 200 * t ^ 6) -
    ε * t ^ 3 + (31 : ℝ) / 100 * t ^ 4
  have hderiv := entropyCubic_log_deriv hεsq
  have hmono : MonotoneOn F (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    · exact (continuous_iff_continuousAt.mpr (fun x => (hderiv x).continuousAt)).continuousOn
    · exact fun x _ => (hderiv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hderiv x).deriv]
      have hx0 : 0 ≤ x := (show 0 < x from by
        simpa only [interior_Ici, Set.mem_Ioi] using hx).le
      have hp : 0 < 1 + ε * x ^ 3 + (59 : ℝ) / 200 * x ^ 6 := by
        convert entropyQuadratic_pos (z := x ^ 3) hεsq using 1; ring
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (pow_nonneg hx0 3)
      rcases hε with rfl | rfl
      · simpa [entropyPolyPlus] using entropyPolyPlus_nonneg hx0
      · simpa [entropyPolyMinus, sub_eq_add_neg] using entropyPolyMinus_nonneg hx0
  have h := hmono (show 0 ∈ Set.Ici (0 : ℝ) by simp) ht ht
  simpa [F] using h

/-- Exact exponential majorant used to strengthen the entropy-to-correlation
bound for a feasible contact. -/
theorem exp_sub_abs_rpow_le_quadratic (u : ℝ) :
    Real.exp (u - (31 : ℝ) / 100 * |u| ^ ((4 : ℝ) / 3)) ≤
      1 + u + (59 : ℝ) / 200 * u ^ 2 := by
  let t : ℝ := |u| ^ ((1 : ℝ) / 3)
  have ht : 0 ≤ t := Real.rpow_nonneg (abs_nonneg u) _
  have ht3 : t ^ 3 = |u| := by
    dsimp [t]
    convert Real.rpow_inv_natCast_pow (abs_nonneg u) (show (3 : ℕ) ≠ 0 by decide) using 1
    norm_num
  have ht4 : t ^ 4 = |u| ^ ((4 : ℝ) / 3) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg u)]
    norm_num
  have ht6 : t ^ 6 = u ^ 2 := by
    calc
      t ^ 6 = (t ^ 3) ^ 2 := by ring
      _ = u ^ 2 := by rw [ht3, sq_abs]
  have hp := entropyQuadratic_pos (ε := 1) (z := u) (by norm_num)
  simp only [one_mul] at hp
  apply (Real.le_log_iff_exp_le hp).mp
  by_cases hu : 0 ≤ u
  · have h := entropyCubic_log_nonneg (ε := 1) (Or.inl rfl) ht
    rw [ht3, ht4, ht6, abs_of_nonneg hu] at h
    simp only [one_mul] at h
    rw [abs_of_nonneg hu]
    linarith
  · have h := entropyCubic_log_nonneg (ε := -1) (Or.inr rfl) ht
    rw [ht3, ht4, ht6, abs_of_neg (lt_of_not_ge hu)] at h
    simp only [neg_one_mul, neg_neg] at h
    rw [abs_of_neg (lt_of_not_ge hu)]
    linarith

end stoch_to_det
