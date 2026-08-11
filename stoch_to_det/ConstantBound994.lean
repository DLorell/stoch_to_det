import stoch_to_det.ConstantBound1771
import stoch_to_det.Constants994

namespace stoch_to_det

private theorem infoFloor994_lower :
    (2 * (chi994 / 2) + (chi994 / 2) ^ 2) / Real.log 2 ≤
      infoFloor994 := by
  let u : ℝ := chi994 / 2
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg chi994_pos.le (by norm_num)
  have hu1 : u < 1 := by dsimp [u]; linarith [chi994_lt_two]
  have hquad := neg_log_one_sub_ge_quadratic hu0 hu1
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hfloorMul : infoFloor994 * Real.log 2 =
      -2 * Real.log (1 - chi994 / 2) := by
    unfold infoFloor994
    rw [lg_eq_log_div]
    field_simp [hlog2.ne']
  apply (div_le_iff₀ hlog2).2
  rw [hfloorMul]
  dsimp [u] at hquad ⊢
  nlinarith

noncomputable def u994 : ℝ := chi994 / 2
noncomputable def v994 : ℝ := 2 * u994 + u994 ^ 2
noncomputable def KMbar994 : ℝ := ((2677 : ℝ) / 1000) / v994
noncomputable def KSbar994 : ℝ :=
  2 + 2 * ((2677 : ℝ) / 1000) / delta994

private lemma u994_pos : 0 < u994 := by
  exact div_pos chi994_pos (by norm_num)

private lemma v994_pos : 0 < v994 := by
  unfold v994
  nlinarith [u994_pos, sq_nonneg u994]

private theorem KM994_lt_bar : KM994 < KMbar994 := by
  let a : ℝ := 2 + cOff1771
  let b : ℝ := (2677 : ℝ) / 1000
  let L : ℝ := Real.log 2
  let F : ℝ := infoFloor994
  let v : ℝ := v994
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos one_lt_two
  have hF : 0 < F := by dsimp [F]; exact infoFloor994_pos
  have hv : 0 < v := by dsimp [v]; exact v994_pos
  have ha : 0 < a := by
    have h := mul_pos beta1771_pos hL
    dsimp [a, L] at h ⊢
    rw [beta1771_mul_log_two] at h
    exact h
  have hab : a < b := by
    dsimp [a, b]
    linarith [cOff1771_lt]
  have hfloor : v / L ≤ F := by
    dsimp [v, L, F, v994, u994]
    exact infoFloor994_lower
  have hvLF : v ≤ L * F := by
    have h := (div_le_iff₀ hL).1 hfloor
    simpa [mul_comm] using h
  have hden : 0 < L * F := mul_pos hL hF
  calc
    KM994 = a / (L * F) := by
      dsimp [a, L, F]
      unfold KM994 beta1771
      field_simp [hL.ne', hF.ne']
    _ ≤ a / v := by
      exact (div_le_div_iff₀ hden hv).2
        (mul_le_mul_of_nonneg_left hvLF ha.le)
    _ < b / v := (div_lt_div_iff_of_pos_right hv).2 hab
    _ = KMbar994 := by rfl

private theorem KS994_lt_bar : KS994 < KSbar994 := by
  let a : ℝ := 2 + cOff1771
  let b : ℝ := (2677 : ℝ) / 1000
  have hab : a < b := by
    dsimp [a, b]
    linarith [cOff1771_lt]
  have hdiv : a / delta994 < b / delta994 :=
    (div_lt_div_iff_of_pos_right delta994_pos).2 hab
  calc
    KS994 = 2 + 2 * (a / delta994) := by
      dsimp [a]
      unfold KS994 beta1771
      have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
      field_simp [hlog]
    _ < 2 + 2 * (b / delta994) := by nlinarith
    _ = KSbar994 := by
      dsimp [b]
      unfold KSbar994
      ring

private lemma three_KMbar994_lt_993 : 3 * KMbar994 < (993 : ℝ) := by
  norm_num [KMbar994, v994, u994, chi994, chi994Q]

private lemma six_KSbar994_add_two_lt_993 :
    6 * KSbar994 + 2 < (993 : ℝ) := by
  norm_num [KSbar994, delta994, delta994Q, eta994Q]

theorem KD994_lt_993 : KD994 < (993 : ℝ) := by
  have hM : 3 * KM994 < (993 : ℝ) :=
    (mul_lt_mul_of_pos_left KM994_lt_bar (by norm_num)).trans
      three_KMbar994_lt_993
  have hS : 6 * KS994 + 2 < (993 : ℝ) := by
    nlinarith [KS994_lt_bar, six_KSbar994_add_two_lt_993]
  unfold KD994
  exact (max_lt_iff).2 ⟨hM, hS⟩

end stoch_to_det
