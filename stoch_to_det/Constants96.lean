import Mathlib.Analysis.Complex.ExponentialBounds

/-! Exact calibration and final constants for the standalone `C < 96` proof. -/

namespace stoch_to_det

def eta96Q : ℚ := 221 / 1000
def delta96Q : ℚ := 2 * eta96Q ^ 2
def rho96Q : ℚ := 1 / 2 - eta96Q ^ 2
def floorNat96Q : ℚ := 231 / 10000

noncomputable def eta96 : ℝ := eta96Q
noncomputable def delta96 : ℝ := delta96Q
noncomputable def rho96 : ℝ := rho96Q
noncomputable def floorNat96 : ℝ := floorNat96Q
noncomputable def infoFloor96 : ℝ := floorNat96 / Real.log 2

/-- Coefficient of `M` after the shared-race estimate and mismatch charge. -/
noncomputable def KM96 : ℝ := 1 / infoFloor96

/-- Coefficient of `Sinfo = b_Z` after the shared-race estimate and mismatch charge. -/
noncomputable def KS96 : ℝ := 2 + 2 * Real.log 2 / delta96

/-- The hybrid coefficient before the final deterministic `+1`. -/
noncomputable def KD96 : ℝ :=
  max (3 * KM96) ((3 / 2 : ℝ) * KM96 + 3 * KS96 + 1)

/-- The complete comparison constant delivered by the shared-race route. -/
noncomputable def Cdagger96 : ℝ := KD96 + 1

lemma eta96_eq : eta96 = (221 : ℝ) / 1000 := by
  norm_num [eta96, eta96Q]

lemma delta96_eq : delta96 = 2 * eta96 ^ 2 := by
  norm_num [delta96, delta96Q, eta96, eta96Q]

lemma delta96_eq_value : delta96 = (48841 : ℝ) / 500000 := by
  norm_num [delta96, delta96Q, eta96Q]

lemma rho96_eq : rho96 = 1 / 2 - eta96 ^ 2 := by
  norm_num [rho96, rho96Q, eta96, eta96Q]

lemma rho96_eq_value : rho96 = (451159 : ℝ) / 1000000 := by
  norm_num [rho96, rho96Q, eta96Q]

lemma floorNat96_eq : floorNat96 = (231 : ℝ) / 10000 := by
  norm_num [floorNat96, floorNat96Q]

lemma eta96_pos : 0 < eta96 := by norm_num [eta96_eq]
lemma delta96_pos : 0 < delta96 := by norm_num [delta96_eq_value]
lemma rho96_pos : 0 < rho96 := by norm_num [rho96_eq_value]
lemma floorNat96_pos : 0 < floorNat96 := by norm_num [floorNat96_eq]

lemma two_mul_eta96_sq_lt_one : 2 * eta96 ^ 2 < 1 := by
  norm_num [eta96_eq]

lemma infoFloor96_pos : 0 < infoFloor96 := by
  exact div_pos floorNat96_pos (Real.log_pos one_lt_two)

theorem KM96_eq : KM96 = Real.log 2 * (10000 / 231 : ℝ) := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold KM96 infoFloor96
  rw [floorNat96_eq]
  field_simp [hlog]

theorem KS96_eq : KS96 = 2 + Real.log 2 * (1000000 / 48841 : ℝ) := by
  unfold KS96
  rw [delta96_eq_value]
  ring

theorem near_branch_96_eq :
    3 * KM96 = Real.log 2 * (10000 / 77 : ℝ) := by
  rw [KM96_eq]
  ring

theorem far_branch_96_eq :
    (3 / 2 : ℝ) * KM96 + 3 * KS96 + 1 =
      7 + Real.log 2 * (475205000 / 3760757 : ℝ) := by
  rw [KM96_eq, KS96_eq]
  ring

theorem near_branch_96_lt_far :
    3 * KM96 < (3 / 2 : ℝ) * KM96 + 3 * KS96 + 1 := by
  rw [near_branch_96_eq, far_branch_96_eq]
  have hlog0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2 := Real.log_two_lt_d9
  nlinarith

theorem KD96_eq :
    KD96 = 7 + Real.log 2 * (475205000 / 3760757 : ℝ) := by
  unfold KD96
  rw [max_eq_right near_branch_96_lt_far.le, far_branch_96_eq]

theorem Cdagger96_eq :
    Cdagger96 = 8 + Real.log 2 * (475205000 / 3760757 : ℝ) := by
  unfold Cdagger96
  rw [KD96_eq]
  ring

theorem Cdagger96_lt_96 : Cdagger96 < (96 : ℝ) := by
  rw [Cdagger96_eq]
  nlinarith [Real.log_two_lt_d9]

theorem KM96_nonneg : 0 ≤ KM96 := by
  rw [KM96_eq]
  positivity

theorem KS96_nonneg : 0 ≤ KS96 := by
  rw [KS96_eq]
  positivity

theorem joint_bZ_coefficient_nonneg : 0 ≤ 3 * KS96 + 1 := by
  rw [KS96_eq]
  positivity

end stoch_to_det
