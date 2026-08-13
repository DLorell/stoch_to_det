import stoch_to_det.ConstantBound1771

/-! Exact rational calibration for the `270` endpoint. -/

namespace stoch_to_det

def eta270Q : ℚ := 221 / 1000
def delta270Q : ℚ := 2 * eta270Q ^ 2
def rho270Q : ℚ := 1 / 2 - eta270Q ^ 2
def floorNat270Q : ℚ := 231 / 10000
def betaNat270Q : ℚ := 2071 / 1000

noncomputable def eta270 : ℝ := eta270Q
noncomputable def delta270 : ℝ := delta270Q
noncomputable def rho270 : ℝ := rho270Q
noncomputable def floorNat270 : ℝ := floorNat270Q
noncomputable def betaNat270 : ℝ := betaNat270Q
noncomputable def infoFloor270 : ℝ := floorNat270 / Real.log 2
noncomputable def beta270 : ℝ := betaNat270 / Real.log 2

noncomputable def KM270 : ℝ := beta270 / infoFloor270
noncomputable def KS270 : ℝ := 2 + 2 * beta270 * Real.log 2 / delta270
noncomputable def KD270 : ℝ := max (3 * KM270) (6 * KS270 + 2)
noncomputable def Cdagger270 : ℝ := KD270 + 1

lemma eta270_eq : eta270 = (221 : ℝ) / 1000 := by
  norm_num [eta270, eta270Q]

lemma delta270_eq : delta270 = 2 * eta270 ^ 2 := by
  norm_num [delta270, delta270Q, eta270, eta270Q]

lemma delta270_eq_value : delta270 = (48841 : ℝ) / 500000 := by
  norm_num [delta270, delta270Q, eta270Q]

lemma rho270_eq : rho270 = 1 / 2 - eta270 ^ 2 := by
  norm_num [rho270, rho270Q, eta270, eta270Q]

lemma rho270_eq_value : rho270 = (451159 : ℝ) / 1000000 := by
  norm_num [rho270, rho270Q, eta270Q]

lemma floorNat270_eq : floorNat270 = (231 : ℝ) / 10000 := by
  norm_num [floorNat270, floorNat270Q]

lemma betaNat270_eq : betaNat270 = (2071 : ℝ) / 1000 := by
  norm_num [betaNat270, betaNat270Q]

lemma eta270_pos : 0 < eta270 := by norm_num [eta270_eq]
lemma delta270_pos : 0 < delta270 := by norm_num [delta270_eq_value]
lemma rho270_pos : 0 < rho270 := by norm_num [rho270_eq_value]
lemma floorNat270_pos : 0 < floorNat270 := by norm_num [floorNat270_eq]
lemma betaNat270_pos : 0 < betaNat270 := by norm_num [betaNat270_eq]

lemma two_mul_eta270_sq_lt_one : 2 * eta270 ^ 2 < 1 := by
  norm_num [eta270_eq]

lemma infoFloor270_pos : 0 < infoFloor270 := by
  exact div_pos floorNat270_pos (Real.log_pos one_lt_two)

lemma beta270_pos : 0 < beta270 := by
  exact div_pos betaNat270_pos (Real.log_pos one_lt_two)

theorem KM270_eq : KM270 = (20710 : ℝ) / 231 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold KM270 beta270 infoFloor270
  rw [betaNat270_eq, floorNat270_eq]
  field_simp [hlog]
  norm_num

theorem KS270_eq : KS270 = (2168682 : ℝ) / 48841 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold KS270 beta270
  rw [betaNat270_eq, delta270_eq_value]
  field_simp [hlog]
  norm_num

theorem near_branch_270_eq : 3 * KM270 = (20710 : ℝ) / 77 := by
  rw [KM270_eq]
  ring

theorem far_branch_270_eq : 6 * KS270 + 2 = (13109774 : ℝ) / 48841 := by
  rw [KS270_eq]
  ring

theorem far_branch_270_lt_near : 6 * KS270 + 2 < 3 * KM270 := by
  rw [near_branch_270_eq, far_branch_270_eq]
  norm_num

theorem KD270_eq : KD270 = (20710 : ℝ) / 77 := by
  unfold KD270
  rw [max_eq_left far_branch_270_lt_near.le, near_branch_270_eq]

theorem Cdagger270_eq : Cdagger270 = (20787 : ℝ) / 77 := by
  unfold Cdagger270
  rw [KD270_eq]
  ring

theorem Cdagger270_lt_270 : Cdagger270 < (270 : ℝ) := by
  rw [Cdagger270_eq]
  norm_num

end stoch_to_det
