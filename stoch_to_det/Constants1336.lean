import stoch_to_det.ConstantBound1771

/-!
# Constants for the calibrated `1336` ledger

The secant threshold is `eta1336 = 13/36`.  The information floor is calibrated
so that the near-pair and far-pair contributions to `KD1336` agree exactly:

`3 * KM1336 = far1336 = 6 * KS1336 + 2`.
-/

namespace stoch_to_det

/-- Exact rational secant threshold `13/36`. -/
def eta1336Q : ℚ := 13 / 36

/-- Exact rational squared-Hellinger threshold `(13/36)^3 = 2197/46656`. -/
def delta1336Q : ℚ := eta1336Q ^ 3

/-- Exact rational HGR threshold `1/2-(13/36)^2 = 479/1296`. -/
def rho1336Q : ℚ := 1 / 2 - eta1336Q ^ 2

noncomputable def eta1336 : ℝ := eta1336Q

noncomputable def delta1336 : ℝ := delta1336Q

noncomputable def rho1336 : ℝ := rho1336Q

/-- Far-pair coefficient in the winner-entropy ledger. -/
noncomputable def KS1336 : ℝ :=
  2 + 2 * beta1771 * Real.log 2 / delta1336

/-- The complete far-pair contribution to the cell-defect coefficient. -/
noncomputable def far1336 : ℝ :=
  6 * KS1336 + 2

/-- Calibrated information floor in bits. -/
noncomputable def infoFloor1336 : ℝ :=
  3 * beta1771 / far1336

/-- Near-pair coefficient in the winner-entropy ledger. -/
noncomputable def KM1336 : ℝ :=
  beta1771 / infoFloor1336

/-- Cell-defect coefficient. -/
noncomputable def KD1336 : ℝ :=
  max (3 * KM1336) (6 * KS1336 + 2)

/-- Proposed exact finite-latent coefficient. -/
noncomputable def Cdagger1336 : ℝ :=
  KD1336 + 1

lemma eta1336_eq : eta1336 = (13 : ℝ) / 36 := by
  norm_num [eta1336, eta1336Q]

lemma delta1336_eq : delta1336 = eta1336 ^ 3 := by
  norm_num [delta1336, delta1336Q, eta1336, eta1336Q]

lemma delta1336_eq_2197_div_46656 : delta1336 = (2197 : ℝ) / 46656 := by
  norm_num [delta1336, delta1336Q, eta1336Q]

lemma rho1336_eq : rho1336 = 1 / 2 - eta1336 ^ 2 := by
  norm_num [rho1336, rho1336Q, eta1336, eta1336Q]

lemma rho1336_eq_479_div_1296 : rho1336 = (479 : ℝ) / 1296 := by
  norm_num [rho1336, rho1336Q, eta1336Q]

lemma eta1336_pos : 0 < eta1336 := by
  norm_num [eta1336_eq]

lemma delta1336_pos : 0 < delta1336 := by
  norm_num [delta1336_eq_2197_div_46656]

lemma rho1336_pos : 0 < rho1336 := by
  norm_num [rho1336_eq_479_div_1296]

lemma two_mul_eta1336_sq_lt_one : 2 * eta1336 ^ 2 < 1 := by
  norm_num [eta1336_eq]

lemma KS1336_pos : 0 < KS1336 := by
  have hterm : 0 ≤ 2 * beta1771 * Real.log 2 / delta1336 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) beta1771_pos.le)
        (Real.log_pos one_lt_two).le)
      delta1336_pos.le
  unfold KS1336
  linarith

lemma far1336_pos : 0 < far1336 := by
  unfold far1336
  linarith [KS1336_pos]

lemma infoFloor1336_pos : 0 < infoFloor1336 := by
  unfold infoFloor1336
  exact div_pos (mul_pos (by norm_num) beta1771_pos) far1336_pos

lemma KM1336_pos : 0 < KM1336 := by
  exact div_pos beta1771_pos infoFloor1336_pos

lemma three_mul_KM1336_eq_far1336 : 3 * KM1336 = far1336 := by
  unfold KM1336 infoFloor1336
  field_simp [beta1771_pos.ne', far1336_pos.ne']

lemma KD1336_eq_far1336 : KD1336 = far1336 := by
  unfold KD1336
  rw [three_mul_KM1336_eq_far1336]
  simpa only [far1336] using max_self far1336

lemma KD1336_pos : 0 < KD1336 := by
  rw [KD1336_eq_far1336]
  exact far1336_pos

lemma Cdagger1336_pos : 0 < Cdagger1336 := by
  unfold Cdagger1336
  linarith [KD1336_pos]

/-- Rational upper envelope for `KS1336`. -/
noncomputable def KSbar1336 : ℝ :=
  2 + 2 * ((2677 : ℝ) / 1000) / delta1336

theorem KS1336_lt_bar : KS1336 < KSbar1336 := by
  have hdelta : 0 < delta1336 := delta1336_pos
  have ha : 2 + cOff1771 < (2677 : ℝ) / 1000 := by
    linarith [cOff1771_lt]
  have hrewrite : KS1336 = 2 + 2 * ((2 + cOff1771) / delta1336) := by
    unfold KS1336 beta1771
    have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp [hlog]
  rw [hrewrite]
  unfold KSbar1336
  have hdiv := (div_lt_div_iff_of_pos_right hdelta).2 ha
  calc
    2 + 2 * ((2 + cOff1771) / delta1336) <
        2 + 2 * (((2677 : ℝ) / 1000) / delta1336) := by
      nlinarith
    _ = 2 + 2 * ((2677 : ℝ) / 1000) / delta1336 := by ring

/-- The exact rational value of the certified upper envelope for `far1336`. -/
lemma six_KSbar1336_add_two_eq :
    6 * KSbar1336 + 2 = (191191918 : ℝ) / 274625 := by
  norm_num [KSbar1336, delta1336, delta1336Q, eta1336Q]

lemma six_KSbar1336_add_two_lt_697 :
    6 * KSbar1336 + 2 < (697 : ℝ) := by
  rw [six_KSbar1336_add_two_eq]
  norm_num

lemma far1336_lt_697 : far1336 < (697 : ℝ) := by
  unfold far1336
  nlinarith [KS1336_lt_bar, six_KSbar1336_add_two_lt_697]

/-- Certified analytic bound for the calibrated constant tree. -/
theorem Cdagger1336_lt_698 : Cdagger1336 < (698 : ℝ) := by
  unfold Cdagger1336
  rw [KD1336_eq_far1336]
  linarith [far1336_lt_697]

end stoch_to_det
