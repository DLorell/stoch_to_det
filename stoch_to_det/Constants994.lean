import stoch_to_det.Constants1771

/-!
# Constants for the strengthened HGR moment bound

The near-collision floor is certified below by the rational `χ = 8077/10⁶` at
`η = 1281/4000`.  The irrational powers in the analytic Hellinger floor are
kept out of the closing ledger; `Floor` proves that this rational `χ` is a
valid lower bound.
-/

namespace stoch_to_det

def eta994Q : ℚ := 1281 / 4000

def delta994Q : ℚ := eta994Q ^ 3

def rho994Q : ℚ := 1 / 2 - eta994Q ^ 2

/-- Rational certificate below
`ρ^(14/3) / (1 + ρ^(4/3))²` at `ρ = rho994Q`. -/
def chi994Q : ℚ := 8077 / 1000000

noncomputable def eta994 : ℝ := eta994Q
noncomputable def delta994 : ℝ := delta994Q
noncomputable def rho994 : ℝ := rho994Q
noncomputable def chi994 : ℝ := chi994Q

noncomputable def infoFloor994 : ℝ :=
  -2 * lg (1 - chi994 / 2)

noncomputable def KM994 : ℝ :=
  beta1771 / infoFloor994

noncomputable def KS994 : ℝ :=
  2 + 2 * beta1771 * Real.log 2 / delta994

noncomputable def KD994 : ℝ :=
  max (3 * KM994) (6 * KS994 + 2)

noncomputable def Cdagger994 : ℝ :=
  KD994 + 1

lemma eta994_eq : eta994 = (1281 : ℝ) / 4000 := by
  norm_num [eta994, eta994Q]

lemma delta994_eq : delta994 = eta994 ^ 3 := by
  norm_num [delta994, delta994Q, eta994, eta994Q]

lemma rho994_eq : rho994 = 1 / 2 - eta994 ^ 2 := by
  norm_num [rho994, rho994Q, eta994, eta994Q]

lemma eta994_pos : 0 < eta994 := by
  norm_num [eta994, eta994Q]

lemma delta994_pos : 0 < delta994 := by
  norm_num [delta994, delta994Q, eta994Q]

lemma rho994_pos : 0 < rho994 := by
  norm_num [rho994, rho994Q, eta994Q]

lemma rho994_lt_one : rho994 < 1 := by
  norm_num [rho994, rho994Q, eta994Q]

lemma chi994_pos : 0 < chi994 := by
  norm_num [chi994, chi994Q]

lemma chi994_lt_two : chi994 < 2 := by
  norm_num [chi994, chi994Q]

lemma one_sub_chi994_half_pos : 0 < 1 - chi994 / 2 := by
  linarith [chi994_lt_two]

lemma one_sub_chi994_half_lt_one : 1 - chi994 / 2 < 1 := by
  linarith [chi994_pos]

lemma infoFloor994_pos : 0 < infoFloor994 := by
  have hlog : lg (1 - chi994 / 2) < 0 := by
    rw [lg_eq_log_div]
    exact div_neg_of_neg_of_pos
      (Real.log_neg one_sub_chi994_half_pos one_sub_chi994_half_lt_one)
      (Real.log_pos one_lt_two)
  unfold infoFloor994
  linarith

end stoch_to_det
