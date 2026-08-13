import stoch_to_det.ConstantBound1771

/-!
# Constants at the `517` calibration

`Ixy` is measured in bits: it is built from `H`, whose logarithm is `lg`.
Consequently a conversion of the form

`Ixy_nats q ≥ rhoHGR q ^ 2 / 5`

has the following form in this project:

`rhoHGR q ^ 2 / (5 * Real.log 2) ≤ Ixy q`.

Thus `infoFloor517` below includes the factor `1 / Real.log 2`.

The two analytic inputs at this calibration are fully discharged elsewhere:
`Floor517` instantiates exact-secant rigidity at `eta517 = 2/5`, and
`PriceConv` proves the contact information floor `9/400` bits at
`rho517 = 17/50`.  `Ledger517` assembles those inputs, and `Final517` proves
the unconditional endpoint `T_le_517`.

The `infoFloor517`/`KM517` quantities below retain the earlier reference
calibration based on the displayed quadratic conversion.  The final theorem
instead instantiates the parametric ledger at the certified `9/400` price-dual
floor.  The exact constant-tree calculation recorded here is

```
3 * KM517 < 200775/578 < 516,
6 * KS517 + 2 < 8255/16 < 516,
KD517 < 516,
Cdagger517 < 517.
```
-/

namespace stoch_to_det

/-- Exact rational secant threshold `2/5`. -/
def eta517Q : ℚ := 2 / 5

/-- Exact rational squared-Hellinger threshold `(2/5)^3 = 8/125`. -/
def delta517Q : ℚ := eta517Q ^ 3

/-- Exact rational HGR threshold `1/2-(2/5)^2 = 17/50`. -/
def rho517Q : ℚ := 1 / 2 - eta517Q ^ 2

noncomputable def eta517 : ℝ := eta517Q

noncomputable def delta517 : ℝ := delta517Q

noncomputable def rho517 : ℝ := rho517Q

/-- Reference information floor in bits for the quadratic conversion above. -/
noncomputable def infoFloor517 : ℝ :=
  rho517 ^ 2 / (5 * Real.log 2)

/-- Near-pair coefficient in the winner-entropy ledger. -/
noncomputable def KM517 : ℝ :=
  beta1771 / infoFloor517

/-- Far-pair coefficient in the winner-entropy ledger. -/
noncomputable def KS517 : ℝ :=
  2 + 2 * beta1771 * Real.log 2 / delta517

/-- Cell-defect coefficient. -/
noncomputable def KD517 : ℝ :=
  max (3 * KM517) (6 * KS517 + 2)

/-- Exact finite-latent coefficient for the reference quadratic calibration. -/
noncomputable def Cdagger517 : ℝ :=
  KD517 + 1

lemma eta517_eq : eta517 = (2 : ℝ) / 5 := by
  norm_num [eta517, eta517Q]

lemma delta517_eq : delta517 = eta517 ^ 3 := by
  norm_num [delta517, delta517Q, eta517, eta517Q]

lemma delta517_eq_eight_div_125 : delta517 = (8 : ℝ) / 125 := by
  norm_num [delta517, delta517Q, eta517Q]

lemma rho517_eq : rho517 = 1 / 2 - eta517 ^ 2 := by
  norm_num [rho517, rho517Q, eta517, eta517Q]

lemma rho517_eq_seventeen_div_50 : rho517 = (17 : ℝ) / 50 := by
  norm_num [rho517, rho517Q, eta517Q]

lemma eta517_pos : 0 < eta517 := by
  norm_num [eta517_eq]

lemma delta517_pos : 0 < delta517 := by
  norm_num [delta517_eq_eight_div_125]

lemma rho517_pos : 0 < rho517 := by
  norm_num [rho517_eq_seventeen_div_50]

lemma two_mul_eta517_sq_lt_one : 2 * eta517 ^ 2 < 1 := by
  norm_num [eta517_eq]

lemma infoFloor517_pos : 0 < infoFloor517 := by
  unfold infoFloor517
  exact div_pos (sq_pos_of_pos rho517_pos)
    (mul_pos (by norm_num) (Real.log_pos one_lt_two))

lemma KM517_pos : 0 < KM517 := by
  exact div_pos beta1771_pos infoFloor517_pos

lemma KS517_pos : 0 < KS517 := by
  have hterm : 0 ≤ 2 * beta1771 * Real.log 2 / delta517 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) beta1771_pos.le)
        (Real.log_pos one_lt_two).le)
      delta517_pos.le
  unfold KS517
  linarith

lemma KD517_nonneg : 0 ≤ KD517 := by
  unfold KD517
  exact le_max_of_le_left (mul_nonneg (by norm_num) KM517_pos.le)

lemma Cdagger517_pos : 0 < Cdagger517 := by
  unfold Cdagger517
  linarith [KD517_nonneg]

/-- Rational upper envelope for `KM517`; the logarithms cancel because both
`beta1771` and `infoFloor517` are expressed in bits. -/
noncomputable def KMbar517 : ℝ :=
  5 * ((2677 : ℝ) / 1000) / rho517 ^ 2

/-- Rational upper envelope for `KS517`. -/
noncomputable def KSbar517 : ℝ :=
  2 + 2 * ((2677 : ℝ) / 1000) / delta517

theorem KM517_lt_bar : KM517 < KMbar517 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrho : 0 < rho517 := rho517_pos
  have ha : 2 + cOff1771 < (2677 : ℝ) / 1000 := by
    linarith [cOff1771_lt]
  have hrewrite : KM517 = 5 * (2 + cOff1771) / rho517 ^ 2 := by
    unfold KM517 infoFloor517 beta1771
    field_simp [hlog.ne', hrho.ne']
  rw [hrewrite]
  unfold KMbar517
  exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos hrho)).2 (by nlinarith)

theorem KS517_lt_bar : KS517 < KSbar517 := by
  have hdelta : 0 < delta517 := delta517_pos
  have ha : 2 + cOff1771 < (2677 : ℝ) / 1000 := by
    linarith [cOff1771_lt]
  have hrewrite : KS517 = 2 + 2 * ((2 + cOff1771) / delta517) := by
    unfold KS517 beta1771
    have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp [hlog]
  rw [hrewrite]
  unfold KSbar517
  have hdiv := (div_lt_div_iff_of_pos_right hdelta).2 ha
  calc
    2 + 2 * ((2 + cOff1771) / delta517) <
        2 + 2 * (((2677 : ℝ) / 1000) / delta517) := by
      nlinarith
    _ = 2 + 2 * ((2677 : ℝ) / 1000) / delta517 := by ring

lemma three_KMbar517_lt_516 : 3 * KMbar517 < (516 : ℝ) := by
  norm_num [KMbar517, rho517, rho517Q, eta517Q]

lemma six_KSbar517_add_two_lt_516 :
    6 * KSbar517 + 2 < (516 : ℝ) := by
  norm_num [KSbar517, delta517, delta517Q, eta517Q]

theorem KD517_lt_516 : KD517 < (516 : ℝ) := by
  have hM : 3 * KM517 < (516 : ℝ) :=
    (mul_lt_mul_of_pos_left KM517_lt_bar (by norm_num)).trans
      three_KMbar517_lt_516
  have hS : 6 * KS517 + 2 < (516 : ℝ) := by
    nlinarith [KS517_lt_bar, six_KSbar517_add_two_lt_516]
  unfold KD517
  exact (max_lt_iff).2 ⟨hM, hS⟩

/-- Certified analytic bound for the reference constant tree. -/
theorem Cdagger517_lt_517 : Cdagger517 < (517 : ℝ) := by
  unfold Cdagger517
  linarith [KD517_lt_516]

/-- A looser rounded form matching the initial target. -/
theorem Cdagger517_lt_520 : Cdagger517 < (520 : ℝ) :=
  Cdagger517_lt_517.trans (by norm_num)

end stoch_to_det
