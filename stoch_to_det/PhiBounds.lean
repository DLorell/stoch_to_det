import Mathlib

/-!
# Elementary bounds for `r * log r - r + 1`

All logarithms are natural logarithms.  At `r = 0`, Lean's convention
`Real.log 0 = 0` gives `phi 0 = 1`, matching the continuous extension of
`r * log r - r + 1` from the positive half-line.
-/

namespace stoch_to_det

/-- The scalar relative-entropy integrand, with its continuous value at zero. -/
noncomputable def phi (r : ℝ) : ℝ := r * Real.log r - r + 1

lemma continuous_phi : Continuous phi := by
  exact (Real.continuous_mul_log.sub continuous_id).add continuous_const

lemma hasDerivAt_phi {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt phi (Real.log r) r := by
  have hraw := ((Real.hasDerivAt_mul_log hr).sub (hasDerivAt_id r)).add_const 1
  refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with y
    rfl
  · ring

/-- `phi` is nonnegative on the nonnegative half-line. -/
theorem phi_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ phi r := by
  by_cases hr0 : r = 0
  · simp [phi, hr0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hrpos)
    rw [Real.log_inv] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hr
    rw [mul_sub, mul_inv_cancel₀ hr0, mul_one] at hmul
    unfold phi
    nlinarith

/-- On `(0,1]`, the tangent-quadratic lower bound for `phi`. -/
lemma phi_half_sq_lower_of_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (r - 1) ^ 2 / 2 ≤ phi r := by
  by_cases hz : r = 0
  · norm_num [phi, hz]
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hz)
  let f : ℝ → ℝ := fun x => phi x - (x - 1) ^ 2 / 2
  have hfcont : Continuous f := by
    exact continuous_phi.sub (((continuous_id.sub continuous_const).pow 2).div_const 2)
  have hanti : AntitoneOn f (Set.Icc r 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc r 1) hfcont.continuousOn
    · intro x hx
      have hx' : x ∈ Set.Ioo r 1 := by
        simpa only [interior_Icc] using hx
      have hxr : r < x := hx'.1
      have hxpos : 0 < x := hrpos.trans hxr
      have hsq : HasDerivAt (fun y : ℝ => (y - 1) ^ 2 / 2) (x - 1) x := by
        have hraw := (((hasDerivAt_id x).sub_const 1).pow 2).div_const 2
        refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
        · filter_upwards with y
          rfl
        · norm_num
      have hderiv : HasDerivAt f (Real.log x - (x - 1)) x := by
        have hraw := (hasDerivAt_phi hxpos.ne').sub hsq
        refine (hraw.congr_of_eventuallyEq ?_).congr_deriv rfl
        filter_upwards with y
        rfl
      exact hderiv.differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Ioo r 1 := by
        simpa only [interior_Icc] using hx
      have hxr : r < x := hx'.1
      have hxpos : 0 < x := hrpos.trans hxr
      have hsq : HasDerivAt (fun y : ℝ => (y - 1) ^ 2 / 2) (x - 1) x := by
        have hraw := (((hasDerivAt_id x).sub_const 1).pow 2).div_const 2
        refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
        · filter_upwards with y
          rfl
        · norm_num
      have hderiv : HasDerivAt f (Real.log x - (x - 1)) x := by
        have hraw := (hasDerivAt_phi hxpos.ne').sub hsq
        refine (hraw.congr_of_eventuallyEq ?_).congr_deriv rfl
        filter_upwards with y
        rfl
      rw [hderiv.deriv]
      exact sub_nonpos.mpr (Real.log_le_sub_one_of_pos hxpos)
  have hle := hanti
    (show r ∈ Set.Icc r 1 from ⟨le_rfl, hr1⟩)
    (show (1 : ℝ) ∈ Set.Icc r 1 from ⟨hr1, le_rfl⟩) hr1
  simpa [f, phi] using hle

/-- The symmetric elementary logarithm bound on `[1,∞)`. -/
lemma two_mul_sub_one_le_add_one_mul_log {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) ≤ (x + 1) * Real.log x := by
  have h := Real.le_log_one_add_of_nonneg (x := x - 1) (sub_nonneg.mpr hx)
  rw [show (x - 1) + 2 = x + 1 by ring,
      show 1 + (x - 1) = x by ring] at h
  have h' := (div_le_iff₀ (by linarith : 0 < x + 1)).1 h
  simpa only [mul_comm] using h'

/-- The quotient `phi r / (r-1)^2` decreases to the right of `1`. -/
lemma phi_div_sq_antitone_Icc {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    phi b / (b - 1) ^ 2 ≤ phi a / (a - 1) ^ 2 := by
  let g : ℝ → ℝ := fun x => phi x / (x - 1) ^ 2
  have hgcont : ContinuousOn g (Set.Icc a b) := by
    apply continuous_phi.continuousOn.div
      (((continuous_id.sub continuous_const).pow 2).continuousOn)
    intro x hx
    have hx1 : 1 < x := ha.trans_le hx.1
    exact pow_ne_zero 2 (sub_ne_zero.mpr hx1.ne')
  have hderiv (x : ℝ) (hx1 : 1 < x) :
      HasDerivAt g
        ((Real.log x * (x - 1) ^ 2 - phi x * (2 * (x - 1))) /
          ((x - 1) ^ 2) ^ 2) x := by
    have hden : HasDerivAt (fun y : ℝ => (y - 1) ^ 2) (2 * (x - 1)) x := by
      have hraw := ((hasDerivAt_id x).sub_const 1).pow 2
      refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with y
        rfl
      · norm_num
    have hraw := (hasDerivAt_phi (by linarith : x ≠ 0)).div hden
      (pow_ne_zero 2 (sub_ne_zero.mpr hx1.ne'))
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv rfl
    filter_upwards with y
    rfl
  have hanti : AntitoneOn g (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hgcont
    · intro x hx
      have hx' : x ∈ Set.Ioo a b := by
        simpa only [interior_Icc] using hx
      have hx1 : 1 < x := ha.trans hx'.1
      exact (hderiv x hx1).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Ioo a b := by
        simpa only [interior_Icc] using hx
      have hx1 : 1 < x := ha.trans hx'.1
      rw [(hderiv x hx1).deriv]
      apply div_nonpos_of_nonpos_of_nonneg
      · calc
          Real.log x * (x - 1) ^ 2 - phi x * (2 * (x - 1)) =
              (x - 1) * (2 * (x - 1) - (x + 1) * Real.log x) := by
                unfold phi
                ring
          _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith)
            (sub_nonpos.mpr (two_mul_sub_one_le_add_one_mul_log hx1.le))
      · exact sq_nonneg _
  exact hanti
    (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)
    (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩) hab

/-- On `[0,3]`, `phi` dominates the endpoint-matched quadratic. -/
theorem phi_quad_lower_bulk {r : ℝ} (hr0 : 0 ≤ r) (hr3 : r ≤ 3) :
    (r - 1) ^ 2 * phi 3 ≤ 4 * phi r := by
  by_cases hr1 : r ≤ 1
  · have hsq := phi_half_sq_lower_of_le_one hr0 hr1
    have hlog3 := Real.log_three_lt_d9
    have hp3 : phi 3 ≤ 2 := by
      unfold phi
      norm_num at hlog3 ⊢
      linarith
    calc
      (r - 1) ^ 2 * phi 3 ≤ (r - 1) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left hp3 (sq_nonneg _)
      _ ≤ 4 * phi r := by nlinarith
  · have hr1lt : 1 < r := lt_of_not_ge hr1
    have hratio := phi_div_sq_antitone_Icc hr1lt hr3
    norm_num at hratio
    have hsqpos : 0 < (r - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr1lt)
    have hcross := (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hsqpos).1 hratio
    simpa only [mul_comm] using hcross

/-- On the tail, one quarter of `r log r` is absorbed by `phi r`. -/
theorem phi_linear_lower_tail {r : ℝ} (hr : 2 ≤ r) :
    (r / 4) * Real.log r ≤ phi r := by
  have hrpos : 0 < r := by linarith
  have htwo_div_r_pos : 0 < (2 : ℝ) / r := div_pos (by norm_num) hrpos
  have hlog := Real.log_le_sub_one_of_pos htwo_div_r_pos
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hrpos.ne'] at hlog
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
    exact lt_trans (by norm_num) Real.log_two_gt_d9
  have hinv_bound : (2 : ℝ) / r ≤ 1 := (div_le_one hrpos).2 hr
  unfold phi
  have hrne : r ≠ 0 := hrpos.ne'
  field_simp [hrne] at hlog ⊢
  nlinarith

/-- The sharp multiplied-out absolute envelope, maximized at `r = 3`. -/
theorem env_absolute {r : ℝ} (hr : 3 ≤ r) :
    r - 1 ≤ (2 * Real.sqrt 3 / 9) * r * Real.sqrt r := by
  have hr0 : 0 ≤ r := by linarith
  let t : ℝ := Real.sqrt r
  let s : ℝ := Real.sqrt 3
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = r := by
    dsimp [t]
    exact Real.sq_sqrt hr0
  have hs2 : s ^ 2 = 3 := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hfac : 0 ≤ (t - s) ^ 2 * (2 * s * t + 3) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hid : (t - s) ^ 2 * (2 * s * t + 3) =
      2 * s * t ^ 3 - 9 * t ^ 2 + 9 := by
    calc
      (t - s) ^ 2 * (2 * s * t + 3) =
          2 * s * t ^ 3 + (3 - 4 * s ^ 2) * t ^ 2 +
            2 * s * (s ^ 2 - 3) * t + 3 * s ^ 2 := by ring
      _ = 2 * s * t ^ 3 - 9 * t ^ 2 + 9 := by rw [hs2]; ring
  rw [hid] at hfac
  dsimp [t, s] at ht2 hs2 hfac ⊢
  have ht3 : (Real.sqrt r) ^ 3 = r * Real.sqrt r := by
    calc
      (Real.sqrt r) ^ 3 = (Real.sqrt r) ^ 2 * Real.sqrt r := by ring
      _ = r * Real.sqrt r := by rw [ht2]
  rw [ht3, ht2] at hfac
  nlinarith

/-- A `phi` upper bound by `K r^3` forces the logarithmic tail ratio bound. -/
theorem tail_ratio_from_phi {r K : ℝ} (hr : 3 ≤ r) (hK : 0 < K)
    (hphi : phi r ≤ K * r ^ 3) :
    Real.log r ≤ 4 * K * r ^ 2 := by
  have hrpos : 0 < r := by linarith
  have hlower := phi_linear_lower_tail (show 2 ≤ r by linarith)
  have hchain : (r / 4) * Real.log r ≤ K * r ^ 3 := hlower.trans hphi
  calc
    Real.log r = (4 / r) * ((r / 4) * Real.log r) := by
      field_simp [hrpos.ne']
    _ ≤ (4 / r) * (K * r ^ 3) :=
      mul_le_mul_of_nonneg_left hchain (div_nonneg (by norm_num) hrpos.le)
    _ = 4 * K * r ^ 2 := by
      field_simp [hrpos.ne']

/-- Fourth-power decay of the normalized envelope. -/
theorem env_pow4 {r : ℝ} (hr : 3 ≤ r) :
    (((r - 1) * r ^ (-(3 : ℝ) / 2)) ^ 4 ≤ (r - 1) ^ 4 / r ^ 6) ∧
      ((r - 1) ^ 4 / r ^ 6 ≤ 1 / r ^ 2) := by
  have hrpos : 0 < r := by linarith
  have hr0 : 0 ≤ r := hrpos.le
  have hrpow : (r ^ (-(3 : ℝ) / 2)) ^ 4 = (r ^ 6)⁻¹ := by
    rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring, Real.rpow_neg hr0]
    rw [inv_pow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hr0]
    norm_num
  constructor
  · rw [mul_pow, hrpow, div_eq_mul_inv]
  · have hbase : 0 ≤ r - 1 := by linarith
    have hbase_le : r - 1 ≤ r := by linarith
    have hp4 : (r - 1) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ hbase hbase_le 4
    apply (div_le_div_iff₀ (pow_pos hrpos 6) (pow_pos hrpos 2)).2
    calc
      (r - 1) ^ 4 * r ^ 2 ≤ r ^ 4 * r ^ 2 :=
        mul_le_mul_of_nonneg_right hp4 (sq_nonneg r)
      _ = 1 * r ^ 6 := by ring

/-- Tight certified decimal bounds for `phi 3 = 3 log 3 - 2`. -/
theorem phi_three_bounds :
    (12958 : ℝ) / 10000 ≤ phi 3 ∧ phi 3 ≤ (12959 : ℝ) / 10000 := by
  constructor
  · have h := Real.log_three_gt_d9
    unfold phi
    norm_num at h ⊢
    linarith
  · have h := Real.log_three_lt_d9
    unfold phi
    norm_num at h ⊢
    linarith

end stoch_to_det
