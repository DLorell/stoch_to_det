import stoch_to_det.PhiBounds
import stoch_to_det.PhiBounds2

namespace stoch_to_det

private lemma phi_tangent {r t : ℝ} (hr0 : 0 ≤ r) (ht : 0 < t) :
    phi t + Real.log t * (r - t) ≤ phi r := by
  by_cases hrz : r = 0
  · subst r
    unfold phi
    simp
    ring_nf
    linarith
  · have hr : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
    have hq0 : 0 ≤ r / t := div_nonneg hr0 ht.le
    have hrem : 0 ≤ t * phi (r / t) := mul_nonneg ht.le (phi_nonneg hq0)
    have hid :
        phi r = phi t + Real.log t * (r - t) + t * phi (r / t) := by
      unfold phi
      rw [Real.log_div hr.ne' ht.ne']
      field_simp [ht.ne']
      ring
    rw [hid]
    linarith

private lemma phi_left_affine {r t s : ℝ} (hr0 : 0 ≤ r) (ht : 0 < t)
    (htr : t ≤ r) (hs : s ≤ Real.log t) :
    1 - t + s * r ≤ phi r := by
  have hp : t * s - t + 1 ≤ phi t := by
    have hm := mul_le_mul_of_nonneg_left hs ht.le
    unfold phi
    linarith
  have hm := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr htr)
  calc
    1 - t + s * r = (t * s - t + 1) + s * (r - t) := by ring
    _ ≤ phi t + Real.log t * (r - t) := add_le_add hp hm
    _ ≤ phi r := phi_tangent hr0 ht

private lemma phi_right_affine {r t p s : ℝ} (hr0 : 0 ≤ r) (ht : 0 < t)
    (hrt : r ≤ t) (hp : p ≤ phi t) (hs : Real.log t ≤ s) :
    p + s * (r - t) ≤ phi r := by
  have hm := mul_le_mul_of_nonpos_right hs (sub_nonpos.mpr hrt)
  calc
    p + s * (r - t) ≤ phi t + Real.log t * (r - t) := add_le_add hp hm
    _ ≤ phi r := phi_tangent hr0 ht

private lemma zone2_affine_step {a b r p s : ℝ}
    (har : a ≤ r) (hrb : r ≤ b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hs : s ≤ 0) (htan : p + s * r ≤ phi r)
    (hE0 : 0 ≤ p + s * b)
    (hnum : (1 - a) ^ 16 ≤ (934 : ℝ) * a ^ 3 * (p + s * b) ^ 7) :
    (1 - r) ^ 16 ≤ (934 : ℝ) * r ^ 3 * phi r ^ 7 := by
  have hr0 : 0 ≤ r := ha0.trans har
  have hr1 : r ≤ 1 := hrb.trans hb1
  have hE : p + s * b ≤ phi r := by
    have hm : 0 ≤ (-s) * (b - r) :=
      mul_nonneg (neg_nonneg.mpr hs) (sub_nonneg.mpr hrb)
    nlinarith
  have hleft := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - r)
    (by linarith : 1 - r ≤ 1 - a) 16
  have hrpow := pow_le_pow_left₀ ha0 har 3
  have hEpow := pow_le_pow_left₀ hE0 hE 7
  calc
    (1 - r) ^ 16 ≤ (1 - a) ^ 16 := hleft
    _ ≤ (934 : ℝ) * a ^ 3 * (p + s * b) ^ 7 := hnum
    _ ≤ (934 : ℝ) * r ^ 3 * (p + s * b) ^ 7 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrpow (by norm_num)) (by positivity)
    _ ≤ (934 : ℝ) * r ^ 3 * phi r ^ 7 := by
      exact mul_le_mul_of_nonneg_left hEpow (by positivity)

private lemma zone3_left_affine_step {a b r p s : ℝ}
    (har : a ≤ r) (hrb : r ≤ b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hs : s ≤ 0) (htan : p + s * r ≤ phi r)
    (hE0 : 0 ≤ p + s * b)
    (hnum : (1 - a) ^ 8 ≤ (217 / 10 : ℝ) * a ^ 3 * (p + s * b) ^ 3) :
    (r - 1) ^ 8 ≤ (217 / 10 : ℝ) * r ^ 3 * phi r ^ 3 := by
  have hr0 : 0 ≤ r := ha0.trans har
  have hr1 : r ≤ 1 := hrb.trans hb1
  have hE : p + s * b ≤ phi r := by
    have hm : 0 ≤ (-s) * (b - r) :=
      mul_nonneg (neg_nonneg.mpr hs) (sub_nonneg.mpr hrb)
    nlinarith
  have hleft := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - r)
    (by linarith : 1 - r ≤ 1 - a) 8
  have hrpow := pow_le_pow_left₀ ha0 har 3
  have hEpow := pow_le_pow_left₀ hE0 hE 3
  calc
    (r - 1) ^ 8 = (1 - r) ^ 8 := by ring
    _ ≤ (1 - a) ^ 8 := hleft
    _ ≤ (217 / 10 : ℝ) * a ^ 3 * (p + s * b) ^ 3 := hnum
    _ ≤ (217 / 10 : ℝ) * r ^ 3 * (p + s * b) ^ 3 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrpow (by norm_num)) (by positivity)
    _ ≤ (217 / 10 : ℝ) * r ^ 3 * phi r ^ 3 := by
      exact mul_le_mul_of_nonneg_left hEpow (by positivity)

private lemma zone3_right_affine_step {a b r p s : ℝ}
    (har : a ≤ r) (hrb : r ≤ b) (ha1 : 1 ≤ a)
    (hs : 0 ≤ s) (htan : p + s * r ≤ phi r)
    (hE0 : 0 ≤ p + s * a)
    (hnum : (b - 1) ^ 8 ≤ (217 / 10 : ℝ) * a ^ 3 * (p + s * a) ^ 3) :
    (r - 1) ^ 8 ≤ (217 / 10 : ℝ) * r ^ 3 * phi r ^ 3 := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha1
  have hr0 : 0 ≤ r := ha0.trans har
  have hE : p + s * a ≤ phi r := by
    have hm : 0 ≤ s * (r - a) := mul_nonneg hs (sub_nonneg.mpr har)
    nlinarith
  have hleft := pow_le_pow_left₀ (by linarith : 0 ≤ r - 1)
    (by linarith : r - 1 ≤ b - 1) 8
  have hrpow := pow_le_pow_left₀ ha0 har 3
  have hEpow := pow_le_pow_left₀ hE0 hE 3
  calc
    (r - 1) ^ 8 ≤ (b - 1) ^ 8 := hleft
    _ ≤ (217 / 10 : ℝ) * a ^ 3 * (p + s * a) ^ 3 := hnum
    _ ≤ (217 / 10 : ℝ) * r ^ 3 * (p + s * a) ^ 3 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrpow (by norm_num)) (by positivity)
    _ ≤ (217 / 10 : ℝ) * r ^ 3 * phi r ^ 3 := by
      exact mul_le_mul_of_nonneg_left hEpow (by positivity)

private noncomputable def c5lo : ℝ := 16094379123 / 10000000000
private noncomputable def c5hi : ℝ := 16094379126 / 10000000000
private noncomputable def c3hi : ℝ := 10986122888 / 10000000000
private noncomputable def s45 : ℝ :=
  2 * (10986122885 / 10000000000) -
    2 * (6931471808 / 10000000000) - 16094379126 / 10000000000
private noncomputable def s2 : ℝ := 6931471803 / 10000000000
private noncomputable def s10 : ℝ :=
  (6931471803 + 16094379123 - 10986122888) / 10000000000
private noncomputable def s25 : ℝ :=
  (2 * 16094379123 - 2 * 6931471808) / 10000000000
private noncomputable def s9 : ℝ := 2 * 10986122885 / 10000000000

private lemma log_one_fifth : Real.log (1 / 5 : ℝ) = -Real.log 5 := by
  rw [show (1 / 5 : ℝ) = (5 : ℝ)⁻¹ by norm_num, Real.log_inv]

private lemma log_nine_twentieths :
    Real.log (9 / 20 : ℝ) = 2 * Real.log 3 - 2 * Real.log 2 - Real.log 5 := by
  rw [show (9 / 20 : ℝ) = (3 * 3) / ((2 * 2) * 5) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  ring

private lemma log_ten_thirds :
    Real.log (10 / 3 : ℝ) = Real.log 2 + Real.log 5 - Real.log 3 := by
  rw [show (10 / 3 : ℝ) = (2 * 5) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]

private lemma log_twentyfive_fourths :
    Real.log (25 / 4 : ℝ) = 2 * Real.log 5 - 2 * Real.log 2 := by
  rw [show (25 / 4 : ℝ) = (5 * 5) / (2 * 2) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  ring

private lemma log_nine : Real.log (9 : ℝ) = 2 * Real.log 3 := by
  rw [show (9 : ℝ) = 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

theorem price_zone1 {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 5) :
    (r - 1) ^ 2 ≤ (687 / 500 : ℝ) * phi r := by
  have hp : (4 / 5 : ℝ) - (1 / 5) * c5hi ≤ phi (1 / 5) := by
    rw [show phi (1 / 5) = (1 / 5 : ℝ) * Real.log (1 / 5) - 1 / 5 + 1 by rfl,
      log_one_fifth]
    dsimp [c5hi]
    linarith [Real.log_five_lt_d9]
  have hs : Real.log (1 / 5 : ℝ) ≤ -c5lo := by
    rw [log_one_fifth]
    dsimp [c5lo]
    linarith [Real.log_five_gt_d9]
  have hphi := phi_right_affine hr0 (by norm_num : (0 : ℝ) < 1 / 5) hr hp hs
  have hprod : 0 ≤ r * (1 / 5 - r) :=
    mul_nonneg hr0 (sub_nonneg.mpr hr)
  have hpoly :
      (r - 1) ^ 2 ≤ (687 / 500 : ℝ) *
        ((4 / 5 : ℝ) - (1 / 5) * c5hi + (-c5lo) * (r - 1 / 5)) := by
    dsimp [c5hi, c5lo]
    nlinarith
  calc
    (r - 1) ^ 2 ≤ (687 / 500 : ℝ) *
        ((4 / 5 : ℝ) - (1 / 5) * c5hi + (-c5lo) * (r - 1 / 5)) := hpoly
    _ ≤ (687 / 500 : ℝ) * phi r :=
      mul_le_mul_of_nonneg_left hphi (by norm_num)

theorem price_zone2 {r : ℝ} (hlo : 1 / 5 ≤ r) (hhi : r ≤ 9 / 20) :
    (1 - r) ^ 16 ≤ (934 : ℝ) * r ^ 3 * phi r ^ 7 := by
  have hr0 : 0 ≤ r := by linarith
  by_cases hthird : r ≤ 1 / 3
  · have hslope : -c5hi ≤ Real.log (1 / 5 : ℝ) := by
      rw [log_one_fifth]
      dsimp [c5hi]
      linarith [Real.log_five_lt_d9]
    have htan := phi_left_affine hr0 (by norm_num : (0 : ℝ) < 1 / 5) hlo hslope
    have htan' : (4 / 5 : ℝ) + (-c5hi) * r ≤ phi r := by
      calc
        (4 / 5 : ℝ) + (-c5hi) * r = 1 - 1 / 5 + (-c5hi) * r := by ring
        _ ≤ phi r := htan
    by_cases h1 : r ≤ 43 / 200
    · apply zone2_affine_step (a := 1 / 5) (b := 43 / 200)
        (p := 4 / 5) (s := -c5hi) hlo h1 (by norm_num) (by norm_num)
      · norm_num [c5hi]
      · exact htan'
      · norm_num [c5hi]
      · norm_num [c5hi]
    · have hl : 43 / 200 ≤ r := (lt_of_not_ge h1).le
      by_cases h2 : r ≤ 47 / 200
      · apply zone2_affine_step (a := 43 / 200) (b := 47 / 200)
          (p := 4 / 5) (s := -c5hi) hl h2 (by norm_num) (by norm_num)
        · norm_num [c5hi]
        · exact htan'
        · norm_num [c5hi]
        · norm_num [c5hi]
      · have hl : 47 / 200 ≤ r := (lt_of_not_ge h2).le
        by_cases h3 : r ≤ 13 / 50
        · apply zone2_affine_step (a := 47 / 200) (b := 13 / 50)
            (p := 4 / 5) (s := -c5hi) hl h3 (by norm_num) (by norm_num)
          · norm_num [c5hi]
          · exact htan'
          · norm_num [c5hi]
          · norm_num [c5hi]
        · have hl : 13 / 50 ≤ r := (lt_of_not_ge h3).le
          by_cases h4 : r ≤ 57 / 200
          · apply zone2_affine_step (a := 13 / 50) (b := 57 / 200)
              (p := 4 / 5) (s := -c5hi) hl h4 (by norm_num) (by norm_num)
            · norm_num [c5hi]
            · exact htan'
            · norm_num [c5hi]
            · norm_num [c5hi]
          · have hl : 57 / 200 ≤ r := (lt_of_not_ge h4).le
            by_cases h5 : r ≤ 31 / 100
            · apply zone2_affine_step (a := 57 / 200) (b := 31 / 100)
                (p := 4 / 5) (s := -c5hi) hl h5 (by norm_num) (by norm_num)
              · norm_num [c5hi]
              · exact htan'
              · norm_num [c5hi]
              · norm_num [c5hi]
            · have hl : 31 / 100 ≤ r := (lt_of_not_ge h5).le
              by_cases h6 : r ≤ 33 / 100
              · apply zone2_affine_step (a := 31 / 100) (b := 33 / 100)
                  (p := 4 / 5) (s := -c5hi) hl h6 (by norm_num) (by norm_num)
                · norm_num [c5hi]
                · exact htan'
                · norm_num [c5hi]
                · norm_num [c5hi]
              · have hl : 33 / 100 ≤ r := (lt_of_not_ge h6).le
                apply zone2_affine_step (a := 33 / 100) (b := 1 / 3)
                  (p := 4 / 5) (s := -c5hi) hl hthird (by norm_num) (by norm_num)
                · norm_num [c5hi]
                · exact htan'
                · norm_num [c5hi]
                · norm_num [c5hi]
  · have hthirdlo : 1 / 3 ≤ r := (lt_of_not_ge hthird).le
    have hslope : -c3hi ≤ Real.log (1 / 3 : ℝ) := by
      rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv]
      dsimp [c3hi]
      linarith [Real.log_three_lt_d9]
    have htan := phi_left_affine hr0 (by norm_num : (0 : ℝ) < 1 / 3) hthirdlo hslope
    have htan' : (2 / 3 : ℝ) + (-c3hi) * r ≤ phi r := by
      calc
        (2 / 3 : ℝ) + (-c3hi) * r = 1 - 1 / 3 + (-c3hi) * r := by ring
        _ ≤ phi r := htan
    by_cases h1 : r ≤ 233 / 600
    · apply zone2_affine_step (a := 1 / 3) (b := 233 / 600)
        (p := 2 / 3) (s := -c3hi) hthirdlo h1 (by norm_num) (by norm_num)
      · norm_num [c3hi]
      · exact htan'
      · norm_num [c3hi]
      · norm_num [c3hi]
    · have hl : 233 / 600 ≤ r := (lt_of_not_ge h1).le
      by_cases h2 : r ≤ 263 / 600
      · apply zone2_affine_step (a := 233 / 600) (b := 263 / 600)
          (p := 2 / 3) (s := -c3hi) hl h2 (by norm_num) (by norm_num)
        · norm_num [c3hi]
        · exact htan'
        · norm_num [c3hi]
        · norm_num [c3hi]
      · have hl : 263 / 600 ≤ r := (lt_of_not_ge h2).le
        apply zone2_affine_step (a := 263 / 600) (b := 9 / 20)
          (p := 2 / 3) (s := -c3hi) hl hhi (by norm_num) (by norm_num)
        · norm_num [c3hi]
        · exact htan'
        · norm_num [c3hi]
        · norm_num [c3hi]

private lemma price_zone3_bulk {r : ℝ} (hlo : 5 / 8 ≤ r) (hhi : r ≤ 2) :
    (r - 1) ^ 8 ≤ (217 / 10 : ℝ) * r ^ 3 * phi r ^ 3 := by
  have hr0 : 0 ≤ r := by linarith
  have hphi0 := phi_nonneg hr0
  have hbulk := bulk_quad_two r hr0 hhi
  change (r - 1) ^ 2 ≤ (259 / 100 : ℝ) * phi r at hbulk
  have hscaled : (100 / 259 : ℝ) * (r - 1) ^ 2 ≤ phi r := by
    have hm := mul_le_mul_of_nonneg_left hbulk (by norm_num : (0 : ℝ) ≤ 100 / 259)
    calc
      (100 / 259 : ℝ) * (r - 1) ^ 2 ≤
          (100 / 259 : ℝ) * ((259 / 100 : ℝ) * phi r) := hm
      _ = phi r := by ring
  have hscaled0 : 0 ≤ (100 / 259 : ℝ) * (r - 1) ^ 2 := by positivity
  have hcube := pow_le_pow_left₀ hscaled0 hscaled 3
  have hcoeff :
      (r - 1) ^ 2 ≤ (21700000 / 17373979 : ℝ) * r ^ 3 := by
    by_cases hr1 : r ≤ 1
    · have hp2 := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - r)
        (by linarith : 1 - r ≤ 3 / 8) 2
      have hp3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 8) hlo 3
      rw [show (r - 1) ^ 2 = (1 - r) ^ 2 by ring]
      nlinarith
    · have hr1 : 1 ≤ r := (lt_of_not_ge hr1).le
      have hp2 := pow_le_pow_left₀ (by linarith : 0 ≤ r - 1)
        (by linarith : r - 1 ≤ r) 2
      have h23 : r ^ 2 ≤ r ^ 3 := by
        have hm : 0 ≤ r ^ 2 * (r - 1) := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr1)
        nlinarith
      nlinarith
  calc
    (r - 1) ^ 8 = (r - 1) ^ 2 * ((r - 1) ^ 2) ^ 3 := by ring
    _ ≤ (21700000 / 17373979 : ℝ) * r ^ 3 * ((r - 1) ^ 2) ^ 3 :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = (217 / 10 : ℝ) * r ^ 3 *
        (((100 / 259 : ℝ) * (r - 1) ^ 2) ^ 3) := by ring
    _ ≤ (217 / 10 : ℝ) * r ^ 3 * phi r ^ 3 :=
      mul_le_mul_of_nonneg_left hcube (by positivity)

theorem price_zone3 {r : ℝ} (hlo : 9 / 20 ≤ r) (hhi : r ≤ 12) :
    (r - 1) ^ 8 ≤ (217 / 10 : ℝ) * r ^ 3 * phi r ^ 3 := by
  have hr0 : 0 ≤ r := by linarith
  by_cases h58 : r ≤ 5 / 8
  · have hslope : s45 ≤ Real.log (9 / 20 : ℝ) := by
      rw [log_nine_twentieths]
      dsimp [s45]
      linarith [Real.log_three_gt_d9, Real.log_two_lt_d9, Real.log_five_lt_d9]
    have htan := phi_left_affine hr0 (by norm_num : (0 : ℝ) < 9 / 20) hlo hslope
    have htan' : (11 / 20 : ℝ) + s45 * r ≤ phi r := by
      calc
        (11 / 20 : ℝ) + s45 * r = 1 - 9 / 20 + s45 * r := by ring
        _ ≤ phi r := htan
    by_cases h1 : r ≤ 97 / 200
    · apply zone3_left_affine_step (a := 9 / 20) (b := 97 / 200)
        (p := 11 / 20) (s := s45) hlo h1 (by norm_num) (by norm_num)
      · norm_num [s45]
      · exact htan'
      · norm_num [s45]
      · norm_num [s45]
    · have hl : 97 / 200 ≤ r := (lt_of_not_ge h1).le
      by_cases h2 : r ≤ 53 / 100
      · apply zone3_left_affine_step (a := 97 / 200) (b := 53 / 100)
          (p := 11 / 20) (s := s45) hl h2 (by norm_num) (by norm_num)
        · norm_num [s45]
        · exact htan'
        · norm_num [s45]
        · norm_num [s45]
      · have hl : 53 / 100 ≤ r := (lt_of_not_ge h2).le
        by_cases h3 : r ≤ 23 / 40
        · apply zone3_left_affine_step (a := 53 / 100) (b := 23 / 40)
            (p := 11 / 20) (s := s45) hl h3 (by norm_num) (by norm_num)
          · norm_num [s45]
          · exact htan'
          · norm_num [s45]
          · norm_num [s45]
        · have hl : 23 / 40 ≤ r := (lt_of_not_ge h3).le
          by_cases h4 : r ≤ 121 / 200
          · apply zone3_left_affine_step (a := 23 / 40) (b := 121 / 200)
              (p := 11 / 20) (s := s45) hl h4 (by norm_num) (by norm_num)
            · norm_num [s45]
            · exact htan'
            · norm_num [s45]
            · norm_num [s45]
          · have hl : 121 / 200 ≤ r := (lt_of_not_ge h4).le
            apply zone3_left_affine_step (a := 121 / 200) (b := 5 / 8)
              (p := 11 / 20) (s := s45) hl h58 (by norm_num) (by norm_num)
            · norm_num [s45]
            · exact htan'
            · norm_num [s45]
            · norm_num [s45]
  · have h58lo : 5 / 8 ≤ r := (lt_of_not_ge h58).le
    by_cases h2 : r ≤ 2
    · exact price_zone3_bulk h58lo h2
    · have h2lo : 2 ≤ r := (lt_of_not_ge h2).le
      by_cases h103 : r ≤ 10 / 3
      · have hslope : s2 ≤ Real.log (2 : ℝ) := by
          dsimp [s2]
          linarith [Real.log_two_gt_d9]
        have htan := phi_left_affine hr0 (by norm_num : (0 : ℝ) < 2) h2lo hslope
        have htan' : (-1 : ℝ) + s2 * r ≤ phi r := by
          calc
            (-1 : ℝ) + s2 * r = 1 - 2 + s2 * r := by ring
            _ ≤ phi r := htan
        by_cases h1 : r ≤ 23 / 10
        · apply zone3_right_affine_step (a := 2) (b := 23 / 10)
            (p := -1) (s := s2) h2lo h1 (by norm_num)
          · norm_num [s2]
          · exact htan'
          · norm_num [s2]
          · norm_num [s2]
        · have hl : 23 / 10 ≤ r := (lt_of_not_ge h1).le
          by_cases h2 : r ≤ 53 / 20
          · apply zone3_right_affine_step (a := 23 / 10) (b := 53 / 20)
              (p := -1) (s := s2) hl h2 (by norm_num)
            · norm_num [s2]
            · exact htan'
            · norm_num [s2]
            · norm_num [s2]
          · have hl : 53 / 20 ≤ r := (lt_of_not_ge h2).le
            by_cases h3 : r ≤ 59 / 20
            · apply zone3_right_affine_step (a := 53 / 20) (b := 59 / 20)
                (p := -1) (s := s2) hl h3 (by norm_num)
              · norm_num [s2]
              · exact htan'
              · norm_num [s2]
              · norm_num [s2]
            · have hl : 59 / 20 ≤ r := (lt_of_not_ge h3).le
              by_cases h4 : r ≤ 16 / 5
              · apply zone3_right_affine_step (a := 59 / 20) (b := 16 / 5)
                  (p := -1) (s := s2) hl h4 (by norm_num)
                · norm_num [s2]
                · exact htan'
                · norm_num [s2]
                · norm_num [s2]
              · have hl : 16 / 5 ≤ r := (lt_of_not_ge h4).le
                apply zone3_right_affine_step (a := 16 / 5) (b := 10 / 3)
                  (p := -1) (s := s2) hl h103 (by norm_num)
                · norm_num [s2]
                · exact htan'
                · norm_num [s2]
                · norm_num [s2]
      · have h103lo : 10 / 3 ≤ r := (lt_of_not_ge h103).le
        by_cases h254 : r ≤ 25 / 4
        · have hslope : s10 ≤ Real.log (10 / 3 : ℝ) := by
            rw [log_ten_thirds]
            dsimp [s10]
            linarith [Real.log_two_gt_d9, Real.log_five_gt_d9, Real.log_three_lt_d9]
          have htan := phi_left_affine hr0 (by norm_num : (0 : ℝ) < 10 / 3) h103lo hslope
          have htan' : (-7 / 3 : ℝ) + s10 * r ≤ phi r := by
            calc
              (-7 / 3 : ℝ) + s10 * r = 1 - 10 / 3 + s10 * r := by ring
              _ ≤ phi r := htan
          by_cases h1 : r ≤ 227 / 60
          · apply zone3_right_affine_step (a := 10 / 3) (b := 227 / 60)
              (p := -7 / 3) (s := s10) h103lo h1 (by norm_num)
            · norm_num [s10]
            · exact htan'
            · norm_num [s10]
            · norm_num [s10]
          · have hl : 227 / 60 ≤ r := (lt_of_not_ge h1).le
            by_cases h2 : r ≤ 127 / 30
            · apply zone3_right_affine_step (a := 227 / 60) (b := 127 / 30)
                (p := -7 / 3) (s := s10) hl h2 (by norm_num)
              · norm_num [s10]
              · exact htan'
              · norm_num [s10]
              · norm_num [s10]
            · have hl : 127 / 30 ≤ r := (lt_of_not_ge h2).le
              by_cases h3 : r ≤ 281 / 60
              · apply zone3_right_affine_step (a := 127 / 30) (b := 281 / 60)
                  (p := -7 / 3) (s := s10) hl h3 (by norm_num)
                · norm_num [s10]
                · exact htan'
                · norm_num [s10]
                · norm_num [s10]
              · have hl : 281 / 60 ≤ r := (lt_of_not_ge h3).le
                by_cases h4 : r ≤ 61 / 12
                · apply zone3_right_affine_step (a := 281 / 60) (b := 61 / 12)
                    (p := -7 / 3) (s := s10) hl h4 (by norm_num)
                  · norm_num [s10]
                  · exact htan'
                  · norm_num [s10]
                  · norm_num [s10]
                · have hl : 61 / 12 ≤ r := (lt_of_not_ge h4).le
                  by_cases h5 : r ≤ 163 / 30
                  · apply zone3_right_affine_step (a := 61 / 12) (b := 163 / 30)
                      (p := -7 / 3) (s := s10) hl h5 (by norm_num)
                    · norm_num [s10]
                    · exact htan'
                    · norm_num [s10]
                    · norm_num [s10]
                  · have hl : 163 / 30 ≤ r := (lt_of_not_ge h5).le
                    by_cases h6 : r ≤ 86 / 15
                    · apply zone3_right_affine_step (a := 163 / 30) (b := 86 / 15)
                        (p := -7 / 3) (s := s10) hl h6 (by norm_num)
                      · norm_num [s10]
                      · exact htan'
                      · norm_num [s10]
                      · norm_num [s10]
                    · have hl : 86 / 15 ≤ r := (lt_of_not_ge h6).le
                      by_cases h7 : r ≤ 359 / 60
                      · apply zone3_right_affine_step (a := 86 / 15) (b := 359 / 60)
                          (p := -7 / 3) (s := s10) hl h7 (by norm_num)
                        · norm_num [s10]
                        · exact htan'
                        · norm_num [s10]
                        · norm_num [s10]
                      · have hl : 359 / 60 ≤ r := (lt_of_not_ge h7).le
                        by_cases h8 : r ≤ 371 / 60
                        · apply zone3_right_affine_step (a := 359 / 60) (b := 371 / 60)
                            (p := -7 / 3) (s := s10) hl h8 (by norm_num)
                          · norm_num [s10]
                          · exact htan'
                          · norm_num [s10]
                          · norm_num [s10]
                        · have hl : 371 / 60 ≤ r := (lt_of_not_ge h8).le
                          apply zone3_right_affine_step (a := 371 / 60) (b := 25 / 4)
                            (p := -7 / 3) (s := s10) hl h254 (by norm_num)
                          · norm_num [s10]
                          · exact htan'
                          · norm_num [s10]
                          · norm_num [s10]
        · have h254lo : 25 / 4 ≤ r := (lt_of_not_ge h254).le
          by_cases h9 : r ≤ 9
          · have hslope : s25 ≤ Real.log (25 / 4 : ℝ) := by
              rw [log_twentyfive_fourths]
              dsimp [s25]
              linarith [Real.log_five_gt_d9, Real.log_two_lt_d9]
            have htan := phi_left_affine hr0 (by norm_num : (0 : ℝ) < 25 / 4) h254lo hslope
            have htan' : (-21 / 4 : ℝ) + s25 * r ≤ phi r := by
              calc
                (-21 / 4 : ℝ) + s25 * r = 1 - 25 / 4 + s25 * r := by ring
                _ ≤ phi r := htan
            by_cases h1 : r ≤ 27 / 4
            · apply zone3_right_affine_step (a := 25 / 4) (b := 27 / 4)
                (p := -21 / 4) (s := s25) h254lo h1 (by norm_num)
              · norm_num [s25]
              · exact htan'
              · norm_num [s25]
              · norm_num [s25]
            · have hl : 27 / 4 ≤ r := (lt_of_not_ge h1).le
              by_cases h2 : r ≤ 29 / 4
              · apply zone3_right_affine_step (a := 27 / 4) (b := 29 / 4)
                  (p := -21 / 4) (s := s25) hl h2 (by norm_num)
                · norm_num [s25]
                · exact htan'
                · norm_num [s25]
                · norm_num [s25]
              · have hl : 29 / 4 ≤ r := (lt_of_not_ge h2).le
                by_cases h3 : r ≤ 77 / 10
                · apply zone3_right_affine_step (a := 29 / 4) (b := 77 / 10)
                    (p := -21 / 4) (s := s25) hl h3 (by norm_num)
                  · norm_num [s25]
                  · exact htan'
                  · norm_num [s25]
                  · norm_num [s25]
                · have hl : 77 / 10 ≤ r := (lt_of_not_ge h3).le
                  by_cases h4 : r ≤ 163 / 20
                  · apply zone3_right_affine_step (a := 77 / 10) (b := 163 / 20)
                      (p := -21 / 4) (s := s25) hl h4 (by norm_num)
                    · norm_num [s25]
                    · exact htan'
                    · norm_num [s25]
                    · norm_num [s25]
                  · have hl : 163 / 20 ≤ r := (lt_of_not_ge h4).le
                    by_cases h5 : r ≤ 171 / 20
                    · apply zone3_right_affine_step (a := 163 / 20) (b := 171 / 20)
                        (p := -21 / 4) (s := s25) hl h5 (by norm_num)
                      · norm_num [s25]
                      · exact htan'
                      · norm_num [s25]
                      · norm_num [s25]
                    · have hl : 171 / 20 ≤ r := (lt_of_not_ge h5).le
                      by_cases h6 : r ≤ 89 / 10
                      · apply zone3_right_affine_step (a := 171 / 20) (b := 89 / 10)
                          (p := -21 / 4) (s := s25) hl h6 (by norm_num)
                        · norm_num [s25]
                        · exact htan'
                        · norm_num [s25]
                        · norm_num [s25]
                      · have hl : 89 / 10 ≤ r := (lt_of_not_ge h6).le
                        apply zone3_right_affine_step (a := 89 / 10) (b := 9)
                          (p := -21 / 4) (s := s25) hl h9 (by norm_num)
                        · norm_num [s25]
                        · exact htan'
                        · norm_num [s25]
                        · norm_num [s25]
          · have h9lo : 9 ≤ r := (lt_of_not_ge h9).le
            have hslope : s9 ≤ Real.log (9 : ℝ) := by
              rw [log_nine]
              dsimp [s9]
              linarith [Real.log_three_gt_d9]
            have htan := phi_left_affine hr0 (by norm_num : (0 : ℝ) < 9) h9lo hslope
            have htan' : (-8 : ℝ) + s9 * r ≤ phi r := by
              calc
                (-8 : ℝ) + s9 * r = 1 - 9 + s9 * r := by ring
                _ ≤ phi r := htan
            by_cases h1 : r ≤ 236 / 25
            · apply zone3_right_affine_step (a := 9) (b := 236 / 25)
                (p := -8) (s := s9) h9lo h1 (by norm_num)
              · norm_num [s9]
              · exact htan'
              · norm_num [s9]
              · norm_num [s9]
            · have hl : 236 / 25 ≤ r := (lt_of_not_ge h1).le
              by_cases h2 : r ≤ 197 / 20
              · apply zone3_right_affine_step (a := 236 / 25) (b := 197 / 20)
                  (p := -8) (s := s9) hl h2 (by norm_num)
                · norm_num [s9]
                · exact htan'
                · norm_num [s9]
                · norm_num [s9]
              · have hl : 197 / 20 ≤ r := (lt_of_not_ge h2).le
                by_cases h3 : r ≤ 511 / 50
                · apply zone3_right_affine_step (a := 197 / 20) (b := 511 / 50)
                    (p := -8) (s := s9) hl h3 (by norm_num)
                  · norm_num [s9]
                  · exact htan'
                  · norm_num [s9]
                  · norm_num [s9]
                · have hl : 511 / 50 ≤ r := (lt_of_not_ge h3).le
                  by_cases h4 : r ≤ 264 / 25
                  · apply zone3_right_affine_step (a := 511 / 50) (b := 264 / 25)
                      (p := -8) (s := s9) hl h4 (by norm_num)
                    · norm_num [s9]
                    · exact htan'
                    · norm_num [s9]
                    · norm_num [s9]
                  · have hl : 264 / 25 ≤ r := (lt_of_not_ge h4).le
                    by_cases h5 : r ≤ 543 / 50
                    · apply zone3_right_affine_step (a := 264 / 25) (b := 543 / 50)
                        (p := -8) (s := s9) hl h5 (by norm_num)
                      · norm_num [s9]
                      · exact htan'
                      · norm_num [s9]
                      · norm_num [s9]
                    · have hl : 543 / 50 ≤ r := (lt_of_not_ge h5).le
                      by_cases h6 : r ≤ 1113 / 100
                      · apply zone3_right_affine_step (a := 543 / 50) (b := 1113 / 100)
                          (p := -8) (s := s9) hl h6 (by norm_num)
                        · norm_num [s9]
                        · exact htan'
                        · norm_num [s9]
                        · norm_num [s9]
                      · have hl : 1113 / 100 ≤ r := (lt_of_not_ge h6).le
                        by_cases h7 : r ≤ 284 / 25
                        · apply zone3_right_affine_step (a := 1113 / 100) (b := 284 / 25)
                            (p := -8) (s := s9) hl h7 (by norm_num)
                          · norm_num [s9]
                          · exact htan'
                          · norm_num [s9]
                          · norm_num [s9]
                        · have hl : 284 / 25 ≤ r := (lt_of_not_ge h7).le
                          by_cases h8 : r ≤ 289 / 25
                          · apply zone3_right_affine_step (a := 284 / 25) (b := 289 / 25)
                              (p := -8) (s := s9) hl h8 (by norm_num)
                            · norm_num [s9]
                            · exact htan'
                            · norm_num [s9]
                            · norm_num [s9]
                          · have hl : 289 / 25 ≤ r := (lt_of_not_ge h8).le
                            by_cases h9' : r ≤ 1173 / 100
                            · apply zone3_right_affine_step (a := 289 / 25) (b := 1173 / 100)
                                (p := -8) (s := s9) hl h9' (by norm_num)
                              · norm_num [s9]
                              · exact htan'
                              · norm_num [s9]
                              · norm_num [s9]
                            · have hl : 1173 / 100 ≤ r := (lt_of_not_ge h9').le
                              by_cases h10 : r ≤ 297 / 25
                              · apply zone3_right_affine_step (a := 1173 / 100) (b := 297 / 25)
                                  (p := -8) (s := s9) hl h10 (by norm_num)
                                · norm_num [s9]
                                · exact htan'
                                · norm_num [s9]
                                · norm_num [s9]
                              · have hl : 297 / 25 ≤ r := (lt_of_not_ge h10).le
                                apply zone3_right_affine_step (a := 297 / 25) (b := 12)
                                  (p := -8) (s := s9) hl hhi (by norm_num)
                                · norm_num [s9]
                                · exact htan'
                                · norm_num [s9]
                                · norm_num [s9]

end stoch_to_det
