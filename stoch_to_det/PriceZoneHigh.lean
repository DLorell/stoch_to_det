import stoch_to_det.PhiBounds

namespace stoch_to_det

private lemma log_twelve_lower :
    (24849066491 / 10000000000 : ℝ) ≤ Real.log 12 := by
  rw [show (12 : ℝ) = 3 * (2 * 2) by norm_num,
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

private lemma log_twentyfive_lower :
    (32188758246 / 10000000000 : ℝ) ≤ Real.log 25 := by
  rw [show (25 : ℝ) = 5 * 5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_five_gt_d9]

private lemma log_thirtytwo_lower :
    (34657359015 / 10000000000 : ℝ) ≤ Real.log 32 := by
  rw [show (32 : ℝ) = 2 * (2 * (2 * (2 * 2))) by norm_num,
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9]

private lemma log_fifty_lower :
    (39120230049 / 10000000000 : ℝ) ≤ Real.log 50 := by
  rw [show (50 : ℝ) = 2 * (5 * 5) by norm_num,
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

private lemma log_seventytwo_lower :
    (42716661179 / 10000000000 : ℝ) ≤ Real.log 72 := by
  rw [show (72 : ℝ) = 2 * (2 * (2 * (3 * 3))) by norm_num,
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

private lemma log_ninety_lower :
    (44998096696 / 10000000000 : ℝ) ≤ Real.log 90 := by
  rw [show (90 : ℝ) = 2 * (3 * (3 * 5)) by norm_num,
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]

private lemma phi_tangent_lower {r t s : ℝ} (ht : 0 < t) (htr : t ≤ r)
    (hs : s ≤ Real.log t) :
    s * r - t + 1 ≤ phi r := by
  have hr : 0 < r := ht.trans_le htr
  have hratio : 0 ≤ r / t := (div_pos hr ht).le
  have hrem : 0 ≤ t * phi (r / t) :=
    mul_nonneg ht.le (phi_nonneg hratio)
  have hid : phi r = phi t + Real.log t * (r - t) + t * phi (r / t) := by
    unfold phi
    rw [Real.log_div hr.ne' ht.ne']
    field_simp [ht.ne']
    all_goals ring
  have htangent : s * r - t + 1 ≤ phi t + Real.log t * (r - t) := by
    have htlog := mul_le_mul_of_nonneg_left hs ht.le
    have hshift := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr htr)
    unfold phi
    nlinarith
  rw [hid]
  linarith

private lemma z4_step {r a b t s : ℝ}
    (ha : 1 ≤ a) (hs : 0 ≤ s) (hella : 0 ≤ s * a - t + 1)
    (hcheck : (b - 1) ^ 16 ≤
      (147 / 10 : ℝ) * a ^ 9 * (s * a - t + 1) ^ 5)
    (har : a ≤ r) (hrb : r ≤ b) :
    (r - 1) ^ 16 ≤
      (147 / 10 : ℝ) * r ^ 9 * (s * r - t + 1) ^ 5 := by
  have hrbase : 0 ≤ r - 1 := by linarith
  have hleft : (r - 1) ^ 16 ≤ (b - 1) ^ 16 :=
    pow_le_pow_left₀ hrbase (by linarith) 16
  have ha0 : 0 ≤ a := by linarith
  have hr0 : 0 ≤ r := ha0.trans har
  have hp9 : a ^ 9 ≤ r ^ 9 := pow_le_pow_left₀ ha0 har 9
  have hell : s * a - t + 1 ≤ s * r - t + 1 := by
    nlinarith [mul_nonneg hs (sub_nonneg.mpr har)]
  have hp5 : (s * a - t + 1) ^ 5 ≤ (s * r - t + 1) ^ 5 :=
    pow_le_pow_left₀ hella hell 5
  have hprod : a ^ 9 * (s * a - t + 1) ^ 5 ≤
      r ^ 9 * (s * r - t + 1) ^ 5 :=
    mul_le_mul hp9 hp5 (pow_nonneg hella 5) (pow_nonneg hr0 9)
  calc
    (r - 1) ^ 16 ≤ (b - 1) ^ 16 := hleft
    _ ≤ (147 / 10 : ℝ) * a ^ 9 * (s * a - t + 1) ^ 5 := hcheck
    _ ≤ (147 / 10 : ℝ) * r ^ 9 * (s * r - t + 1) ^ 5 := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 147 / 10)

private lemma z4_lift {r t s : ℝ} (hr0 : 0 ≤ r)
    (hell0 : 0 ≤ s * r - t + 1) (hell : s * r - t + 1 ≤ phi r)
    (hpoly : (r - 1) ^ 16 ≤
      (147 / 10 : ℝ) * r ^ 9 * (s * r - t + 1) ^ 5) :
    (r - 1) ^ 16 ≤ (147 / 10 : ℝ) * r ^ 9 * phi r ^ 5 := by
  have hp5 : (s * r - t + 1) ^ 5 ≤ phi r ^ 5 :=
    pow_le_pow_left₀ hell0 hell 5
  calc
    (r - 1) ^ 16 ≤
        (147 / 10 : ℝ) * r ^ 9 * (s * r - t + 1) ^ 5 := hpoly
    _ ≤ (147 / 10 : ℝ) * r ^ 9 * phi r ^ 5 := by
      exact mul_le_mul_of_nonneg_left hp5
        (mul_nonneg (by norm_num) (pow_nonneg hr0 9))

private lemma z4_piece_twelve {r : ℝ} (hlo : 12 ≤ r) (hhi : r ≤ 25) :
    (r - 1) ^ 16 ≤ (147 / 10 : ℝ) * r ^ 9 *
      ((24849066491 / 10000000000 : ℝ) * r - 12 + 1) ^ 5 := by
  by_cases h1 : r ≤ (103 / 8 : ℝ)
  · exact z4_step (a := 12) (b := (103 / 8 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo h1
  · have hlo1 : (103 / 8 : ℝ) ≤ r := by linarith
    by_cases h2 : r ≤ (111 / 8 : ℝ)
    · exact z4_step (a := (103 / 8 : ℝ)) (b := (111 / 8 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo1 h2
    · have hlo2 : (111 / 8 : ℝ) ≤ r := by linarith
      by_cases h3 : r ≤ (119 / 8 : ℝ)
      · exact z4_step (a := (111 / 8 : ℝ)) (b := (119 / 8 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo2 h3
      · have hlo3 : (119 / 8 : ℝ) ≤ r := by linarith
        by_cases h4 : r ≤ (127 / 8 : ℝ)
        · exact z4_step (a := (119 / 8 : ℝ)) (b := (127 / 8 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo3 h4
        · have hlo4 : (127 / 8 : ℝ) ≤ r := by linarith
          by_cases h5 : r ≤ (135 / 8 : ℝ)
          · exact z4_step (a := (127 / 8 : ℝ)) (b := (135 / 8 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo4 h5
          · have hlo5 : (135 / 8 : ℝ) ≤ r := by linarith
            by_cases h6 : r ≤ (143 / 8 : ℝ)
            · exact z4_step (a := (135 / 8 : ℝ)) (b := (143 / 8 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo5 h6
            · have hlo6 : (143 / 8 : ℝ) ≤ r := by linarith
              by_cases h7 : r ≤ (151 / 8 : ℝ)
              · exact z4_step (a := (143 / 8 : ℝ)) (b := (151 / 8 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo6 h7
              · have hlo7 : (151 / 8 : ℝ) ≤ r := by linarith
                by_cases h8 : r ≤ (159 / 8 : ℝ)
                · exact z4_step (a := (151 / 8 : ℝ)) (b := (159 / 8 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo7 h8
                · have hlo8 : (159 / 8 : ℝ) ≤ r := by linarith
                  by_cases h9 : r ≤ (167 / 8 : ℝ)
                  · exact z4_step (a := (159 / 8 : ℝ)) (b := (167 / 8 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo8 h9
                  · have hlo9 : (167 / 8 : ℝ) ≤ r := by linarith
                    by_cases h10 : r ≤ (87 / 4 : ℝ)
                    · exact z4_step (a := (167 / 8 : ℝ)) (b := (87 / 4 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo9 h10
                    · have hlo10 : (87 / 4 : ℝ) ≤ r := by linarith
                      by_cases h11 : r ≤ (181 / 8 : ℝ)
                      · exact z4_step (a := (87 / 4 : ℝ)) (b := (181 / 8 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo10 h11
                      · have hlo11 : (181 / 8 : ℝ) ≤ r := by linarith
                        by_cases h12 : r ≤ (47 / 2 : ℝ)
                        · exact z4_step (a := (181 / 8 : ℝ)) (b := (47 / 2 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo11 h12
                        · have hlo12 : (47 / 2 : ℝ) ≤ r := by linarith
                          by_cases h13 : r ≤ (97 / 4 : ℝ)
                          · exact z4_step (a := (47 / 2 : ℝ)) (b := (97 / 4 : ℝ)) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo12 h13
                          · have hlo13 : (97 / 4 : ℝ) ≤ r := by linarith
                            exact z4_step (a := (97 / 4 : ℝ)) (b := 25) (t := 12) (s := (24849066491 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo13 hhi

private lemma z4_piece_twentyfive {r : ℝ} (hlo : 25 ≤ r) (hhi : r ≤ 32) :
    (r - 1) ^ 16 ≤ (147 / 10 : ℝ) * r ^ 9 *
      ((16094379123 / 5000000000 : ℝ) * r - 25 + 1) ^ 5 := by
  by_cases h1 : r ≤ (53 / 2 : ℝ)
  · exact z4_step (a := 25) (b := (53 / 2 : ℝ)) (t := 25) (s := (16094379123 / 5000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo h1
  · have hlo1 : (53 / 2 : ℝ) ≤ r := by linarith
    by_cases h2 : r ≤ 28
    · exact z4_step (a := (53 / 2 : ℝ)) (b := 28) (t := 25) (s := (16094379123 / 5000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo1 h2
    · have hlo2 : 28 ≤ r := by linarith
      by_cases h3 : r ≤ (59 / 2 : ℝ)
      · exact z4_step (a := 28) (b := (59 / 2 : ℝ)) (t := 25) (s := (16094379123 / 5000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo2 h3
      · have hlo3 : (59 / 2 : ℝ) ≤ r := by linarith
        by_cases h4 : r ≤ 31
        · exact z4_step (a := (59 / 2 : ℝ)) (b := 31) (t := 25) (s := (16094379123 / 5000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo3 h4
        · have hlo4 : 31 ≤ r := by linarith
          exact z4_step (a := 31) (b := 32) (t := 25) (s := (16094379123 / 5000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo4 hhi

private lemma z4_piece_thirtytwo {r : ℝ} (hlo : 32 ≤ r) (hhi : r ≤ 50) :
    (r - 1) ^ 16 ≤ (147 / 10 : ℝ) * r ^ 9 *
      ((6931471803 / 2000000000 : ℝ) * r - 32 + 1) ^ 5 := by
  by_cases h1 : r ≤ (269 / 8 : ℝ)
  · exact z4_step (a := 32) (b := (269 / 8 : ℝ)) (t := 32) (s := (6931471803 / 2000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo h1
  · have hlo1 : (269 / 8 : ℝ) ≤ r := by linarith
    by_cases h2 : r ≤ (141 / 4 : ℝ)
    · exact z4_step (a := (269 / 8 : ℝ)) (b := (141 / 4 : ℝ)) (t := 32) (s := (6931471803 / 2000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo1 h2
    · have hlo2 : (141 / 4 : ℝ) ≤ r := by linarith
      by_cases h3 : r ≤ (295 / 8 : ℝ)
      · exact z4_step (a := (141 / 4 : ℝ)) (b := (295 / 8 : ℝ)) (t := 32) (s := (6931471803 / 2000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo2 h3
      · have hlo3 : (295 / 8 : ℝ) ≤ r := by linarith
        by_cases h4 : r ≤ (77 / 2 : ℝ)
        · exact z4_step (a := (295 / 8 : ℝ)) (b := (77 / 2 : ℝ)) (t := 32) (s := (6931471803 / 2000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo3 h4
        · have hlo4 : (77 / 2 : ℝ) ≤ r := by linarith
          by_cases h5 : r ≤ (321 / 8 : ℝ)
          · exact z4_step (a := (77 / 2 : ℝ)) (b := (321 / 8 : ℝ)) (t := 32) (s := (6931471803 / 2000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo4 h5
          · have hlo5 : (321 / 8 : ℝ) ≤ r := by linarith
            by_cases h6 : r ≤ (167 / 4 : ℝ)
            · exact z4_step (a := (321 / 8 : ℝ)) (b := (167 / 4 : ℝ)) (t := 32) (s := (6931471803 / 2000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo5 h6
            · have hlo6 : (167 / 4 : ℝ) ≤ r := by linarith
              by_cases h7 : r ≤ (173 / 4 : ℝ)
              · exact z4_step (a := (167 / 4 : ℝ)) (b := (173 / 4 : ℝ)) (t := 32) (s := (6931471803 / 2000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo6 h7
              · have hlo7 : (173 / 4 : ℝ) ≤ r := by linarith
                by_cases h8 : r ≤ (179 / 4 : ℝ)
                · exact z4_step (a := (173 / 4 : ℝ)) (b := (179 / 4 : ℝ)) (t := 32) (s := (6931471803 / 2000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo7 h8
                · have hlo8 : (179 / 4 : ℝ) ≤ r := by linarith
                  by_cases h9 : r ≤ (185 / 4 : ℝ)
                  · exact z4_step (a := (179 / 4 : ℝ)) (b := (185 / 4 : ℝ)) (t := 32) (s := (6931471803 / 2000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo8 h9
                  · have hlo9 : (185 / 4 : ℝ) ≤ r := by linarith
                    by_cases h10 : r ≤ (381 / 8 : ℝ)
                    · exact z4_step (a := (185 / 4 : ℝ)) (b := (381 / 8 : ℝ)) (t := 32) (s := (6931471803 / 2000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo9 h10
                    · have hlo10 : (381 / 8 : ℝ) ≤ r := by linarith
                      by_cases h11 : r ≤ 49
                      · exact z4_step (a := (381 / 8 : ℝ)) (b := 49) (t := 32) (s := (6931471803 / 2000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo10 h11
                      · have hlo11 : 49 ≤ r := by linarith
                        exact z4_step (a := 49) (b := 50) (t := 32) (s := (6931471803 / 2000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo11 hhi

private lemma z4_piece_fifty {r : ℝ} (hlo : 50 ≤ r) (hhi : r ≤ 72) :
    (r - 1) ^ 16 ≤ (147 / 10 : ℝ) * r ^ 9 *
      ((39120230049 / 10000000000 : ℝ) * r - 50 + 1) ^ 5 := by
  by_cases h1 : r ≤ (207 / 4 : ℝ)
  · exact z4_step (a := 50) (b := (207 / 4 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo h1
  · have hlo1 : (207 / 4 : ℝ) ≤ r := by linarith
    by_cases h2 : r ≤ (427 / 8 : ℝ)
    · exact z4_step (a := (207 / 4 : ℝ)) (b := (427 / 8 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo1 h2
    · have hlo2 : (427 / 8 : ℝ) ≤ r := by linarith
      by_cases h3 : r ≤ 55
      · exact z4_step (a := (427 / 8 : ℝ)) (b := 55) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo2 h3
      · have hlo3 : 55 ≤ r := by linarith
        by_cases h4 : r ≤ (453 / 8 : ℝ)
        · exact z4_step (a := 55) (b := (453 / 8 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo3 h4
        · have hlo4 : (453 / 8 : ℝ) ≤ r := by linarith
          by_cases h5 : r ≤ (233 / 4 : ℝ)
          · exact z4_step (a := (453 / 8 : ℝ)) (b := (233 / 4 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo4 h5
          · have hlo5 : (233 / 4 : ℝ) ≤ r := by linarith
            by_cases h6 : r ≤ (239 / 4 : ℝ)
            · exact z4_step (a := (233 / 4 : ℝ)) (b := (239 / 4 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo5 h6
            · have hlo6 : (239 / 4 : ℝ) ≤ r := by linarith
              by_cases h7 : r ≤ (245 / 4 : ℝ)
              · exact z4_step (a := (239 / 4 : ℝ)) (b := (245 / 4 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo6 h7
              · have hlo7 : (245 / 4 : ℝ) ≤ r := by linarith
                by_cases h8 : r ≤ (251 / 4 : ℝ)
                · exact z4_step (a := (245 / 4 : ℝ)) (b := (251 / 4 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo7 h8
                · have hlo8 : (251 / 4 : ℝ) ≤ r := by linarith
                  by_cases h9 : r ≤ (513 / 8 : ℝ)
                  · exact z4_step (a := (251 / 4 : ℝ)) (b := (513 / 8 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo8 h9
                  · have hlo9 : (513 / 8 : ℝ) ≤ r := by linarith
                    by_cases h10 : r ≤ (131 / 2 : ℝ)
                    · exact z4_step (a := (513 / 8 : ℝ)) (b := (131 / 2 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo9 h10
                    · have hlo10 : (131 / 2 : ℝ) ≤ r := by linarith
                      by_cases h11 : r ≤ (267 / 4 : ℝ)
                      · exact z4_step (a := (131 / 2 : ℝ)) (b := (267 / 4 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo10 h11
                      · have hlo11 : (267 / 4 : ℝ) ≤ r := by linarith
                        by_cases h12 : r ≤ 68
                        · exact z4_step (a := (267 / 4 : ℝ)) (b := 68) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo11 h12
                        · have hlo12 : 68 ≤ r := by linarith
                          by_cases h13 : r ≤ (553 / 8 : ℝ)
                          · exact z4_step (a := 68) (b := (553 / 8 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo12 h13
                          · have hlo13 : (553 / 8 : ℝ) ≤ r := by linarith
                            by_cases h14 : r ≤ (281 / 4 : ℝ)
                            · exact z4_step (a := (553 / 8 : ℝ)) (b := (281 / 4 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo13 h14
                            · have hlo14 : (281 / 4 : ℝ) ≤ r := by linarith
                              by_cases h15 : r ≤ (285 / 4 : ℝ)
                              · exact z4_step (a := (281 / 4 : ℝ)) (b := (285 / 4 : ℝ)) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo14 h15
                              · have hlo15 : (285 / 4 : ℝ) ≤ r := by linarith
                                exact z4_step (a := (285 / 4 : ℝ)) (b := 72) (t := 50) (s := (39120230049 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo15 hhi

private lemma z4_piece_seventytwo {r : ℝ} (hlo : 72 ≤ r) (hhi : r ≤ 90) :
    (r - 1) ^ 16 ≤ (147 / 10 : ℝ) * r ^ 9 *
      ((42716661179 / 10000000000 : ℝ) * r - 72 + 1) ^ 5 := by
  by_cases h1 : r ≤ (293 / 4 : ℝ)
  · exact z4_step (a := 72) (b := (293 / 4 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo h1
  · have hlo1 : (293 / 4 : ℝ) ≤ r := by linarith
    by_cases h2 : r ≤ (149 / 2 : ℝ)
    · exact z4_step (a := (293 / 4 : ℝ)) (b := (149 / 2 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo1 h2
    · have hlo2 : (149 / 2 : ℝ) ≤ r := by linarith
      by_cases h3 : r ≤ (303 / 4 : ℝ)
      · exact z4_step (a := (149 / 2 : ℝ)) (b := (303 / 4 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo2 h3
      · have hlo3 : (303 / 4 : ℝ) ≤ r := by linarith
        by_cases h4 : r ≤ 77
        · exact z4_step (a := (303 / 4 : ℝ)) (b := 77) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo3 h4
        · have hlo4 : 77 ≤ r := by linarith
          by_cases h5 : r ≤ (625 / 8 : ℝ)
          · exact z4_step (a := 77) (b := (625 / 8 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo4 h5
          · have hlo5 : (625 / 8 : ℝ) ≤ r := by linarith
            by_cases h6 : r ≤ (317 / 4 : ℝ)
            · exact z4_step (a := (625 / 8 : ℝ)) (b := (317 / 4 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo5 h6
            · have hlo6 : (317 / 4 : ℝ) ≤ r := by linarith
              by_cases h7 : r ≤ (643 / 8 : ℝ)
              · exact z4_step (a := (317 / 4 : ℝ)) (b := (643 / 8 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo6 h7
              · have hlo7 : (643 / 8 : ℝ) ≤ r := by linarith
                by_cases h8 : r ≤ (651 / 8 : ℝ)
                · exact z4_step (a := (643 / 8 : ℝ)) (b := (651 / 8 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo7 h8
                · have hlo8 : (651 / 8 : ℝ) ≤ r := by linarith
                  by_cases h9 : r ≤ (659 / 8 : ℝ)
                  · exact z4_step (a := (651 / 8 : ℝ)) (b := (659 / 8 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo8 h9
                  · have hlo9 : (659 / 8 : ℝ) ≤ r := by linarith
                    by_cases h10 : r ≤ (333 / 4 : ℝ)
                    · exact z4_step (a := (659 / 8 : ℝ)) (b := (333 / 4 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo9 h10
                    · have hlo10 : (333 / 4 : ℝ) ≤ r := by linarith
                      by_cases h11 : r ≤ (673 / 8 : ℝ)
                      · exact z4_step (a := (333 / 4 : ℝ)) (b := (673 / 8 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo10 h11
                      · have hlo11 : (673 / 8 : ℝ) ≤ r := by linarith
                        by_cases h12 : r ≤ 85
                        · exact z4_step (a := (673 / 8 : ℝ)) (b := 85) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo11 h12
                        · have hlo12 : 85 ≤ r := by linarith
                          by_cases h13 : r ≤ (343 / 4 : ℝ)
                          · exact z4_step (a := 85) (b := (343 / 4 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo12 h13
                          · have hlo13 : (343 / 4 : ℝ) ≤ r := by linarith
                            by_cases h14 : r ≤ (173 / 2 : ℝ)
                            · exact z4_step (a := (343 / 4 : ℝ)) (b := (173 / 2 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo13 h14
                            · have hlo14 : (173 / 2 : ℝ) ≤ r := by linarith
                              by_cases h15 : r ≤ (349 / 4 : ℝ)
                              · exact z4_step (a := (173 / 2 : ℝ)) (b := (349 / 4 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo14 h15
                              · have hlo15 : (349 / 4 : ℝ) ≤ r := by linarith
                                by_cases h16 : r ≤ (703 / 8 : ℝ)
                                · exact z4_step (a := (349 / 4 : ℝ)) (b := (703 / 8 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo15 h16
                                · have hlo16 : (703 / 8 : ℝ) ≤ r := by linarith
                                  by_cases h17 : r ≤ (177 / 2 : ℝ)
                                  · exact z4_step (a := (703 / 8 : ℝ)) (b := (177 / 2 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo16 h17
                                  · have hlo17 : (177 / 2 : ℝ) ≤ r := by linarith
                                    by_cases h18 : r ≤ (713 / 8 : ℝ)
                                    · exact z4_step (a := (177 / 2 : ℝ)) (b := (713 / 8 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo17 h18
                                    · have hlo18 : (713 / 8 : ℝ) ≤ r := by linarith
                                      by_cases h19 : r ≤ (359 / 4 : ℝ)
                                      · exact z4_step (a := (713 / 8 : ℝ)) (b := (359 / 4 : ℝ)) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo18 h19
                                      · have hlo19 : (359 / 4 : ℝ) ≤ r := by linarith
                                        exact z4_step (a := (359 / 4 : ℝ)) (b := 90) (t := 72) (s := (42716661179 / 10000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo19 hhi

theorem price_zone4 {r : ℝ} (hlo : 12 ≤ r) (hhi : r ≤ 90) :
    (r - 1)^16 ≤ (147/10 : ℝ) * r^9 * phi r ^ 5 := by
  have hr0 : 0 ≤ r := by linarith
  by_cases h25 : r ≤ 25
  · have hpoly := z4_piece_twelve hlo h25
    have hell0 : 0 ≤ (24849066491 / 10000000000 : ℝ) * r - 12 + 1 := by
      nlinarith [mul_nonneg
        (by norm_num : (0 : ℝ) ≤ 24849066491 / 10000000000)
        (sub_nonneg.mpr hlo)]
    have hell := phi_tangent_lower (r := r) (t := 12)
      (s := (24849066491 / 10000000000 : ℝ))
      (by norm_num) hlo log_twelve_lower
    exact z4_lift hr0 hell0 hell hpoly
  · have hlo25 : 25 ≤ r := by linarith
    by_cases h32 : r ≤ 32
    · have hpoly := z4_piece_twentyfive hlo25 h32
      have hell0 : 0 ≤ (32188758246 / 10000000000 : ℝ) * r - 25 + 1 := by
        nlinarith [mul_nonneg
          (by norm_num : (0 : ℝ) ≤ 32188758246 / 10000000000)
          (sub_nonneg.mpr hlo25)]
      have hell := phi_tangent_lower (r := r) (t := 25)
        (s := (32188758246 / 10000000000 : ℝ))
        (by norm_num) hlo25 log_twentyfive_lower
      rw [show (32188758246 / 10000000000 : ℝ) =
        16094379123 / 5000000000 by norm_num] at hell0 hell
      exact z4_lift hr0 hell0 hell hpoly
    · have hlo32 : 32 ≤ r := by linarith
      by_cases h50 : r ≤ 50
      · have hpoly := z4_piece_thirtytwo hlo32 h50
        have hell0 : 0 ≤ (34657359015 / 10000000000 : ℝ) * r - 32 + 1 := by
          nlinarith [mul_nonneg
            (by norm_num : (0 : ℝ) ≤ 34657359015 / 10000000000)
            (sub_nonneg.mpr hlo32)]
        have hell := phi_tangent_lower (r := r) (t := 32)
          (s := (34657359015 / 10000000000 : ℝ))
          (by norm_num) hlo32 log_thirtytwo_lower
        rw [show (34657359015 / 10000000000 : ℝ) =
          6931471803 / 2000000000 by norm_num] at hell0 hell
        exact z4_lift hr0 hell0 hell hpoly
      · have hlo50 : 50 ≤ r := by linarith
        by_cases h72 : r ≤ 72
        · have hpoly := z4_piece_fifty hlo50 h72
          have hell0 : 0 ≤ (39120230049 / 10000000000 : ℝ) * r - 50 + 1 := by
            nlinarith [mul_nonneg
              (by norm_num : (0 : ℝ) ≤ 39120230049 / 10000000000)
              (sub_nonneg.mpr hlo50)]
          have hell := phi_tangent_lower (r := r) (t := 50)
            (s := (39120230049 / 10000000000 : ℝ))
            (by norm_num) hlo50 log_fifty_lower
          exact z4_lift hr0 hell0 hell hpoly
        · have hlo72 : 72 ≤ r := by linarith
          have hpoly := z4_piece_seventytwo hlo72 hhi
          have hell0 : 0 ≤ (42716661179 / 10000000000 : ℝ) * r - 72 + 1 := by
            nlinarith [mul_nonneg
              (by norm_num : (0 : ℝ) ≤ 42716661179 / 10000000000)
              (sub_nonneg.mpr hlo72)]
          have hell := phi_tangent_lower (r := r) (t := 72)
            (s := (42716661179 / 10000000000 : ℝ))
            (by norm_num) hlo72 log_seventytwo_lower
          exact z4_lift hr0 hell0 hell hpoly

theorem price_zone5 {r : ℝ} (hr : 90 ≤ r) :
    (r - 1)^4 ≤ (303/1000 : ℝ) * r^3 * phi r := by
  have hrpos : 0 < r := by linarith
  have hr0 : 0 ≤ r := hrpos.le
  have hlogmono : Real.log 90 ≤ Real.log r :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hrpos hr
  have hlog : (44998096696 / 10000000000 : ℝ) ≤ Real.log r :=
    log_ninety_lower.trans hlogmono
  have hphi : (34998 / 10000 : ℝ) * r ≤ phi r := by
    have hm := mul_le_mul_of_nonneg_left hlog hr0
    unfold phi
    nlinarith
  have hp4 : (r - 1) ^ 4 ≤ r ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hc : (1 : ℝ) ≤ (303 / 1000) * (34998 / 10000) := by norm_num
  have hr4 : 0 ≤ r ^ 4 := by positivity
  calc
    (r - 1) ^ 4 ≤ r ^ 4 := hp4
    _ ≤ ((303 / 1000 : ℝ) * (34998 / 10000)) * r ^ 4 := by nlinarith
    _ = (303 / 1000 : ℝ) * r ^ 3 * ((34998 / 10000) * r) := by ring
    _ ≤ (303 / 1000 : ℝ) * r ^ 3 * phi r := by
      exact mul_le_mul_of_nonneg_left hphi (by positivity)

end stoch_to_det
