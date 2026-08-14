import stoch_to_det.PhiBounds

/-!
# Further elementary bounds for `r * log r - r + 1`
-/

namespace stoch_to_det

/-- A local affine lower bound for `log`, obtained from the symmetric Padé bound. -/
private lemma log_lower_on_segment {a b r L : ℝ}
    (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) (hL : L ≤ Real.log a) :
    L + 2 * (r - a) / (a + b) ≤ Real.log r := by
  have hr : 0 < r := lt_of_lt_of_le ha har
  have habpos : 0 < a + b := by linarith
  have hrapos : 0 < r + a := by linarith
  have hratio : 1 ≤ r / a := (one_le_div ha).2 har
  have hpade := two_mul_sub_one_le_add_one_mul_log hratio
  have hden : 0 < r / a + 1 := by positivity
  have hpade' : 2 * (r / a - 1) / (r / a + 1) ≤ Real.log (r / a) := by
    apply (div_le_iff₀ hden).2
    simpa only [mul_comm] using hpade
  rw [Real.log_div hr.ne' ha.ne'] at hpade'
  have hfrac : 2 * (r - a) / (a + b) ≤ 2 * (r - a) / (r + a) := by
    apply (div_le_div_iff₀ habpos hrapos).2
    nlinarith
  have hid : 2 * (r / a - 1) / (r / a + 1) = 2 * (r - a) / (r + a) := by
    field_simp [ha.ne']
  rw [hid] at hpade'
  linarith

private lemma quartic_of_log_lower {r ell : ℝ} (hr : 0 ≤ r)
    (hlog : ell ≤ Real.log r)
    (hpoly : (r - 1) ^ 4 ≤ (2531 / 5000 : ℝ) * r ^ 3 * (r * ell - r + 1)) :
    (r - 1) ^ 4 ≤ (2531 / 5000 : ℝ) * (r ^ 3 * phi r) := by
  have hphi : r * ell - r + 1 ≤ phi r := by
    have hm := mul_le_mul_of_nonneg_left hlog hr
    unfold phi
    linarith
  calc
    (r - 1) ^ 4 ≤ (2531 / 5000 : ℝ) * r ^ 3 * (r * ell - r + 1) := hpoly
    _ ≤ (2531 / 5000 : ℝ) * (r ^ 3 * phi r) := by
      have hc : 0 ≤ (2531 / 5000 : ℝ) * r ^ 3 := by positivity
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hphi hc

private lemma log_two_lower : (6931 / 10000 : ℝ) ≤ Real.log 2 := by
  linarith [Real.log_two_gt_d9]

private lemma log_three_lower : (5493 / 5000 : ℝ) ≤ Real.log 3 := by
  linarith [Real.log_three_gt_d9]

private lemma log_four_lower : (6931 / 5000 : ℝ) ≤ Real.log 4 := by
  rw [Real.log_four_eq]
  linarith [Real.log_two_gt_d9]

private lemma log_nine_halves_lower : (188 / 125 : ℝ) ≤ Real.log (9 / 2) := by
  have hid : Real.log (9 / 2 : ℝ) = 2 * Real.log 3 - Real.log 2 := by
    rw [show (9 / 2 : ℝ) = 3 * 3 / 2 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hid]
  linarith [Real.log_three_gt_d9, Real.log_two_lt_d9]

private lemma log_twentyfour_fifths_lower :
    (7843 / 5000 : ℝ) ≤ Real.log (24 / 5) := by
  have hid : Real.log (24 / 5 : ℝ) = Real.log 3 + 3 * Real.log 2 - Real.log 5 := by
    rw [show (24 / 5 : ℝ) = (3 * (2 * (2 * 2))) / 5 by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hid]
  linarith [Real.log_three_gt_d9, Real.log_two_gt_d9, Real.log_five_lt_d9]

private lemma log_five_lower : (8047 / 5000 : ℝ) ≤ Real.log 5 := by
  linarith [Real.log_five_gt_d9]

private lemma log_fiftyone_tenths_lower :
    (4073 / 2500 : ℝ) ≤ Real.log (51 / 10) := by
  have h := Real.sum_range_le_log_div (x := (41 / 61 : ℝ))
    (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private lemma log_twentysix_fifths_lower :
    (8243 / 5000 : ℝ) ≤ Real.log (26 / 5) := by
  have h := Real.sum_range_le_log_div (x := (21 / 31 : ℝ))
    (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private lemma log_twentyseven_fifths_lower :
    (16863 / 10000 : ℝ) ≤ Real.log (27 / 5) := by
  have hid : Real.log (27 / 5 : ℝ) = 3 * Real.log 3 - Real.log 5 := by
    rw [show (27 / 5 : ℝ) = (3 * (3 * 3)) / 5 by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hid]
  linarith [Real.log_three_gt_d9, Real.log_five_lt_d9]

private lemma log_six_lower : (17917 / 10000 : ℝ) ≤ Real.log 6 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

private lemma log_eight_lower : (10397 / 5000 : ℝ) ≤ Real.log 8 := by
  rw [show (8 : ℝ) = 2 * (2 * 2) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9]

private lemma log_twelve_lower : (24849 / 10000 : ℝ) ≤ Real.log 12 := by
  rw [show (12 : ℝ) = 3 * (2 * 2) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

private lemma log_twenty_lower : (29957 / 10000 : ℝ) ≤ Real.log 20 := by
  rw [show (20 : ℝ) = 5 * (2 * 2) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

/-- On `[0,2]`, `phi` dominates `(r-1)^2` with certified factor `2.59`. -/
theorem bulk_quad_two (r : ℝ) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    (r - 1) ^ 2 ≤ (259 / 100 : ℝ) * (r * Real.log r - r + 1) := by
  change (r - 1) ^ 2 ≤ (259 / 100 : ℝ) * phi r
  by_cases hr1 : r ≤ 1
  · have hhalf := phi_half_sq_lower_of_le_one hr0 hr1
    have hphi := phi_nonneg hr0
    nlinarith
  · have hr1lt : 1 < r := lt_of_not_ge hr1
    have hratio := phi_div_sq_antitone_Icc hr1lt hr2
    have hlog2 := Real.log_two_gt_d9
    have hphi2 : (100 / 259 : ℝ) ≤ phi 2 := by
      unfold phi
      norm_num at hlog2 ⊢
      linarith
    have hsqpos : 0 < (r - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr1lt)
    norm_num [phi] at hratio
    have hcross : phi 2 * (r - 1) ^ 2 ≤ phi r := by
      exact (le_div_iff₀ hsqpos).1 hratio
    have hscaled := mul_le_mul_of_nonneg_right hphi2 (sq_nonneg (r - 1))
    nlinarith

/-- On the full tail, the normalized quartic cell is at most `0.5062`. -/
theorem tail_quartic_cell (r : ℝ) (hr2 : 2 ≤ r) :
    (r - 1) ^ 4 ≤ (5062 / 10000 : ℝ) *
      (r ^ 3 * (r * Real.log r - r + 1)) := by
  change (r - 1) ^ 4 ≤ (5062 / 10000 : ℝ) * (r ^ 3 * phi r)
  rw [show (5062 / 10000 : ℝ) = 2531 / 5000 by norm_num]
  have hr0 : 0 ≤ r := by linarith
  by_cases hr20 : 20 ≤ r
  · have hrpos : 0 < r := by linarith
    have hlogmono : Real.log 20 ≤ Real.log r := by
      exact Real.strictMonoOn_log.monotoneOn
        (show (20 : ℝ) ∈ Set.Ioi 0 by norm_num)
        (show r ∈ Set.Ioi 0 from lt_of_lt_of_le (by norm_num) hr20) hr20
    have hlog : (29957 / 10000 : ℝ) ≤ Real.log r := log_twenty_lower.trans hlogmono
    have hbase : 0 ≤ r - 1 := by linarith
    have hp4 : (r - 1) ^ 4 ≤ r ^ 4 :=
      pow_le_pow_left₀ hbase (by linarith) 4
    have hphi : r * (19957 / 10000 : ℝ) ≤ phi r := by
      have hm := mul_le_mul_of_nonneg_left hlog hr0
      unfold phi
      nlinarith
    have hc : (1 : ℝ) ≤ (2531 / 5000) * (19957 / 10000) := by norm_num
    have hr4 : r ^ 4 ≤ (2531 / 5000 : ℝ) *
        (r ^ 3 * (r * (19957 / 10000 : ℝ))) := by
      have hr4nonneg : 0 ≤ r ^ 4 := by positivity
      calc
        r ^ 4 ≤ ((2531 / 5000 : ℝ) * (19957 / 10000)) * r ^ 4 := by nlinarith
        _ = (2531 / 5000 : ℝ) * (r ^ 3 * (r * (19957 / 10000 : ℝ))) := by ring
    calc
      (r - 1) ^ 4 ≤ r ^ 4 := hp4
      _ ≤ (2531 / 5000 : ℝ) * (r ^ 3 * (r * (19957 / 10000 : ℝ))) := hr4
      _ ≤ (2531 / 5000 : ℝ) * (r ^ 3 * phi r) := by gcongr
  · have hr20' : r ≤ 20 := (lt_of_not_ge hr20).le
    by_cases hr3 : r ≤ 3
    · have hlog := log_lower_on_segment (a := 2) (b := 3) (r := r)
        (L := (6931 / 10000 : ℝ)) (by norm_num) hr2 hr3 log_two_lower
      apply quartic_of_log_lower hr0 hlog
      have ht : 0 ≤ r - 2 := by linarith
      have hu : 0 ≤ 3 - r := by linarith
      have hnonneg : 0 ≤
          (1762361 / 3125000 : ℝ) * (3 - r) ^ 5 +
          (9883027 / 3125000 : ℝ) * (r - 2) * (3 - r) ^ 4 +
          (42492579 / 6250000 : ℝ) * (r - 2) ^ 2 * (3 - r) ^ 3 +
          (5612093 / 781250 : ℝ) * (r - 2) ^ 3 * (3 - r) ^ 2 +
          (213275217 / 50000000 : ℝ) * (r - 2) ^ 4 * (3 - r) +
          (74235241 / 50000000 : ℝ) * (r - 2) ^ 5 := by positivity
      rw [← sub_nonneg]
      (convert hnonneg using 1; ring)
    · have hr3' : 3 ≤ r := (lt_of_not_ge hr3).le
      by_cases hr4 : r ≤ 4
      · have hlog := log_lower_on_segment (a := 3) (b := 4) (r := r)
          (L := (5493 / 5000 : ℝ)) (by norm_num) hr3' hr4 log_three_lower
        apply quartic_of_log_lower hr0 hlog
        have ht : 0 ≤ r - 3 := by linarith
        have hu : 0 ≤ 4 - r := by linarith
        have hnonneg : 0 ≤
            (42755423 / 25000000 : ℝ) * (4 - r) ^ 5 +
            (1281668753 / 175000000 : ℝ) * (r - 3) * (4 - r) ^ 4 +
            (242025297 / 21875000 : ℝ) * (r - 3) ^ 2 * (4 - r) ^ 3 +
            (19868953 / 2734375 : ℝ) * (r - 3) ^ 3 * (4 - r) ^ 2 +
            (7848571 / 2734375 : ℝ) * (r - 3) ^ 4 * (4 - r) +
            (3278549 / 2734375 : ℝ) * (r - 3) ^ 5 := by positivity
        rw [← sub_nonneg]
        (convert hnonneg using 1; ring)
      · have hr4' : 4 ≤ r := (lt_of_not_ge hr4).le
        by_cases hr45 : r ≤ 9 / 2
        · have hlog := log_lower_on_segment (a := 4) (b := 9 / 2) (r := r)
            (L := (6931 / 5000 : ℝ)) (by norm_num) hr4' hr45 log_four_lower
          apply quartic_of_log_lower hr0 hlog
          have ht : 0 ≤ r - 4 := by linarith
          have hu : 0 ≤ 9 / 2 - r := by linarith
          have hnonneg : 0 ≤
              (18042208 / 390625 : ℝ) * (9 / 2 - r) ^ 5 +
              (1197336448 / 6640625 : ℝ) * (r - 4) * (9 / 2 - r) ^ 4 +
              (1792984576 / 6640625 : ℝ) * (r - 4) ^ 2 * (9 / 2 - r) ^ 3 +
              (2687222949 / 13281250 : ℝ) * (r - 4) ^ 3 * (9 / 2 - r) ^ 2 +
              (18516879793 / 212500000 : ℝ) * (r - 4) ^ 4 * (9 / 2 - r) +
              (4422323857 / 212500000 : ℝ) * (r - 4) ^ 5 := by positivity
          rw [← sub_nonneg]
          (convert hnonneg using 1; ring)
        · have hr45' : 9 / 2 ≤ r := (lt_of_not_ge hr45).le
          by_cases hr48 : r ≤ 24 / 5
          · have hlog := log_lower_on_segment (a := 9 / 2) (b := 24 / 5) (r := r)
              (L := (188 / 125 : ℝ)) (by norm_num) hr45' hr48 log_nine_halves_lower
            apply quartic_of_log_lower hr0 hlog
            have ht : 0 ≤ r - 9 / 2 := by linarith
            have hu : 0 ≤ 24 / 5 - r := by linarith
            have hnonneg : 0 ≤
                (6820883 / 24300 : ℝ) * (24 / 5 - r) ^ 5 +
                (3837305489 / 3766500 : ℝ) * (r - 9 / 2) * (24 / 5 - r) ^ 4 +
                (13340938681 / 9416250 : ℝ) * (r - 9 / 2) ^ 2 * (24 / 5 - r) ^ 3 +
                (23366636344 / 23540625 : ℝ) * (r - 9 / 2) ^ 3 * (24 / 5 - r) ^ 2 +
                (48327632992 / 117703125 : ℝ) * (r - 9 / 2) ^ 4 * (24 / 5 - r) +
                (11391853472 / 117703125 : ℝ) * (r - 9 / 2) ^ 5 := by positivity
            rw [← sub_nonneg]
            (convert hnonneg using 1; ring)
          · have hr48' : 24 / 5 ≤ r := (lt_of_not_ge hr48).le
            by_cases hr5 : r ≤ 5
            · have hlog := log_lower_on_segment (a := 24 / 5) (b := 5) (r := r)
                (L := (7843 / 5000 : ℝ)) (by norm_num) hr48' hr5
                log_twentyfour_fifths_lower
              apply quartic_of_log_lower hr0 hlog
              have ht : 0 ≤ r - 24 / 5 := by linarith
              have hu : 0 ≤ 5 - r := by linarith
              have hnonneg : 0 ≤
                  (62920847 / 78125 : ℝ) * (5 - r) ^ 5 +
                  (9827603703 / 3828125 : ℝ) * (r - 24 / 5) * (5 - r) ^ 4 +
                  (456645013 / 153125 : ℝ) * (r - 24 / 5) ^ 2 * (5 - r) ^ 3 +
                  (84522819 / 49000 : ℝ) * (r - 24 / 5) ^ 3 * (5 - r) ^ 2 +
                  (11786057 / 15680 : ℝ) * (r - 24 / 5) ^ 4 * (5 - r) +
                  (775085 / 3136 : ℝ) * (r - 24 / 5) ^ 5 := by positivity
              rw [← sub_nonneg]
              (convert hnonneg using 1; ring)
            · have hr5' : 5 ≤ r := (lt_of_not_ge hr5).le
              by_cases hr51 : r ≤ 51 / 10
              · have hlog := log_lower_on_segment (a := 5) (b := 51 / 10) (r := r)
                  (L := (8047 / 5000 : ℝ)) (by norm_num) hr5' hr51 log_five_lower
                apply quartic_of_log_lower hr0 hlog
                have ht : 0 ≤ r - 5 := by linarith
                have hu : 0 ≤ 51 / 10 - r := by linarith
                have hnonneg : 0 ≤
                    (14785 / 2 : ℝ) * (51 / 10 - r) ^ 5 +
                    (25743939 / 1010 : ℝ) * (r - 5) * (51 / 10 - r) ^ 4 +
                    (1818744771 / 50500 : ℝ) * (r - 5) ^ 2 * (51 / 10 - r) ^ 3 +
                    (9344423308 / 315625 : ℝ) * (r - 5) ^ 3 * (51 / 10 - r) ^ 2 +
                    (4084129385457 / 252500000 : ℝ) * (r - 5) ^ 4 * (51 / 10 - r) +
                    (1132961404057 / 252500000 : ℝ) * (r - 5) ^ 5 := by positivity
                rw [← sub_nonneg]
                (convert hnonneg using 1; ring)
              · have hr51' : 51 / 10 ≤ r := (lt_of_not_ge hr51).le
                by_cases hr52 : r ≤ 26 / 5
                · have hlog := log_lower_on_segment (a := 51 / 10) (b := 26 / 5) (r := r)
                    (L := (4073 / 2500 : ℝ)) (by norm_num) hr51' hr52
                    log_fiftyone_tenths_lower
                  apply quartic_of_log_lower hr0 hlog
                  have ht : 0 ≤ r - 51 / 10 := by linarith
                  have hu : 0 ≤ 26 / 5 - r := by linarith
                  have hnonneg : 0 ≤
                      (5523953863 / 1250000 : ℝ) * (26 / 5 - r) ^ 5 +
                      (1954821373201 / 128750000 : ℝ) * (r - 51 / 10) * (26 / 5 - r) ^ 4 +
                      (406923270981 / 16093750 : ℝ) * (r - 51 / 10) ^ 2 * (26 / 5 - r) ^ 3 +
                      (237713643524 / 8046875 : ℝ) * (r - 51 / 10) ^ 3 * (26 / 5 - r) ^ 2 +
                      (176051970792 / 8046875 : ℝ) * (r - 51 / 10) ^ 4 * (26 / 5 - r) +
                      (55184870864 / 8046875 : ℝ) * (r - 51 / 10) ^ 5 := by positivity
                  rw [← sub_nonneg]
                  (convert hnonneg using 1; ring)
                · have hr52' : 26 / 5 ≤ r := (lt_of_not_ge hr52).le
                  by_cases hr54 : r ≤ 27 / 5
                  · have hlog := log_lower_on_segment (a := 26 / 5) (b := 27 / 5) (r := r)
                      (L := (8243 / 5000 : ℝ)) (by norm_num) hr52' hr54
                      log_twentysix_fifths_lower
                    apply quartic_of_log_lower hr0 hlog
                    have ht : 0 ≤ r - 26 / 5 := by linarith
                    have hu : 0 ≤ 27 / 5 - r := by linarith
                    have hnonneg : 0 ≤
                        (60655513 / 312500 : ℝ) * (27 / 5 - r) ^ 5 +
                        (7815143301 / 16562500 : ℝ) * (r - 26 / 5) * (27 / 5 - r) ^ 4 +
                        (35662243621 / 33125000 : ℝ) * (r - 26 / 5) ^ 2 * (27 / 5 - r) ^ 3 +
                        (82494056643 / 33125000 : ℝ) * (r - 26 / 5) ^ 3 * (27 / 5 - r) ^ 2 +
                        (708743121277 / 265000000 : ℝ) * (r - 26 / 5) ^ 4 * (27 / 5 - r) +
                        (260507509309 / 265000000 : ℝ) * (r - 26 / 5) ^ 5 := by positivity
                    rw [← sub_nonneg]
                    (convert hnonneg using 1; ring)
                  · have hr54' : 27 / 5 ≤ r := (lt_of_not_ge hr54).le
                    by_cases hr6 : r ≤ 6
                    · have hlog := log_lower_on_segment (a := 27 / 5) (b := 6) (r := r)
                        (L := (16863 / 10000 : ℝ)) (by norm_num) hr54' hr6
                        log_twentyseven_fifths_lower
                      apply quartic_of_log_lower hr0 hlog
                      have ht : 0 ≤ r - 27 / 5 := by linarith
                      have hu : 0 ≤ 6 - r := by linarith
                      have hnonneg : 0 ≤
                          (9348274573 / 2430000000 : ℝ) * (6 - r) ^ 5 +
                          (130927228607 / 46170000000 : ℝ) * (r - 27 / 5) * (6 - r) ^ 4 +
                          (7744656599 / 577125000 : ℝ) * (r - 27 / 5) ^ 2 * (6 - r) ^ 3 +
                          (18060674741 / 230850000 : ℝ) * (r - 27 / 5) ^ 3 * (6 - r) ^ 2 +
                          (2549282941 / 23085000 : ℝ) * (r - 27 / 5) ^ 4 * (6 - r) +
                          (215679367 / 4617000 : ℝ) * (r - 27 / 5) ^ 5 := by positivity
                      rw [← sub_nonneg]
                      (convert hnonneg using 1; ring)
                    · have hr6' : 6 ≤ r := (lt_of_not_ge hr6).le
                      by_cases hr8 : r ≤ 8
                      · have hlog := log_lower_on_segment (a := 6) (b := 8) (r := r)
                          (L := (17917 / 10000 : ℝ)) (by norm_num) hr6' hr8 log_six_lower
                        apply quartic_of_log_lower hr0 hlog
                        have ht : 0 ≤ r - 6 := by linarith
                        have hu : 0 ≤ 8 - r := by linarith
                        have hnonneg : 0 ≤
                            (11632087 / 100000000 : ℝ) * (8 - r) ^ 5 +
                            (172810857 / 700000000 : ℝ) * (r - 6) * (8 - r) ^ 4 +
                            (73819843 / 87500000 : ℝ) * (r - 6) ^ 2 * (8 - r) ^ 3 +
                            (159644253 / 43750000 : ℝ) * (r - 6) ^ 3 * (8 - r) ^ 2 +
                            (502345717 / 87500000 : ℝ) * (r - 6) ^ 4 * (8 - r) +
                            (251781273 / 87500000 : ℝ) * (r - 6) ^ 5 := by positivity
                        rw [← sub_nonneg]
                        (convert hnonneg using 1; ring)
                      · have hr8' : 8 ≤ r := (lt_of_not_ge hr8).le
                        by_cases hr12 : r ≤ 12
                        · have hlog := log_lower_on_segment (a := 8) (b := 12) (r := r)
                            (L := (10397 / 5000 : ℝ)) (by norm_num) hr8' hr12 log_eight_lower
                          apply quartic_of_log_lower hr0 hlog
                          have ht : 0 ≤ r - 8 := by linarith
                          have hu : 0 ≤ 12 - r := by linarith
                          have hnonneg : 0 ≤
                              (37577023 / 400000000 : ℝ) * (12 - r) ^ 5 +
                              (268418411 / 400000000 : ℝ) * (r - 8) * (12 - r) ^ 4 +
                              (447805443 / 200000000 : ℝ) * (r - 8) ^ 2 * (12 - r) ^ 3 +
                              (843906623 / 200000000 : ℝ) * (r - 8) ^ 3 * (12 - r) ^ 2 +
                              (1691205591 / 400000000 : ℝ) * (r - 8) ^ 4 * (12 - r) +
                              (688409843 / 400000000 : ℝ) * (r - 8) ^ 5 := by positivity
                          rw [← sub_nonneg]
                          (convert hnonneg using 1; ring)
                        · have hr12' : 12 ≤ r := (lt_of_not_ge hr12).le
                          have hlog := log_lower_on_segment (a := 12) (b := 20) (r := r)
                            (L := (24849 / 10000 : ℝ)) (by norm_num) hr12' hr20'
                            log_twelve_lower
                          apply quartic_of_log_lower hr0 hlog
                          have ht : 0 ≤ r - 12 := by linarith
                          have hu : 0 ≤ 20 - r := by linarith
                          have hnonneg : 0 ≤
                              (710961053 / 12800000000 : ℝ) * (20 - r) ^ 5 +
                              (5886563073 / 12800000000 : ℝ) * (r - 12) * (20 - r) ^ 4 +
                              (2044495957 / 1280000000 : ℝ) * (r - 12) ^ 2 * (20 - r) ^ 3 +
                              (742184241 / 256000000 : ℝ) * (r - 12) ^ 3 * (20 - r) ^ 2 +
                              (279259221 / 102400000 : ℝ) * (r - 12) ^ 4 * (20 - r) +
                              (21556013 / 20480000 : ℝ) * (r - 12) ^ 5 := by positivity
                          rw [← sub_nonneg]
                          (convert hnonneg using 1; ring)

end stoch_to_det
