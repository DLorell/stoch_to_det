import stoch_to_det.ContactEntropyScalarCertificates

noncomputable section
namespace stoch_to_det
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def entropyTaylorUpper (v : ℝ) : ℝ :=
  1+v+v^2/2+v^3/6+v^4/24+v^5/120+v^6/720+v^7/5040+v^8/20160

private def entropyTaylorLower (v : ℝ) : ℝ :=
  1+v+v^2/2+v^3/6+v^4/24+v^5/120+v^6/720

private lemma entropy_exp_le_taylor {v : ℝ} (hv : 0 ≤ v) (hv9 : v ≤ 9/2) :
    Real.exp v ≤ entropyTaylorUpper v := by
  have hc : ‖(v : ℂ)‖ / (8+1 : ℕ) ≤ (1 : ℝ)/2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
    norm_num
    linarith
  have hh := Complex.exp_bound' (x := (v : ℂ)) (n := 8) hc
  have hr : |Real.exp v - ∑ m ∈ Finset.range 8, v^m/(m.factorial : ℝ)| ≤
      |v|^8 / (Nat.factorial 8 : ℝ) * 2 := by
    convert hh using 1 <;> norm_cast
  rw [abs_of_nonneg hv] at hr
  have hup := (le_abs_self (Real.exp v - ∑ m ∈ Finset.range 8, v^m/(m.factorial : ℝ))).trans hr
  norm_num [Finset.sum_range_succ, Nat.factorial] at hup
  unfold entropyTaylorUpper
  linarith

private lemma entropy_taylor_le_exp {v : ℝ} (hv : 0 ≤ v) :
    entropyTaylorLower v ≤ Real.exp v := by
  have h := Real.sum_le_exp_of_nonneg hv 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  simpa [entropyTaylorLower, div_eq_mul_inv] using h

private lemma entropy_exp_positive_refined {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (t^3-(589:ℝ)/2000*t^4) ≤ 1+t^3+(71:ℝ)/250*t^6 := by
  let v : ℝ := t^3-(589:ℝ)/2000*t^4
  by_cases hv : v ≤ 0
  · have h := Real.exp_le_one_iff.mpr hv
    have ht3 : 0 ≤ t^3 := pow_nonneg ht _
    have ht6 : 0 ≤ t^6 := pow_nonneg ht _
    dsimp [v] at h
    linarith
  have hv0 : 0 ≤ v := (lt_of_not_ge hv).le
  have hmax : v ≤ 9/2 := by
    have hprod : 0 ≤ (589:ℝ)/2000 * (t-(1500:ℝ)/589)^2 *
        (t^2+(1000:ℝ)/589*t+(750000:ℝ)/346921) := by positivity
    have hid : (589:ℝ)/2000 * (t-(1500:ℝ)/589)^2 *
        (t^2+(1000:ℝ)/589*t+(750000:ℝ)/346921) =
        (843750000:ℝ)/204336469-v := by dsimp [v]; ring
    linarith
  have ht7 : t ≤ 7/2 := by
    by_contra h
    have htgt : 7/2 < t := lt_of_not_ge h
    have ht3 : 0 < t^3 := pow_pos (by linarith) _
    have hfac : t^3 * (1-(589:ℝ)/2000*t) < 0 :=
      mul_neg_of_pos_of_neg ht3 (by linarith)
    dsimp [v] at hv
    nlinarith only [hfac, hv]
  have hpoly := mul_nonneg (pow_nonneg ht 4) (entropyRefinedPositivePoly_nonneg ht ht7)
  have hid : t^4*entropyRefinedPositivePoly t =
      1+t^3+(71:ℝ)/250*t^6-entropyTaylorUpper v := by
    dsimp [entropyRefinedPositivePoly, entropyTaylorUpper, v]
    ring
  have hexp := entropy_exp_le_taylor hv0 hmax
  dsimp [v] at hexp
  rw [hid] at hpoly
  dsimp [v] at hpoly
  linarith

private lemma entropy_exp_negative_refined {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t^3-(589:ℝ)/2000*t^4) ≤ 1-t^3+(71:ℝ)/250*t^6 := by
  let w : ℝ := t^3+(589:ℝ)/2000*t^4
  let P : ℝ := 1-t^3+(71:ℝ)/250*t^6
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hP : 0 < P := by
    have hs := sq_nonneg (t^3-(125:ℝ)/71)
    dsimp [P]
    nlinarith [sq_nonneg (t^3)]
  have hR : 0 ≤ entropyRefinedNegativePoly t := by
    by_cases h : t ≤ 2
    · exact entropyRefinedNegativePoly_nonneg ht h
    · exact entropyRefinedNegativePoly_tail (lt_of_not_ge h).le
  have hpoly := mul_nonneg (pow_nonneg ht 4) hR
  have hid : t^4*entropyRefinedNegativePoly t = P*entropyTaylorLower w-1 := by
    dsimp [entropyRefinedNegativePoly, entropyTaylorLower, P, w]
    ring
  rw [hid] at hpoly
  have hmul := mul_le_mul_of_nonneg_left (entropy_taylor_le_exp hw) hP.le
  have h1 : 1 ≤ P*Real.exp w := by linarith
  have hdiv : 1/Real.exp w ≤ P := (div_le_iff₀ (Real.exp_pos w)).2 h1
  have heq : -t^3-(589:ℝ)/2000*t^4 = -w := by dsimp [w]; ring
  rw [heq, Real.exp_neg]
  simpa [P, one_div] using hdiv

/-- A sharper global exponential majorant, certified using rational Taylor polynomials. -/
theorem exp_sub_abs_rpow_le_quadratic_refined (u : ℝ) :
    Real.exp (u-(589:ℝ)/2000*|u|^((4:ℝ)/3)) ≤
      1+u+(71:ℝ)/250*u^2 := by
  let t := |u|^((1:ℝ)/3)
  have ht : 0 ≤ t := Real.rpow_nonneg (abs_nonneg u) _
  have ht3 : t^3=|u| := by
    dsimp [t]
    convert Real.rpow_inv_natCast_pow (abs_nonneg u) (show (3:ℕ)≠0 by decide) using 1
    norm_num
  have ht4 : t^4=|u|^((4:ℝ)/3) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg u)]
    norm_num
  have ht6 : t^6=u^2 := calc
    t^6=(t^3)^2 := by ring
    _=u^2 := by rw [ht3, sq_abs]
  by_cases hu : 0 ≤ u
  · have h := entropy_exp_positive_refined ht
    rw [ht3, ht4, ht6, abs_of_nonneg hu] at h
    simpa [abs_of_nonneg hu] using h
  · have h := entropy_exp_negative_refined ht
    rw [ht3, ht4, ht6, abs_of_neg (lt_of_not_ge hu)] at h
    simpa [abs_of_neg (lt_of_not_ge hu)] using h

end stoch_to_det
