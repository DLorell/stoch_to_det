import stoch_to_det.Mismatch
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Continuous pair charges avoid the loss from a fixed near/far threshold. -/

namespace stoch_to_det

open Finset

theorem log_le_quadratic_at_one {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ x - 1 - (x - 1)^2 / 2 := by
  let F : ℝ → ℝ := fun x => Real.log x - (x - 1) + (x - 1)^2 / 2
  have hderiv (x : ℝ) (hx : 0 < x) :
      HasDerivAt F ((x - 1)^2 / x) x := by
    have hsub : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
      simpa using (hasDerivAt_id x).sub_const 1
    convert ((Real.hasDerivAt_log hx.ne').sub hsub).add
      ((hsub.pow 2).div_const 2) using 1 <;> try rfl
    field_simp
    ring
  have hm : MonotoneOn F (Set.Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
    · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx0 : 0 < x := by simpa using hx
      exact (hderiv x hx0).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : 0 < x := by simpa using hx
      rw [(hderiv x hx0).deriv]
      exact div_nonneg (sq_nonneg _) hx0.le
  have h := hm hx (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) hx1
  dsimp [F] at h
  norm_num at h
  linarith

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)

/-- The exact Bhattacharyya pair cost, expressed using squared Hellinger distance. -/
theorem pair_log_hellinger_le_KL (c d : K.κ) :
    -2 * Real.log (1 - hellingerSq (K.Q c) (K.Q d) / 2) ≤
      Real.log 2 * (KL (overlapLaw K c d) (K.Q c) +
        KL (overlapLaw K c d) (K.Q d)) := by
  have hQc := (K.Q_isContact c).1
  have hQd := (K.Q_isContact d).1
  have hdist := hellingerSq_eq_two_mul_one_sub_BC hQc hQd
  have harg : 1 - hellingerSq (K.Q c) (K.Q d) / 2 = BC (K.Q c) (K.Q d) := by
    rw [hdist]
    ring
  rw [harg]
  have hbh := bhattacharyya_le hQc hQd (overlapLaw_isPMF K c d)
    (overlapLaw_absCont_Q K c d) (overlapLaw_absCont_Q_right K c d)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmul := mul_le_mul_of_nonneg_left hbh hlog2.le
  rw [lg_eq_log_div] at hmul
  have heq : Real.log 2 * (-2 * (Real.log (BC (K.Q c) (K.Q d)) / Real.log 2)) =
      -2 * Real.log (BC (K.Q c) (K.Q d)) := by field_simp
  rwa [heq] at hmul

/-- A quadratic lower bound for the Bhattacharyya pair cost. KL uses bits;
the factor `log 2` converts the sum to natural-log units. -/
theorem pair_hellinger_quadratic_le_KL (c d : K.κ) :
    hellingerSq (K.Q c) (K.Q d) + (hellingerSq (K.Q c) (K.Q d))^2 / 4 ≤
      Real.log 2 * (KL (overlapLaw K c d) (K.Q c) +
        KL (overlapLaw K c d) (K.Q d)) := by
  have hQc := (K.Q_isContact c).1
  have hQd := (K.Q_isContact d).1
  have hB := BC_Q_pos K c d
  have hd0 := hellingerSq_nonneg (K.Q c) (K.Q d)
  have hdist := hellingerSq_eq_two_mul_one_sub_BC hQc hQd
  have hB1 : BC (K.Q c) (K.Q d) ≤ 1 := by rw [hdist] at hd0; linarith
  have hlog := log_le_quadratic_at_one hB hB1
  have hbh := bhattacharyya_le hQc hQd (overlapLaw_isPMF K c d)
    (overlapLaw_absCont_Q K c d) (overlapLaw_absCont_Q_right K c d)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmul := mul_le_mul_of_nonneg_left hbh hlog2.le
  rw [lg_eq_log_div] at hmul
  have heq : Real.log 2 * (-2 * (Real.log (BC (K.Q c) (K.Q d)) / Real.log 2)) =
      -2 * Real.log (BC (K.Q c) (K.Q d)) := by field_simp
  rw [heq] at hmul
  rw [hdist]
  nlinarith

/-- Summing a nonnegative pair charge gives a linear mismatch estimate. -/
theorem mismatch_le_of_pair_charge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpair : ∀ c d : K.κ, c ≠ d →
      1 ≤ a * Ixy (K.Q c) + b *
        (KL (overlapLaw K c d) (K.Q c) + KL (overlapLaw K c d) (K.Q d))) :
    K.dMis ≤ a * D.M + 2 * b * K.Sinfo := by
  have hI (c : K.κ) : 0 ≤ Ixy (K.Q c) := Ixy_nonneg_local (K.Q_isContact c).1
  have hKLc (c d : K.κ) : 0 ≤ KL (overlapLaw K c d) (K.Q c) :=
    KL_nonneg_local (overlapLaw_isPMF K c d) (K.Q_isContact c).1
      (overlapLaw_absCont_Q K c d)
  have hKLd (c d : K.κ) : 0 ≤ KL (overlapLaw K c d) (K.Q d) :=
    KL_nonneg_local (overlapLaw_isPMF K c d) (K.Q_isContact d).1
      (overlapLaw_absCont_Q_right K c d)
  have hright : (∑ c, ∑ d, pairMass K c d *
      KL (overlapLaw K c d) (K.Q d)) = K.Sinfo := by
    rw [Sinfo_eq_sum_KL K, sum_comm]
    apply sum_congr rfl
    intro c _
    apply sum_congr rfl
    intro d _
    rw [pairMass_comm K d c, overlapLaw_comm K d c]
  have hinfo : (∑ c, ∑ d, pairMass K c d * Ixy (K.Q c)) = D.M := by
    rw [M_eq_sum_s_Ixy K]
    apply sum_congr rfl
    intro c _
    rw [← sum_mul, sum_pairMass_right K c]
  calc
    K.dMis = ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d), pairMass K c d :=
      dMis_eq_sum_pairMass K
    _ ≤ ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d), pairMass K c d *
        (a * Ixy (K.Q c) + b *
          (KL (overlapLaw K c d) (K.Q c) + KL (overlapLaw K c d) (K.Q d))) := by
      apply sum_le_sum
      intro c _
      apply sum_le_sum
      intro d hd
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (hpair c d (mem_filter.mp hd).2) (pairMass_nonneg K c d)
    _ ≤ ∑ c, ∑ d, pairMass K c d *
        (a * Ixy (K.Q c) + b *
          (KL (overlapLaw K c d) (K.Q c) + KL (overlapLaw K c d) (K.Q d))) := by
      apply sum_le_sum
      intro c _
      apply sum_le_univ_sum_of_nonneg
      intro d
      exact mul_nonneg (pairMass_nonneg K c d)
        (add_nonneg (mul_nonneg ha (hI c)) (mul_nonneg hb (add_nonneg (hKLc c d) (hKLd c d))))
    _ = a * (∑ c, ∑ d, pairMass K c d * Ixy (K.Q c)) +
        b * (∑ c, ∑ d, pairMass K c d * KL (overlapLaw K c d) (K.Q c)) +
        b * (∑ c, ∑ d, pairMass K c d * KL (overlapLaw K c d) (K.Q d)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro c _
      apply sum_congr rfl
      intro d _
      ring
    _ = a * D.M + 2 * b * K.Sinfo := by
      rw [hinfo, ← Sinfo_eq_sum_KL K, hright]
      ring

/-- The continuous charge calibrated for the constant below twenty. -/
theorem mismatch_continuous_charge
    (hpair : ∀ c d : K.κ, c ≠ d →
      1 ≤ 16 * Real.log 2 * Ixy (K.Q c) + (79 : ℝ)/100 * Real.log 2 *
        (KL (overlapLaw K c d) (K.Q c) + KL (overlapLaw K c d) (K.Q d))) :
    K.dMis ≤ 16 * Real.log 2 * D.M + (79 : ℝ)/50 * Real.log 2 * K.Sinfo := by
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
  have h := mismatch_le_of_pair_charge K (a := 16 * Real.log 2)
    (b := (79 : ℝ)/100 * Real.log 2) (by positivity) (by positivity) hpair
  convert h using 1; ring

/-- A charge stated only in terms of contact information and Hellinger distance
is sufficient for the mismatch estimate. -/
theorem mismatch_continuous_charge_of_hellinger
    (hpair : ∀ c d : K.κ, c ≠ d →
      1 ≤ 16 * Real.log 2 * Ixy (K.Q c) + (79 : ℝ)/100 *
        (hellingerSq (K.Q c) (K.Q d) + (hellingerSq (K.Q c) (K.Q d))^2/4)) :
    K.dMis ≤ 16 * Real.log 2 * D.M + (79 : ℝ)/50 * Real.log 2 * K.Sinfo := by
  apply mismatch_continuous_charge K
  intro c d hcd
  have hp := hpair c d hcd
  have hdist := mul_le_mul_of_nonneg_left (pair_hellinger_quadratic_le_KL K c d)
    (show (0 : ℝ) ≤ 79/100 by norm_num)
  nlinarith only [hp, hdist]

/-- The exact logarithmic pair charge implies the continuous mismatch estimate. -/
theorem mismatch_continuous_charge_of_log_hellinger
    (hpair : ∀ c d : K.κ, c ≠ d →
      1 ≤ 16 * Real.log 2 * Ixy (K.Q c) + (79 : ℝ)/100 *
        (-2 * Real.log (1 - hellingerSq (K.Q c) (K.Q d) / 2))) :
    K.dMis ≤ 16 * Real.log 2 * D.M + (79 : ℝ)/50 * Real.log 2 * K.Sinfo := by
  apply mismatch_continuous_charge K
  intro c d hcd
  have hp := hpair c d hcd
  have hdist := mul_le_mul_of_nonneg_left (pair_log_hellinger_le_KL K c d)
    (show (0 : ℝ) ≤ 79/100 by norm_num)
  nlinarith only [hp, hdist]

end stoch_to_det
