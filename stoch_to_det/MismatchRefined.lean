import stoch_to_det.ContactPairChargeRefined

/-! The sharpened unconditional mismatch estimate for common contacts. -/

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- The improved scalar contact estimate gives a smaller mismatch charge. -/
theorem mismatch_refined
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D) :
    K.dMis ≤ (733 : ℝ)/50 * Real.log 2 * D.M +
      (77 : ℝ)/50 * Real.log 2 * K.Sinfo := by
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
  have hpair (c d : K.κ) (hcd : c ≠ d) :
      1 ≤ ((733 : ℝ)/50 * Real.log 2) * Ixy (K.Q c) +
        ((77 : ℝ)/100 * Real.log 2) *
          (KL (overlapLaw K c d) (K.Q c) + KL (overlapLaw K c d) (K.Q d)) := by
    have h := contact_pair_charge_log_refined D.feasible
      (K.Q_isContact c) (K.Q_isContact d)
      (contact_support_eq D.feasible D.conn (K.Q_isContact c))
      (contact_support_eq D.feasible D.conn (K.Q_isContact d))
      (fun heq => hcd (K.Q_injective heq))
    rw [Knat_eq_log_two_mul_Ixy (K.Q_isContact c).1] at h
    have hdist := mul_le_mul_of_nonneg_left (pair_log_hellinger_le_KL K c d)
      (show (0 : ℝ) ≤ 77/100 by norm_num)
    nlinarith only [h, hdist]
  have h := mismatch_le_of_pair_charge K
    (a := (733 : ℝ)/50 * Real.log 2) (b := (77 : ℝ)/100 * Real.log 2)
    (by positivity) (by positivity) hpair
  convert h using 1; ring

end stoch_to_det
