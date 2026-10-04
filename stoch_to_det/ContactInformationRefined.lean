import stoch_to_det.ContactInformation
import stoch_to_det.ContactEntropyScalarRefined
import stoch_to_det.PairChargeScalarRefined

/-! Improved contact-information bounds from the sharper scalar majorant. -/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- A contact's mutual information controls every normalized correlation test. -/
theorem contact_information_affine_refined
    {S : Finset (α × β)} {w q : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q)
    {f : α → ℝ} {g : β → ℝ}
    (hf0 : ∑ x, mX q x * f x = 0)
    (hg0 : ∑ y, mY q y * g y = 0)
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1)
    (hg2 : ∑ y, mY q y * g y ^ 2 = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    t ^ 3 * (∑ z, q z * f z.1 * g z.2) ≤
      Knat q + (589 : ℝ) / 2000 * t ^ 4 +
        Real.log (1 + (71 : ℝ) / 250 * t ^ 6) := by
  let Q : α × β → ℝ := fun z => mX q z.1 * mY q z.2
  have hQ : IsPMF Q := product_isPMF_dom (isPMF_push hq.1) (isPMF_push hq.1)
  have hprod (F : α → ℝ) (G : β → ℝ) :
      (∑ z, Q z * (F z.1 * G z.2)) =
        (∑ x, mX q x * F x) * (∑ y, mY q y * G y) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    dsimp [Q]
    ring
  have hz : ∑ z, Q z * (f z.1 * g z.2) = 0 := by
    rw [hprod, hf0, hg0, zero_mul]
  have hz2 : ∑ z, Q z * (f z.1 * g z.2) ^ 2 = 1 := by
    simp_rw [mul_pow]
    rw [hprod (fun x => f x ^ 2) (fun y => g y ^ 2), hf2, hg2, one_mul]
  have h := product_moment_information hq.1 hQ (joint_absCont_product hq.1)
    (fun z => f z.1 * g z.2) (contact_product_moment_four_thirds hw hq hf2 hg2)
    hz hz2 (by norm_num : (0 : ℝ) ≤ 71 / 250) (by norm_num : (0 : ℝ) ≤ 589 / 2000)
    exp_sub_abs_rpow_le_quadratic_refined t ht
  rw [← Knat_eq_sum_log hq.1] at h
  simpa only [mul_assoc] using h

/-- The affine information estimate also bounds the supremal correlation. -/
theorem contact_information_hgr_refined
    {S : Finset (α × β)} {w q : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q)
    (t : ℝ) (ht : 0 < t) :
    t ^ 3 * rhoHGR q ≤ Knat q + (589 : ℝ) / 2000 * t ^ 4 +
        Real.log (1 + (71 : ℝ) / 250 * t ^ 6) := by
  have ht3 : 0 < t ^ 3 := pow_pos ht _
  have hc : 0 ≤ Knat q + (589 : ℝ) / 2000 * t ^ 4 +
      Real.log (1 + (71 : ℝ) / 250 * t ^ 6) := by
    exact add_nonneg (add_nonneg (Knat_nonneg hq.1) (by positivity))
      (Real.log_nonneg (by
        have hh : 0 ≤ (71 : ℝ) / 250 * t ^ 6 := by positivity
        linarith))
  have hb : rhoHGR q ≤ (Knat q + (589 : ℝ) / 2000 * t ^ 4 +
        Real.log (1 + (71 : ℝ) / 250 * t ^ 6)) / t ^ 3 := by
    apply Real.iSup_le
    · intro fg
      apply (le_div_iff₀ ht3).2
      simpa only [mul_comm] using contact_information_affine_refined hw hq
        fg.2.1 fg.2.2.1 fg.2.2.2.1 fg.2.2.2.2 t ht.le
    · exact div_nonneg hc ht3.le
  have h := (le_div_iff₀ ht3).mp hb
  simpa only [mul_comm] using h

/-- A polynomial form suited to exact certificates for continuous pair charging. -/
theorem contact_information_polynomial_refined
    {S : Finset (α × β)} {w q : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q)
    (t : ℝ) (ht : 0 < t) :
    t ^ 3 * rhoHGR q - pairEntropyCostRefined t ≤ Knat q := by
  have hi := contact_information_hgr_refined hw hq t ht
  have hl := log_one_add_le_cubic
    (show 0 ≤ (71 : ℝ) / 250 * t ^ 6 by positivity)
  dsimp [pairEntropyCostRefined]
  linarith

end stoch_to_det
