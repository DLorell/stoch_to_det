import stoch_to_det.ContactPairCharge
import stoch_to_det.ContactInformationRefined

/-! The sharpened continuous charge for common contacts. -/

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

private theorem contact_pair_hellinger_lt_two_refined
    {S : Finset (α × β)} {w q q' : α × β → ℝ}
    (hq : IsContact S w q) (hq' : IsContact S w q')
    (hqs : support q = S) (hqs' : support q' = S) :
    hellingerSq q q' < 2 := by
  have hex : ∃ z, q z ≠ 0 := by
    by_contra h
    push Not at h
    have htotal := hq.1.total
    simp [mass, h] at htotal
  obtain ⟨z, hz⟩ := hex
  have hzq : z ∈ support q := by simp [support, hz]
  have hzq' : z ∈ support q' := by rwa [hqs', ← hqs]
  have hz' : q' z ≠ 0 := by simpa [support] using hzq'
  have hB : 0 < BC q q' := by
    unfold BC
    apply Finset.sum_pos'
    · intro i _
      exact Real.sqrt_nonneg _
    · exact ⟨z, Finset.mem_univ _, Real.sqrt_pos.2
        (mul_pos (lt_of_le_of_ne (hq.1.nonneg z) (Ne.symm hz))
          (lt_of_le_of_ne (hq'.1.nonneg z) (Ne.symm hz')))⟩
  rw [hellingerSq_eq_two_mul_one_sub_BC hq.1 hq'.1]
  linarith

/-- The continuous charge for distinct common contacts, in natural-log units.
No overlap law or latent representation is needed for this pairwise estimate. -/
theorem contact_pair_charge_log_refined
    {S : Finset (α × β)} {w q q' : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q) (hq' : IsContact S w q')
    (hqs : support q = S) (hqs' : support q' = S) (hne : q ≠ q') :
    1 ≤ (733 : ℝ)/50*Knat q + (77 : ℝ)/100*
      (-2*Real.log (1-hellingerSq q q'/2)) := by
  have hd0 := hellingerSq_nonneg q q'
  have hd2 := contact_pair_hellinger_lt_two_refined hq hq' hqs hqs'
  have harg : 0 < 1-hellingerSq q q'/2 := by linarith
  by_cases hd1 : hellingerSq q q' < 1
  · let r : ℝ := pairSecantParameter (hellingerSq q q')
    obtain ⟨hr0, hr1, hrd⟩ := pair_secant_parameter_properties hd0 hd1
    have hρ := contact_rho_ge_pair_secant hw hq hq' hqs hqs' hne hd1
    have hinfo (t : ℝ) (ht : 0 < t) :
        t^3*(pairSecantN r/pairSecantD r)-pairEntropyCostRefined t ≤ Knat q := by
      have hm := mul_le_mul_of_nonneg_left hρ (pow_nonneg ht.le 3)
      have hi := contact_information_polynomial_refined hw hq t ht
      dsimp [r]
      linarith
    have hc := pair_charge_scalar_refined hr0 hr1 hinfo
    rw [hrd] at hc
    have hl := log_le_quadratic_at_one harg
      (show 1-hellingerSq q q'/2 ≤ 1 by linarith)
    have hcost : hellingerSq q q' + (hellingerSq q q')^2/4 ≤
        -2*Real.log (1-hellingerSq q q'/2) := by nlinarith
    linarith
  · have hhalf : 1-hellingerSq q q'/2 ≤ (1 : ℝ)/2 := by linarith
    have hl := Real.log_le_log harg hhalf
    have hloghalf : Real.log ((1 : ℝ)/2) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [hloghalf] at hl
    have hK := Knat_nonneg hq.1
    have hlog2 := Real.log_two_gt_d9
    linarith

end stoch_to_det
