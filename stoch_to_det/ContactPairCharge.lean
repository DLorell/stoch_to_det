import stoch_to_det.Floor
import stoch_to_det.PairChargeScalar
import stoch_to_det.ContactInformation
import stoch_to_det.ContinuousMismatch

/-! Refined secant parameters for continuous contact-pair charging. -/
namespace stoch_to_det

noncomputable def pairSecantParameter (d : ℝ) : ℝ :=
  (3 - Real.sqrt (9-2*d))/2

theorem pair_secant_parameter_properties {d : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d < 1) :
    0 ≤ pairSecantParameter d ∧ pairSecantParameter d ≤ (9 : ℝ)/50 ∧
      pairSecantDistance (pairSecantParameter d) = d := by
  have hrad : 0 ≤ 9-2*d := by linarith
  have hsq := Real.sq_sqrt hrad
  have hs0 := Real.sqrt_nonneg (9-2*d)
  refine ⟨?_, ?_, ?_⟩
  · dsimp [pairSecantParameter]
    nlinarith
  · dsimp [pairSecantParameter]
    nlinarith
  · dsimp [pairSecantParameter, pairSecantDistance]
    nlinarith only [hsq]

private theorem refined_secant_scalar
    {d r s t g : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ (9 : ℝ)/50)
    (hd : pairSecantDistance r = d)
    (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (hts : t ≤ s/2-s^2/4)
    (hg : s-d/2-s^2/4 ≤ g)
    (hquartic : (s-d/2)^2 ≤ 3*s-2*d) :
    pairSecantN r / pairSecantD r ≤ g/t := by
  have hD := pair_secant_denominator_pos hr0 hr1
  let a : ℝ := 4*r-r^2
  let b : ℝ := 3+2*r-r^2
  let k : ℝ := pairSecantN r / pairSecantD r
  have hrprod : 0 ≤ r*(1-r) := mul_nonneg hr0 (by linarith)
  have hb : s < b := by dsimp [b]; nlinarith
  have hq : (s-a)*(s-b) ≤ 0 := by
    have heq : (s-a)*(s-b) = (s-d/2)^2-(3*s-2*d) := by
      rw [← hd]
      dsimp [a, b, pairSecantDistance]
      ring
    rw [heq]
    linarith
  have has : a ≤ s := by
    by_contra hnot
    have hpos : 0 < (s-a)*(s-b) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    linarith
  have hN0 : 0 ≤ pairSecantN r := by
    have hr2 : r^2 ≤ r := by nlinarith
    have hr3 : r^3 ≤ r^2 := by
      nlinarith [mul_nonneg (sq_nonneg r) (show 0 ≤ 1-r by linarith)]
    dsimp [pairSecantN]
    nlinarith [sq_nonneg r]
  have hk0 : 0 ≤ k := div_nonneg hN0 hD.le
  have hk1 : k ≤ 1 := by
    dsimp [k]
    apply (div_le_iff₀ hD).2
    dsimp [pairSecantN, pairSecantD]
    nlinarith
  have haeq : a-d/2-a^2/4-k*(a/2-a^2/4) = 0 := by
    rw [← hd]
    dsimp [k]
    field_simp
    dsimp [a, pairSecantN, pairSecantD, pairSecantDistance]
    ring
  have hfac : 0 ≤ 1-k/2-(1-k)*(s+a)/4 := by
    have hm := mul_le_mul_of_nonneg_left
      (show s+a ≤ 2 by linarith) (show 0 ≤ 1-k by linarith)
    nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr has) hfac
  have hmain : k*(s/2-s^2/4) ≤ s-d/2-s^2/4 := by
    nlinarith only [hp, haeq]
  apply (le_div_iff₀ ht0).2
  have hmul := mul_le_mul_of_nonneg_left hts hk0
  change k*t ≤ g
  linarith

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- The quartic secant constraint gives a rational correlation floor after
the parameter substitution `d=6r-2r²`. -/
theorem contact_rho_ge_pair_secant
    {S : Finset (α × β)} {w q q' : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q) (hq' : IsContact S w q')
    (hqs : support q = S) (hqs' : support q' = S) (hne : q ≠ q')
    (hd1 : hellingerSq q q' < 1) :
    pairSecantN (pairSecantParameter (hellingerSq q q')) /
      pairSecantD (pairSecantParameter (hellingerSq q q')) ≤ rhoHGR q := by
  let d : ℝ := hellingerSq q q'
  have hd0 : 0 ≤ d := hellingerSq_nonneg q q'
  let η : ℝ := Real.sqrt ((d+1)/4)
  have hη : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hηsq : η^2 = (d+1)/4 := Real.sq_sqrt (by positivity)
  have hη1 : 2*η^2 < 1 := by rw [hηsq]; dsimp [d]; linarith
  have henergy : contactSecantEnergy q q' ≤ 2*η^2 := by
    have he := contactSecantEnergy_le_hellingerSq hq hq' hqs hqs'
    rw [hηsq]
    dsimp [d]
    linarith
  obtain ⟨s, t, g, hs0, hs1, _, ht0, hts, _, hg, hquartic, hρ⟩ :=
    contact_secant_hgr_witness η hη hη1 hw hq hq' hqs hqs' hne henergy
  obtain ⟨hr0, hr1, hrδ⟩ := pair_secant_parameter_properties hd0 hd1
  exact (refined_secant_scalar hr0 hr1 hrδ hs0 hs1 ht0 hts hg hquartic).trans hρ

private theorem contact_pair_hellinger_lt_two
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
theorem contact_pair_charge_log
    {S : Finset (α × β)} {w q q' : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q) (hq' : IsContact S w q')
    (hqs : support q = S) (hqs' : support q' = S) (hne : q ≠ q') :
    1 ≤ 16*Knat q + (79 : ℝ)/100*
      (-2*Real.log (1-hellingerSq q q'/2)) := by
  have hd0 := hellingerSq_nonneg q q'
  have hd2 := contact_pair_hellinger_lt_two hq hq' hqs hqs'
  have harg : 0 < 1-hellingerSq q q'/2 := by linarith
  by_cases hd1 : hellingerSq q q' < 1
  · let r : ℝ := pairSecantParameter (hellingerSq q q')
    obtain ⟨hr0, hr1, hrd⟩ := pair_secant_parameter_properties hd0 hd1
    have hρ := contact_rho_ge_pair_secant hw hq hq' hqs hqs' hne hd1
    have hinfo (t : ℝ) (ht : 0 < t) :
        t^3*(pairSecantN r/pairSecantD r)-pairEntropyCost t ≤ Knat q := by
      have hm := mul_le_mul_of_nonneg_left hρ (pow_nonneg ht.le 3)
      have hi := contact_information_polynomial hw hq t ht
      dsimp [r]
      linarith
    have hc := pair_charge_scalar hr0 hr1
      (hinfo ((69 : ℝ)/100) (by norm_num))
      (hinfo ((33 : ℝ)/50) (by norm_num))
      (hinfo ((31 : ℝ)/50) (by norm_num))
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
