import stoch_to_det.DomFloorCore
import stoch_to_det.Toolkit
import stoch_to_det.ContactEntropyScalar
import stoch_to_det.Floor
import stoch_to_det.PairChargeScalar

/-! Information bounds using the full contact moment and a scalar exponential estimate. -/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Feasibility controls the full `4/3` moment of a normalized product test. -/
theorem contact_product_moment_four_thirds
    {S : Finset (α × β)} {w q : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q)
    {f : α → ℝ} {g : β → ℝ}
    (hf : ∑ x, mX q x * f x ^ 2 = 1)
    (hg : ∑ y, mY q y * g y ^ 2 = 1) :
    (∑ z, q z * |f z.1 * g z.2| ^ ((4 : ℝ) / 3)) ≤ 1 := by
  have h := contact_hypercontractive hw hq
    (f := fun x => |f x| ^ ((4 : ℝ) / 3))
    (g := fun y => |g y| ^ ((4 : ℝ) / 3))
    (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    (fun y => Real.rpow_nonneg (abs_nonneg _) _)
  have hp (a : ℝ) :
      (|a| ^ ((4 : ℝ) / 3)) ^ ((3 : ℝ) / 2) = a ^ 2 := by
    rw [← Real.rpow_mul (abs_nonneg a)]
    norm_num [Real.rpow_two, sq_abs]
  simp_rw [hp] at h
  rw [hf, hg] at h
  norm_num only [Real.one_rpow, one_mul] at h
  calc
    (∑ z, q z * |f z.1 * g z.2| ^ ((4 : ℝ) / 3)) =
        ∑ z ∈ S, q z * |f z.1 * g z.2| ^ ((4 : ℝ) / 3) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro z _ hz
      rw [hq.2.1 z hz, zero_mul]
    _ = ∑ z ∈ S, q z * |f z.1| ^ ((4 : ℝ) / 3) *
          |g z.2| ^ ((4 : ℝ) / 3) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      ring
    _ ≤ 1 := h

/-- The finite variational inequality in natural-log units. -/
theorem variational_nats
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : ι → ℝ} (hP : IsPMF P) (hQ : IsPMF Q)
    (hac : AbsCont P Q) (h : ι → ℝ) :
    (∑ i, P i * h i) - Real.log (∑ i, Q i * Real.exp (h i)) ≤
      ∑ i, P i * Real.log (P i / Q i) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hv := variational_le hP hQ hac (fun i => h i / Real.log 2)
  have hp (i : ι) : (2 : ℝ) ^ (h i / Real.log 2) = Real.exp (h i) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    field_simp
  simp_rw [hp] at hv
  unfold KL lg Real.logb at hv
  simp_rw [← mul_div_assoc] at hv
  rw [← Finset.sum_div, ← Finset.sum_div] at hv
  have hv' := mul_le_mul_of_nonneg_right hv hlog.le
  field_simp at hv'
  exact hv'

/-- The product of marginals dominates the joint support. -/
theorem joint_absCont_product {q : α × β → ℝ} (hq : IsPMF q) :
    AbsCont q (fun z => mX q z.1 * mY q z.2) := by
  intro z hz
  by_contra hqz
  have hp := joint_pos_marginals hq (lt_of_le_of_ne (hq.nonneg z) (Ne.symm hqz))
  exact (mul_ne_zero hp.1.ne' hp.2.ne') hz

/-- The natural information budget equals the finite KL sum. -/
theorem Knat_eq_sum_log {q : α × β → ℝ} (hq : IsPMF q) :
    Knat q = ∑ z, q z * Real.log (q z / (mX q z.1 * mY q z.2)) := by
  let Q : α × β → ℝ := fun z => mX q z.1 * mY q z.2
  have hac := joint_absCont_product hq
  have hQ : IsPMF Q := product_isPMF_dom (isPMF_push hq) (isPMF_push hq)
  have hterm (z : α × β) :
      Q z * ((q z / Q z) * Real.log (q z / Q z) - q z / Q z + 1) =
        q z * Real.log (q z / Q z) - q z + Q z := by
    by_cases hz : Q z = 0
    · have hqz := hac z hz
      simp [hz, hqz]
    · field_simp [hz]
  change (∑ z, Q z * ((q z / Q z) * Real.log (q z / Q z) - q z / Q z + 1)) = _
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hqsum : ∑ z, q z = 1 := hq.total
  have hQsum : ∑ z, Q z = 1 := hQ.total
  rw [hqsum, hQsum]
  simp [Q]

/-- A scalar exponential majorant turns a `4/3` moment into an information bound. -/
theorem product_moment_information
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : ι → ℝ} (hP : IsPMF P) (hQ : IsPMF Q)
    (hac : AbsCont P Q) (z : ι → ℝ)
    (hm : (∑ i, P i * |z i| ^ ((4 : ℝ) / 3)) ≤ 1)
    (hz : ∑ i, Q i * z i = 0)
    (hz2 : ∑ i, Q i * (z i) ^ 2 = 1)
    {a γ : ℝ} (_ha : 0 ≤ a) (hγ : 0 ≤ γ)
    (hscalar : ∀ u : ℝ, Real.exp (u - γ * |u| ^ ((4 : ℝ) / 3)) ≤
      1 + u + a * u ^ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    t ^ 3 * (∑ i, P i * z i) ≤
      (∑ i, P i * Real.log (P i / Q i)) +
        γ * t ^ 4 + Real.log (1 + a * t ^ 6) := by
  let h : ι → ℝ := fun i => t ^ 3 * z i - γ * t ^ 4 * |z i| ^ ((4 : ℝ) / 3)
  have hp (i : ι) : |t ^ 3 * z i| ^ ((4 : ℝ) / 3) =
      t ^ 4 * |z i| ^ ((4 : ℝ) / 3) := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht _),
      Real.mul_rpow (pow_nonneg ht _) (abs_nonneg _),
      ← Real.rpow_natCast, ← Real.rpow_mul ht]
    norm_num [Real.rpow_natCast]
  have hpoint (i : ι) : Real.exp (h i) ≤ 1 + t ^ 3 * z i + a * t ^ 6 * (z i) ^ 2 := by
    have hs := hscalar (t ^ 3 * z i)
    rw [hp] at hs
    change Real.exp (t ^ 3 * z i - γ * t ^ 4 * |z i| ^ ((4 : ℝ) / 3)) ≤ _
    calc
      _ = Real.exp (t ^ 3 * z i - γ * (t ^ 4 * |z i| ^ ((4 : ℝ) / 3))) := by
        congr 1
        ring
      _ ≤ 1 + t ^ 3 * z i + a * (t ^ 3 * z i) ^ 2 := hs
      _ = _ := by ring
  have hZ : (∑ i, Q i * Real.exp (h i)) ≤ 1 + a * t ^ 6 := by
    calc
      (∑ i, Q i * Real.exp (h i)) ≤
          ∑ i, Q i * (1 + t ^ 3 * z i + a * t ^ 6 * (z i) ^ 2) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hQ.nonneg i)
      _ = (∑ i, Q i) + t ^ 3 * (∑ i, Q i * z i) +
          a * t ^ 6 * (∑ i, Q i * (z i) ^ 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 1 + a * t ^ 6 := by rw [hz, hz2]; simpa [mass] using hQ.total
  have hZpos : 0 < ∑ i, Q i * Real.exp (h i) := by
    have htotal : ∑ i, Q i = 1 := hQ.total
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun i _ => hQ.nonneg i)).mp (show 0 < ∑ i, Q i by rw [htotal]; norm_num)
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hQ.nonneg i) (Real.exp_pos _).le)
      ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩
  have hlog := Real.log_le_log hZpos hZ
  have hv := variational_nats hP hQ hac h
  have hsum : (∑ i, P i * h i) = t ^ 3 * (∑ i, P i * z i) -
      γ * t ^ 4 * (∑ i, P i * |z i| ^ ((4 : ℝ) / 3)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [h]
    ring
  rw [hsum] at hv
  have hm' := mul_le_mul_of_nonneg_left hm (mul_nonneg hγ (pow_nonneg ht 4))
  linarith

/-- A contact's mutual information controls every normalized correlation test. -/
theorem contact_information_affine
    {S : Finset (α × β)} {w q : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q)
    {f : α → ℝ} {g : β → ℝ}
    (hf0 : ∑ x, mX q x * f x = 0)
    (hg0 : ∑ y, mY q y * g y = 0)
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1)
    (hg2 : ∑ y, mY q y * g y ^ 2 = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    t ^ 3 * (∑ z, q z * f z.1 * g z.2) ≤
      Knat q + (31 : ℝ) / 100 * t ^ 4 +
        Real.log (1 + (59 : ℝ) / 200 * t ^ 6) := by
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
    hz hz2 (by norm_num : (0 : ℝ) ≤ 59 / 200) (by norm_num : (0 : ℝ) ≤ 31 / 100)
    exp_sub_abs_rpow_le_quadratic t ht
  rw [← Knat_eq_sum_log hq.1] at h
  simpa only [mul_assoc] using h

/-- Nonnegativity of the natural mutual-information budget. -/
theorem Knat_nonneg {q : α × β → ℝ} (hq : IsPMF q) : 0 ≤ Knat q := by
  apply Finset.sum_nonneg
  intro z _
  have hm : 0 ≤ mX q z.1 * mY q z.2 :=
    mul_nonneg ((isPMF_push hq).nonneg _) ((isPMF_push hq).nonneg _)
  exact mul_nonneg hm (phi_nonneg (div_nonneg (hq.nonneg z) hm))

/-- The affine information estimate also bounds the supremal correlation. -/
theorem contact_information_hgr
    {S : Finset (α × β)} {w q : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q)
    (t : ℝ) (ht : 0 < t) :
    t ^ 3 * rhoHGR q ≤ Knat q + (31 : ℝ) / 100 * t ^ 4 +
        Real.log (1 + (59 : ℝ) / 200 * t ^ 6) := by
  have ht3 : 0 < t ^ 3 := pow_pos ht _
  have hc : 0 ≤ Knat q + (31 : ℝ) / 100 * t ^ 4 +
      Real.log (1 + (59 : ℝ) / 200 * t ^ 6) := by
    exact add_nonneg (add_nonneg (Knat_nonneg hq.1) (by positivity))
      (Real.log_nonneg (by
        have hh : 0 ≤ (59 : ℝ) / 200 * t ^ 6 := by positivity
        linarith))
  have hb : rhoHGR q ≤ (Knat q + (31 : ℝ) / 100 * t ^ 4 +
        Real.log (1 + (59 : ℝ) / 200 * t ^ 6)) / t ^ 3 := by
    apply Real.iSup_le
    · intro fg
      apply (le_div_iff₀ ht3).2
      simpa only [mul_comm] using contact_information_affine hw hq
        fg.2.1 fg.2.2.1 fg.2.2.2.1 fg.2.2.2.2 t ht.le
    · exact div_nonneg hc ht3.le
  have h := (le_div_iff₀ ht3).mp hb
  simpa only [mul_comm] using h

/-- The cubic alternating Taylor upper bound, valid on the entire nonnegative axis. -/
theorem log_one_add_le_cubic {v : ℝ} (hv : 0 ≤ v) :
    Real.log (1 + v) ≤ v - v ^ 2 / 2 + v ^ 3 / 3 := by
  let F : ℝ → ℝ := fun x => x - x ^ 2 / 2 + x ^ 3 / 3 - Real.log (1 + x)
  have hd (x : ℝ) (hx : 0 ≤ x) : HasDerivAt F (x ^ 3 / (1 + x)) x := by
    have hx1 : 1 + x ≠ 0 := ne_of_gt (by linarith)
    have hp := (((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2).div_const 2)).add
      (((hasDerivAt_id x).pow 3).div_const 3)).sub
      (((hasDerivAt_id x).const_add 1).log hx1)
    apply hp.congr_deriv
    norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hx1]
    ring
  have hmono : MonotoneOn F (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx0 : 0 ≤ x := (interior_subset hx : x ∈ Set.Ici 0)
      exact (hd x hx0).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : 0 ≤ x := (interior_subset hx : x ∈ Set.Ici 0)
      rw [(hd x hx0).deriv]
      exact div_nonneg (pow_nonneg hx0 _) (by linarith)
  have h := hmono (by simp) (show v ∈ Set.Ici 0 from hv) hv
  simp only [F, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (3 : ℕ) ≠ 0), zero_div, sub_zero, add_zero,
    Real.log_one] at h
  linarith

/-- A polynomial form suited to exact certificates for continuous pair charging. -/
theorem contact_information_polynomial
    {S : Finset (α × β)} {w q : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q)
    (t : ℝ) (ht : 0 < t) :
    t ^ 3 * rhoHGR q - pairEntropyCost t ≤ Knat q := by
  have hi := contact_information_hgr hw hq t ht
  have hl := log_one_add_le_cubic
    (show 0 ≤ (59 : ℝ) / 200 * t ^ 6 by positivity)
  dsimp [pairEntropyCost]
  linarith

end stoch_to_det
