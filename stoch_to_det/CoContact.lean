import stoch_to_det.Duality

/-!
# Structural consequences of feasibility at contacts

Three exact, division-free facts feeding the sharp-floor program:

1. Feasibility tested at point-mass probability vectors caps the kernel:
   `w ≤ 1` on the support.
2. Hence every contact is **pointwise dominated** by the 2/3-power of its
   product marginal: `q ≤ (q_X q_Y)^{2/3}` — the anti-concentration bound
   that blocks rare-event correlation.
3. Two contacts of one kernel satisfy the **co-contact ratio identity**
   `q · r_X^{2/3} r_Y^{2/3} = r · q_X^{2/3} q_Y^{2/3}` pointwise, and its
   fibered sum, the **half-tilt identity** — the division-free form of
   `e^{a/2} = E_r[e^b | X]` for the log-tilts `a = (2/3)ln(q_X/r_X)`,
   `b = (2/3)ln(q_Y/r_Y)`, which is the engine of the exact co-contact
   rigidity system.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **Feasibility at point masses: the kernel is capped by 1 on `S`.** -/
theorem feasible_kernel_le_one {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) : ∀ z ∈ S, w z ≤ 1 := by
  intro z hz
  set u : α → ℝ := fun x => if x = z.1 then 1 else 0 with hu_def
  set v : β → ℝ := fun y => if y = z.2 then 1 else 0 with hv_def
  have hu : IsPMF u := by
    constructor
    · intro x
      by_cases hx : x = z.1 <;> simp [hu_def, hx]
    · simp [mass, hu_def]
  have hv : IsPMF v := by
    constructor
    · intro y
      by_cases hy : y = z.2 <;> simp [hv_def, hy]
    · simp [mass, hv_def]
  have hterm : ∀ z' ∈ S, 0 ≤ w z' * u z'.1 ^ ((2:ℝ)/3) * v z'.2 ^ ((2:ℝ)/3) := by
    intro z' hz'
    exact mul_nonneg (mul_nonneg (hw.1 z' hz').le
      (Real.rpow_nonneg (hu.nonneg z'.1) _)) (Real.rpow_nonneg (hv.nonneg z'.2) _)
  have hzterm : w z * u z.1 ^ ((2:ℝ)/3) * v z.2 ^ ((2:ℝ)/3) = w z := by
    simp [hu_def, hv_def, Real.one_rpow]
  have hsingle : w z ≤ Lambda S w u v := by
    rw [← hzterm]
    exact Finset.single_le_sum hterm hz
  exact hsingle.trans (hw.2 u v hu hv)

/-- **Pointwise domination.** Every contact of a feasible kernel satisfies
`q(x,y) ≤ (q_X(x) q_Y(y))^{2/3}` on the support (and trivially off it) —
correlation cannot hide in rare cells. -/
theorem contact_pointwise_dom {S : Finset (α × β)} {w q : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q) :
    ∀ z ∈ S, q z ≤ mX q z.1 ^ ((2:ℝ)/3) * mY q z.2 ^ ((2:ℝ)/3) := by
  intro z hz
  obtain ⟨hqPMF, _, hqeq⟩ := hq
  have hXnn : (0:ℝ) ≤ mX q z.1 ^ ((2:ℝ)/3) :=
    Real.rpow_nonneg ((isPMF_push hqPMF).nonneg z.1) _
  have hYnn : (0:ℝ) ≤ mY q z.2 ^ ((2:ℝ)/3) :=
    Real.rpow_nonneg ((isPMF_push hqPMF).nonneg z.2) _
  calc q z = w z * mX q z.1 ^ ((2:ℝ)/3) * mY q z.2 ^ ((2:ℝ)/3) := hqeq z hz
    _ ≤ 1 * mX q z.1 ^ ((2:ℝ)/3) * mY q z.2 ^ ((2:ℝ)/3) := by
        apply mul_le_mul_of_nonneg_right _ hYnn
        exact mul_le_mul_of_nonneg_right (feasible_kernel_le_one hw z hz) hXnn
    _ = mX q z.1 ^ ((2:ℝ)/3) * mY q z.2 ^ ((2:ℝ)/3) := by ring

/-- **Co-contact ratio identity** (division-free): two contacts of one
kernel satisfy `q · r_X^{2/3} r_Y^{2/3} = r · q_X^{2/3} q_Y^{2/3}`
pointwise on the support — i.e. `q/r` is an exact product tilt. -/
theorem cocontact_ratio {S : Finset (α × β)} {w q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) :
    ∀ z ∈ S,
      q z * (mX r z.1 ^ ((2:ℝ)/3) * mY r z.2 ^ ((2:ℝ)/3)) =
      r z * (mX q z.1 ^ ((2:ℝ)/3) * mY q z.2 ^ ((2:ℝ)/3)) := by
  intro z hz
  rw [hq.2.2 z hz, hr.2.2 z hz]
  ring

/-- **Half-tilt identity** (division-free form of `e^{a/2} = E_r[e^b ∣ X]`).
For every `x`, fibered sums of the ratio identity give

`r_X(x)^{2/3} · ∑_y q(x,y) r_Y(y)^{2/3} = q_X(x)^{2/3} · ∑_y r(x,y) q_Y(y)^{2/3}`.

This is the engine of the exact co-contact rigidity system: dividing by
`r_X q_X^{...}` where positive recovers the conditional-moment equations
whose contraction properties force the knife edge. -/
theorem cocontact_halftilt {S : Finset (α × β)} {w q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) :
    ∀ x : α,
      mX r x ^ ((2:ℝ)/3) * (∑ y, q (x, y) * mY r y ^ ((2:ℝ)/3)) =
      mX q x ^ ((2:ℝ)/3) * (∑ y, r (x, y) * mY q y ^ ((2:ℝ)/3)) := by
  intro x
  have hpt : ∀ y : β,
      q (x, y) * (mX r x ^ ((2:ℝ)/3) * mY r y ^ ((2:ℝ)/3)) =
      r (x, y) * (mX q x ^ ((2:ℝ)/3) * mY q y ^ ((2:ℝ)/3)) := by
    intro y
    by_cases hz : (x, y) ∈ S
    · exact cocontact_ratio hq hr (x, y) hz
    · rw [hq.2.1 (x, y) hz, hr.2.1 (x, y) hz]
      ring
  calc
    mX r x ^ ((2:ℝ)/3) * (∑ y, q (x, y) * mY r y ^ ((2:ℝ)/3))
        = ∑ y, q (x, y) * (mX r x ^ ((2:ℝ)/3) * mY r y ^ ((2:ℝ)/3)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = ∑ y, r (x, y) * (mX q x ^ ((2:ℝ)/3) * mY q y ^ ((2:ℝ)/3)) :=
          Finset.sum_congr rfl (fun y _ => hpt y)
    _ = mX q x ^ ((2:ℝ)/3) * (∑ y, r (x, y) * mY q y ^ ((2:ℝ)/3)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring

/-- The symmetric (Y-fibered) half-tilt identity. -/
theorem cocontact_halftilt_snd {S : Finset (α × β)} {w q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) :
    ∀ y : β,
      mY r y ^ ((2:ℝ)/3) * (∑ x, q (x, y) * mX r x ^ ((2:ℝ)/3)) =
      mY q y ^ ((2:ℝ)/3) * (∑ x, r (x, y) * mX q x ^ ((2:ℝ)/3)) := by
  intro y
  have hpt : ∀ x : α,
      q (x, y) * (mX r x ^ ((2:ℝ)/3) * mY r y ^ ((2:ℝ)/3)) =
      r (x, y) * (mX q x ^ ((2:ℝ)/3) * mY q y ^ ((2:ℝ)/3)) := by
    intro x
    by_cases hz : (x, y) ∈ S
    · exact cocontact_ratio hq hr (x, y) hz
    · rw [hq.2.1 (x, y) hz, hr.2.1 (x, y) hz]
      ring
  calc
    mY r y ^ ((2:ℝ)/3) * (∑ x, q (x, y) * mX r x ^ ((2:ℝ)/3))
        = ∑ x, q (x, y) * (mX r x ^ ((2:ℝ)/3) * mY r y ^ ((2:ℝ)/3)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = ∑ x, r (x, y) * (mX q x ^ ((2:ℝ)/3) * mY q y ^ ((2:ℝ)/3)) :=
          Finset.sum_congr rfl (fun x _ => hpt x)
    _ = mY q y ^ ((2:ℝ)/3) * (∑ x, r (x, y) * mX q x ^ ((2:ℝ)/3)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring

/-- **Set-level domination** (alphabet-free anti-concentration). Feasibility
tested at renormalized restriction tilts bounds every product event at every
contact: `q(U×V) ≤ (q_X(U) · q_Y(V))^{2/3}`. Rare product blocks cannot carry
correlation — the singleton case is `contact_pointwise_dom`. -/
theorem contact_set_dom {S : Finset (α × β)} {w q : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q)
    (U : Finset α) (V : Finset β)
    (hU : 0 < ∑ x ∈ U, mX q x) (hV : 0 < ∑ y ∈ V, mY q y) :
    ∑ z ∈ S.filter (fun z => z.1 ∈ U ∧ z.2 ∈ V), q z ≤
      ((∑ x ∈ U, mX q x) * (∑ y ∈ V, mY q y)) ^ ((2:ℝ)/3) := by
  obtain ⟨hqPMF, hqsupp, hqeq⟩ := hq
  set cU : ℝ := ∑ x ∈ U, mX q x with hcU
  set cV : ℝ := ∑ y ∈ V, mY q y with hcV
  set u : α → ℝ := fun x => if x ∈ U then mX q x / cU else 0 with hu_def
  set v : β → ℝ := fun y => if y ∈ V then mY q y / cV else 0 with hv_def
  have hmXnn : ∀ x, 0 ≤ mX q x := fun x => (isPMF_push hqPMF).nonneg x
  have hmYnn : ∀ y, 0 ≤ mY q y := fun y => (isPMF_push hqPMF).nonneg y
  have hu : IsPMF u := by
    constructor
    · intro x
      by_cases hx : x ∈ U
      · simp only [hu_def, hx, if_true]
        exact div_nonneg (hmXnn x) hU.le
      · simp [hu_def, hx]
    · unfold mass
      simp only [hu_def]
      rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div, ← hcU]
      exact div_self hU.ne'
  have hv : IsPMF v := by
    constructor
    · intro y
      by_cases hy : y ∈ V
      · simp only [hv_def, hy, if_true]
        exact div_nonneg (hmYnn y) hV.le
      · simp [hv_def, hy]
    · unfold mass
      simp only [hv_def]
      rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div, ← hcV]
      exact div_self hV.ne'
  have hcUpow : (0:ℝ) < cU ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos hU _
  have hcVpow : (0:ℝ) < cV ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos hV _
  have hin : ∀ z ∈ S.filter (fun z => z.1 ∈ U ∧ z.2 ∈ V),
      q z = (cU ^ ((2:ℝ)/3) * cV ^ ((2:ℝ)/3)) *
        (w z * u z.1 ^ ((2:ℝ)/3) * v z.2 ^ ((2:ℝ)/3)) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzS, hzU, hzV⟩ := hz
    simp only [hu_def, hv_def, hzU, hzV, if_true]
    rw [Real.div_rpow (hmXnn z.1) hU.le, Real.div_rpow (hmYnn z.2) hV.le]
    rw [hqeq z hzS]
    field_simp
  have hterm_nonneg : ∀ z ∈ S, 0 ≤ w z * u z.1 ^ ((2:ℝ)/3) * v z.2 ^ ((2:ℝ)/3) := by
    intro z hzS
    exact mul_nonneg (mul_nonneg (hw.1 z hzS).le
      (Real.rpow_nonneg (hu.nonneg z.1) _)) (Real.rpow_nonneg (hv.nonneg z.2) _)
  have hsub : (∑ z ∈ S.filter (fun z => z.1 ∈ U ∧ z.2 ∈ V),
      w z * u z.1 ^ ((2:ℝ)/3) * v z.2 ^ ((2:ℝ)/3)) ≤ Lambda S w u v := by
    unfold Lambda
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro z hzS _
    exact hterm_nonneg z hzS
  calc
    ∑ z ∈ S.filter (fun z => z.1 ∈ U ∧ z.2 ∈ V), q z
        = (cU ^ ((2:ℝ)/3) * cV ^ ((2:ℝ)/3)) *
          ∑ z ∈ S.filter (fun z => z.1 ∈ U ∧ z.2 ∈ V),
            w z * u z.1 ^ ((2:ℝ)/3) * v z.2 ^ ((2:ℝ)/3) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl hin
    _ ≤ (cU ^ ((2:ℝ)/3) * cV ^ ((2:ℝ)/3)) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hcUpow.le hcVpow.le)
          exact hsub.trans (hw.2 u v hu hv)
    _ = (cU * cV) ^ ((2:ℝ)/3) := by
          rw [mul_one, ← Real.mul_rpow hU.le hV.le]

end stoch_to_det
