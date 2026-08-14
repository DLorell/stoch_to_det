import stoch_to_det.PhiBounds2
import stoch_to_det.QuarticMoment

/-!
# Entropy control of contact correlations

The natural-log mutual information budget is split into bulk cells, where a
quadratic estimate and Cauchy--Schwarz apply, and tail cells, where feasibility
controls a quartic moment.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

private lemma product_isPMF_local {ι κ : Type*} [Fintype ι] [Fintype κ]
    {u : ι → ℝ} {v : κ → ℝ} (hu : IsPMF u) (hv : IsPMF v) :
    IsPMF (fun z : ι × κ => u z.1 * v z.2) := by
  refine ⟨fun z => mul_nonneg (hu.nonneg z.1) (hv.nonneg z.2), ?_⟩
  have hu_sum : ∑ i, u i = 1 := by simpa [mass] using hu.total
  have hv_sum : ∑ k, v k = 1 := by simpa [mass] using hv.total
  rw [mass, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [hv_sum]
  simpa using hu_sum

/-- Mutual information in nats, written with the scalar entropy integrand and
product marginals. -/
noncomputable def Knat (q : α × β → ℝ) : ℝ :=
  ∑ z, (mX q z.1 * mY q z.2) *
    ((q z / (mX q z.1 * mY q z.2)) *
      Real.log (q z / (mX q z.1 * mY q z.2)) -
      q z / (mX q z.1 * mY q z.2) + 1)

/-- The scalar-integrand formula for mutual information, in natural-log units. -/
theorem Knat_eq_log_two_mul_Ixy {q : α × β → ℝ} (hq : IsPMF q) :
    Knat q = Real.log 2 * Ixy q := by
  let Q : α × β → ℝ := fun z => mX q z.1 * mY q z.2
  have hqX : IsPMF (mX q) := isPMF_push hq
  have hqY : IsPMF (mY q) := isPMF_push hq
  have hQ : IsPMF Q := product_isPMF_local hqX hqY
  have hac : ∀ z, Q z = 0 → q z = 0 := by
    intro z hQz
    by_contra hqz
    have hqpos : 0 < q z := lt_of_le_of_ne (hq.nonneg z) (Ne.symm hqz)
    have hxle : q z ≤ mX q z.1 := by
      change q z ≤ push Prod.fst q z.1
      unfold push
      exact Finset.single_le_sum (fun u _ => hq.nonneg u) (by simp)
    have hyle : q z ≤ mY q z.2 := by
      change q z ≤ push Prod.snd q z.2
      unfold push
      exact Finset.single_le_sum (fun u _ => hq.nonneg u) (by simp)
    have hxpos : 0 < mX q z.1 := lt_of_lt_of_le hqpos hxle
    have hypos : 0 < mY q z.2 := lt_of_lt_of_le hqpos hyle
    exact (mul_ne_zero hxpos.ne' hypos.ne') hQz
  have hliftX : ∑ x, Real.negMulLog (mX q x) =
      ∑ z, q z * (-Real.log (mX q z.1)) := by
    calc
      ∑ x, Real.negMulLog (mX q x) =
          ∑ x, mX q x * (-Real.log (mX q x)) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Real.negMulLog]
            ring
      _ = ∑ z, q z * (-Real.log (mX q z.1)) := sum_push_mul Prod.fst q _
  have hliftY : ∑ y, Real.negMulLog (mY q y) =
      ∑ z, q z * (-Real.log (mY q z.2)) := by
    calc
      ∑ y, Real.negMulLog (mY q y) =
          ∑ y, mY q y * (-Real.log (mY q y)) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [Real.negMulLog]
            ring
      _ = ∑ z, q z * (-Real.log (mY q z.2)) := sum_push_mul Prod.snd q _
  have hliftq : ∑ z, Real.negMulLog (q z) =
      ∑ z, q z * (-Real.log (q z)) := by
    apply Finset.sum_congr rfl
    intro z _
    rw [Real.negMulLog]
    ring
  have hEntropyKL :
      (∑ x, Real.negMulLog (mX q x)) + (∑ y, Real.negMulLog (mY q y)) -
          ∑ z, Real.negMulLog (q z) =
        ∑ z, q z * Real.log (q z / Q z) := by
    rw [hliftX, hliftY, hliftq, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hqz : q z = 0
    · simp [hqz]
    · have hQz : Q z ≠ 0 := fun h => hqz (hac z h)
      have hxy : mX q z.1 * mY q z.2 ≠ 0 := by simpa [Q] using hQz
      have hx0 : mX q z.1 ≠ 0 := (mul_ne_zero_iff.mp hxy).1
      have hy0 : mY q z.2 ≠ 0 := (mul_ne_zero_iff.mp hxy).2
      rw [Real.log_div hqz hQz]
      dsimp [Q]
      rw [Real.log_mul hx0 hy0]
      ring
  have hEq_q := H_eq_negMulLog hq.isFinMeas
  have hEq_X := H_eq_negMulLog hqX.isFinMeas
  have hEq_Y := H_eq_negMulLog hqY.isFinMeas
  rw [hq.total, Real.log_one, mul_zero, zero_add] at hEq_q
  rw [hqX.total, Real.log_one, mul_zero, zero_add] at hEq_X
  rw [hqY.total, Real.log_one, mul_zero, zero_add] at hEq_Y
  have hI_nats : Real.log 2 * Ixy q = ∑ z, q z * Real.log (q z / Q z) := by
    calc
      Real.log 2 * Ixy q =
          Real.log 2 * H (mX q) + Real.log 2 * H (mY q) - Real.log 2 * H q := by
            unfold Ixy
            ring
      _ = (∑ x, Real.negMulLog (mX q x)) + (∑ y, Real.negMulLog (mY q y)) -
          ∑ z, Real.negMulLog (q z) := by rw [hEq_X, hEq_Y, hEq_q]
      _ = ∑ z, q z * Real.log (q z / Q z) := hEntropyKL
  have hterm : ∀ z,
      Q z * ((q z / Q z) * Real.log (q z / Q z) - q z / Q z + 1) =
        q z * Real.log (q z / Q z) - q z + Q z := by
    intro z
    by_cases hQz : Q z = 0
    · have hqz := hac z hQz
      simp [hQz, hqz]
    · field_simp [hQz]
  have hsumq : ∑ z, q z = 1 := by simpa [mass] using hq.total
  have hsumQ : ∑ z, Q z = 1 := by simpa [mass] using hQ.total
  calc
    Knat q = ∑ z, Q z *
        ((q z / Q z) * Real.log (q z / Q z) - q z / Q z + 1) := by rfl
    _ = ∑ z, (q z * Real.log (q z / Q z) - q z + Q z) :=
      Finset.sum_congr rfl (fun z _ => hterm z)
    _ = ∑ z, q z * Real.log (q z / Q z) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsumq, hsumQ]
      ring
    _ = Real.log 2 * Ixy q := hI_nats.symm


private lemma joint_pos_marginals {q : α × β → ℝ} (hq : IsPMF q)
    {z : α × β} (hz : 0 < q z) :
    0 < mX q z.1 ∧ 0 < mY q z.2 := by
  have hxle : q z ≤ mX q z.1 := by
    change q z ≤ push Prod.fst q z.1
    unfold push
    exact Finset.single_le_sum (fun u _ => hq.nonneg u) (by simp)
  have hyle : q z ≤ mY q z.2 := by
    change q z ≤ push Prod.snd q z.2
    unfold push
    exact Finset.single_le_sum (fun u _ => hq.nonneg u) (by simp)
  exact ⟨hz.trans_le hxle, hz.trans_le hyle⟩

/-- The bulk/tail argument, parameterized by the natural-information budget,
the target correlation cap, the final two-term assembly, and the scalar tail
estimate.  Keeping the assembly abstract lets later calibrations reuse the
load-bearing bulk and quartic estimates without duplicating this proof. -/
theorem contact_correlation_cap_of_tail_param
    (K cap : ℝ)
    {S : Finset (α × β)} {w q : α × β → ℝ}
    (hq : IsPMF q) (hw : Feasible S w) (hcontact : IsContact S w q)
    {f : α → ℝ} {g : β → ℝ}
    (hf0 : ∑ x, mX q x * f x = 0)
    (hg0 : ∑ y, mY q y * g y = 0)
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1)
    (hg2 : ∑ y, mY q y * g y ^ 2 = 1)
    (htail : ∀ r : ℝ, 2 ≤ r →
      (r - 1) ^ 4 ≤ ((5062 : ℝ) / 10000) *
        (r ^ 3 * (r * Real.log r - r + 1)))
    (hassembly : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x + y ≤ K →
      Real.sqrt (((259 : ℝ) / 100) * x) +
          (((5062 : ℝ) / 10000) * y) ^ ((1 : ℝ) / 4) ≤ cap)
    (hK : Knat q ≤ K) :
    (∑ z, q z * f z.1 * g z.2) ≤ cap := by
  classical
  let μ : α × β → ℝ := fun z => mX q z.1 * mY q z.2
  let k : α × β → ℝ := fun z => μ z *
    ((q z / μ z) * Real.log (q z / μ z) - q z / μ z + 1)
  let Bulk : Finset (α × β) := Finset.univ.filter (fun z => q z ≤ 2 * μ z)
  let Tail : Finset (α × β) := Finset.univ.filter (fun z => 2 * μ z < q z)
  have hqX : IsPMF (mX q) := isPMF_push hq
  have hqY : IsPMF (mY q) := isPMF_push hq
  have hμ0 : ∀ z, 0 ≤ μ z := fun z => mul_nonneg (hqX.nonneg z.1) (hqY.nonneg z.2)
  have hac : ∀ z, μ z = 0 → q z = 0 := by
    intro z hμz
    by_contra hqz
    have hqpos : 0 < q z := lt_of_le_of_ne (hq.nonneg z) (Ne.symm hqz)
    obtain ⟨hxpos, hypos⟩ := joint_pos_marginals hq hqpos
    exact (mul_ne_zero hxpos.ne' hypos.ne') hμz
  have hk0 : ∀ z, 0 ≤ k z := by
    intro z
    have hr0 : 0 ≤ q z / μ z := div_nonneg (hq.nonneg z) (hμ0 z)
    exact mul_nonneg (hμ0 z) (by simpa [phi] using phi_nonneg hr0)
  have hmu_fg : (∑ z, μ z * f z.1 * g z.2) = 0 := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x, ∑ y, μ (x, y) * f x * g y) =
          ∑ x, (mX q x * f x) * (∑ y, mY q y * g y) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            dsimp [μ]
            ring
      _ = (∑ x, mX q x * f x) * (∑ y, mY q y * g y) := by
        rw [Finset.sum_mul]
      _ = 0 := by rw [hf0, hg0]; norm_num
  have hcorr : (∑ z, q z * f z.1 * g z.2) =
      ∑ z, (q z - μ z) * f z.1 * g z.2 := by
    calc
      (∑ z, q z * f z.1 * g z.2) =
          (∑ z, (q z - μ z) * f z.1 * g z.2) +
            ∑ z, μ z * f z.1 * g z.2 := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro z _
              ring
      _ = ∑ z, (q z - μ z) * f z.1 * g z.2 := by rw [hmu_fg, add_zero]
  have hpart (F : α × β → ℝ) :
      (∑ z, F z) = (∑ z ∈ Bulk, F z) + ∑ z ∈ Tail, F z := by
    dsimp [Bulk, Tail]
    rw [← Finset.sum_filter_add_sum_filter_not
      (p := fun z : α × β => q z ≤ 2 * μ z)]
    simp only [not_le]
  let x : ℝ := ∑ z ∈ Bulk, k z
  let y : ℝ := ∑ z ∈ Tail, k z
  have hx0 : 0 ≤ x := Finset.sum_nonneg fun z hz => hk0 z
  have hy0 : 0 ≤ y := Finset.sum_nonneg fun z hz => hk0 z
  have hxyK : x + y = Knat q := by
    rw [← hpart k]
    simp [Knat, k, μ]
  have hxy : x + y ≤ K := by rw [hxyK]; exact hK

  -- Bulk cells: the quadratic scalar bound and Cauchy--Schwarz.
  let A : α × β → ℝ := fun z => ((259 : ℝ) / 100) * k z
  let B : α × β → ℝ := fun z => μ z * f z.1 ^ 2 * g z.2 ^ 2
  let R : α × β → ℝ := fun z => |q z - μ z| * |f z.1| * |g z.2|
  have hA0 : ∀ z, 0 ≤ A z := fun z => mul_nonneg (by norm_num) (hk0 z)
  have hB0 : ∀ z, 0 ≤ B z := fun z =>
    mul_nonneg (mul_nonneg (hμ0 z) (sq_nonneg _)) (sq_nonneg _)
  have hbulk_cell : ∀ z ∈ Bulk, R z ^ 2 ≤ A z * B z := by
    intro z hz
    have hzmem := (Finset.mem_filter.mp hz).2
    by_cases hμz : μ z = 0
    · have hqz := hac z hμz
      simp [R, A, B, k, hμz, hqz]
    · have hμpos : 0 < μ z := lt_of_le_of_ne (hμ0 z) (Ne.symm hμz)
      let r : ℝ := q z / μ z
      have hr0 : 0 ≤ r := div_nonneg (hq.nonneg z) hμpos.le
      have hr2 : r ≤ 2 := by
        dsimp [r]
        exact (div_le_iff₀ hμpos).2 (by simpa [mul_comm] using hzmem)
      have hs := bulk_quad_two r hr0 hr2
      have hscale := mul_le_mul_of_nonneg_left hs (sq_nonneg (μ z))
      have hdiff : q z - μ z = μ z * (r - 1) := by
        dsimp [r]
        field_simp [hμz]
      have hbase : (q z - μ z) ^ 2 ≤
          ((259 : ℝ) / 100) * (μ z) ^ 2 *
            (r * Real.log r - r + 1) := by
        rw [hdiff, mul_pow]
        nlinarith
      have hfg := mul_le_mul_of_nonneg_right hbase
        (mul_nonneg (sq_nonneg (f z.1)) (sq_nonneg (g z.2)))
      calc
        R z ^ 2 = (q z - μ z) ^ 2 * (f z.1 ^ 2 * g z.2 ^ 2) := by
          dsimp [R]
          rw [mul_pow, mul_pow, sq_abs, sq_abs, sq_abs]
          ring
        _ ≤ (((259 : ℝ) / 100) * (μ z) ^ 2 *
            (r * Real.log r - r + 1)) *
              (f z.1 ^ 2 * g z.2 ^ 2) := hfg
        _ = A z * B z := by
          dsimp [A, B, k]
          dsimp [r]
          ring
  have hBsum_all : (∑ z, B z) = 1 := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ a, ∑ b, B (a, b)) =
          ∑ a, (mX q a * f a ^ 2) * (∑ b, mY q b * g b ^ 2) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            dsimp [B, μ]
            ring
      _ = 1 := by rw [hg2]; simpa using hf2
  have hBsum_le : (∑ z ∈ Bulk, B z) ≤ 1 := by
    calc
      (∑ z ∈ Bulk, B z) ≤ ∑ z, B z := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Bulk)
        intro z _ _
        exact hB0 z
      _ = 1 := hBsum_all
  have hAsum : (∑ z ∈ Bulk, A z) = ((259 : ℝ) / 100) * x := by
    dsimp [A, x]
    rw [Finset.mul_sum]
  have hbulk_sq : (∑ z ∈ Bulk, R z) ^ 2 ≤ ((259 : ℝ) / 100) * x := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Bulk
      (fun z _ => hA0 z) (fun z _ => hB0 z) hbulk_cell
    rw [hAsum] at hcs
    calc
      (∑ z ∈ Bulk, R z) ^ 2 ≤
          (((259 : ℝ) / 100) * x) * ∑ z ∈ Bulk, B z := hcs
      _ ≤ (((259 : ℝ) / 100) * x) * 1 :=
        mul_le_mul_of_nonneg_left hBsum_le (mul_nonneg (by norm_num) hx0)
      _ = ((259 : ℝ) / 100) * x := mul_one _
  have hbulk_abs : (∑ z ∈ Bulk, R z) ≤
      Real.sqrt (((259 : ℝ) / 100) * x) :=
    Real.le_sqrt_of_sq_le hbulk_sq

  -- Tail cells: contact structure converts feasibility into a quartic bound.
  have hTailS : Tail ⊆ S := by
    intro z hz
    have htailz := (Finset.mem_filter.mp hz).2
    have hqpos : 0 < q z := lt_of_le_of_lt (mul_nonneg (by norm_num) (hμ0 z)) htailz
    by_contra hzS
    exact hqpos.ne' (hcontact.2.1 z hzS)
  let c : α × β → ℝ := fun z =>
    (q z - μ z) / (w z ^ ((3 : ℝ) / 2) * Real.sqrt (μ z))
  let F : α → ℝ := fun a => Real.sqrt (mX q a) * |f a|
  let G : β → ℝ := fun b => Real.sqrt (mY q b) * |g b|
  have hF0 : ∀ a, 0 ≤ F a := fun a => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hG0 : ∀ b, 0 ≤ G b := fun b => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hF2 : ∑ a, F a ^ 2 = 1 := by
    calc
      ∑ a, F a ^ 2 = ∑ a, mX q a * f a ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        dsimp [F]
        rw [mul_pow, Real.sq_sqrt (hqX.nonneg a), sq_abs]
      _ = 1 := hf2
  have hG2 : ∑ b, G b ^ 2 = 1 := by
    calc
      ∑ b, G b ^ 2 = ∑ b, mY q b * g b ^ 2 := by
        apply Finset.sum_congr rfl
        intro b _
        dsimp [G]
        rw [mul_pow, Real.sq_sqrt (hqY.nonneg b), sq_abs]
      _ = 1 := hg2
  have hc0 : ∀ z ∈ Tail, 0 ≤ c z := by
    intro z hz
    have hzS := hTailS hz
    have htailz := (Finset.mem_filter.mp hz).2
    have hqpos : 0 < q z := lt_of_le_of_lt (mul_nonneg (by norm_num) (hμ0 z)) htailz
    have hμpos : 0 < μ z := by
      obtain ⟨hxpos, hypos⟩ := joint_pos_marginals hq hqpos
      exact mul_pos hxpos hypos
    have hnum : 0 ≤ q z - μ z := by linarith [hμ0 z]
    have hden : 0 < w z ^ ((3 : ℝ) / 2) * Real.sqrt (μ z) :=
      mul_pos (Real.rpow_pos_of_pos (hw.1 z hzS) _) (Real.sqrt_pos.2 hμpos)
    exact div_nonneg hnum hden.le
  have htail_term : ∀ z ∈ Tail,
      w z ^ ((3 : ℝ) / 2) * c z * (F z.1 * G z.2) =
        (q z - μ z) * |f z.1| * |g z.2| := by
    intro z hz
    have hzS := hTailS hz
    have htailz := (Finset.mem_filter.mp hz).2
    have hqpos : 0 < q z := lt_of_le_of_lt (mul_nonneg (by norm_num) (hμ0 z)) htailz
    obtain ⟨hxpos, hypos⟩ := joint_pos_marginals hq hqpos
    have hμpos : 0 < μ z := mul_pos hxpos hypos
    have hwpow : 0 < w z ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (hw.1 z hzS) _
    have hsqrt : 0 < Real.sqrt (μ z) := Real.sqrt_pos.2 hμpos
    have hsqrt_mul : Real.sqrt (μ z) =
        Real.sqrt (mX q z.1) * Real.sqrt (mY q z.2) := by
      dsimp [μ]
      exact Real.sqrt_mul (hqX.nonneg z.1) (mY q z.2)
    dsimp [c, F, G]
    rw [show (Real.sqrt (mX q z.1) * |f z.1|) *
        (Real.sqrt (mY q z.2) * |g z.2|) =
        Real.sqrt (μ z) * (|f z.1| * |g z.2|) by rw [hsqrt_mul]; ring]
    field_simp [hwpow.ne', hsqrt.ne']
  have htail_sum_term :
      (∑ z ∈ Tail, w z ^ ((3 : ℝ) / 2) * c z * (F z.1 * G z.2)) =
        ∑ z ∈ Tail, R z := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [htail_term z hz]
    have htailz := (Finset.mem_filter.mp hz).2
    have hdiff0 : 0 ≤ q z - μ z := by linarith [hμ0 z]
    simp [R, abs_of_nonneg hdiff0]
  have hquartic := quartic_bilinear hTailS hw hc0 hF0 hG0 hF2 hG2
  have hcontact_cube : ∀ z ∈ Tail, w z ^ 3 * μ z ^ 2 = q z ^ 3 := by
    intro z hz
    have hzS := hTailS hz
    have htailz := (Finset.mem_filter.mp hz).2
    have hqpos : 0 < q z := lt_of_le_of_lt (mul_nonneg (by norm_num) (hμ0 z)) htailz
    obtain ⟨hxpos, hypos⟩ := joint_pos_marginals hq hqpos
    have hxpow : (mX q z.1 ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = mX q z.1 ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
      norm_num
    have hypow : (mY q z.2 ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = mY q z.2 ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hypos.le]
      norm_num
    rw [hcontact.2.2 z hzS]
    ring_nf
    rw [hxpow, hypow]
    dsimp [μ]
    ring
  have hc4 : ∀ z ∈ Tail,
      w z ^ 3 * c z ^ 4 = (q z - μ z) ^ 4 / q z ^ 3 := by
    intro z hz
    have hzS := hTailS hz
    have htailz := (Finset.mem_filter.mp hz).2
    have hqpos : 0 < q z := lt_of_le_of_lt (mul_nonneg (by norm_num) (hμ0 z)) htailz
    obtain ⟨hxpos, hypos⟩ := joint_pos_marginals hq hqpos
    have hμpos : 0 < μ z := mul_pos hxpos hypos
    have hwpos : 0 < w z := hw.1 z hzS
    have hwpow4 : (w z ^ ((3 : ℝ) / 2)) ^ (4 : ℕ) = w z ^ 6 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hwpos.le]
      norm_num
    have hsqrt4 : (Real.sqrt (μ z)) ^ (4 : ℕ) = μ z ^ 2 := by
      calc
        Real.sqrt (μ z) ^ (4 : ℕ) = (Real.sqrt (μ z) ^ 2) ^ 2 := by ring
        _ = μ z ^ 2 := by rw [Real.sq_sqrt hμpos.le]
    dsimp [c]
    rw [div_pow, mul_pow, hwpow4, hsqrt4]
    have hcube := hcontact_cube z hz
    rw [show w z ^ 6 * μ z ^ 2 = w z ^ 3 * q z ^ 3 by rw [← hcube]; ring]
    field_simp [hwpos.ne', hqpos.ne']
  have htail_cell : ∀ z ∈ Tail,
      w z ^ 3 * c z ^ 4 ≤ ((5062 : ℝ) / 10000) * k z := by
    intro z hz
    have htailz := (Finset.mem_filter.mp hz).2
    have hqpos : 0 < q z := lt_of_le_of_lt (mul_nonneg (by norm_num) (hμ0 z)) htailz
    obtain ⟨hxpos, hypos⟩ := joint_pos_marginals hq hqpos
    have hμpos : 0 < μ z := mul_pos hxpos hypos
    let r : ℝ := q z / μ z
    have hr2 : 2 ≤ r := by
      dsimp [r]
      exact (le_div_iff₀ hμpos).2 (by simpa [mul_comm] using htailz.le)
    have hs := htail r hr2
    have hscaled := mul_le_mul_of_nonneg_left hs (pow_nonneg hμpos.le 4)
    have hqr : μ z * r = q z := by
      dsimp [r]
      field_simp [hμpos.ne']
    have hkz : k z = μ z * (r * Real.log r - r + 1) := by rfl
    have hdiff : q z - μ z = μ z * (r - 1) := by rw [← hqr]; ring
    rw [hc4 z hz]
    apply (div_le_iff₀ (pow_pos hqpos 3)).2
    rw [hdiff, mul_pow]
    calc
      μ z ^ 4 * (r - 1) ^ 4 ≤
          μ z ^ 4 * (((5062 : ℝ) / 10000) *
            (r ^ 3 * (r * Real.log r - r + 1))) := hscaled
      _ = (((5062 : ℝ) / 10000) * k z) * q z ^ 3 := by
        rw [hkz, ← hqr]
        ring
  have htail_moment : (∑ z ∈ Tail, w z ^ 3 * c z ^ 4) ≤
      ((5062 : ℝ) / 10000) * y := by
    calc
      (∑ z ∈ Tail, w z ^ 3 * c z ^ 4) ≤
          ∑ z ∈ Tail, ((5062 : ℝ) / 10000) * k z :=
            Finset.sum_le_sum htail_cell
      _ = ((5062 : ℝ) / 10000) * y := by dsimp [y]; rw [Finset.mul_sum]
  have htail_fourth_nonneg : 0 ≤ ∑ z ∈ Tail, w z ^ 3 * c z ^ 4 := by
    exact Finset.sum_nonneg fun z hz =>
      mul_nonneg (pow_nonneg (hw.1 z (hTailS hz)).le _) (pow_nonneg (hc0 z hz) _)
  have htail_R_nonneg : 0 ≤ ∑ z ∈ Tail, R z := by
    exact Finset.sum_nonneg fun z hz => by dsimp [R]; positivity
  have htail_abs : (∑ z ∈ Tail, R z) ≤
      (((5062 : ℝ) / 10000) * y) ^ ((1 : ℝ) / 4) := by
    rw [htail_sum_term] at hquartic
    have hroot := Real.rpow_le_rpow (pow_nonneg htail_R_nonneg 4)
      hquartic (by norm_num : 0 ≤ (1 : ℝ) / 4)
    have hleft : ((∑ z ∈ Tail, R z) ^ 4) ^ ((1 : ℝ) / 4) =
        ∑ z ∈ Tail, R z := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul htail_R_nonneg]
      norm_num
    rw [hleft] at hroot
    have hroot' := Real.rpow_le_rpow htail_fourth_nonneg htail_moment
      (by norm_num : 0 ≤ (1 : ℝ) / 4)
    exact hroot.trans hroot'

  have hsigned (T : Finset (α × β)) :
      (∑ z ∈ T, (q z - μ z) * f z.1 * g z.2) ≤ ∑ z ∈ T, R z := by
    apply Finset.sum_le_sum
    intro z hz
    calc
      (q z - μ z) * f z.1 * g z.2 ≤ |(q z - μ z) * f z.1 * g z.2| :=
        le_abs_self _
      _ = R z := by dsimp [R]; rw [abs_mul, abs_mul]
  have hcap := hassembly x y hx0 hy0 hxy
  rw [hcorr, hpart (fun z => (q z - μ z) * f z.1 * g z.2)]
  calc
    (∑ z ∈ Bulk, (q z - μ z) * f z.1 * g z.2) +
          ∑ z ∈ Tail, (q z - μ z) * f z.1 * g z.2 ≤
        (∑ z ∈ Bulk, R z) + ∑ z ∈ Tail, R z :=
          add_le_add (hsigned Bulk) (hsigned Tail)
    _ ≤ Real.sqrt (((259 : ℝ) / 100) * x) +
          (((5062 : ℝ) / 10000) * y) ^ ((1 : ℝ) / 4) :=
        add_le_add hbulk_abs htail_abs
    _ ≤ cap := hcap

end stoch_to_det
