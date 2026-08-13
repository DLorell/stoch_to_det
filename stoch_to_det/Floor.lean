import stoch_to_det.Constants
import stoch_to_det.Constants1771
import stoch_to_det.Duality
import stoch_to_det.Toolkit

/-!
# §6. The near-collision information floor


Two theorems:

* `Ixy_ge_hgr_floor` (Thm 6.1, *contact-hgr-information-floor-v2*) — a contact
  with maximal correlation `ρ` has `I_q(X;Y) ≥ 8ρ¹⁰/(729(1+ρ)⁴ ln 2)` bits.
* `nearcollision_floor` (Thm 6.2, *common-contact-explicit-nearcollision-floor*)
  — two *distinct* contacts of one kernel that are within `δ_*` in total
  variation both have `ρ ≥ 1/16`, hence `I ≥ c_*`.

## Scope

The section is entirely finite-dimensional — no probability space, no seed, no
measure theory — and its only input from earlier sections is
`stoch_to_det.Duality.contact_hypercontractive` (Lemma 2.7). It is where `c_*` and `δ_*`
are created, the constants §9 and §10 then spend.

The arguments use real analysis on finite alphabets: singular
vectors of the conditional-expectation operator, interpolation between
`L^{3/2}`, `L²`, `L^{9/4}`, `L³`, a clipping argument, and Pinsker (T2).
Pinsker is `stoch_to_det.Toolkit.pinsker`; Mathlib has no finite bits-valued form of it
(`klDiv` is `ℝ≥0∞`-valued in nats).
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

private noncomputable def moment {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (p : ℝ) (f : ι → ℝ) : ℝ :=
  ∑ i, m i * |f i| ^ p

private noncomputable def normTwo {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (f : ι → ℝ) : ℝ :=
  (moment m 2 f) ^ ((1 : ℝ) / 2)

private noncomputable def normThree {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (f : ι → ℝ) : ℝ :=
  (moment m 3 f) ^ ((1 : ℝ) / 3)

private noncomputable def weightedMean {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (f : ι → ℝ) : ℝ :=
  ∑ i, m i * f i

private noncomputable def centered {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (f : ι → ℝ) : ι → ℝ :=
  fun i => f i - weightedMean m f

private lemma moment_nonneg {ι : Type*} [Fintype ι]
    {m : ι → ℝ} (hm : ∀ i, 0 ≤ m i) (p : ℝ) (f : ι → ℝ) :
    0 ≤ moment m p f := by
  unfold moment
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (Real.rpow_nonneg (abs_nonneg _) _)

private lemma moment_two_eq {ι : Type*} [Fintype ι]
    {m : ι → ℝ} (hm : ∀ i, 0 ≤ m i) (f : ι → ℝ) :
    moment m 2 f = ∑ i, m i * f i ^ 2 := by
  unfold moment
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.rpow_two, sq_abs]

private lemma moment_three_halves_le_one {ι : Type*} [Fintype ι]
    {m : ι → ℝ} (hm : IsPMF m) {f : ι → ℝ} (h2 : moment m 2 f = 1) :
    moment m ((3 : ℝ) / 2) f ≤ 1 := by
  have h := Real.inner_le_weight_mul_Lp_of_nonneg (Finset.univ : Finset ι)
    (p := (4 : ℝ) / 3) (by norm_num) m (fun i => |f i| ^ ((3 : ℝ) / 2))
    hm.nonneg (fun i => Real.rpow_nonneg (abs_nonneg _) _)
  have hsum : ∑ i, m i = 1 := by simpa [mass] using hm.total
  have h2' : ∑ i, m i * f i ^ 2 = 1 := by
    rw [← moment_two_eq hm.nonneg]
    exact h2
  have hpow : ∀ i, (|f i| ^ ((3 : ℝ) / 2)) ^ ((4 : ℝ) / 3) = |f i| ^ (2 : ℝ) := by
    intro i
    rw [← Real.rpow_mul (abs_nonneg _)]
    norm_num
  simp_rw [hpow] at h
  simpa [moment, hsum, h2'] using h

private lemma normTwo_nonneg {ι : Type*} [Fintype ι] {m : ι → ℝ}
    (hm : ∀ i, 0 ≤ m i) (f : ι → ℝ) : 0 ≤ normTwo m f := by
  exact Real.rpow_nonneg (moment_nonneg hm _ _) _

private lemma normThree_nonneg {ι : Type*} [Fintype ι] {m : ι → ℝ}
    (hm : ∀ i, 0 ≤ m i) (f : ι → ℝ) : 0 ≤ normThree m f := by
  exact Real.rpow_nonneg (moment_nonneg hm _ _) _

private lemma normTwo_sq {ι : Type*} [Fintype ι] {m : ι → ℝ}
    (hm : ∀ i, 0 ≤ m i) (f : ι → ℝ) : normTwo m f ^ 2 = moment m 2 f := by
  unfold normTwo
  convert Real.rpow_inv_natCast_pow (moment_nonneg hm _ _) (by norm_num : (2 : ℕ) ≠ 0)
    using 1 <;> norm_num

private lemma normThree_cube {ι : Type*} [Fintype ι] {m : ι → ℝ}
    (hm : ∀ i, 0 ≤ m i) (f : ι → ℝ) : normThree m f ^ 3 = moment m 3 f := by
  unfold normThree
  convert Real.rpow_inv_natCast_pow (moment_nonneg hm _ _) (by norm_num : (3 : ℕ) ≠ 0)
    using 1 <;> norm_num

private lemma weightedMean_centered_eq_zero {ι : Type*} [Fintype ι]
    {m : ι → ℝ} (hm : IsPMF m) (f : ι → ℝ) :
    weightedMean m (centered m f) = 0 := by
  have hmass : ∑ i, m i = 1 := by simpa [mass] using hm.total
  unfold weightedMean centered
  calc
    ∑ i, m i * (f i - ∑ j, m j * f j) =
        (∑ i, m i * f i) - (∑ i, m i) * (∑ j, m j * f j) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = 0 := by rw [hmass]; ring

private lemma normTwo_centered_sq {ι : Type*} [Fintype ι]
    {m : ι → ℝ} (hm : IsPMF m) (f : ι → ℝ) :
    normTwo m (centered m f) ^ 2 = normTwo m f ^ 2 - weightedMean m f ^ 2 := by
  have hmass : ∑ i, m i = 1 := by simpa [mass] using hm.total
  rw [normTwo_sq hm.nonneg, normTwo_sq hm.nonneg,
    moment_two_eq hm.nonneg, moment_two_eq hm.nonneg]
  let μ : ℝ := weightedMean m f
  change (∑ i, m i * (f i - μ) ^ 2) = (∑ i, m i * f i ^ 2) - μ ^ 2
  have hμ : ∑ i, m i * f i = μ := by rfl
  have hsecond : (∑ i, 2 * μ * (m i * f i)) = 2 * μ * (∑ i, m i * f i) := by
    rw [Finset.mul_sum]
  have hthird : (∑ i, μ ^ 2 * m i) = μ ^ 2 * (∑ i, m i) := by
    rw [Finset.mul_sum]
  calc
    ∑ i, m i * (f i - μ) ^ 2 =
        (∑ i, m i * f i ^ 2) - 2 * μ * (∑ i, m i * f i) +
          μ ^ 2 * (∑ i, m i) := by
      have hpoint : ∀ i, m i * (f i - μ) ^ 2 =
          (m i * f i ^ 2 - 2 * μ * (m i * f i)) + μ ^ 2 * m i := by
        intro i
        ring
      simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        hsecond, hthird]
    _ = (∑ i, m i * f i ^ 2) - μ ^ 2 := by rw [hμ, hmass]; ring

private lemma normTwo_le_centered_add_abs_mean {ι : Type*} [Fintype ι]
    {m : ι → ℝ} (hm : IsPMF m) (f : ι → ℝ) :
    normTwo m f ≤ normTwo m (centered m f) + |weightedMean m f| := by
  have hsq := normTwo_centered_sq hm f
  have hf0 := normTwo_nonneg hm.nonneg f
  have hc0 := normTwo_nonneg hm.nonneg (centered m f)
  have hμ0 := abs_nonneg (weightedMean m f)
  have hμsq : |weightedMean m f| ^ 2 = weightedMean m f ^ 2 := sq_abs _
  nlinarith [mul_nonneg hc0 hμ0]

private lemma value_eq_zero_of_moment_three_eq_zero {ι : Type*} [Fintype ι]
    {m : ι → ℝ} (hm : ∀ i, 0 ≤ m i) {f : ι → ℝ}
    (hmom : moment m 3 f = 0) {i : ι} (hmi : m i ≠ 0) : f i = 0 := by
  have hterm : m i * |f i| ^ (3 : ℝ) = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hm j) (Real.rpow_nonneg (abs_nonneg _) _))).mp
    · simpa [moment] using hmom
    · exact Finset.mem_univ i
  have hpow : |f i| ^ (3 : ℝ) = 0 := (mul_eq_zero.mp hterm).resolve_left hmi
  have habs : |f i| = 0 := (Real.rpow_eq_zero (abs_nonneg _) (by norm_num)).mp hpow
  exact abs_eq_zero.mp habs

private lemma abs_le_one_add_inv_of_weighted_sq_sum_eq_one
    {ι : Type*} [Fintype ι] {m : ι → ℝ} (hm : ∀ i, 0 ≤ m i)
    {f : ι → ℝ} (hsq : ∑ i, m i * f i ^ 2 = 1)
    (hzero : ∀ i, m i = 0 → f i = 0) (i : ι) :
    |f i| ≤ 1 + (m i)⁻¹ := by
  by_cases hmi0 : m i = 0
  · simp [hzero i hmi0, hmi0]
  · have hmip : 0 < m i := lt_of_le_of_ne (hm i) (Ne.symm hmi0)
    have hterm : m i * f i ^ 2 ≤ 1 := by
      rw [← hsq]
      exact Finset.single_le_sum (fun j _ => mul_nonneg (hm j) (sq_nonneg _))
        (Finset.mem_univ i)
    have hfinv : f i ^ 2 ≤ (m i)⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hmip).2
      nlinarith
    have hinv0 : 0 ≤ (m i)⁻¹ := inv_nonneg.mpr hmip.le
    by_cases hsmall : |f i| ≤ 1
    · linarith
    · have hone : 1 < |f i| := lt_of_not_ge hsmall
      have habssq : |f i| ≤ |f i| ^ 2 := by nlinarith [abs_nonneg (f i)]
      rw [sq_abs] at habssq
      linarith

private lemma normTwo_le_normThree {ι : Type*} [Fintype ι]
    {m : ι → ℝ} (hm : IsPMF m) (f : ι → ℝ) : normTwo m f ≤ normThree m f := by
  have hholder := Real.inner_le_weight_mul_Lp_of_nonneg (Finset.univ : Finset ι)
    (p := (3 : ℝ) / 2) (by norm_num) m (fun i => |f i| ^ (2 : ℝ))
    hm.nonneg (fun i => Real.rpow_nonneg (abs_nonneg _) _)
  have hsum : ∑ i, m i = 1 := by simpa [mass] using hm.total
  have hpow : ∀ i, (|f i| ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) = |f i| ^ (3 : ℝ) := by
    intro i
    rw [← Real.rpow_mul (abs_nonneg _)]
    norm_num
  simp_rw [hpow] at hholder
  have hmom : moment m 2 f ≤ (moment m 3 f) ^ ((2 : ℝ) / 3) := by
    simpa [moment, hsum] using hholder
  have hp := Real.rpow_le_rpow (moment_nonneg hm.nonneg _ _) hmom
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  unfold normTwo normThree
  calc
    (moment m 2 f) ^ ((1 : ℝ) / 2)
        ≤ ((moment m 3 f) ^ ((2 : ℝ) / 3)) ^ ((1 : ℝ) / 2) := hp
    _ = (moment m 3 f) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_mul (moment_nonneg hm.nonneg _ _)]
      norm_num

private lemma norm_three_halves_le_normTwo {ι : Type*} [Fintype ι]
    {m : ι → ℝ} (hm : IsPMF m) (f : ι → ℝ) :
    (moment m ((3 : ℝ) / 2) f) ^ ((2 : ℝ) / 3) ≤ normTwo m f := by
  have hholder := Real.inner_le_weight_mul_Lp_of_nonneg (Finset.univ : Finset ι)
    (p := (4 : ℝ) / 3) (by norm_num) m (fun i => |f i| ^ ((3 : ℝ) / 2))
    hm.nonneg (fun i => Real.rpow_nonneg (abs_nonneg _) _)
  have hsum : ∑ i, m i = 1 := by simpa [mass] using hm.total
  have hpow : ∀ i, (|f i| ^ ((3 : ℝ) / 2)) ^ ((4 : ℝ) / 3) =
      |f i| ^ (2 : ℝ) := by
    intro i
    rw [← Real.rpow_mul (abs_nonneg _)]
    norm_num
  simp_rw [hpow] at hholder
  have hmom : moment m ((3 : ℝ) / 2) f ≤ (moment m 2 f) ^ ((3 : ℝ) / 4) := by
    simpa [moment, hsum] using hholder
  have hp := Real.rpow_le_rpow (moment_nonneg hm.nonneg _ _) hmom
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  unfold normTwo
  calc
    (moment m ((3 : ℝ) / 2) f) ^ ((2 : ℝ) / 3)
        ≤ ((moment m 2 f) ^ ((3 : ℝ) / 4)) ^ ((2 : ℝ) / 3) := hp
    _ = (moment m 2 f) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul (moment_nonneg hm.nonneg _ _)]
      norm_num

private lemma moment_nine_fourths_interpolate {ι : Type*} [Fintype ι]
    {m : ι → ℝ} (hm : ∀ i, 0 ≤ m i) (f : ι → ℝ) :
    moment m ((9 : ℝ) / 4) f
      ≤ (moment m 2 f) ^ ((3 : ℝ) / 4) * (moment m 3 f) ^ ((1 : ℝ) / 4) := by
  let A : ι → ℝ := fun i => (m i * |f i| ^ (2 : ℝ)) ^ ((3 : ℝ) / 4)
  let B : ι → ℝ := fun i => (m i * |f i| ^ (3 : ℝ)) ^ ((1 : ℝ) / 4)
  have hpq : ((4 : ℝ) / 3).HolderConjugate 4 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hA0 : ∀ i, 0 ≤ A i := fun i => Real.rpow_nonneg
    (mul_nonneg (hm i) (Real.rpow_nonneg (abs_nonneg _) _)) _
  have hB0 : ∀ i, 0 ≤ B i := fun i => Real.rpow_nonneg
    (mul_nonneg (hm i) (Real.rpow_nonneg (abs_nonneg _) _)) _
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := (Finset.univ : Finset ι)) (f := A) (g := B) hpq
    (fun i _ => hA0 i) (fun i _ => hB0 i)
  have hprod : ∀ i, A i * B i = m i * |f i| ^ ((9 : ℝ) / 4) := by
    intro i
    have hmi := hm i
    have hfi : 0 ≤ |f i| := abs_nonneg _
    dsimp [A, B]
    rw [Real.mul_rpow hmi (Real.rpow_nonneg hfi _),
      Real.mul_rpow hmi (Real.rpow_nonneg hfi _)]
    rw [← Real.rpow_mul hfi, ← Real.rpow_mul hfi]
    calc
      (m i ^ ((3 : ℝ) / 4) * |f i| ^ ((2 : ℝ) * (3 / 4))) *
          (m i ^ ((1 : ℝ) / 4) * |f i| ^ ((3 : ℝ) * (1 / 4))) =
          (m i ^ ((3 : ℝ) / 4) * m i ^ ((1 : ℝ) / 4)) *
            (|f i| ^ ((2 : ℝ) * (3 / 4)) * |f i| ^ ((3 : ℝ) * (1 / 4))) := by ring
      _ = m i * |f i| ^ ((9 : ℝ) / 4) := by
        rw [← Real.rpow_add' hmi (by norm_num : (3 : ℝ) / 4 + 1 / 4 ≠ 0),
          ← Real.rpow_add' hfi
            (by norm_num : (2 : ℝ) * (3 / 4) + 3 * (1 / 4) ≠ 0)]
        norm_num
  have hApow : ∀ i, A i ^ ((4 : ℝ) / 3) = m i * |f i| ^ (2 : ℝ) := by
    intro i
    dsimp [A]
    rw [← Real.rpow_mul (mul_nonneg (hm i) (Real.rpow_nonneg (abs_nonneg _) _))]
    norm_num
  have hBpow : ∀ i, B i ^ (4 : ℝ) = m i * |f i| ^ (3 : ℝ) := by
    intro i
    dsimp [B]
    rw [← Real.rpow_mul (mul_nonneg (hm i) (Real.rpow_nonneg (abs_nonneg _) _))]
    norm_num
  simp_rw [hprod] at hholder
  simp_rw [hApow, hBpow] at hholder
  simpa [moment] using hholder

private lemma sum_eq_sum_support {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {S : Finset (ι × κ)} {m : ι × κ → ℝ} (hm : Supported S m) (F : ι × κ → ℝ) :
    (∑ i, m i * F i) = ∑ i ∈ S, m i * F i := by
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro i _ hi
  simp [hm i hi]

private lemma product_isPMF {ι κ : Type*} [Fintype ι] [Fintype κ]
    {u : ι → ℝ} {v : κ → ℝ} (hu : IsPMF u) (hv : IsPMF v) :
    IsPMF (fun z : ι × κ => u z.1 * v z.2) := by
  refine ⟨fun z => mul_nonneg (hu.nonneg z.1) (hv.nonneg z.2), ?_⟩
  have hu_sum : ∑ i, u i = 1 := by simpa [mass] using hu.total
  have hv_sum : ∑ k, v k = 1 := by simpa [mass] using hv.total
  rw [mass, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [hv_sum]
  simpa using hu_sum

private lemma abs_expectation_sub_le_tv {ι : Type*} [Fintype ι]
    {P Q : ι → ℝ} {F : ι → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ i, |F i| ≤ B) :
    |(∑ i, P i * F i) - ∑ i, Q i * F i| ≤ 2 * B * tvDist P Q := by
  rw [tvDist]
  calc
    |(∑ i, P i * F i) - ∑ i, Q i * F i|
        = |∑ i, (P i - Q i) * F i| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, |(P i - Q i) * F i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |P i - Q i| * |F i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul]
    _ ≤ ∑ i, |P i - Q i| * B := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hF i) (abs_nonneg _)
    _ = 2 * B * ((∑ i, |P i - Q i|) / 2) := by
      rw [← Finset.sum_mul]
      ring

private lemma abs_le_rpow_three_halves_div {z t : ℝ} (ht : 0 < t)
    (hzt : t ^ 2 ≤ |z|) : |z| ≤ |z| ^ ((3 : ℝ) / 2) / t := by
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hsqrt : t ≤ Real.sqrt |z| := by
    have hsqrt0 : 0 ≤ Real.sqrt |z| := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt |z|) ^ 2 = |z| := Real.sq_sqrt hz0
    nlinarith
  apply (le_div_iff₀ ht).2
  calc
    |z| * t ≤ |z| * Real.sqrt |z| := mul_le_mul_of_nonneg_left hsqrt hz0
    _ = |z| ^ ((3 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      symm
      convert Real.rpow_one_add' hz0 (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0) using 1 <;>
        norm_num

private lemma clipping_error_le {z t : ℝ} (ht : 0 < t) :
    |z - max (-(t ^ 2)) (min (t ^ 2) z)|
      ≤ |z| ^ ((3 : ℝ) / 2) / t := by
  have hB : 0 ≤ t ^ 2 := sq_nonneg t
  by_cases hlo : z < -(t ^ 2)
  · have hzB : z ≤ t ^ 2 := by linarith
    have hz0 : z < 0 := lt_of_lt_of_le hlo (neg_nonpos.mpr hB)
    have htail : t ^ 2 ≤ |z| := by rw [abs_of_neg hz0]; linarith
    rw [min_eq_right hzB, max_eq_left hlo.le, abs_of_neg (by linarith : z - -(t ^ 2) < 0)]
    calc
      -(z - -(t ^ 2)) ≤ |z| := by rw [abs_of_neg hz0]; linarith
      _ ≤ |z| ^ ((3 : ℝ) / 2) / t := abs_le_rpow_three_halves_div ht htail
  · have hlo' : -(t ^ 2) ≤ z := le_of_not_gt hlo
    by_cases hhi : t ^ 2 < z
    · have hz0 : 0 < z := lt_of_le_of_lt hB hhi
      have htail : t ^ 2 ≤ |z| := by rw [abs_of_pos hz0]; exact hhi.le
      rw [min_eq_left hhi.le, max_eq_right (by linarith : -(t ^ 2) ≤ t ^ 2),
        abs_of_pos (by linarith : 0 < z - t ^ 2)]
      calc
        z - t ^ 2 ≤ |z| := by rw [abs_of_pos hz0]; linarith
        _ ≤ |z| ^ ((3 : ℝ) / 2) / t := abs_le_rpow_three_halves_div ht htail
    · have hhi' : z ≤ t ^ 2 := le_of_not_gt hhi
      rw [min_eq_right hhi', max_eq_right hlo', sub_self, abs_zero]
      exact div_nonneg (Real.rpow_nonneg (abs_nonneg z) _) ht.le

private lemma abs_weighted_clipping_error_le {ι : Type*} [Fintype ι]
    {P : ι → ℝ} (hP : ∀ i, 0 ≤ P i) {Z : ι → ℝ} {t : ℝ} (ht : 0 < t) :
    |∑ i, P i * (Z i - max (-(t ^ 2)) (min (t ^ 2) (Z i)))|
      ≤ moment P ((3 : ℝ) / 2) Z / t := by
  calc
    |∑ i, P i * (Z i - max (-(t ^ 2)) (min (t ^ 2) (Z i)))|
        ≤ ∑ i, |P i * (Z i - max (-(t ^ 2)) (min (t ^ 2) (Z i)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, P i * |Z i - max (-(t ^ 2)) (min (t ^ 2) (Z i))| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hP i)]
    _ ≤ ∑ i, P i * (|Z i| ^ ((3 : ℝ) / 2) / t) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (clipping_error_le ht) (hP i)
    _ = ∑ i, (P i * |Z i| ^ ((3 : ℝ) / 2)) / t := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = moment P ((3 : ℝ) / 2) Z / t := by rw [← Finset.sum_div]; rfl

private lemma abs_clip_le {z B : ℝ} (hB : 0 ≤ B) :
    |max (-B) (min B z)| ≤ B := by
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · apply max_le
    · exact neg_le_self hB
    · exact min_le_left _ _

private lemma le_inv_cube_of_mul_le_rpow_two_thirds {ρ A : ℝ}
    (hρ : 0 < ρ) (hA : 0 ≤ A) (h : ρ * A ≤ A ^ ((2 : ℝ) / 3)) :
    A ≤ ρ⁻¹ ^ 3 := by
  rcases hA.eq_or_lt with rfl | hApos
  · positivity
  · have hsplit : A = A ^ ((2 : ℝ) / 3) * A ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_add' hApos.le (by norm_num : (2 : ℝ) / 3 + 1 / 3 ≠ 0)]
      norm_num
    have hfac : 0 < A ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hApos _
    have hcancel :
        A ^ ((2 : ℝ) / 3) * (ρ * A ^ ((1 : ℝ) / 3))
          ≤ A ^ ((2 : ℝ) / 3) * 1 := by
      calc
        A ^ ((2 : ℝ) / 3) * (ρ * A ^ ((1 : ℝ) / 3))
            = ρ * (A ^ ((2 : ℝ) / 3) * A ^ ((1 : ℝ) / 3)) := by ring
        _ = ρ * A := by rw [← hsplit]
        _ ≤ A ^ ((2 : ℝ) / 3) := h
        _ = A ^ ((2 : ℝ) / 3) * 1 := by ring
    have hroot_mul : ρ * A ^ ((1 : ℝ) / 3) ≤ 1 := by
      have hc := le_of_mul_le_mul_left hcancel hfac
      simpa [mul_comm] using hc
    have hroot : A ^ ((1 : ℝ) / 3) ≤ ρ⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hρ).2
      simpa [mul_comm] using hroot_mul
    have hcubes : (A ^ ((1 : ℝ) / 3)) ^ 3 ≤ ρ⁻¹ ^ 3 := by
      exact pow_le_pow_left₀ (Real.rpow_nonneg hA _) hroot 3
    have hroot_cube : (A ^ ((1 : ℝ) / 3)) ^ 3 = A := by
      convert Real.rpow_inv_natCast_pow hA (by norm_num : (3 : ℕ) ≠ 0) using 1 <;>
        norm_num
    rwa [hroot_cube] at hcubes

private lemma mX_eq_sum (q : α × β → ℝ) (x : α) : mX q x = ∑ y, q (x, y) := by
  change push Prod.fst q x = ∑ y, q (x, y)
  unfold push
  rw [show (Finset.univ.filter fun a : α × β => a.1 = x) =
      Finset.univ.image fun y : β => (x, y) by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hz
      exact ⟨z.2, by ext <;> simp [hz]⟩
    · rintro ⟨y, rfl⟩
      rfl]
  rw [Finset.sum_image]
  intro y₁ _ y₂ _ h
  exact congrArg Prod.snd h

private lemma mY_eq_sum (q : α × β → ℝ) (y : β) : mY q y = ∑ x, q (x, y) := by
  change push Prod.snd q y = ∑ x, q (x, y)
  unfold push
  rw [show (Finset.univ.filter fun a : α × β => a.2 = y) =
      Finset.univ.image fun x : α => (x, y) by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hz
      exact ⟨z.1, by ext <;> simp [hz]⟩
    · rintro ⟨x, rfl⟩
      rfl]
  rw [Finset.sum_image]
  intro x₁ _ x₂ _ h
  exact congrArg Prod.fst h

private lemma abs_rpow_one_third_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a ^ ((1 : ℝ) / 3) - b ^ ((1 : ℝ) / 3)| ^ 3 ≤ |a - b| := by
  let s : ℝ := a ^ ((1 : ℝ) / 3)
  let t : ℝ := b ^ ((1 : ℝ) / 3)
  have hs : 0 ≤ s := Real.rpow_nonneg ha _
  have ht : 0 ≤ t := Real.rpow_nonneg hb _
  have hs3 : s ^ 3 = a := by
    dsimp [s]
    convert Real.rpow_inv_natCast_pow ha (by norm_num : (3 : ℕ) ≠ 0) using 1 <;>
      norm_num
  have ht3 : t ^ 3 = b := by
    dsimp [t]
    convert Real.rpow_inv_natCast_pow hb (by norm_num : (3 : ℕ) ≠ 0) using 1 <;>
      norm_num
  change |s - t| ^ 3 ≤ |a - b|
  rcases le_total t s with hts | hst
  · have hba : b ≤ a := by
      rw [← ht3, ← hs3]
      exact pow_le_pow_left₀ ht hts 3
    rw [abs_of_nonneg (sub_nonneg.mpr hts), abs_of_nonneg (sub_nonneg.mpr hba)]
    rw [← hs3, ← ht3]
    nlinarith [mul_nonneg (mul_nonneg (by nlinarith : 0 ≤ 3 * s) ht) (sub_nonneg.mpr hts)]
  · have hab : a ≤ b := by
      rw [← hs3, ← ht3]
      exact pow_le_pow_left₀ hs hst 3
    rw [abs_of_nonpos (sub_nonpos.mpr hst), abs_of_nonpos (sub_nonpos.mpr hab)]
    rw [← hs3, ← ht3]
    nlinarith [mul_nonneg (mul_nonneg (by nlinarith : 0 ≤ 3 * t) hs) (sub_nonneg.mpr hst)]

private lemma sum_abs_mX_sub_le (q r : α × β → ℝ) :
    (∑ x, |mX r x - mX q x|) ≤ ∑ z, |r z - q z| := by
  calc
    (∑ x, |mX r x - mX q x|)
        = ∑ x, |∑ y, (r (x, y) - q (x, y))| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [mX_eq_sum r x, mX_eq_sum q x, ← Finset.sum_sub_distrib]
    _ ≤ ∑ x, ∑ y, |r (x, y) - q (x, y)| := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, |r z - q z| := by rw [Fintype.sum_prod_type]

private lemma sum_abs_mY_sub_le (q r : α × β → ℝ) :
    (∑ y, |mY r y - mY q y|) ≤ ∑ z, |r z - q z| := by
  calc
    (∑ y, |mY r y - mY q y|)
        = ∑ y, |∑ x, (r (x, y) - q (x, y))| := by
      apply Finset.sum_congr rfl
      intro y _
      rw [mY_eq_sum r y, mY_eq_sum q y, ← Finset.sum_sub_distrib]
    _ ≤ ∑ y, ∑ x, |r (x, y) - q (x, y)| := by
      apply Finset.sum_le_sum
      intro y _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, |r z - q z| := by rw [Fintype.sum_prod_type, Finset.sum_comm]

private lemma mX_zero_of_support_eq {q r : α × β → ℝ}
    (hq : IsPMF q) (hr : IsPMF r) (hs : support q = support r) {x : α}
    (hx : mX q x = 0) : mX r x = 0 := by
  rw [mX_eq_sum]
  apply Finset.sum_eq_zero
  intro y _
  have hqxy : q (x, y) = 0 := by
    apply le_antisymm
    · have hle : q (x, y) ≤ mX q x := by
        rw [mX_eq_sum]
        exact Finset.single_le_sum (fun y _ => hq.nonneg (x, y)) (Finset.mem_univ y)
      simpa [hx] using hle
    · exact hq.nonneg _
  have hnotq : (x, y) ∉ support q := by simp [support, hqxy]
  have hnotr : (x, y) ∉ support r := by simpa [hs] using hnotq
  simpa [support] using hnotr

private lemma mX_zero_iff_of_support_eq {q r : α × β → ℝ}
    (hq : IsPMF q) (hr : IsPMF r) (hs : support q = support r) (x : α) :
    mX q x = 0 ↔ mX r x = 0 := by
  exact ⟨mX_zero_of_support_eq hq hr hs,
    mX_zero_of_support_eq hr hq hs.symm⟩

private lemma mY_zero_of_support_eq {q r : α × β → ℝ}
    (hq : IsPMF q) (hr : IsPMF r) (hs : support q = support r) {y : β}
    (hy : mY q y = 0) : mY r y = 0 := by
  rw [mY_eq_sum]
  apply Finset.sum_eq_zero
  intro x _
  have hqxy : q (x, y) = 0 := by
    apply le_antisymm
    · have hle : q (x, y) ≤ mY q y := by
        rw [mY_eq_sum]
        exact Finset.single_le_sum (fun x _ => hq.nonneg (x, y)) (Finset.mem_univ x)
      simpa [hy] using hle
    · exact hq.nonneg _
  have hnotq : (x, y) ∉ support q := by simp [support, hqxy]
  have hnotr : (x, y) ∉ support r := by simpa [hs] using hnotq
  simpa [support] using hnotr

private lemma mY_zero_iff_of_support_eq {q r : α × β → ℝ}
    (hq : IsPMF q) (hr : IsPMF r) (hs : support q = support r) (y : β) :
    mY q y = 0 ↔ mY r y = 0 := by
  exact ⟨mY_zero_of_support_eq hq hr hs,
    mY_zero_of_support_eq hr hq hs.symm⟩

private lemma mul_ratio_rpow_one_third_cube {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hzero : b = 0 ↔ a = 0) :
    b * ((a / b) ^ ((1 : ℝ) / 3)) ^ 3 = a := by
  by_cases hb0 : b = 0
  · have ha0 := hzero.mp hb0
    simp [hb0, ha0]
  · have hratio : 0 ≤ a / b := div_nonneg ha hb
    have hcube : ((a / b) ^ ((1 : ℝ) / 3)) ^ 3 = a / b := by
      convert Real.rpow_inv_natCast_pow hratio (by norm_num : (3 : ℕ) ≠ 0) using 1 <;>
        norm_num
    rw [hcube]
    field_simp

private lemma ratio_root_mean_bound {ι : Type*} [Fintype ι]
    {m n : ι → ℝ} (hm : IsPMF m) (hn : IsPMF n)
    (hzero : ∀ i, m i = 0 ↔ n i = 0) :
    |weightedMean m (fun i => (n i / m i) ^ ((1 : ℝ) / 3) - 1)| ≤
      normTwo m (fun i => (n i / m i) ^ ((1 : ℝ) / 3) - 1) ^ 2 +
        normThree m (fun i => (n i / m i) ^ ((1 : ℝ) / 3) - 1) ^ 3 / 3 := by
  let f : ι → ℝ := fun i => (n i / m i) ^ ((1 : ℝ) / 3) - 1
  let μ : ℝ := weightedMean m f
  let A₂ : ℝ := ∑ i, m i * f i ^ 2
  let C₃ : ℝ := ∑ i, m i * f i ^ 3
  have hmassm : ∑ i, m i = 1 := by simpa [mass] using hm.total
  have hmassn : ∑ i, n i = 1 := by simpa [mass] using hn.total
  have hcube : ∑ i, m i * (1 + f i) ^ 3 = 1 := by
    calc
      ∑ i, m i * (1 + f i) ^ 3 = ∑ i, n i := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := mul_ratio_rpow_one_third_cube (hn.nonneg i) (hm.nonneg i)
          (hzero i)
        dsimp [f]
        convert hi using 1 <;> ring
      _ = 1 := hmassn
  have hexpand : 3 * μ + 3 * A₂ + C₃ = 0 := by
    have hpoint : ∀ i, m i * (1 + f i) ^ 3 =
        m i + 3 * (m i * f i) + 3 * (m i * f i ^ 2) + m i * f i ^ 3 := by
      intro i
      ring
    have hsum : (∑ i, m i * (1 + f i) ^ 3) =
        (∑ i, m i) + 3 * (∑ i, m i * f i) +
          3 * (∑ i, m i * f i ^ 2) + ∑ i, m i * f i ^ 3 := by
      simp_rw [hpoint, Finset.sum_add_distrib, Finset.mul_sum]
    dsimp [μ, weightedMean, A₂, C₃]
    rw [hcube, hmassm] at hsum
    linarith
  have hC₃ : |C₃| ≤ moment m 3 f := by
    calc
      |C₃| ≤ ∑ i, |m i * f i ^ 3| := by
        dsimp [C₃]
        exact Finset.abs_sum_le_sum_abs _ _
      _ = moment m 3 f := by
        unfold moment
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_nonneg (hm.nonneg i), abs_pow, Real.rpow_ofNat]
  have hA₂0 : 0 ≤ A₂ := by
    dsimp [A₂]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hm.nonneg i) (sq_nonneg _)
  have hmean : |μ| ≤ A₂ + moment m 3 f / 3 := by
    have hμeq : μ = -A₂ - C₃ / 3 := by linarith
    rw [hμeq]
    calc
      |-A₂ - C₃ / 3| ≤ |-A₂| + |-C₃ / 3| := by
        simpa [sub_eq_add_neg, neg_div] using abs_add_le (-A₂) (-C₃ / 3)
      _ = A₂ + |C₃| / 3 := by
        rw [abs_neg, abs_of_nonneg hA₂0, abs_div, abs_neg]
        norm_num
      _ ≤ A₂ + moment m 3 f / 3 := by linarith
  have htwo := normTwo_sq hm.nonneg f
  have hthree := normThree_cube hm.nonneg f
  simpa [f, μ, A₂, moment_two_eq hm.nonneg] using
    (show |μ| ≤ normTwo m f ^ 2 + normThree m f ^ 3 / 3 by
      rw [htwo, hthree, moment_two_eq hm.nonneg]
      exact hmean)

private lemma contact_ratio_eq {S : Finset (α × β)} {w q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r)
    (hqs : support q = S) (hrs : support r = S) :
    ∀ z, r z = q z *
      ((mX r z.1 / mX q z.1) ^ ((1 : ℝ) / 3)) ^ 2 *
      ((mY r z.2 / mY q z.2) ^ ((1 : ℝ) / 3)) ^ 2 := by
  intro z
  by_cases hz : z ∈ S
  · have hqmem : z ∈ support q := by simpa [hqs] using hz
    have hrmem : z ∈ support r := by simpa [hrs] using hz
    have hqne : q z ≠ 0 := by simpa [support] using hqmem
    have hrne : r z ≠ 0 := by simpa [support] using hrmem
    have hqpos : 0 < q z := lt_of_le_of_ne (hq.1.nonneg z) (Ne.symm hqne)
    have hrpos : 0 < r z := lt_of_le_of_ne (hr.1.nonneg z) (Ne.symm hrne)
    have hqxpos : 0 < mX q z.1 := by
      have hle : q z ≤ mX q z.1 := by
        rw [mX_eq_sum]
        exact Finset.single_le_sum (fun y _ => hq.1.nonneg (z.1, y)) (Finset.mem_univ z.2)
      exact lt_of_lt_of_le hqpos hle
    have hqypos : 0 < mY q z.2 := by
      have hle : q z ≤ mY q z.2 := by
        rw [mY_eq_sum]
        exact Finset.single_le_sum (fun x _ => hq.1.nonneg (x, z.2)) (Finset.mem_univ z.1)
      exact lt_of_lt_of_le hqpos hle
    have hrxpos : 0 < mX r z.1 := by
      have hle : r z ≤ mX r z.1 := by
        rw [mX_eq_sum]
        exact Finset.single_le_sum (fun y _ => hr.1.nonneg (z.1, y)) (Finset.mem_univ z.2)
      exact lt_of_lt_of_le hrpos hle
    have hrypos : 0 < mY r z.2 := by
      have hle : r z ≤ mY r z.2 := by
        rw [mY_eq_sum]
        exact Finset.single_le_sum (fun x _ => hr.1.nonneg (x, z.2)) (Finset.mem_univ z.1)
      exact lt_of_lt_of_le hrpos hle
    have hratioX : 0 ≤ mX r z.1 / mX q z.1 := div_nonneg hrxpos.le hqxpos.le
    have hratioY : 0 ≤ mY r z.2 / mY q z.2 := div_nonneg hrypos.le hqypos.le
    have hF2 : ((mX r z.1 / mX q z.1) ^ ((1 : ℝ) / 3)) ^ 2 =
        (mX r z.1 / mX q z.1) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hratioX]
      norm_num
    have hG2 : ((mY r z.2 / mY q z.2) ^ ((1 : ℝ) / 3)) ^ 2 =
        (mY r z.2 / mY q z.2) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hratioY]
      norm_num
    have hcombineX : mX q z.1 ^ ((2 : ℝ) / 3) *
        (mX r z.1 / mX q z.1) ^ ((2 : ℝ) / 3) =
        mX r z.1 ^ ((2 : ℝ) / 3) := by
      rw [← Real.mul_rpow hqxpos.le hratioX]
      congr 1
      field_simp
    have hcombineY : mY q z.2 ^ ((2 : ℝ) / 3) *
        (mY r z.2 / mY q z.2) ^ ((2 : ℝ) / 3) =
        mY r z.2 ^ ((2 : ℝ) / 3) := by
      rw [← Real.mul_rpow hqypos.le hratioY]
      congr 1
      field_simp
    rw [hF2, hG2]
    calc
      r z = w z * mX r z.1 ^ ((2 : ℝ) / 3) * mY r z.2 ^ ((2 : ℝ) / 3) :=
        hr.2.2 z hz
      _ = (w z * mX q z.1 ^ ((2 : ℝ) / 3) * mY q z.2 ^ ((2 : ℝ) / 3)) *
          (mX r z.1 / mX q z.1) ^ ((2 : ℝ) / 3) *
          (mY r z.2 / mY q z.2) ^ ((2 : ℝ) / 3) := by
        rw [← hcombineX, ← hcombineY]
        ring
      _ = q z * (mX r z.1 / mX q z.1) ^ ((2 : ℝ) / 3) *
          (mY r z.2 / mY q z.2) ^ ((2 : ℝ) / 3) := by rw [← hq.2.2 z hz]
  · rw [hq.2.1 z hz, hr.2.1 z hz]
    simp

private lemma secant_equations {S : Finset (α × β)} {w q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r)
    (hqs : support q = S) (hrs : support r = S) :
    (∀ x, (∑ y, q (x, y) *
        ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2) =
      mX q x * (mX r x / mX q x) ^ ((1 : ℝ) / 3)) ∧
    (∀ y, (∑ x, q (x, y) *
        ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2) =
      mY q y * (mY r y / mY q y) ^ ((1 : ℝ) / 3)) := by
  have hsqr : support q = support r := hqs.trans hrs.symm
  have hratio := contact_ratio_eq hq hr hqs hrs
  constructor
  · intro x
    by_cases hqx0 : mX q x = 0
    · have hrx0 := (mX_zero_iff_of_support_eq hq.1 hr.1 hsqr x).mp hqx0
      have hrowzero : ∑ y, q (x, y) *
          ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro y _
        have hqxy : q (x, y) = 0 := by
          apply le_antisymm
          · have hle : q (x, y) ≤ mX q x := by
              rw [mX_eq_sum]
              exact Finset.single_le_sum (fun y _ => hq.1.nonneg (x, y)) (Finset.mem_univ y)
            simpa [hqx0] using hle
          · exact hq.1.nonneg _
        simp [hqxy]
      rw [hrowzero, hqx0, hrx0]
      simp
    · have hqxpos : 0 < mX q x :=
        lt_of_le_of_ne ((isPMF_push hq.1).nonneg x) (Ne.symm hqx0)
      have hrx0iff := mX_zero_iff_of_support_eq hq.1 hr.1 hsqr x
      have hrxne : mX r x ≠ 0 := fun h => hqx0 (hrx0iff.mpr h)
      have hrxpos : 0 < mX r x :=
        lt_of_le_of_ne ((isPMF_push hr.1).nonneg x) (Ne.symm hrxne)
      let F : ℝ := (mX r x / mX q x) ^ ((1 : ℝ) / 3)
      have hFpos : 0 < F := Real.rpow_pos_of_pos (div_pos hrxpos hqxpos) _
      have hrow : mX r x = F ^ 2 * (∑ y, q (x, y) *
          ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2) := by
        rw [mX_eq_sum]
        calc
          ∑ y, r (x, y) = ∑ y, q (x, y) * F ^ 2 *
              ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro y _
            simpa [F] using hratio (x, y)
          _ = F ^ 2 * (∑ y, q (x, y) *
              ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
      have hcube : mX q x * F ^ 3 = mX r x := by
        dsimp [F]
        exact mul_ratio_rpow_one_third_cube hrxpos.le hqxpos.le hrx0iff
      apply mul_left_cancel₀ (pow_ne_zero 2 hFpos.ne')
      calc
        F ^ 2 * (∑ y, q (x, y) *
            ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2) = mX r x := hrow.symm
        _ = mX q x * F ^ 3 := hcube.symm
        _ = F ^ 2 * (mX q x * (mX r x / mX q x) ^ ((1 : ℝ) / 3)) := by
          dsimp [F]
          ring
  · intro y
    by_cases hqy0 : mY q y = 0
    · have hry0 := (mY_zero_iff_of_support_eq hq.1 hr.1 hsqr y).mp hqy0
      have hcolzero : ∑ x, q (x, y) *
          ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        have hqxy : q (x, y) = 0 := by
          apply le_antisymm
          · have hle : q (x, y) ≤ mY q y := by
              rw [mY_eq_sum]
              exact Finset.single_le_sum (fun x _ => hq.1.nonneg (x, y)) (Finset.mem_univ x)
            simpa [hqy0] using hle
          · exact hq.1.nonneg _
        simp [hqxy]
      rw [hcolzero, hqy0, hry0]
      simp
    · have hqypos : 0 < mY q y :=
        lt_of_le_of_ne ((isPMF_push hq.1).nonneg y) (Ne.symm hqy0)
      have hry0iff := mY_zero_iff_of_support_eq hq.1 hr.1 hsqr y
      have hryne : mY r y ≠ 0 := fun h => hqy0 (hry0iff.mpr h)
      have hrypos : 0 < mY r y :=
        lt_of_le_of_ne ((isPMF_push hr.1).nonneg y) (Ne.symm hryne)
      let G : ℝ := (mY r y / mY q y) ^ ((1 : ℝ) / 3)
      have hGpos : 0 < G := Real.rpow_pos_of_pos (div_pos hrypos hqypos) _
      have hcol : mY r y = G ^ 2 * (∑ x, q (x, y) *
          ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2) := by
        rw [mY_eq_sum]
        calc
          ∑ x, r (x, y) = ∑ x, q (x, y) *
              ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2 * G ^ 2 := by
            apply Finset.sum_congr rfl
            intro x _
            simpa [G] using hratio (x, y)
          _ = G ^ 2 * (∑ x, q (x, y) *
              ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
      have hcube : mY q y * G ^ 3 = mY r y := by
        dsimp [G]
        exact mul_ratio_rpow_one_third_cube hrypos.le hqypos.le hry0iff
      apply mul_left_cancel₀ (pow_ne_zero 2 hGpos.ne')
      calc
        G ^ 2 * (∑ x, q (x, y) *
            ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2) = mY r y := hcol.symm
        _ = mY q y * G ^ 3 := hcube.symm
        _ = G ^ 2 * (mY q y * (mY r y / mY q y) ^ ((1 : ℝ) / 3)) := by
          dsimp [G]
          ring

private lemma ratio_root_smallness {q r : α × β → ℝ}
    (hq : IsPMF q) (hr : IsPMF r) (hs : support q = support r) :
    moment (mX q) 3 (fun x => (mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1)
        ≤ 2 * tvDist q r ∧
    moment (mY q) 3 (fun y => (mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1)
        ≤ 2 * tvDist q r := by
  have hXpoint : ∀ x, mX q x *
      |(mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1| ^ (3 : ℝ)
        ≤ |mX r x - mX q x| := by
    intro x
    by_cases hqx0 : mX q x = 0
    · simp [hqx0]
    · have hqxpos : 0 < mX q x :=
        lt_of_le_of_ne ((isPMF_push hq).nonneg x) (Ne.symm hqx0)
      have hrx0iff := mX_zero_iff_of_support_eq hq hr hs x
      have hrx0 : 0 ≤ mX r x := (isPMF_push hr).nonneg x
      have hscalar := abs_rpow_one_third_sub_le
        (div_nonneg hrx0 hqxpos.le) (by norm_num : (0 : ℝ) ≤ 1)
      rw [Real.one_rpow] at hscalar
      rw [Real.rpow_ofNat]
      calc
        mX q x * |(mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1| ^ 3
            ≤ mX q x * |mX r x / mX q x - 1| :=
          mul_le_mul_of_nonneg_left hscalar hqxpos.le
        _ = |mX r x - mX q x| := by
          rw [show mX r x / mX q x - 1 = (mX r x - mX q x) / mX q x by
            field_simp]
          rw [abs_div, abs_of_pos hqxpos]
          field_simp
  have hYpoint : ∀ y, mY q y *
      |(mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1| ^ (3 : ℝ)
        ≤ |mY r y - mY q y| := by
    intro y
    by_cases hqy0 : mY q y = 0
    · simp [hqy0]
    · have hqypos : 0 < mY q y :=
        lt_of_le_of_ne ((isPMF_push hq).nonneg y) (Ne.symm hqy0)
      have hry0 : 0 ≤ mY r y := (isPMF_push hr).nonneg y
      have hscalar := abs_rpow_one_third_sub_le
        (div_nonneg hry0 hqypos.le) (by norm_num : (0 : ℝ) ≤ 1)
      rw [Real.one_rpow] at hscalar
      rw [Real.rpow_ofNat]
      calc
        mY q y * |(mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1| ^ 3
            ≤ mY q y * |mY r y / mY q y - 1| :=
          mul_le_mul_of_nonneg_left hscalar hqypos.le
        _ = |mY r y - mY q y| := by
          rw [show mY r y / mY q y - 1 = (mY r y - mY q y) / mY q y by
            field_simp]
          rw [abs_div, abs_of_pos hqypos]
          field_simp
  constructor
  · calc
      moment (mX q) 3 (fun x => (mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1)
          ≤ ∑ x, |mX r x - mX q x| := by
        unfold moment
        exact Finset.sum_le_sum fun x _ => hXpoint x
      _ ≤ ∑ z, |r z - q z| := sum_abs_mX_sub_le q r
      _ = ∑ z, |q z - r z| := by
        apply Finset.sum_congr rfl
        intro z _
        rw [abs_sub_comm]
      _ = 2 * tvDist q r := by unfold tvDist; ring
  · calc
      moment (mY q) 3 (fun y => (mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1)
          ≤ ∑ y, |mY r y - mY q y| := by
        unfold moment
        exact Finset.sum_le_sum fun y _ => hYpoint y
      _ ≤ ∑ z, |r z - q z| := sum_abs_mY_sub_le q r
      _ = ∑ z, |q z - r z| := by
        apply Finset.sum_congr rfl
        intro z _
        rw [abs_sub_comm]
      _ = 2 * tvDist q r := by unfold tvDist; ring

private lemma secant_expanded_equations {S : Finset (α × β)}
    {w q r : α × β → ℝ} (hq : IsContact S w q) (hr : IsContact S w r)
    (hqs : support q = S) (hrs : support r = S) :
    (∀ x, mX q x * ((mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1) =
      2 * (∑ y, q (x, y) *
        ((mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1)) +
      ∑ y, q (x, y) *
        ((mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1) ^ 2) ∧
    (∀ y, mY q y * ((mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1) =
      2 * (∑ x, q (x, y) *
        ((mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1)) +
      ∑ x, q (x, y) *
        ((mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1) ^ 2) := by
  have hsec := secant_equations hq hr hqs hrs
  constructor
  · intro x
    calc
      mX q x * ((mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1) =
          (∑ y, q (x, y) *
            ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2) - mX q x := by
        rw [hsec.1 x]
        ring
      _ = 2 * (∑ y, q (x, y) *
            ((mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1)) +
          ∑ y, q (x, y) *
            ((mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1) ^ 2 := by
        rw [mX_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro y _
        ring
  · intro y
    calc
      mY q y * ((mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1) =
          (∑ x, q (x, y) *
            ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2) - mY q y := by
        rw [hsec.2 y]
        ring
      _ = 2 * (∑ x, q (x, y) *
            ((mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1)) +
          ∑ x, q (x, y) *
            ((mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1) ^ 2 := by
        rw [mY_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring

private lemma secant_X_norm_relation {S : Finset (α × β)} {w : α × β → ℝ}
    {q : α × β → ℝ} (hw : Feasible S w) (hq : IsContact S w q)
    {f : α → ℝ} {g : β → ℝ}
    (heq : ∀ x, mX q x * f x =
      2 * (∑ y, q (x, y) * g y) + ∑ y, q (x, y) * g y ^ 2) :
    normThree (mX q) f ≤ 2 * normTwo (mY q) g + normThree (mY q) g ^ 2 := by
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  let A : ℝ := moment (mX q) 3 f
  have hA0 : 0 ≤ A := moment_nonneg hqX.nonneg _ _
  rcases hA0.eq_or_lt with hAzero | hApos
  · have hnormzero : normThree (mX q) f = 0 := by simp [normThree, A, hAzero.symm]
    rw [hnormzero]
    exact add_nonneg (mul_nonneg (by norm_num) (normTwo_nonneg hqY.nonneg g))
      (sq_nonneg _)
  · have habs_cube : ∀ x, |f x| ^ (3 : ℝ) = (f x * |f x|) * f x := by
      intro x
      calc
        |f x| ^ (3 : ℝ) = |f x| ^ (3 : ℕ) := Real.rpow_ofNat _ _
        _ = |f x| ^ 2 * |f x| := by ring
        _ = f x ^ 2 * |f x| := by rw [sq_abs]
        _ = (f x * |f x|) * f x := by ring
    have hidentity : A =
        2 * (∑ z, q z * (f z.1 * |f z.1|) * g z.2) +
          ∑ z, q z * (f z.1 * |f z.1|) * g z.2 ^ 2 := by
      calc
        A = ∑ x, (f x * |f x|) * (mX q x * f x) := by
          dsimp [A, moment]
          apply Finset.sum_congr rfl
          intro x _
          rw [habs_cube]
          ring
        _ = ∑ x, (f x * |f x|) *
            (2 * (∑ y, q (x, y) * g y) + ∑ y, q (x, y) * g y ^ 2) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [heq x]
        _ = 2 * (∑ z, q z * (f z.1 * |f z.1|) * g z.2) +
            ∑ z, q z * (f z.1 * |f z.1|) * g z.2 ^ 2 := by
          have hfirst : (∑ x, (f x * |f x|) * (∑ y, q (x, y) * g y)) =
              ∑ z, q z * (f z.1 * |f z.1|) * g z.2 := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
          have hsecond : (∑ x, (f x * |f x|) * (∑ y, q (x, y) * g y ^ 2)) =
              ∑ z, q z * (f z.1 * |f z.1|) * g z.2 ^ 2 := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
          rw [show (∑ x, (f x * |f x|) *
              (2 * (∑ y, q (x, y) * g y) + ∑ y, q (x, y) * g y ^ 2)) =
              ∑ x, (2 * ((f x * |f x|) * (∑ y, q (x, y) * g y)) +
                (f x * |f x|) * (∑ y, q (x, y) * g y ^ 2)) by
            apply Finset.sum_congr rfl
            intro x _
            ring]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfirst, hsecond]
    have hsigned1 : (∑ z, q z * (f z.1 * |f z.1|) * g z.2) ≤
        ∑ z, q z * |f z.1| ^ (2 : ℝ) * |g z.2| := by
      apply Finset.sum_le_sum
      intro z _
      calc
        q z * (f z.1 * |f z.1|) * g z.2
            ≤ q z * |(f z.1 * |f z.1|) * g z.2| := by
          have hz := mul_le_mul_of_nonneg_left
            (le_abs_self ((f z.1 * |f z.1|) * g z.2)) (hq.1.nonneg z)
          simpa [mul_assoc] using hz
        _ = q z * |f z.1| ^ (2 : ℝ) * |g z.2| := by
          rw [abs_mul, abs_mul, abs_abs, Real.rpow_two]
          ring
    have hsigned2 : (∑ z, q z * (f z.1 * |f z.1|) * g z.2 ^ 2) ≤
        ∑ z, q z * |f z.1| ^ (2 : ℝ) * g z.2 ^ 2 := by
      apply Finset.sum_le_sum
      intro z _
      have hg20 : 0 ≤ g z.2 ^ 2 := sq_nonneg _
      calc
        q z * (f z.1 * |f z.1|) * g z.2 ^ 2
            ≤ q z * |f z.1 * abs (f z.1)| * g z.2 ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_abs_self _) (hq.1.nonneg z)) hg20
        _ = q z * |f z.1| ^ (2 : ℝ) * g z.2 ^ 2 := by
          rw [abs_mul, abs_abs, Real.rpow_two]
          ring
    have hhc1 := contact_hypercontractive hw hq
      (f := fun x => |f x| ^ (2 : ℝ)) (g := fun y => |g y|)
      (fun x => Real.rpow_nonneg (abs_nonneg _) _) (fun y => abs_nonneg _)
    have hhc1_all : (∑ z, q z * |f z.1| ^ (2 : ℝ) * |g z.2|) ≤
        A ^ ((2 : ℝ) / 3) *
          (moment (mY q) ((3 : ℝ) / 2) g) ^ ((2 : ℝ) / 3) := by
      have hsupp := sum_eq_sum_support hq.2.1
        (fun z => |f z.1| ^ (2 : ℝ) * |g z.2|)
      rw [show (∑ z, q z * |f z.1| ^ (2 : ℝ) * |g z.2|) =
          ∑ z ∈ S, q z * |f z.1| ^ (2 : ℝ) * |g z.2| by
        simpa [mul_assoc] using hsupp]
      have hpow : ∀ x, (|f x| ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) = |f x| ^ (3 : ℝ) := by
        intro x
        rw [← Real.rpow_mul (abs_nonneg _)]
        norm_num
      simp_rw [hpow] at hhc1
      simpa [A, moment] using hhc1
    have hhc2 := contact_hypercontractive hw hq
      (f := fun x => |f x| ^ (2 : ℝ)) (g := fun y => g y ^ 2)
      (fun x => Real.rpow_nonneg (abs_nonneg _) _) (fun y => sq_nonneg _)
    have hhc2_all : (∑ z, q z * |f z.1| ^ (2 : ℝ) * g z.2 ^ 2) ≤
        A ^ ((2 : ℝ) / 3) * (moment (mY q) 3 g) ^ ((2 : ℝ) / 3) := by
      have hsupp := sum_eq_sum_support hq.2.1
        (fun z => |f z.1| ^ (2 : ℝ) * g z.2 ^ 2)
      rw [show (∑ z, q z * |f z.1| ^ (2 : ℝ) * g z.2 ^ 2) =
          ∑ z ∈ S, q z * |f z.1| ^ (2 : ℝ) * g z.2 ^ 2 by
        simpa [mul_assoc] using hsupp]
      have hpowf : ∀ x, (|f x| ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) = |f x| ^ (3 : ℝ) := by
        intro x
        rw [← Real.rpow_mul (abs_nonneg _)]
        norm_num
      have hpowg : ∀ y, (g y ^ 2) ^ ((3 : ℝ) / 2) = |g y| ^ (3 : ℝ) := by
        intro y
        rw [show g y ^ 2 = |g y| ^ (2 : ℝ) by rw [Real.rpow_two, sq_abs]]
        rw [← Real.rpow_mul (abs_nonneg _)]
        norm_num
      simp_rw [hpowf, hpowg] at hhc2
      simpa [A, moment] using hhc2
    have hAineq : A ≤ A ^ ((2 : ℝ) / 3) *
        (2 * (moment (mY q) ((3 : ℝ) / 2) g) ^ ((2 : ℝ) / 3) +
          (moment (mY q) 3 g) ^ ((2 : ℝ) / 3)) := by
      calc
        A = 2 * (∑ z, q z * (f z.1 * |f z.1|) * g z.2) +
            ∑ z, q z * (f z.1 * |f z.1|) * g z.2 ^ 2 := hidentity
        _ ≤ 2 * (∑ z, q z * |f z.1| ^ (2 : ℝ) * |g z.2|) +
            ∑ z, q z * |f z.1| ^ (2 : ℝ) * g z.2 ^ 2 := by linarith
        _ ≤ 2 * (A ^ ((2 : ℝ) / 3) *
              (moment (mY q) ((3 : ℝ) / 2) g) ^ ((2 : ℝ) / 3)) +
            A ^ ((2 : ℝ) / 3) *
              (moment (mY q) 3 g) ^ ((2 : ℝ) / 3) := by linarith
        _ = A ^ ((2 : ℝ) / 3) *
            (2 * (moment (mY q) ((3 : ℝ) / 2) g) ^ ((2 : ℝ) / 3) +
              (moment (mY q) 3 g) ^ ((2 : ℝ) / 3)) := by ring
    have hsplit : A = A ^ ((2 : ℝ) / 3) * A ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_add' hApos.le (by norm_num : (2 : ℝ) / 3 + 1 / 3 ≠ 0)]
      norm_num
    have hfac : 0 < A ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hApos _
    have hcancel : A ^ ((1 : ℝ) / 3) ≤
        2 * (moment (mY q) ((3 : ℝ) / 2) g) ^ ((2 : ℝ) / 3) +
          (moment (mY q) 3 g) ^ ((2 : ℝ) / 3) := by
      apply le_of_mul_le_mul_left _ hfac
      rw [← hsplit]
      exact hAineq
    have h32 := norm_three_halves_le_normTwo hqY g
    have hnorm3sq : (moment (mY q) 3 g) ^ ((2 : ℝ) / 3) =
        normThree (mY q) g ^ 2 := by
      unfold normThree
      rw [← Real.rpow_natCast, ← Real.rpow_mul (moment_nonneg hqY.nonneg _ _)]
      norm_num
    change A ^ ((1 : ℝ) / 3) ≤ 2 * normTwo (mY q) g + normThree (mY q) g ^ 2
    rw [← hnorm3sq]
    linarith

private lemma secant_Y_norm_relation {S : Finset (α × β)} {w : α × β → ℝ}
    {q : α × β → ℝ} (hw : Feasible S w) (hq : IsContact S w q)
    {f : α → ℝ} {g : β → ℝ}
    (heq : ∀ y, mY q y * g y =
      2 * (∑ x, q (x, y) * f x) + ∑ x, q (x, y) * f x ^ 2) :
    normThree (mY q) g ≤ 2 * normTwo (mX q) f + normThree (mX q) f ^ 2 := by
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  let A : ℝ := moment (mY q) 3 g
  have hA0 : 0 ≤ A := moment_nonneg hqY.nonneg _ _
  rcases hA0.eq_or_lt with hAzero | hApos
  · have hnormzero : normThree (mY q) g = 0 := by simp [normThree, A, hAzero.symm]
    rw [hnormzero]
    exact add_nonneg (mul_nonneg (by norm_num) (normTwo_nonneg hqX.nonneg f))
      (sq_nonneg _)
  · have habs_cube : ∀ y, |g y| ^ (3 : ℝ) = (g y * |g y|) * g y := by
      intro y
      calc
        |g y| ^ (3 : ℝ) = |g y| ^ (3 : ℕ) := Real.rpow_ofNat _ _
        _ = |g y| ^ 2 * |g y| := by ring
        _ = g y ^ 2 * |g y| := by rw [sq_abs]
        _ = (g y * |g y|) * g y := by ring
    have hidentity : A =
        2 * (∑ z, q z * f z.1 * (g z.2 * |g z.2|)) +
          ∑ z, q z * f z.1 ^ 2 * (g z.2 * |g z.2|) := by
      calc
        A = ∑ y, (g y * |g y|) * (mY q y * g y) := by
          dsimp [A, moment]
          apply Finset.sum_congr rfl
          intro y _
          rw [habs_cube]
          ring
        _ = ∑ y, (g y * |g y|) *
            (2 * (∑ x, q (x, y) * f x) + ∑ x, q (x, y) * f x ^ 2) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [heq y]
        _ = 2 * (∑ z, q z * f z.1 * (g z.2 * |g z.2|)) +
            ∑ z, q z * f z.1 ^ 2 * (g z.2 * |g z.2|) := by
          have hfirst : (∑ y, (g y * |g y|) * (∑ x, q (x, y) * f x)) =
              ∑ z, q z * f z.1 * (g z.2 * |g z.2|) := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
          have hsecond : (∑ y, (g y * |g y|) * (∑ x, q (x, y) * f x ^ 2)) =
              ∑ z, q z * f z.1 ^ 2 * (g z.2 * |g z.2|) := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
          rw [show (∑ y, (g y * |g y|) *
              (2 * (∑ x, q (x, y) * f x) + ∑ x, q (x, y) * f x ^ 2)) =
              ∑ y, (2 * ((g y * |g y|) * (∑ x, q (x, y) * f x)) +
                (g y * |g y|) * (∑ x, q (x, y) * f x ^ 2)) by
            apply Finset.sum_congr rfl
            intro y _
            ring]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfirst, hsecond]
    have hsigned1 : (∑ z, q z * f z.1 * (g z.2 * |g z.2|)) ≤
        ∑ z, q z * |f z.1| * |g z.2| ^ (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro z _
      calc
        q z * f z.1 * (g z.2 * |g z.2|)
            ≤ q z * |f z.1 * (g z.2 * |g z.2|)| := by
          have hz := mul_le_mul_of_nonneg_left
            (le_abs_self (f z.1 * (g z.2 * |g z.2|))) (hq.1.nonneg z)
          simpa [mul_assoc] using hz
        _ = q z * |f z.1| * |g z.2| ^ (2 : ℝ) := by
          rw [abs_mul, abs_mul, abs_abs, Real.rpow_two]
          ring
    have hsigned2 : (∑ z, q z * f z.1 ^ 2 * (g z.2 * |g z.2|)) ≤
        ∑ z, q z * f z.1 ^ 2 * |g z.2| ^ (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro z _
      have hf20 : 0 ≤ f z.1 ^ 2 := sq_nonneg _
      calc
        q z * f z.1 ^ 2 * (g z.2 * |g z.2|)
            ≤ q z * f z.1 ^ 2 * |g z.2 * abs (g z.2)| := by
          exact mul_le_mul_of_nonneg_left (le_abs_self _)
            (mul_nonneg (hq.1.nonneg z) hf20)
        _ = q z * f z.1 ^ 2 * |g z.2| ^ (2 : ℝ) := by
          rw [abs_mul, abs_abs, Real.rpow_two]
          ring
    have hhc1 := contact_hypercontractive hw hq
      (f := fun x => |f x|) (g := fun y => |g y| ^ (2 : ℝ))
      (fun x => abs_nonneg _) (fun y => Real.rpow_nonneg (abs_nonneg _) _)
    have hhc1_all : (∑ z, q z * |f z.1| * |g z.2| ^ (2 : ℝ)) ≤
        (moment (mX q) ((3 : ℝ) / 2) f) ^ ((2 : ℝ) / 3) *
          A ^ ((2 : ℝ) / 3) := by
      have hsupp := sum_eq_sum_support hq.2.1
        (fun z => |f z.1| * |g z.2| ^ (2 : ℝ))
      rw [show (∑ z, q z * |f z.1| * |g z.2| ^ (2 : ℝ)) =
          ∑ z ∈ S, q z * |f z.1| * |g z.2| ^ (2 : ℝ) by
        simpa [mul_assoc] using hsupp]
      have hpow : ∀ y, (|g y| ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) = |g y| ^ (3 : ℝ) := by
        intro y
        rw [← Real.rpow_mul (abs_nonneg _)]
        norm_num
      simp_rw [hpow] at hhc1
      simpa [A, moment] using hhc1
    have hhc2 := contact_hypercontractive hw hq
      (f := fun x => f x ^ 2) (g := fun y => |g y| ^ (2 : ℝ))
      (fun x => sq_nonneg _) (fun y => Real.rpow_nonneg (abs_nonneg _) _)
    have hhc2_all : (∑ z, q z * f z.1 ^ 2 * |g z.2| ^ (2 : ℝ)) ≤
        (moment (mX q) 3 f) ^ ((2 : ℝ) / 3) * A ^ ((2 : ℝ) / 3) := by
      have hsupp := sum_eq_sum_support hq.2.1
        (fun z => f z.1 ^ 2 * |g z.2| ^ (2 : ℝ))
      rw [show (∑ z, q z * f z.1 ^ 2 * |g z.2| ^ (2 : ℝ)) =
          ∑ z ∈ S, q z * f z.1 ^ 2 * |g z.2| ^ (2 : ℝ) by
        simpa [mul_assoc] using hsupp]
      have hpowf : ∀ x, (f x ^ 2) ^ ((3 : ℝ) / 2) = |f x| ^ (3 : ℝ) := by
        intro x
        rw [show f x ^ 2 = |f x| ^ (2 : ℝ) by rw [Real.rpow_two, sq_abs]]
        rw [← Real.rpow_mul (abs_nonneg _)]
        norm_num
      have hpowg : ∀ y, (|g y| ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) =
          |g y| ^ (3 : ℝ) := by
        intro y
        rw [← Real.rpow_mul (abs_nonneg _)]
        norm_num
      simp_rw [hpowf, hpowg] at hhc2
      simpa [A, moment] using hhc2
    have hAineq : A ≤ A ^ ((2 : ℝ) / 3) *
        (2 * (moment (mX q) ((3 : ℝ) / 2) f) ^ ((2 : ℝ) / 3) +
          (moment (mX q) 3 f) ^ ((2 : ℝ) / 3)) := by
      calc
        A = 2 * (∑ z, q z * f z.1 * (g z.2 * |g z.2|)) +
            ∑ z, q z * f z.1 ^ 2 * (g z.2 * |g z.2|) := hidentity
        _ ≤ 2 * (∑ z, q z * |f z.1| * |g z.2| ^ (2 : ℝ)) +
            ∑ z, q z * f z.1 ^ 2 * |g z.2| ^ (2 : ℝ) := by linarith
        _ ≤ 2 * ((moment (mX q) ((3 : ℝ) / 2) f) ^ ((2 : ℝ) / 3) *
              A ^ ((2 : ℝ) / 3)) +
            (moment (mX q) 3 f) ^ ((2 : ℝ) / 3) * A ^ ((2 : ℝ) / 3) := by
          linarith
        _ = A ^ ((2 : ℝ) / 3) *
            (2 * (moment (mX q) ((3 : ℝ) / 2) f) ^ ((2 : ℝ) / 3) +
              (moment (mX q) 3 f) ^ ((2 : ℝ) / 3)) := by ring
    have hsplit : A = A ^ ((2 : ℝ) / 3) * A ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_add' hApos.le (by norm_num : (2 : ℝ) / 3 + 1 / 3 ≠ 0)]
      norm_num
    have hfac : 0 < A ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hApos _
    have hcancel : A ^ ((1 : ℝ) / 3) ≤
        2 * (moment (mX q) ((3 : ℝ) / 2) f) ^ ((2 : ℝ) / 3) +
          (moment (mX q) 3 f) ^ ((2 : ℝ) / 3) := by
      apply le_of_mul_le_mul_left _ hfac
      rw [← hsplit]
      exact hAineq
    have h32 := norm_three_halves_le_normTwo hqX f
    have hnorm3sq : (moment (mX q) 3 f) ^ ((2 : ℝ) / 3) =
        normThree (mX q) f ^ 2 := by
      unfold normThree
      rw [← Real.rpow_natCast, ← Real.rpow_mul (moment_nonneg hqX.nonneg _ _)]
      norm_num
    change A ^ ((1 : ℝ) / 3) ≤ 2 * normTwo (mX q) f + normThree (mX q) f ^ 2
    rw [← hnorm3sq]
    linarith

private lemma abs_joint_mul_square_le {S : Finset (α × β)} {w : α × β → ℝ}
    {q : α × β → ℝ} (hw : Feasible S w) (hq : IsContact S w q)
    (f : α → ℝ) (g : β → ℝ) :
    |∑ z, q z * f z.1 * g z.2 ^ 2| ≤
      normTwo (mX q) f * normThree (mY q) g ^ 2 := by
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  have habs : |∑ z, q z * f z.1 * g z.2 ^ 2| ≤
      ∑ z, q z * |f z.1| * g z.2 ^ 2 := by
    calc
      |∑ z, q z * f z.1 * g z.2 ^ 2| ≤
          ∑ z, |q z * f z.1 * g z.2 ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ z, q z * |f z.1| * g z.2 ^ 2 := by
        apply Finset.sum_congr rfl
        intro z _
        rw [abs_mul, abs_mul, abs_of_nonneg (hq.1.nonneg z), abs_sq]
  have hhc := contact_hypercontractive hw hq
    (f := fun x => |f x|) (g := fun y => g y ^ 2)
    (fun x => abs_nonneg _) (fun y => sq_nonneg _)
  have hhc_all : (∑ z, q z * |f z.1| * g z.2 ^ 2) ≤
      (moment (mX q) ((3 : ℝ) / 2) f) ^ ((2 : ℝ) / 3) *
        (moment (mY q) 3 g) ^ ((2 : ℝ) / 3) := by
    have hsupp := sum_eq_sum_support hq.2.1
      (fun z => |f z.1| * g z.2 ^ 2)
    rw [show (∑ z, q z * |f z.1| * g z.2 ^ 2) =
        ∑ z ∈ S, q z * |f z.1| * g z.2 ^ 2 by
      simpa [mul_assoc] using hsupp]
    have hpow : ∀ y, (g y ^ 2) ^ ((3 : ℝ) / 2) = |g y| ^ (3 : ℝ) := by
      intro y
      rw [show g y ^ 2 = |g y| ^ (2 : ℝ) by rw [Real.rpow_two, sq_abs]]
      rw [← Real.rpow_mul (abs_nonneg _)]
      norm_num
    simp_rw [hpow] at hhc
    simpa [moment] using hhc
  have h32 := norm_three_halves_le_normTwo hqX f
  have hnorm3sq : (moment (mY q) 3 g) ^ ((2 : ℝ) / 3) =
      normThree (mY q) g ^ 2 := by
    unfold normThree
    rw [← Real.rpow_natCast, ← Real.rpow_mul (moment_nonneg hqY.nonneg _ _)]
    norm_num
  rw [← hnorm3sq]
  exact habs.trans (hhc_all.trans (mul_le_mul_of_nonneg_right h32
    (Real.rpow_nonneg (moment_nonneg hqY.nonneg _ _) _)))
/-- Total variation distance between two laws on the product,
`TV(q,r) := ½ ∑ |q − r|`. -/
noncomputable def TV (q r : α × β → ℝ) : ℝ := (∑ z, |q z - r z|) / 2

/-- The Hirschfeld-Gebelein-Rényi maximal correlation of a law `q`:
`ρ(q) := sup { E_q[f(X)g(Y)] : E f = E g = 0, E f² = E g² = 1 }`. -/
noncomputable def rhoHGR (q : α × β → ℝ) : ℝ :=
  ⨆ fg : {fg : (α → ℝ) × (β → ℝ) //
      (∑ x, mX q x * fg.1 x = 0) ∧ (∑ y, mY q y * fg.2 y = 0) ∧
      (∑ x, mX q x * fg.1 x ^ 2 = 1) ∧ (∑ y, mY q y * fg.2 y ^ 2 = 1)},
    ∑ z, q z * fg.1.1 z.1 * fg.1.2 z.2

private lemma correlation_le_one {q : α × β → ℝ} (hq : IsPMF q)
    {f : α → ℝ} {g : β → ℝ}
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1) (hg2 : ∑ y, mY q y * g y ^ 2 = 1) :
    (∑ z, q z * f z.1 * g z.2) ≤ 1 := by
  have hjointF : ∑ z, q z * f z.1 ^ 2 = 1 := by
    rw [← sum_push_mul Prod.fst q (fun x => f x ^ 2)]
    exact hf2
  have hjointG : ∑ z, q z * g z.2 ^ 2 = 1 := by
    rw [← sum_push_mul Prod.snd q (fun y => g y ^ 2)]
    exact hg2
  calc
    (∑ z, q z * f z.1 * g z.2)
        ≤ ∑ z, q z * ((f z.1 ^ 2 + g z.2 ^ 2) / 2) := by
      apply Finset.sum_le_sum
      intro z _
      calc
        q z * f z.1 * g z.2 = q z * (f z.1 * g z.2) := by ring
        _ ≤ q z * ((f z.1 ^ 2 + g z.2 ^ 2) / 2) := by
          apply mul_le_mul_of_nonneg_left _ (hq.nonneg z)
          nlinarith [sq_nonneg (f z.1 - g z.2)]
    _ = 1 := by
      calc
        ∑ z, q z * ((f z.1 ^ 2 + g z.2 ^ 2) / 2) =
            ∑ z, (q z * f z.1 ^ 2 + q z * g z.2 ^ 2) / 2 := by
          apply Finset.sum_congr rfl
          intro z _
          ring
        _ = (∑ z, (q z * f z.1 ^ 2 + q z * g z.2 ^ 2)) / 2 := by
          rw [← Finset.sum_div]
        _ = ((∑ z, q z * f z.1 ^ 2) + ∑ z, q z * g z.2 ^ 2) / 2 := by
          rw [Finset.sum_add_distrib]
        _ = 1 := by rw [hjointF, hjointG]; norm_num

private lemma correlation_le_rhoHGR {q : α × β → ℝ} (hq : IsPMF q)
    {f : α → ℝ} {g : β → ℝ}
    (hf0 : ∑ x, mX q x * f x = 0) (hg0 : ∑ y, mY q y * g y = 0)
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1) (hg2 : ∑ y, mY q y * g y ^ 2 = 1) :
    (∑ z, q z * f z.1 * g z.2) ≤ rhoHGR q := by
  let fg : {fg : (α → ℝ) × (β → ℝ) //
      (∑ x, mX q x * fg.1 x = 0) ∧ (∑ y, mY q y * fg.2 y = 0) ∧
      (∑ x, mX q x * fg.1 x ^ 2 = 1) ∧ (∑ y, mY q y * fg.2 y ^ 2 = 1)} :=
    ⟨(f, g), hf0, hg0, hf2, hg2⟩
  have hbdd : BddAbove (Set.range fun uv : {fg : (α → ℝ) × (β → ℝ) //
      (∑ x, mX q x * fg.1 x = 0) ∧ (∑ y, mY q y * fg.2 y = 0) ∧
      (∑ x, mX q x * fg.1 x ^ 2 = 1) ∧ (∑ y, mY q y * fg.2 y ^ 2 = 1)} =>
      ∑ z, q z * uv.1.1 z.1 * uv.1.2 z.2) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨uv, rfl⟩
    exact correlation_le_one hq uv.2.2.2.1 uv.2.2.2.2
  unfold rhoHGR
  exact le_ciSup hbdd fg

private lemma rhoHGR_le_one {q : α × β → ℝ} (hq : IsPMF q) : rhoHGR q ≤ 1 := by
  let ι := {fg : (α → ℝ) × (β → ℝ) //
      (∑ x, mX q x * fg.1 x = 0) ∧ (∑ y, mY q y * fg.2 y = 0) ∧
      (∑ x, mX q x * fg.1 x ^ 2 = 1) ∧ (∑ y, mY q y * fg.2 y ^ 2 = 1)}
  change (⨆ fg : ι, ∑ z, q z * fg.1.1 z.1 * fg.1.2 z.2) ≤ 1
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI := hempty
      simp
  | inr hnonempty =>
      letI := hnonempty
      apply ciSup_le
      intro fg
      exact correlation_le_one hq fg.2.2.2.1 fg.2.2.2.2

private lemma exists_hgr_maximizer {q : α × β → ℝ} (hq : IsPMF q)
    (hpos : 0 < rhoHGR q) :
    ∃ (f : α → ℝ) (g : β → ℝ),
      (∑ x, mX q x * f x = 0) ∧ (∑ y, mY q y * g y = 0) ∧
      (∑ x, mX q x * f x ^ 2 = 1) ∧ (∑ y, mY q y * g y ^ 2 = 1) ∧
      (∑ z, q z * f z.1 * g z.2) = rhoHGR q := by
  let I := {fg : (α → ℝ) × (β → ℝ) //
      (∑ x, mX q x * fg.1 x = 0) ∧ (∑ y, mY q y * fg.2 y = 0) ∧
      (∑ x, mX q x * fg.1 x ^ 2 = 1) ∧ (∑ y, mY q y * fg.2 y ^ 2 = 1)}
  have hI : Nonempty I := by
    cases isEmpty_or_nonempty I with
    | inl hempty =>
        letI := hempty
        have hz : rhoHGR q = 0 := by simp [rhoHGR, I]
        exfalso
        linarith
    | inr hnonempty => exact hnonempty
  let BX : α → ℝ := fun x => 1 + (mX q x)⁻¹
  let BY : β → ℝ := fun y => 1 + (mY q y)⁻¹
  let KX : Set (α → ℝ) := Set.pi Set.univ (fun x => Set.Icc (-BX x) (BX x))
  let KY : Set (β → ℝ) := Set.pi Set.univ (fun y => Set.Icc (-BY y) (BY y))
  let C : Set ((α → ℝ) × (β → ℝ)) := {fg |
      (∑ x, mX q x * fg.1 x = 0) ∧ (∑ y, mY q y * fg.2 y = 0) ∧
      (∑ x, mX q x * fg.1 x ^ 2 = 1) ∧ (∑ y, mY q y * fg.2 y ^ 2 = 1)}
  let K : Set ((α → ℝ) × (β → ℝ)) := (KX ×ˢ KY) ∩ C
  let objective : ((α → ℝ) × (β → ℝ)) → ℝ :=
    fun fg => ∑ z, q z * fg.1 z.1 * fg.2 z.2
  let cf : (α → ℝ) → (α → ℝ) :=
    fun f x => if mX q x = 0 then 0 else f x
  let cg : (β → ℝ) → (β → ℝ) :=
    fun g y => if mY q y = 0 then 0 else g y
  let canon : ((α → ℝ) × (β → ℝ)) → ((α → ℝ) × (β → ℝ)) :=
    fun fg => (cf fg.1, cg fg.2)
  have hcf_mean (f : α → ℝ) :
      ∑ x, mX q x * cf f x = ∑ x, mX q x * f x := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : mX q x = 0 <;> simp [cf, hx]
  have hcg_mean (g : β → ℝ) :
      ∑ y, mY q y * cg g y = ∑ y, mY q y * g y := by
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : mY q y = 0 <;> simp [cg, hy]
  have hcf_sq (f : α → ℝ) :
      ∑ x, mX q x * cf f x ^ 2 = ∑ x, mX q x * f x ^ 2 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : mX q x = 0 <;> simp [cf, hx]
  have hcg_sq (g : β → ℝ) :
      ∑ y, mY q y * cg g y ^ 2 = ∑ y, mY q y * g y ^ 2 := by
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : mY q y = 0 <;> simp [cg, hy]
  have hcanon_objective (fg : (α → ℝ) × (β → ℝ)) :
      objective (canon fg) = objective fg := by
    dsimp [objective, canon]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : q z = 0
    · simp [hz]
    · have hqpos : 0 < q z := lt_of_le_of_ne (hq.nonneg z) (Ne.symm hz)
      have hxpos : 0 < mX q z.1 := by
        have hxle : q z ≤ mX q z.1 := by
          rw [mX_eq_sum]
          exact Finset.single_le_sum (fun y _ => hq.nonneg (z.1, y)) (Finset.mem_univ z.2)
        exact hqpos.trans_le hxle
      have hypos : 0 < mY q z.2 := by
        have hyle : q z ≤ mY q z.2 := by
          rw [mY_eq_sum]
          exact Finset.single_le_sum (fun x _ => hq.nonneg (x, z.2)) (Finset.mem_univ z.1)
        exact hqpos.trans_le hyle
      simp [cf, cg, hxpos.ne', hypos.ne']
  have hcanon_C (u : I) : canon u.1 ∈ C := by
    dsimp [C, canon]
    exact ⟨(hcf_mean u.1.1).trans u.2.1,
      (hcg_mean u.1.2).trans u.2.2.1,
      (hcf_sq u.1.1).trans u.2.2.2.1,
      (hcg_sq u.1.2).trans u.2.2.2.2⟩
  have hcanon_box (u : I) : canon u.1 ∈ KX ×ˢ KY := by
    have hcfzero : ∀ x, mX q x = 0 → cf u.1.1 x = 0 := by
      intro x hx
      simp [cf, hx]
    have hcgzero : ∀ y, mY q y = 0 → cg u.1.2 y = 0 := by
      intro y hy
      simp [cg, hy]
    have hfb (x : α) : |cf u.1.1 x| ≤ BX x := by
      dsimp [BX]
      exact abs_le_one_add_inv_of_weighted_sq_sum_eq_one
        (isPMF_push hq).nonneg ((hcf_sq u.1.1).trans u.2.2.2.1) hcfzero x
    have hgb (y : β) : |cg u.1.2 y| ≤ BY y := by
      dsimp [BY]
      exact abs_le_one_add_inv_of_weighted_sq_sum_eq_one
        (isPMF_push hq).nonneg ((hcg_sq u.1.2).trans u.2.2.2.2) hcgzero y
    constructor
    · rw [Set.mem_pi]
      intro x _
      constructor <;> dsimp [canon] <;>
        nlinarith [hfb x, le_abs_self (cf u.1.1 x), neg_le_abs (cf u.1.1 x)]
    · rw [Set.mem_pi]
      intro y _
      constructor <;> dsimp [canon] <;>
        nlinarith [hgb y, le_abs_self (cg u.1.2 y), neg_le_abs (cg u.1.2 y)]
  have hKX : IsCompact KX := by
    dsimp [KX]
    exact isCompact_univ_pi fun x => isCompact_Icc
  have hKY : IsCompact KY := by
    dsimp [KY]
    exact isCompact_univ_pi fun y => isCompact_Icc
  have hC : IsClosed C := by
    have hc1 : Continuous (fun fg : (α → ℝ) × (β → ℝ) =>
        ∑ x, mX q x * fg.1 x) := by
      exact continuous_finsetSum _ fun x _ =>
        continuous_const.mul ((continuous_apply x).comp continuous_fst)
    have hc2 : Continuous (fun fg : (α → ℝ) × (β → ℝ) =>
        ∑ y, mY q y * fg.2 y) := by
      exact continuous_finsetSum _ fun y _ =>
        continuous_const.mul ((continuous_apply y).comp continuous_snd)
    have hc3 : Continuous (fun fg : (α → ℝ) × (β → ℝ) =>
        ∑ x, mX q x * fg.1 x ^ 2) := by
      exact continuous_finsetSum _ fun x _ =>
        continuous_const.mul (((continuous_apply x).comp continuous_fst).pow 2)
    have hc4 : Continuous (fun fg : (α → ℝ) × (β → ℝ) =>
        ∑ y, mY q y * fg.2 y ^ 2) := by
      exact continuous_finsetSum _ fun y _ =>
        continuous_const.mul (((continuous_apply y).comp continuous_snd).pow 2)
    have hcl1 : IsClosed {fg : (α → ℝ) × (β → ℝ) |
        ∑ x, mX q x * fg.1 x = 0} := isClosed_eq hc1 continuous_const
    have hcl2 : IsClosed {fg : (α → ℝ) × (β → ℝ) |
        ∑ y, mY q y * fg.2 y = 0} := isClosed_eq hc2 continuous_const
    have hcl3 : IsClosed {fg : (α → ℝ) × (β → ℝ) |
        ∑ x, mX q x * fg.1 x ^ 2 = 1} := isClosed_eq hc3 continuous_const
    have hcl4 : IsClosed {fg : (α → ℝ) × (β → ℝ) |
        ∑ y, mY q y * fg.2 y ^ 2 = 1} := isClosed_eq hc4 continuous_const
    dsimp [C]
    exact hcl1.inter (hcl2.inter (hcl3.inter hcl4))
  have hK : IsCompact K := by
    dsimp [K]
    exact (hKX.prod hKY).inter_right hC
  have hKne : K.Nonempty := by
    let u : I := Classical.choice hI
    exact ⟨canon u.1, hcanon_box u, hcanon_C u⟩
  have hobjective : Continuous objective := by fun_prop
  obtain ⟨fg, hfgK, hfgmax⟩ := hK.exists_isMaxOn hKne hobjective.continuousOn
  have hupper (u : I) : objective u.1 ≤ objective fg := by
    rw [← hcanon_objective u.1]
    exact hfgmax ⟨hcanon_box u, hcanon_C u⟩
  have hfgC : fg ∈ C := hfgK.2
  have hconstraints :
      (∑ x, mX q x * fg.1 x = 0) ∧ (∑ y, mY q y * fg.2 y = 0) ∧
      (∑ x, mX q x * fg.1 x ^ 2 = 1) ∧ (∑ y, mY q y * fg.2 y ^ 2 = 1) := by
    simpa [C] using hfgC
  have hle : objective fg ≤ rhoHGR q := by
    dsimp [objective]
    exact correlation_le_rhoHGR hq hconstraints.1 hconstraints.2.1
      hconstraints.2.2.1 hconstraints.2.2.2
  have hge : rhoHGR q ≤ objective fg := by
    change (⨆ u : I, objective u.1) ≤ objective fg
    exact ciSup_le hupper
  refine ⟨fg.1, fg.2, hconstraints.1, hconstraints.2.1,
    hconstraints.2.2.1, hconstraints.2.2.2, ?_⟩
  exact le_antisymm hle hge

private lemma left_singular_of_hgr_maximizer {q : α × β → ℝ} (hq : IsPMF q)
    {f : α → ℝ} {g : β → ℝ}
    (hf0 : ∑ x, mX q x * f x = 0) (hg0 : ∑ y, mY q y * g y = 0)
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1) (hg2 : ∑ y, mY q y * g y ^ 2 = 1)
    (hcorr : (∑ z, q z * f z.1 * g z.2) = rhoHGR q) (hpos : 0 < rhoHGR q) :
    ∀ x, (∑ y, q (x, y) * g y) = rhoHGR q * (mX q x * f x) := by
  let A : α → ℝ := fun x => ∑ y, q (x, y) * g y
  let h : α → ℝ := fun x => if mX q x = 0 then 0 else A x / mX q x
  have hA_zero {x : α} (hx : mX q x = 0) : A x = 0 := by
    dsimp [A]
    apply Finset.sum_eq_zero
    intro y _
    have hqxy : q (x, y) = 0 := by
      apply le_antisymm
      · have hle : q (x, y) ≤ mX q x := by
          rw [mX_eq_sum]
          exact Finset.single_le_sum (fun y _ => hq.nonneg (x, y)) (Finset.mem_univ y)
        simpa [hx] using hle
      · exact hq.nonneg _
    simp [hqxy]
  have hmul (x : α) : mX q x * h x = A x := by
    by_cases hx : mX q x = 0
    · simp [h, hx, hA_zero hx]
    · dsimp [h]
      rw [if_neg hx]
      field_simp
  have hh0 : ∑ x, mX q x * h x = 0 := by
    calc
      ∑ x, mX q x * h x = ∑ x, A x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hmul]
      _ = ∑ y, mY q y * g y := by
        dsimp [A]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        rw [mY_eq_sum, Finset.sum_mul]
      _ = 0 := hg0
  have hrow (x : α) : mX q x * h x ^ 2 ≤ ∑ y, q (x, y) * g y ^ 2 := by
    by_cases hx : mX q x = 0
    · simp [h, hx]
      exact Finset.sum_nonneg fun y _ => mul_nonneg (hq.nonneg _) (sq_nonneg _)
    · have hxp : 0 < mX q x :=
        lt_of_le_of_ne ((isPMF_push hq).nonneg x) (Ne.symm hx)
      have hcauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
        (s := (Finset.univ : Finset β))
        (r := fun y => q (x, y) * g y)
        (f := fun y => q (x, y))
        (g := fun y => q (x, y) * g y ^ 2)
        (fun y _ => hq.nonneg (x, y))
        (fun y _ => mul_nonneg (hq.nonneg (x, y)) (sq_nonneg _))
        (fun y _ => by ring_nf; exact le_rfl)
      have hcauchy' : A x ^ 2 ≤ mX q x * (∑ y, q (x, y) * g y ^ 2) := by
        simpa [A, mX_eq_sum] using hcauchy
      dsimp [h]
      rw [if_neg hx]
      calc
        mX q x * (A x / mX q x) ^ 2 = A x ^ 2 / mX q x := by
          field_simp [hx]
        _ ≤ ∑ y, q (x, y) * g y ^ 2 := by
          apply (div_le_iff₀ hxp).2
          nlinarith
  let s : ℝ := ∑ x, mX q x * h x ^ 2
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg ((isPMF_push hq).nonneg x) (sq_nonneg _)
  have hs_le : s ≤ 1 := by
    calc
      s ≤ ∑ x, ∑ y, q (x, y) * g y ^ 2 := by
        dsimp [s]
        exact Finset.sum_le_sum fun x _ => hrow x
      _ = ∑ z, q z * g z.2 ^ 2 := by rw [Fintype.sum_prod_type]
      _ = ∑ y, mY q y * g y ^ 2 := by
        rw [sum_push_mul Prod.snd q (fun y => g y ^ 2)]
      _ = 1 := hg2
  have hfh : ∑ x, mX q x * f x * h x = rhoHGR q := by
    calc
      ∑ x, mX q x * f x * h x = ∑ x, f x * A x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← hmul]
        ring
      _ = ∑ z, q z * f z.1 * g z.2 := by
        dsimp [A]
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = rhoHGR q := hcorr
  have hhg : ∑ z, q z * h z.1 * g z.2 = s := by
    calc
      ∑ z, q z * h z.1 * g z.2 = ∑ x, h x * A x := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x _
        dsimp [A]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = s := by
        dsimp [s]
        apply Finset.sum_congr rfl
        intro x _
        rw [← hmul]
        ring
  have hcauchy_fh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset α))
    (r := fun x => mX q x * f x * h x)
    (f := fun x => mX q x * f x ^ 2)
    (g := fun x => mX q x * h x ^ 2)
    (fun x _ => mul_nonneg ((isPMF_push hq).nonneg x) (sq_nonneg _))
    (fun x _ => mul_nonneg ((isPMF_push hq).nonneg x) (sq_nonneg _))
    (fun x _ => by ring_nf; exact le_rfl)
  have hrho_sq : rhoHGR q ^ 2 ≤ s := by
    rw [hfh, hf2] at hcauchy_fh
    simpa [s] using hcauchy_fh
  let t : ℝ := normTwo (mX q) h
  have ht0 : 0 ≤ t := normTwo_nonneg (isPMF_push hq).nonneg h
  have ht_sq : t ^ 2 = s := by
    dsimp [t, s]
    rw [normTwo_sq (isPMF_push hq).nonneg, moment_two_eq (isPMF_push hq).nonneg]
  have hrho_le_t : rhoHGR q ≤ t := by
    apply (pow_le_pow_iff_left₀ hpos.le ht0 (by norm_num : (2 : ℕ) ≠ 0)).mp
    rwa [ht_sq]
  have htpos : 0 < t := hpos.trans_le hrho_le_t
  let hn : α → ℝ := fun x => h x / t
  have hhn0 : ∑ x, mX q x * hn x = 0 := by
    calc
      ∑ x, mX q x * hn x = (∑ x, mX q x * h x) / t := by
        dsimp [hn]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hh0, zero_div]
  have hhn2 : ∑ x, mX q x * hn x ^ 2 = 1 := by
    calc
      ∑ x, mX q x * hn x ^ 2 = s / t ^ 2 := by
        dsimp [hn, s]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        field_simp [htpos.ne']
      _ = 1 := by rw [← ht_sq]; field_simp [htpos.ne']
  have hnorm_corr : ∑ z, q z * hn z.1 * g z.2 = t := by
    calc
      ∑ z, q z * hn z.1 * g z.2 = (∑ z, q z * h z.1 * g z.2) / t := by
        dsimp [hn]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = s / t := by rw [hhg]
      _ = t := by rw [← ht_sq]; field_simp [htpos.ne']
  have ht_le_rho := correlation_le_rhoHGR hq hhn0 hg0 hhn2 hg2
  rw [hnorm_corr] at ht_le_rho
  have ht_eq : t = rhoHGR q := le_antisymm ht_le_rho hrho_le_t
  have hs_eq : s = rhoHGR q ^ 2 := by rw [← ht_sq, ht_eq]
  have herr : ∑ x, mX q x * (h x - rhoHGR q * f x) ^ 2 = 0 := by
    have hsecond : (∑ x, 2 * rhoHGR q * (mX q x * f x * h x)) =
        2 * rhoHGR q * (∑ x, mX q x * f x * h x) := by rw [Finset.mul_sum]
    have hthird : (∑ x, rhoHGR q ^ 2 * (mX q x * f x ^ 2)) =
        rhoHGR q ^ 2 * (∑ x, mX q x * f x ^ 2) := by rw [Finset.mul_sum]
    calc
      ∑ x, mX q x * (h x - rhoHGR q * f x) ^ 2 =
          s - 2 * rhoHGR q * (∑ x, mX q x * f x * h x) +
            rhoHGR q ^ 2 * (∑ x, mX q x * f x ^ 2) := by
        have hpoint : ∀ x, mX q x * (h x - rhoHGR q * f x) ^ 2 =
            (mX q x * h x ^ 2 - 2 * rhoHGR q * (mX q x * f x * h x)) +
              rhoHGR q ^ 2 * (mX q x * f x ^ 2) := by
          intro x
          ring
        simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          hsecond, hthird]
        rfl
      _ = 0 := by rw [hs_eq, hfh, hf2]; ring
  intro x
  by_cases hx : mX q x = 0
  · change A x = rhoHGR q * (mX q x * f x)
    rw [hA_zero hx, hx]
    ring
  · have hterm : mX q x * (h x - rhoHGR q * f x) ^ 2 = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
        mul_nonneg ((isPMF_push hq).nonneg x) (sq_nonneg _))).mp
      · exact herr
      · exact Finset.mem_univ x
    have heq : h x = rhoHGR q * f x := by
      have hsquare : (h x - rhoHGR q * f x) ^ 2 = 0 :=
        (mul_eq_zero.mp hterm).resolve_left hx
      nlinarith [sq_nonneg (h x - rhoHGR q * f x)]
    change A x = rhoHGR q * (mX q x * f x)
    rw [← hmul x, heq]
    ring

private lemma right_singular_of_hgr_maximizer {q : α × β → ℝ} (hq : IsPMF q)
    {f : α → ℝ} {g : β → ℝ}
    (hf0 : ∑ x, mX q x * f x = 0) (hg0 : ∑ y, mY q y * g y = 0)
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1) (hg2 : ∑ y, mY q y * g y ^ 2 = 1)
    (hcorr : (∑ z, q z * f z.1 * g z.2) = rhoHGR q) (hpos : 0 < rhoHGR q) :
    ∀ y, (∑ x, q (x, y) * f x) = rhoHGR q * (mY q y * g y) := by
  let B : β → ℝ := fun y => ∑ x, q (x, y) * f x
  let k : β → ℝ := fun y => if mY q y = 0 then 0 else B y / mY q y
  have hB_zero {y : β} (hy : mY q y = 0) : B y = 0 := by
    dsimp [B]
    apply Finset.sum_eq_zero
    intro x _
    have hqxy : q (x, y) = 0 := by
      apply le_antisymm
      · have hle : q (x, y) ≤ mY q y := by
          rw [mY_eq_sum]
          exact Finset.single_le_sum (fun x _ => hq.nonneg (x, y)) (Finset.mem_univ x)
        simpa [hy] using hle
      · exact hq.nonneg _
    simp [hqxy]
  have hmul (y : β) : mY q y * k y = B y := by
    by_cases hy : mY q y = 0
    · simp [k, hy, hB_zero hy]
    · dsimp [k]
      rw [if_neg hy]
      field_simp
  have hk0 : ∑ y, mY q y * k y = 0 := by
    calc
      ∑ y, mY q y * k y = ∑ y, B y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [hmul]
      _ = ∑ x, mX q x * f x := by
        dsimp [B]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [mX_eq_sum, Finset.sum_mul]
      _ = 0 := hf0
  have hcol (y : β) : mY q y * k y ^ 2 ≤ ∑ x, q (x, y) * f x ^ 2 := by
    by_cases hy : mY q y = 0
    · simp [k, hy]
      exact Finset.sum_nonneg fun x _ => mul_nonneg (hq.nonneg _) (sq_nonneg _)
    · have hyp : 0 < mY q y :=
        lt_of_le_of_ne ((isPMF_push hq).nonneg y) (Ne.symm hy)
      have hcauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
        (s := (Finset.univ : Finset α))
        (r := fun x => q (x, y) * f x)
        (f := fun x => q (x, y))
        (g := fun x => q (x, y) * f x ^ 2)
        (fun x _ => hq.nonneg (x, y))
        (fun x _ => mul_nonneg (hq.nonneg (x, y)) (sq_nonneg _))
        (fun x _ => by ring_nf; exact le_rfl)
      have hcauchy' : B y ^ 2 ≤ mY q y * (∑ x, q (x, y) * f x ^ 2) := by
        simpa [B, mY_eq_sum] using hcauchy
      dsimp [k]
      rw [if_neg hy]
      calc
        mY q y * (B y / mY q y) ^ 2 = B y ^ 2 / mY q y := by
          field_simp [hy]
        _ ≤ ∑ x, q (x, y) * f x ^ 2 := by
          apply (div_le_iff₀ hyp).2
          nlinarith
  let s : ℝ := ∑ y, mY q y * k y ^ 2
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg ((isPMF_push hq).nonneg y) (sq_nonneg _)
  have hs_le : s ≤ 1 := by
    calc
      s ≤ ∑ y, ∑ x, q (x, y) * f x ^ 2 := by
        dsimp [s]
        exact Finset.sum_le_sum fun y _ => hcol y
      _ = ∑ z, q z * f z.1 ^ 2 := by rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ = ∑ x, mX q x * f x ^ 2 := by
        rw [sum_push_mul Prod.fst q (fun x => f x ^ 2)]
      _ = 1 := hf2
  have hgk : ∑ y, mY q y * g y * k y = rhoHGR q := by
    calc
      ∑ y, mY q y * g y * k y = ∑ y, g y * B y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [← hmul]
        ring
      _ = ∑ z, q z * f z.1 * g z.2 := by
        dsimp [B]
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = rhoHGR q := hcorr
  have hfk : ∑ z, q z * f z.1 * k z.2 = s := by
    calc
      ∑ z, q z * f z.1 * k z.2 = ∑ y, k y * B y := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        dsimp [B]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = s := by
        dsimp [s]
        apply Finset.sum_congr rfl
        intro y _
        rw [← hmul]
        ring
  have hcauchy_gk := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset β))
    (r := fun y => mY q y * g y * k y)
    (f := fun y => mY q y * g y ^ 2)
    (g := fun y => mY q y * k y ^ 2)
    (fun y _ => mul_nonneg ((isPMF_push hq).nonneg y) (sq_nonneg _))
    (fun y _ => mul_nonneg ((isPMF_push hq).nonneg y) (sq_nonneg _))
    (fun y _ => by ring_nf; exact le_rfl)
  have hrho_sq : rhoHGR q ^ 2 ≤ s := by
    rw [hgk, hg2] at hcauchy_gk
    simpa [s] using hcauchy_gk
  let t : ℝ := normTwo (mY q) k
  have ht0 : 0 ≤ t := normTwo_nonneg (isPMF_push hq).nonneg k
  have ht_sq : t ^ 2 = s := by
    dsimp [t, s]
    rw [normTwo_sq (isPMF_push hq).nonneg, moment_two_eq (isPMF_push hq).nonneg]
  have hrho_le_t : rhoHGR q ≤ t := by
    apply (pow_le_pow_iff_left₀ hpos.le ht0 (by norm_num : (2 : ℕ) ≠ 0)).mp
    rwa [ht_sq]
  have htpos : 0 < t := hpos.trans_le hrho_le_t
  let kn : β → ℝ := fun y => k y / t
  have hkn0 : ∑ y, mY q y * kn y = 0 := by
    calc
      ∑ y, mY q y * kn y = (∑ y, mY q y * k y) / t := by
        dsimp [kn]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = 0 := by rw [hk0, zero_div]
  have hkn2 : ∑ y, mY q y * kn y ^ 2 = 1 := by
    calc
      ∑ y, mY q y * kn y ^ 2 = s / t ^ 2 := by
        dsimp [kn, s]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro y _
        field_simp [htpos.ne']
      _ = 1 := by rw [← ht_sq]; field_simp [htpos.ne']
  have hnorm_corr : ∑ z, q z * f z.1 * kn z.2 = t := by
    calc
      ∑ z, q z * f z.1 * kn z.2 = (∑ z, q z * f z.1 * k z.2) / t := by
        dsimp [kn]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = s / t := by rw [hfk]
      _ = t := by rw [← ht_sq]; field_simp [htpos.ne']
  have ht_le_rho := correlation_le_rhoHGR hq hf0 hkn0 hf2 hkn2
  rw [hnorm_corr] at ht_le_rho
  have ht_eq : t = rhoHGR q := le_antisymm ht_le_rho hrho_le_t
  have hs_eq : s = rhoHGR q ^ 2 := by rw [← ht_sq, ht_eq]
  have herr : ∑ y, mY q y * (k y - rhoHGR q * g y) ^ 2 = 0 := by
    have hsecond : (∑ y, 2 * rhoHGR q * (mY q y * g y * k y)) =
        2 * rhoHGR q * (∑ y, mY q y * g y * k y) := by rw [Finset.mul_sum]
    have hthird : (∑ y, rhoHGR q ^ 2 * (mY q y * g y ^ 2)) =
        rhoHGR q ^ 2 * (∑ y, mY q y * g y ^ 2) := by rw [Finset.mul_sum]
    calc
      ∑ y, mY q y * (k y - rhoHGR q * g y) ^ 2 =
          s - 2 * rhoHGR q * (∑ y, mY q y * g y * k y) +
            rhoHGR q ^ 2 * (∑ y, mY q y * g y ^ 2) := by
        have hpoint : ∀ y, mY q y * (k y - rhoHGR q * g y) ^ 2 =
            (mY q y * k y ^ 2 - 2 * rhoHGR q * (mY q y * g y * k y)) +
              rhoHGR q ^ 2 * (mY q y * g y ^ 2) := by
          intro y
          ring
        simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          hsecond, hthird]
        rfl
      _ = 0 := by rw [hs_eq, hgk, hg2]; ring
  intro y
  by_cases hy : mY q y = 0
  · change B y = rhoHGR q * (mY q y * g y)
    rw [hB_zero hy, hy]
    ring
  · have hterm : mY q y * (k y - rhoHGR q * g y) ^ 2 = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun y _ =>
        mul_nonneg ((isPMF_push hq).nonneg y) (sq_nonneg _))).mp
      · exact herr
      · exact Finset.mem_univ y
    have heq : k y = rhoHGR q * g y := by
      have hsquare : (k y - rhoHGR q * g y) ^ 2 = 0 :=
        (mul_eq_zero.mp hterm).resolve_left hy
      nlinarith [sq_nonneg (k y - rhoHGR q * g y)]
    change B y = rhoHGR q * (mY q y * g y)
    rw [← hmul y, heq]
    ring

/-- On finite alphabets the supremum defining `ρ` is attained:
`ρ` is the largest singular value of the conditional-expectation operator `T` of
Lemma 2.7, with a singular pair `(f,g)` satisfying `Tg = ρf`, `T*f = ρg`.
The last two conjuncts below state these relations against `L²(q_X)` and
`L²(q_Y)`, multiplied through by the respective marginals. -/
theorem exists_hgr_singular_pair {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) {q : α × β → ℝ} (hq : IsContact S w q) (hpos : 0 < rhoHGR q) :
    ∃ (f : α → ℝ) (g : β → ℝ),
      (∑ x, mX q x * f x = 0) ∧ (∑ y, mY q y * g y = 0) ∧
      (∑ x, mX q x * f x ^ 2 = 1) ∧ (∑ y, mY q y * g y ^ 2 = 1) ∧
      (∑ z, q z * f z.1 * g z.2) = rhoHGR q ∧
      (∀ x, (∑ y, q (x, y) * g y) = rhoHGR q * (mX q x * f x)) ∧
      (∀ y, (∑ x, q (x, y) * f x) = rhoHGR q * (mY q y * g y)) := by
  rcases exists_hgr_maximizer hq.1 hpos with ⟨f, g, hf0, hg0, hf2, hg2, hcorr⟩
  have hleft := left_singular_of_hgr_maximizer hq.1 hf0 hg0 hf2 hg2 hcorr hpos
  have hright := right_singular_of_hgr_maximizer hq.1 hf0 hg0 hf2 hg2 hcorr hpos
  exact ⟨f, g, hf0, hg0, hf2, hg2, hcorr, hleft, hright⟩

private lemma singular_f_moment_three_le {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) {q : α × β → ℝ} (hq : IsContact S w q)
    {ρ : ℝ} (hρ : 0 < ρ) {f : α → ℝ} {g : β → ℝ}
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1) (hg2 : ∑ y, mY q y * g y ^ 2 = 1)
    (hrel : ∀ x, (∑ y, q (x, y) * g y) = ρ * (mX q x * f x)) :
    moment (mX q) 3 f ≤ ρ⁻¹ ^ 3 := by
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  have hf2m : moment (mX q) 2 f = 1 := by
    rw [moment_two_eq hqX.nonneg]
    exact hf2
  have hg2m : moment (mY q) 2 g = 1 := by
    rw [moment_two_eq hqY.nonneg]
    exact hg2
  have hg32 : moment (mY q) ((3 : ℝ) / 2) g ≤ 1 :=
    moment_three_halves_le_one hqY hg2m
  let A : ℝ := moment (mX q) 3 f
  have hA0 : 0 ≤ A := moment_nonneg hqX.nonneg _ _
  have habs_cube : ∀ x, |f x| ^ (3 : ℝ) = (f x * |f x|) * f x := by
    intro x
    calc
      |f x| ^ (3 : ℝ) = |f x| ^ (3 : ℕ) := Real.rpow_ofNat _ _
      _ = |f x| ^ 2 * |f x| := by ring
      _ = f x ^ 2 * |f x| := by rw [sq_abs]
      _ = (f x * |f x|) * f x := by ring
  have heq : ρ * A = ∑ z, q z * (f z.1 * |f z.1|) * g z.2 := by
    rw [Fintype.sum_prod_type]
    calc
      ρ * A = ∑ x, ρ * (mX q x * |f x| ^ (3 : ℝ)) := by
        dsimp [A, moment]
        rw [Finset.mul_sum]
      _ = ∑ x, (f x * |f x|) * (ρ * (mX q x * f x)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [habs_cube]
        ring
      _ = ∑ x, (f x * |f x|) * (∑ y, q (x, y) * g y) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hrel x]
      _ = ∑ x, ∑ y, q (x, y) * (f x * |f x|) * g y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
  have hsigned :
      (∑ z, q z * (f z.1 * |f z.1|) * g z.2)
        ≤ ∑ z, q z * (|f z.1| ^ (2 : ℝ)) * |g z.2| := by
    apply Finset.sum_le_sum
    intro z _
    calc
      q z * (f z.1 * |f z.1|) * g z.2
          ≤ q z * |(f z.1 * |f z.1|) * g z.2| := by
            have hz := mul_le_mul_of_nonneg_left
              (le_abs_self ((f z.1 * |f z.1|) * g z.2)) (hq.1.nonneg z)
            simpa [mul_assoc] using hz
      _ = q z * (|f z.1| ^ (2 : ℝ)) * |g z.2| := by
        rw [abs_mul, abs_mul, abs_abs, Real.rpow_two]
        ring
  have hhc := contact_hypercontractive hw hq
    (f := fun x => |f x| ^ (2 : ℝ)) (g := fun y => |g y|)
    (fun x => Real.rpow_nonneg (abs_nonneg _) _) (fun y => abs_nonneg _)
  have hhc_all :
      (∑ z, q z * (|f z.1| ^ (2 : ℝ)) * |g z.2|)
        ≤ (moment (mX q) 3 f) ^ ((2 : ℝ) / 3) *
          (moment (mY q) ((3 : ℝ) / 2) g) ^ ((2 : ℝ) / 3) := by
    have hsupp := sum_eq_sum_support hq.2.1
      (fun z => (|f z.1| ^ (2 : ℝ)) * |g z.2|)
    rw [show (∑ z, q z * (|f z.1| ^ (2 : ℝ)) * |g z.2|) =
        ∑ z ∈ S, q z * (|f z.1| ^ (2 : ℝ)) * |g z.2| by
      simpa [mul_assoc] using hsupp]
    have hpow : ∀ x, (|f x| ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) = |f x| ^ (3 : ℝ) := by
      intro x
      rw [← Real.rpow_mul (abs_nonneg _)]
      norm_num
    simp_rw [hpow] at hhc
    simpa [moment] using hhc
  have hmoment : ρ * A ≤ A ^ ((2 : ℝ) / 3) := by
    calc
      ρ * A = ∑ z, q z * (f z.1 * |f z.1|) * g z.2 := heq
      _ ≤ ∑ z, q z * (|f z.1| ^ (2 : ℝ)) * |g z.2| := hsigned
      _ ≤ A ^ ((2 : ℝ) / 3) *
          (moment (mY q) ((3 : ℝ) / 2) g) ^ ((2 : ℝ) / 3) := by simpa [A] using hhc_all
      _ ≤ A ^ ((2 : ℝ) / 3) * 1 := by
        apply mul_le_mul_of_nonneg_left
        · simpa using Real.rpow_le_rpow
            (moment_nonneg hqY.nonneg _ _) hg32 (by norm_num : (0 : ℝ) ≤ 2 / 3)
        · exact Real.rpow_nonneg hA0 _
      _ = A ^ ((2 : ℝ) / 3) := mul_one _
  exact le_inv_cube_of_mul_le_rpow_two_thirds hρ hA0 hmoment

private lemma singular_g_moment_three_le {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) {q : α × β → ℝ} (hq : IsContact S w q)
    {ρ : ℝ} (hρ : 0 < ρ) {f : α → ℝ} {g : β → ℝ}
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1) (hg2 : ∑ y, mY q y * g y ^ 2 = 1)
    (hrel : ∀ y, (∑ x, q (x, y) * f x) = ρ * (mY q y * g y)) :
    moment (mY q) 3 g ≤ ρ⁻¹ ^ 3 := by
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  have hf2m : moment (mX q) 2 f = 1 := by
    rw [moment_two_eq hqX.nonneg]
    exact hf2
  have hg2m : moment (mY q) 2 g = 1 := by
    rw [moment_two_eq hqY.nonneg]
    exact hg2
  have hf32 : moment (mX q) ((3 : ℝ) / 2) f ≤ 1 :=
    moment_three_halves_le_one hqX hf2m
  let A : ℝ := moment (mY q) 3 g
  have hA0 : 0 ≤ A := moment_nonneg hqY.nonneg _ _
  have habs_cube : ∀ y, |g y| ^ (3 : ℝ) = (g y * |g y|) * g y := by
    intro y
    calc
      |g y| ^ (3 : ℝ) = |g y| ^ (3 : ℕ) := Real.rpow_ofNat _ _
      _ = |g y| ^ 2 * |g y| := by ring
      _ = g y ^ 2 * |g y| := by rw [sq_abs]
      _ = (g y * |g y|) * g y := by ring
  have heq : ρ * A = ∑ z, q z * f z.1 * (g z.2 * |g z.2|) := by
    rw [Fintype.sum_prod_type]
    calc
      ρ * A = ∑ y, ρ * (mY q y * |g y| ^ (3 : ℝ)) := by
        dsimp [A, moment]
        rw [Finset.mul_sum]
      _ = ∑ y, (g y * |g y|) * (ρ * (mY q y * g y)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [habs_cube]
        ring
      _ = ∑ y, (g y * |g y|) * (∑ x, q (x, y) * f x) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [hrel y]
      _ = ∑ x, ∑ y, q (x, y) * f x * (g y * |g y|) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hsigned :
      (∑ z, q z * f z.1 * (g z.2 * |g z.2|))
        ≤ ∑ z, q z * |f z.1| * (|g z.2| ^ (2 : ℝ)) := by
    apply Finset.sum_le_sum
    intro z _
    calc
      q z * f z.1 * (g z.2 * |g z.2|)
          ≤ q z * |f z.1 * (g z.2 * |g z.2|)| := by
            have hz := mul_le_mul_of_nonneg_left
              (le_abs_self (f z.1 * (g z.2 * |g z.2|))) (hq.1.nonneg z)
            simpa [mul_assoc] using hz
      _ = q z * |f z.1| * (|g z.2| ^ (2 : ℝ)) := by
        rw [abs_mul, abs_mul, abs_abs, Real.rpow_two]
        ring
  have hhc := contact_hypercontractive hw hq
    (f := fun x => |f x|) (g := fun y => |g y| ^ (2 : ℝ))
    (fun x => abs_nonneg _) (fun y => Real.rpow_nonneg (abs_nonneg _) _)
  have hhc_all :
      (∑ z, q z * |f z.1| * (|g z.2| ^ (2 : ℝ)))
        ≤ (moment (mX q) ((3 : ℝ) / 2) f) ^ ((2 : ℝ) / 3) *
          (moment (mY q) 3 g) ^ ((2 : ℝ) / 3) := by
    have hsupp := sum_eq_sum_support hq.2.1
      (fun z => |f z.1| * (|g z.2| ^ (2 : ℝ)))
    rw [show (∑ z, q z * |f z.1| * (|g z.2| ^ (2 : ℝ))) =
        ∑ z ∈ S, q z * |f z.1| * (|g z.2| ^ (2 : ℝ)) by
      simpa [mul_assoc] using hsupp]
    have hpow : ∀ y, (|g y| ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) = |g y| ^ (3 : ℝ) := by
      intro y
      rw [← Real.rpow_mul (abs_nonneg _)]
      norm_num
    simp_rw [hpow] at hhc
    simpa [moment] using hhc
  have hmoment : ρ * A ≤ A ^ ((2 : ℝ) / 3) := by
    calc
      ρ * A = ∑ z, q z * f z.1 * (g z.2 * |g z.2|) := heq
      _ ≤ ∑ z, q z * |f z.1| * (|g z.2| ^ (2 : ℝ)) := hsigned
      _ ≤ (moment (mX q) ((3 : ℝ) / 2) f) ^ ((2 : ℝ) / 3) *
          A ^ ((2 : ℝ) / 3) := by simpa [A] using hhc_all
      _ ≤ 1 * A ^ ((2 : ℝ) / 3) := by
        apply mul_le_mul_of_nonneg_right
        · simpa using Real.rpow_le_rpow
            (moment_nonneg hqX.nonneg _ _) hf32 (by norm_num : (0 : ℝ) ≤ 2 / 3)
        · exact Real.rpow_nonneg hA0 _
      _ = A ^ ((2 : ℝ) / 3) := one_mul _
  exact le_inv_cube_of_mul_le_rpow_two_thirds hρ hA0 hmoment

private lemma singular_product_moment_le {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) {q : α × β → ℝ} (hq : IsContact S w q)
    {ρ : ℝ} (hρ : 0 < ρ) {f : α → ℝ} {g : β → ℝ}
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1) (hg2 : ∑ y, mY q y * g y ^ 2 = 1)
    (hf3 : moment (mX q) 3 f ≤ ρ⁻¹ ^ 3)
    (hg3 : moment (mY q) 3 g ≤ ρ⁻¹ ^ 3) :
    moment q ((3 : ℝ) / 2) (fun z => f z.1 * g z.2) ≤ ρ⁻¹ := by
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  have hf2m : moment (mX q) 2 f = 1 := by
    rw [moment_two_eq hqX.nonneg]
    exact hf2
  have hg2m : moment (mY q) 2 g = 1 := by
    rw [moment_two_eq hqY.nonneg]
    exact hg2
  have hρinv0 : 0 ≤ ρ⁻¹ := (inv_pos.mpr hρ).le
  have hinvpow : (ρ⁻¹ ^ (3 : ℕ)) ^ ((1 : ℝ) / 4) = ρ⁻¹ ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρinv0]
    norm_num
  have hf94 : moment (mX q) ((9 : ℝ) / 4) f ≤ ρ⁻¹ ^ ((3 : ℝ) / 4) := by
    calc
      moment (mX q) ((9 : ℝ) / 4) f
          ≤ (moment (mX q) 2 f) ^ ((3 : ℝ) / 4) *
            (moment (mX q) 3 f) ^ ((1 : ℝ) / 4) :=
        moment_nine_fourths_interpolate hqX.nonneg f
      _ = (moment (mX q) 3 f) ^ ((1 : ℝ) / 4) := by rw [hf2m]; norm_num
      _ ≤ (ρ⁻¹ ^ 3) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow
        (moment_nonneg hqX.nonneg _ _) hf3 (by norm_num)
      _ = ρ⁻¹ ^ ((3 : ℝ) / 4) := hinvpow
  have hg94 : moment (mY q) ((9 : ℝ) / 4) g ≤ ρ⁻¹ ^ ((3 : ℝ) / 4) := by
    calc
      moment (mY q) ((9 : ℝ) / 4) g
          ≤ (moment (mY q) 2 g) ^ ((3 : ℝ) / 4) *
            (moment (mY q) 3 g) ^ ((1 : ℝ) / 4) :=
        moment_nine_fourths_interpolate hqY.nonneg g
      _ = (moment (mY q) 3 g) ^ ((1 : ℝ) / 4) := by rw [hg2m]; norm_num
      _ ≤ (ρ⁻¹ ^ 3) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow
        (moment_nonneg hqY.nonneg _ _) hg3 (by norm_num)
      _ = ρ⁻¹ ^ ((3 : ℝ) / 4) := hinvpow
  have hhc := contact_hypercontractive hw hq
    (f := fun x => |f x| ^ ((3 : ℝ) / 2))
    (g := fun y => |g y| ^ ((3 : ℝ) / 2))
    (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    (fun y => Real.rpow_nonneg (abs_nonneg _) _)
  have hhc_all :
      moment q ((3 : ℝ) / 2) (fun z => f z.1 * g z.2)
        ≤ (moment (mX q) ((9 : ℝ) / 4) f) ^ ((2 : ℝ) / 3) *
          (moment (mY q) ((9 : ℝ) / 4) g) ^ ((2 : ℝ) / 3) := by
    have hprod : ∀ z : α × β, |f z.1 * g z.2| ^ ((3 : ℝ) / 2) =
        |f z.1| ^ ((3 : ℝ) / 2) * |g z.2| ^ ((3 : ℝ) / 2) := by
      intro z
      rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    have hsupp := sum_eq_sum_support hq.2.1
      (fun z => |f z.1| ^ ((3 : ℝ) / 2) * |g z.2| ^ ((3 : ℝ) / 2))
    rw [moment]
    simp_rw [hprod]
    rw [show (∑ z, q z *
          (|f z.1| ^ ((3 : ℝ) / 2) * |g z.2| ^ ((3 : ℝ) / 2))) =
        ∑ z ∈ S, q z * |f z.1| ^ ((3 : ℝ) / 2) *
          |g z.2| ^ ((3 : ℝ) / 2) by simpa [mul_assoc] using hsupp]
    have hpowf : ∀ x, (|f x| ^ ((3 : ℝ) / 2)) ^ ((3 : ℝ) / 2) =
        |f x| ^ ((9 : ℝ) / 4) := by
      intro x
      rw [← Real.rpow_mul (abs_nonneg _)]
      norm_num

    have hpowg : ∀ y, (|g y| ^ ((3 : ℝ) / 2)) ^ ((3 : ℝ) / 2) =
        |g y| ^ ((9 : ℝ) / 4) := by
      intro y
      rw [← Real.rpow_mul (abs_nonneg _)]
      norm_num
    simp_rw [hpowf, hpowg] at hhc
    simpa [moment] using hhc
  calc
    moment q ((3 : ℝ) / 2) (fun z => f z.1 * g z.2)
        ≤ (moment (mX q) ((9 : ℝ) / 4) f) ^ ((2 : ℝ) / 3) *
          (moment (mY q) ((9 : ℝ) / 4) g) ^ ((2 : ℝ) / 3) := hhc_all
    _ ≤ (ρ⁻¹ ^ ((3 : ℝ) / 4)) ^ ((2 : ℝ) / 3) *
        (ρ⁻¹ ^ ((3 : ℝ) / 4)) ^ ((2 : ℝ) / 3) := by
      exact mul_le_mul
        (Real.rpow_le_rpow (moment_nonneg hqX.nonneg _ _) hf94 (by norm_num))
        (Real.rpow_le_rpow (moment_nonneg hqY.nonneg _ _) hg94 (by norm_num))
        (Real.rpow_nonneg (moment_nonneg hqY.nonneg _ _) _)
        (Real.rpow_nonneg (Real.rpow_nonneg hρinv0 _) _)
    _ = ρ⁻¹ := by
      rw [← Real.rpow_mul hρinv0,
        ← Real.rpow_add' hρinv0 (by norm_num :
          (3 : ℝ) / 4 * (2 / 3) + 3 / 4 * (2 / 3) ≠ 0)]
      norm_num

private lemma independent_product_moment_le_one {q : α × β → ℝ} (hq : IsPMF q)
    {f : α → ℝ} {g : β → ℝ}
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1) (hg2 : ∑ y, mY q y * g y ^ 2 = 1) :
    moment (fun z : α × β => mX q z.1 * mY q z.2) ((3 : ℝ) / 2)
      (fun z : α × β => f z.1 * g z.2) ≤ 1 := by
  have hqX : IsPMF (mX q) := isPMF_push hq
  have hqY : IsPMF (mY q) := isPMF_push hq
  have hf2m : moment (mX q) 2 f = 1 := by
    rw [moment_two_eq hqX.nonneg]
    exact hf2
  have hg2m : moment (mY q) 2 g = 1 := by
    rw [moment_two_eq hqY.nonneg]
    exact hg2
  have hf32 := moment_three_halves_le_one hqX hf2m
  have hg32 := moment_three_halves_le_one hqY hg2m
  have hfactor :
      moment (fun z : α × β => mX q z.1 * mY q z.2) ((3 : ℝ) / 2)
          (fun z : α × β => f z.1 * g z.2)
        = moment (mX q) ((3 : ℝ) / 2) f * moment (mY q) ((3 : ℝ) / 2) g := by
    unfold moment
    rw [Fintype.sum_prod_type]
    have hprod : ∀ x y, |f x * g y| ^ ((3 : ℝ) / 2) =
        |f x| ^ ((3 : ℝ) / 2) * |g y| ^ ((3 : ℝ) / 2) := by
      intro x y
      rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    simp_rw [hprod]
    calc
      ∑ x, ∑ y, (mX q x * mY q y) *
          (|f x| ^ ((3 : ℝ) / 2) * |g y| ^ ((3 : ℝ) / 2)) =
          ∑ x, (mX q x * |f x| ^ ((3 : ℝ) / 2)) *
            (∑ y, mY q y * |g y| ^ ((3 : ℝ) / 2)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = (∑ x, mX q x * |f x| ^ ((3 : ℝ) / 2)) *
          (∑ y, mY q y * |g y| ^ ((3 : ℝ) / 2)) := by rw [Finset.sum_mul]
  rw [hfactor]
  nlinarith [moment_nonneg hqX.nonneg ((3 : ℝ) / 2) f,
    moment_nonneg hqY.nonneg ((3 : ℝ) / 2) g]

private lemma tvDist_ge_of_test {ι : Type*} [Fintype ι]
    {P Q : ι → ℝ} (hP : IsPMF P) (hQ : IsPMF Q) {Z : ι → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hEP : ∑ i, P i * Z i = ρ) (hEQ : ∑ i, Q i * Z i = 0)
    (hMP : moment P ((3 : ℝ) / 2) Z ≤ ρ⁻¹)
    (hMQ : moment Q ((3 : ℝ) / 2) Z ≤ 1) :
    2 * ρ ^ 5 / (27 * (1 + ρ) ^ 2) ≤ tvDist P Q := by
  let t : ℝ := 3 * (1 + ρ) / (2 * ρ ^ 2)
  let C : ι → ℝ := fun i => max (-(t ^ 2)) (min (t ^ 2) (Z i))
  let eP : ℝ := ∑ i, P i * (Z i - C i)
  let eQ : ℝ := ∑ i, Q i * (Z i - C i)
  let d : ℝ := (∑ i, P i * C i) - ∑ i, Q i * C i
  have hρ1 : 0 < 1 + ρ := by linarith
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (mul_pos (by norm_num) hρ1) (mul_pos (by norm_num) (sq_pos_of_pos hρ))
  have heP0 := abs_weighted_clipping_error_le hP.nonneg (Z := Z) ht
  have heP : |eP| ≤ ρ⁻¹ / t := by
    exact heP0.trans ((div_le_div_iff_of_pos_right ht).2 hMP)
  have heQ0 := abs_weighted_clipping_error_le hQ.nonneg (Z := Z) ht
  have heQ : |eQ| ≤ 1 / t := by
    exact heQ0.trans ((div_le_div_iff_of_pos_right ht).2 hMQ)
  have hd : |d| ≤ 2 * t ^ 2 * tvDist P Q := by
    exact abs_expectation_sub_le_tv (P := P) (Q := Q) (F := C) (B := t ^ 2)
      (sq_nonneg t) (fun i => abs_clip_le (sq_nonneg t))
  have hsplitP : (∑ i, P i * Z i) = eP + ∑ i, P i * C i := by
    dsimp [eP]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsplitQ : (∑ i, Q i * Z i) = eQ + ∑ i, Q i * C i := by
    dsimp [eQ]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdecomp : ρ = eP + d - eQ := by
    calc
      ρ = (∑ i, P i * Z i) - ∑ i, Q i * Z i := by rw [hEP, hEQ]; ring
      _ = eP + d - eQ := by rw [hsplitP, hsplitQ]; dsimp [d]; ring
  have htri : ρ ≤ |eP| + |d| + |eQ| := by
    rw [hdecomp]
    nlinarith [le_abs_self eP, le_abs_self d, neg_le_abs eQ]
  have hmain : ρ ≤ ρ⁻¹ / t + 2 * t ^ 2 * tvDist P Q + 1 / t := by
    linarith
  have htail : ρ⁻¹ / t + 1 / t = 2 * ρ / 3 := by
    dsimp [t]
    field_simp [hρ.ne', hρ1.ne']
    <;> ring
  have hmain' : ρ ≤ 2 * t ^ 2 * tvDist P Q + 2 * ρ / 3 := by
    rw [← htail]
    linarith
  have hden : 0 < 6 * t ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos ht)
  have heta : ρ / (6 * t ^ 2) ≤ tvDist P Q := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hid : ρ / (6 * t ^ 2) = 2 * ρ ^ 5 / (27 * (1 + ρ) ^ 2) := by
    dsimp [t]
    field_simp [hρ.ne', hρ1.ne']
    <;> ring
  rwa [← hid]

private lemma Ixy_eq_KL_product {q : α × β → ℝ} (hq : IsPMF q) :
    Ixy q = KL q (fun z => mX q z.1 * mY q z.2) := by
  let Q : α × β → ℝ := fun z => mX q z.1 * mY q z.2
  have hqX : IsPMF (mX q) := isPMF_push hq
  have hqY : IsPMF (mY q) := isPMF_push hq
  have hQ : IsPMF Q := product_isPMF hqX hqY
  have hac : AbsCont q Q := by
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
    exact (mul_ne_zero hxpos.ne' hypos.ne') (by simpa [Q] using hQz)
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
  have hliftq : ∑ z, Real.negMulLog (q z) = ∑ z, q z * (-Real.log (q z)) := by
    apply Finset.sum_congr rfl
    intro z _
    rw [Real.negMulLog]
    ring
  have hEntropyKL :
      (∑ x, Real.negMulLog (mX q x)) + (∑ y, Real.negMulLog (mY q y))
          - ∑ z, Real.negMulLog (q z) =
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
      _ = (∑ x, Real.negMulLog (mX q x)) + (∑ y, Real.negMulLog (mY q y))
          - ∑ z, Real.negMulLog (q z) := by rw [hEq_X, hEq_Y, hEq_q]
      _ = ∑ z, q z * Real.log (q z / Q z) := hEntropyKL
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hKL_nats : Real.log 2 * KL q Q = ∑ z, q z * Real.log (q z / Q z) := by
    unfold KL
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [lg_eq_log_div]
    field_simp [hlog]
  have : Real.log 2 * Ixy q = Real.log 2 * KL q Q := hI_nats.trans hKL_nats.symm
  have hresult : Ixy q = KL q Q := by nlinarith [Real.log_pos one_lt_two]
  simpa [Q] using hresult

private lemma tv_ge_of_hgr_core {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) {q : α × β → ℝ} (hq : IsContact S w q)
    (hrho : 0 < rhoHGR q) :
    2 * rhoHGR q ^ 5 / (27 * (1 + rhoHGR q) ^ 2)
      ≤ tvDist q (fun z => mX q z.1 * mY q z.2) := by
  rcases exists_hgr_singular_pair hw hq hrho with
    ⟨f, g, hf0, hg0, hf2, hg2, hcorr, hrelf, hrelg⟩
  let Q : α × β → ℝ := fun z => mX q z.1 * mY q z.2
  let Z : α × β → ℝ := fun z => f z.1 * g z.2
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  have hQ : IsPMF Q := product_isPMF hqX hqY
  have hf3 : moment (mX q) 3 f ≤ (rhoHGR q)⁻¹ ^ 3 :=
    singular_f_moment_three_le hw hq hrho hf2 hg2 hrelf
  have hg3 : moment (mY q) 3 g ≤ (rhoHGR q)⁻¹ ^ 3 :=
    singular_g_moment_three_le hw hq hrho hf2 hg2 hrelg
  have hMP : moment q ((3 : ℝ) / 2) Z ≤ (rhoHGR q)⁻¹ := by
    exact singular_product_moment_le hw hq hrho hf2 hg2 hf3 hg3
  have hMQ : moment Q ((3 : ℝ) / 2) Z ≤ 1 := by
    exact independent_product_moment_le_one hq.1 hf2 hg2
  have hEP : ∑ z, q z * Z z = rhoHGR q := by
    simpa [Z, mul_assoc] using hcorr
  have hEQ : ∑ z, Q z * Z z = 0 := by
    dsimp [Q, Z]
    rw [Fintype.sum_prod_type]
    calc
      ∑ x, ∑ y, (mX q x * mY q y) * (f x * g y) =
          ∑ x, (mX q x * f x) * (∑ y, mY q y * g y) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = 0 := by rw [hg0]; simp
  have htv := tvDist_ge_of_test hq.1 hQ hrho hEP hEQ hMP hMQ
  simpa [Q] using htv

/-- **Theorem 6.1** (alphabet-free HGR information floor).
For a contact `q` of a feasible kernel with `ρ := ρ_HGR(q) > 0`, in bits:
`I_q(X;Y) ≥ 8ρ¹⁰ / (729 (1+ρ)⁴ ln 2)`.

The constant is alphabet-free — no dependence on `|𝒳|`, `|𝒴|` or `|𝒮|`, which
is what makes the Main Theorem's constant universal. -/
theorem Ixy_ge_hgr_floor {S : Finset (α × β)} {w : α × β → ℝ} (hw : Feasible S w)
    {q : α × β → ℝ} (hq : IsContact S w q) (hrho : 0 < rhoHGR q) :
    8 * rhoHGR q ^ 10 / (729 * (1 + rhoHGR q) ^ 4 * Real.log 2) ≤ Ixy q := by
  let Q : α × β → ℝ := fun z => mX q z.1 * mY q z.2
  let a : ℝ := 2 * rhoHGR q ^ 5 / (27 * (1 + rhoHGR q) ^ 2)
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  have hQ : IsPMF Q := product_isPMF hqX hqY
  have hac : AbsCont q Q := by
    intro z hQz
    by_contra hqz
    have hqpos : 0 < q z := lt_of_le_of_ne (hq.1.nonneg z) (Ne.symm hqz)
    have hxle : q z ≤ mX q z.1 := by
      change q z ≤ push Prod.fst q z.1
      unfold push
      exact Finset.single_le_sum (fun u _ => hq.1.nonneg u) (by simp)
    have hyle : q z ≤ mY q z.2 := by
      change q z ≤ push Prod.snd q z.2
      unfold push
      exact Finset.single_le_sum (fun u _ => hq.1.nonneg u) (by simp)
    have hxpos : 0 < mX q z.1 := lt_of_lt_of_le hqpos hxle
    have hypos : 0 < mY q z.2 := lt_of_lt_of_le hqpos hyle
    exact (mul_ne_zero hxpos.ne' hypos.ne') (by simpa [Q] using hQz)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have htv : a ≤ tvDist q Q := by
    have h := tv_ge_of_hgr_core hw hq hrho
    simpa [a, Q] using h
  have htvd0 : 0 ≤ tvDist q Q := by
    unfold tvDist
    positivity
  have hsq : a ^ 2 ≤ tvDist q Q ^ 2 := by
    nlinarith
  have hpinsker : 2 / Real.log 2 * tvDist q Q ^ 2 ≤ Ixy q := by
    calc
      2 / Real.log 2 * tvDist q Q ^ 2 ≤ KL q Q := pinsker hq.1 hQ hac
      _ = Ixy q := by simpa [Q] using (Ixy_eq_KL_product hq.1).symm
  calc
    8 * rhoHGR q ^ 10 / (729 * (1 + rhoHGR q) ^ 4 * Real.log 2)
        = 2 / Real.log 2 * a ^ 2 := by
          dsimp [a]
          have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
          have hone : 1 + rhoHGR q ≠ 0 := by linarith
          field_simp [hlog, hone]
          <;> ring
    _ ≤ 2 / Real.log 2 * tvDist q Q ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq
        (div_nonneg (by norm_num) (Real.log_pos one_lt_two).le)
    _ ≤ Ixy q := hpinsker

/-- The intermediate TV bound of Theorem 6.1:
`TV(q, q_X ⊗ q_Y) ≥ 2ρ⁵ / (27(1+ρ)²)`. Isolated as the substance of the clipping argument. -/
theorem tv_ge_of_hgr {S : Finset (α × β)} {w : α × β → ℝ} (hw : Feasible S w)
    {q : α × β → ℝ} (hq : IsContact S w q) (hrho : 0 < rhoHGR q) :
    2 * rhoHGR q ^ 5 / (27 * (1 + rhoHGR q) ^ 2)
      ≤ TV q (fun z => mX q z.1 * mY q z.2) := by
  simpa [TV, tvDist] using tv_ge_of_hgr_core hw hq hrho

private lemma rhoHGR_gt_one_sixteen_of_contacts
    {S : Finset (α × β)} {w q r : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q) (hr : IsContact S w r)
    (hqs : support q = S) (hrs : support r = S) (hne : q ≠ r)
    (hclose : tvDist q r ≤ deltaStar) :
    1 / 16 < rhoHGR q := by
  let f : α → ℝ := fun x => (mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1
  let g : β → ℝ := fun y => (mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1
  let af : ℝ := normThree (mX q) f
  let ag : ℝ := normThree (mY q) g
  let d : ℝ := max af ag
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  have hsupp : support q = support r := hqs.trans hrs.symm
  have hsmall := ratio_root_smallness hq.1 hr.1 hsupp
  have haf0 : 0 ≤ af := normThree_nonneg hqX.nonneg f
  have hag0 : 0 ≤ ag := normThree_nonneg hqY.nonneg g
  have hafcube : af ^ 3 = moment (mX q) 3 f := normThree_cube hqX.nonneg f
  have hagcube : ag ^ 3 = moment (mY q) 3 g := normThree_cube hqY.nonneg g
  have haf3 : af ^ 3 ≤ 2 * deltaStar := by
    rw [hafcube]
    exact hsmall.1.trans (mul_le_mul_of_nonneg_left hclose (by norm_num))
  have hag3 : ag ^ 3 ≤ 2 * deltaStar := by
    rw [hagcube]
    exact hsmall.2.trans (mul_le_mul_of_nonneg_left hclose (by norm_num))
  have haf_le : af ≤ 3 / 100 := by
    apply (pow_le_pow_iff_left₀ haf0 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).mp
    calc
      af ^ 3 ≤ 2 * deltaStar := haf3
      _ = (3 / 100 : ℝ) ^ 3 := by norm_num [deltaStar]
  have hag_le : ag ≤ 3 / 100 := by
    apply (pow_le_pow_iff_left₀ hag0 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).mp
    calc
      ag ^ 3 ≤ 2 * deltaStar := hag3
      _ = (3 / 100 : ℝ) ^ 3 := by norm_num [deltaStar]
  have hd0 : 0 ≤ d := by dsimp [d]; exact haf0.trans (le_max_left af ag)
  have hd_le : d ≤ 3 / 100 := by dsimp [d]; exact max_le haf_le hag_le
  have hdpos : 0 < d := by
    by_contra hnot
    have hd_nonpos : d ≤ 0 := le_of_not_gt hnot
    have hafz : af = 0 := le_antisymm ((le_max_left af ag).trans hd_nonpos) haf0
    have hagz : ag = 0 := le_antisymm ((le_max_right af ag).trans hd_nonpos) hag0
    have hfmom : moment (mX q) 3 f = 0 := by rw [← hafcube, hafz]; norm_num
    have hgmom : moment (mY q) 3 g = 0 := by rw [← hagcube, hagz]; norm_num
    have hratio := contact_ratio_eq hq hr hqs hrs
    apply hne
    funext z
    by_cases hz : z ∈ S
    · have hqmem : z ∈ support q := by simpa [hqs] using hz
      have hqne : q z ≠ 0 := by simpa [support] using hqmem
      have hqpos : 0 < q z := lt_of_le_of_ne (hq.1.nonneg z) (Ne.symm hqne)
      have hxpos : 0 < mX q z.1 := by
        have hxle : q z ≤ mX q z.1 := by
          rw [mX_eq_sum]
          exact Finset.single_le_sum (fun y _ => hq.1.nonneg (z.1, y))
            (Finset.mem_univ z.2)
        exact hqpos.trans_le hxle
      have hypos : 0 < mY q z.2 := by
        have hyle : q z ≤ mY q z.2 := by
          rw [mY_eq_sum]
          exact Finset.single_le_sum (fun x _ => hq.1.nonneg (x, z.2))
            (Finset.mem_univ z.1)
        exact hqpos.trans_le hyle
      have hfz : f z.1 = 0 :=
        value_eq_zero_of_moment_three_eq_zero hqX.nonneg hfmom hxpos.ne'
      have hgz : g z.2 = 0 :=
        value_eq_zero_of_moment_three_eq_zero hqY.nonneg hgmom hypos.ne'
      have hF : (mX r z.1 / mX q z.1) ^ ((1 : ℝ) / 3) = 1 := by
        dsimp [f] at hfz
        linarith
      have hG : (mY r z.2 / mY q z.2) ^ ((1 : ℝ) / 3) = 1 := by
        dsimp [g] at hgz
        linarith
      symm
      have hratioz := hratio z
      rw [hF, hG] at hratioz
      norm_num at hratioz
      exact hratioz
    · rw [hq.2.1 z hz, hr.2.1 z hz]
  let a : ℝ := normTwo (mX q) f
  let b : ℝ := normTwo (mY q) g
  have ha0 : 0 ≤ a := normTwo_nonneg hqX.nonneg f
  have hb0 : 0 ≤ b := normTwo_nonneg hqY.nonneg g
  have ha_le_af : a ≤ af := normTwo_le_normThree hqX f
  have hb_le_ag : b ≤ ag := normTwo_le_normThree hqY g
  have haf_le_d : af ≤ d := by dsimp [d]; exact le_max_left _ _
  have hag_le_d : ag ≤ d := by dsimp [d]; exact le_max_right _ _
  have haf_sq : af ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ haf0 haf_le_d 2
  have hag_sq : ag ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hag0 hag_le_d 2
  have hsec :
      (∀ x, mX q x * f x =
        2 * (∑ y, q (x, y) * g y) + ∑ y, q (x, y) * g y ^ 2) ∧
      (∀ y, mY q y * g y =
        2 * (∑ x, q (x, y) * f x) + ∑ x, q (x, y) * f x ^ 2) := by
    simpa [f, g] using secant_expanded_equations hq hr hqs hrs
  have hrelX : af ≤ 2 * b + ag ^ 2 := by
    simpa [af, b] using secant_X_norm_relation hw hq hsec.1
  have hrelY : ag ≤ 2 * a + af ^ 2 := by
    simpa [ag, a] using secant_Y_norm_relation hw hq hsec.2
  have ha_lower : (d - 3 * d ^ 2) / 4 ≤ a := by
    rcases le_total af ag with hfg | hgf
    · have hd_eq : d = ag := by dsimp [d]; exact max_eq_right hfg
      nlinarith
    · have hd_eq : d = af := by dsimp [d]; exact max_eq_left hgf
      nlinarith
  have hb_lower : (d - 3 * d ^ 2) / 4 ≤ b := by
    rcases le_total af ag with hfg | hgf
    · have hd_eq : d = ag := by dsimp [d]; exact max_eq_right hfg
      nlinarith
    · have hd_eq : d = af := by dsimp [d]; exact max_eq_left hgf
      nlinarith
  let μf : ℝ := weightedMean (mX q) f
  let μg : ℝ := weightedMean (mY q) g
  have hrX : IsPMF (mX r) := isPMF_push hr.1
  have hrY : IsPMF (mY r) := isPMF_push hr.1
  have hmeanf_raw : |μf| ≤ a ^ 2 + af ^ 3 / 3 := by
    simpa [μf, f, a, af] using ratio_root_mean_bound hqX hrX
      (fun x => mX_zero_iff_of_support_eq hq.1 hr.1 hsupp x)
  have hmeang_raw : |μg| ≤ b ^ 2 + ag ^ 3 / 3 := by
    simpa [μg, g, b, ag] using ratio_root_mean_bound hqY hrY
      (fun y => mY_zero_iff_of_support_eq hq.1 hr.1 hsupp y)
  have ha_sq : a ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ ha0 (ha_le_af.trans haf_le_d) 2
  have hb_sq : b ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hb0 (hb_le_ag.trans hag_le_d) 2
  have haf_cubed : af ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ haf0 haf_le_d 3
  have hag_cubed : ag ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ hag0 hag_le_d 3
  have hd_one : d ≤ 1 := hd_le.trans (by norm_num)
  have hd_cube_le_sq : d ^ 3 ≤ d ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hd_one)]
  have hmeanf : |μf| ≤ (4 : ℝ) / 3 * d ^ 2 := by nlinarith
  have hmeang : |μg| ≤ (4 : ℝ) / 3 * d ^ 2 := by nlinarith
  let f₀ : α → ℝ := centered (mX q) f
  let g₀ : β → ℝ := centered (mY q) g
  let a₀ : ℝ := normTwo (mX q) f₀
  let b₀ : ℝ := normTwo (mY q) g₀
  have ha₀0 : 0 ≤ a₀ := normTwo_nonneg hqX.nonneg f₀
  have hb₀0 : 0 ≤ b₀ := normTwo_nonneg hqY.nonneg g₀
  have ha_center := normTwo_le_centered_add_abs_mean hqX f
  have hb_center := normTwo_le_centered_add_abs_mean hqY g
  have ha_center' : a ≤ a₀ + |μf| := by simpa [a, a₀, f₀, μf] using ha_center
  have hb_center' : b ≤ b₀ + |μg| := by simpa [b, b₀, g₀, μg] using hb_center
  have hd_gap : 0 ≤ d * ((3 : ℝ) / 100 - d) :=
    mul_nonneg hd0 (sub_nonneg.mpr hd_le)
  have ha₀_lower : 3 * d / 16 ≤ a₀ := by
    nlinarith only [ha_lower, ha_center', hmeanf, hd_gap]
  have hb₀_lower : 3 * d / 16 ≤ b₀ := by
    nlinarith only [hb_lower, hb_center', hmeang, hd_gap]
  have ha₀pos : 0 < a₀ := lt_of_lt_of_le (by positivity : 0 < 3 * d / 16) ha₀_lower
  have hb₀pos : 0 < b₀ := lt_of_lt_of_le (by positivity : 0 < 3 * d / 16) hb₀_lower
  have hf₀mean : weightedMean (mX q) f₀ = 0 := by
    simpa [f₀] using weightedMean_centered_eq_zero hqX f
  have hg₀mean : weightedMean (mY q) g₀ = 0 := by
    simpa [g₀] using weightedMean_centered_eq_zero hqY g
  let c₀ : ℝ := ∑ z, q z * f₀ z.1 * g₀ z.2
  let E : ℝ := ∑ z, q z * f₀ z.1 * g z.2 ^ 2
  have ha₀sq_sum : a₀ ^ 2 = ∑ x, mX q x * f₀ x ^ 2 := by
    rw [normTwo_sq hqX.nonneg, moment_two_eq hqX.nonneg]
  have hleft : (∑ x, mX q x * f₀ x * f x) = a₀ ^ 2 := by
    have hpoint : ∀ x, f x = f₀ x + μf := by
      intro x
      dsimp [f₀, centered, μf]
      ring
    calc
      ∑ x, mX q x * f₀ x * f x =
          ∑ x, (mX q x * f₀ x ^ 2 + μf * (mX q x * f₀ x)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hpoint x]
        ring
      _ = (∑ x, mX q x * f₀ x ^ 2) + μf * weightedMean (mX q) f₀ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
      _ = a₀ ^ 2 := by rw [hf₀mean, mul_zero, add_zero, ha₀sq_sum]
  have hsec_sum : (∑ x, mX q x * f₀ x * f x) =
      2 * (∑ z, q z * f₀ z.1 * g z.2) + E := by
    calc
      ∑ x, mX q x * f₀ x * f x =
          ∑ x, f₀ x * (mX q x * f x) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = ∑ x, f₀ x *
          (2 * (∑ y, q (x, y) * g y) + ∑ y, q (x, y) * g y ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hsec.1 x]
      _ = 2 * (∑ z, q z * f₀ z.1 * g z.2) + E := by
        have hfirst : (∑ x, f₀ x * (∑ y, q (x, y) * g y)) =
            ∑ z, q z * f₀ z.1 * g z.2 := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
        have hsecond : (∑ x, f₀ x * (∑ y, q (x, y) * g y ^ 2)) =
            ∑ z, q z * f₀ z.1 * g z.2 ^ 2 := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
        dsimp [E]
        rw [show (∑ x, f₀ x *
            (2 * (∑ y, q (x, y) * g y) + ∑ y, q (x, y) * g y ^ 2)) =
            ∑ x, (2 * (f₀ x * (∑ y, q (x, y) * g y)) +
              f₀ x * (∑ y, q (x, y) * g y ^ 2)) by
          apply Finset.sum_congr rfl
          intro x _
          ring]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfirst, hsecond]
  have hjoint_f₀ : ∑ z, q z * f₀ z.1 = 0 := by
    rw [← sum_push_mul Prod.fst q f₀]
    exact hf₀mean
  have hcenter_joint : (∑ z, q z * f₀ z.1 * g z.2) = c₀ := by
    have hpoint : ∀ y, g y = g₀ y + μg := by
      intro y
      dsimp [g₀, centered, μg]
      ring
    calc
      ∑ z, q z * f₀ z.1 * g z.2 =
          ∑ z, (q z * f₀ z.1 * g₀ z.2 + μg * (q z * f₀ z.1)) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [hpoint z.2]
        ring
      _ = c₀ + μg * (∑ z, q z * f₀ z.1) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = c₀ := by rw [hjoint_f₀, mul_zero, add_zero]
  have hidentity : a₀ ^ 2 = 2 * c₀ + E := by
    rw [← hleft, hsec_sum, hcenter_joint]
  have hEabs : |E| ≤ a₀ * ag ^ 2 := by
    simpa [E, a₀, ag] using abs_joint_mul_square_le hw hq f₀ g
  have hEabs_d : |E| ≤ a₀ * d ^ 2 :=
    hEabs.trans (mul_le_mul_of_nonneg_left hag_sq ha₀0)
  have hcorr_ineq : a₀ ^ 2 ≤ 2 * c₀ + a₀ * d ^ 2 := by
    rw [hidentity]
    linarith only [hEabs_d, le_abs_self E]
  have hb₀sq := normTwo_centered_sq hqY g
  have hb₀sq' : b₀ ^ 2 = b ^ 2 - μg ^ 2 := by
    simpa [b₀, g₀, b, μg] using hb₀sq
  have hb₀_le_b : b₀ ≤ b := by
    apply (pow_le_pow_iff_left₀ hb₀0 hb0 (by norm_num : (2 : ℕ) ≠ 0)).mp
    nlinarith only [hb₀sq', sq_nonneg μg]
  have hb₀_le_d : b₀ ≤ d := hb₀_le_b.trans (hb_le_ag.trans hag_le_d)
  have hd_lt_sixteenth : d < 1 / 16 := hd_le.trans_lt (by norm_num)
  have hgap_pos : 0 < d * ((1 : ℝ) / 16 - d) :=
    mul_pos hdpos (sub_pos.mpr hd_lt_sixteenth)
  have hgap_corr : b₀ / 8 < a₀ - d ^ 2 := by
    nlinarith only [ha₀_lower, hb₀_le_d, hgap_pos]
  have hscaled_gap : a₀ * b₀ / 8 < a₀ * (a₀ - d ^ 2) := by
    have := mul_lt_mul_of_pos_left hgap_corr ha₀pos
    nlinarith only [this]
  have hc₀_scaled : a₀ * b₀ / 16 < c₀ := by
    nlinarith only [hscaled_gap, hcorr_ineq]
  let fn : α → ℝ := fun x => f₀ x / a₀
  let gn : β → ℝ := fun y => g₀ y / b₀
  have hfn0 : ∑ x, mX q x * fn x = 0 := by
    calc
      ∑ x, mX q x * fn x = weightedMean (mX q) f₀ / a₀ := by
        dsimp [fn, weightedMean]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hf₀mean, zero_div]
  have hgn0 : ∑ y, mY q y * gn y = 0 := by
    calc
      ∑ y, mY q y * gn y = weightedMean (mY q) g₀ / b₀ := by
        dsimp [gn, weightedMean]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = 0 := by rw [hg₀mean, zero_div]
  have hfn2 : ∑ x, mX q x * fn x ^ 2 = 1 := by
    calc
      ∑ x, mX q x * fn x ^ 2 = (∑ x, mX q x * f₀ x ^ 2) / a₀ ^ 2 := by
        dsimp [fn]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        field_simp [ha₀pos.ne']
      _ = 1 := by rw [← ha₀sq_sum]; field_simp [ha₀pos.ne']
  have hb₀sq_sum : b₀ ^ 2 = ∑ y, mY q y * g₀ y ^ 2 := by
    rw [normTwo_sq hqY.nonneg, moment_two_eq hqY.nonneg]
  have hgn2 : ∑ y, mY q y * gn y ^ 2 = 1 := by
    calc
      ∑ y, mY q y * gn y ^ 2 = (∑ y, mY q y * g₀ y ^ 2) / b₀ ^ 2 := by
        dsimp [gn]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro y _
        field_simp [hb₀pos.ne']
      _ = 1 := by rw [← hb₀sq_sum]; field_simp [hb₀pos.ne']
  have hcorr_norm : (∑ z, q z * fn z.1 * gn z.2) = c₀ / (a₀ * b₀) := by
    dsimp [fn, gn, c₀]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z _
    field_simp [ha₀pos.ne', hb₀pos.ne']
  have hdenpos : 0 < a₀ * b₀ := mul_pos ha₀pos hb₀pos
  have hquot : 1 / 16 < c₀ / (a₀ * b₀) := by
    apply (lt_div_iff₀ hdenpos).2
    nlinarith only [hc₀_scaled]
  have hwitness : (∑ z, q z * fn z.1 * gn z.2) ≤ rhoHGR q :=
    correlation_le_rhoHGR hq.1 hfn0 hgn0 hfn2 hgn2
  rw [hcorr_norm] at hwitness
  exact hquot.trans_le hwitness

private lemma cStar_le_hgr_floor {rho : ℝ} (hrho : 1 / 16 ≤ rho) :
    cStar ≤ 8 * rho ^ 10 / (729 * (1 + rho) ^ 4 * Real.log 2) := by
  let a : ℝ := 1 / 16
  have ha0 : 0 ≤ a := by norm_num [a]
  have hap : 0 < a := by norm_num [a]
  have hrho0 : 0 ≤ rho := ha0.trans hrho
  have hrhop : 0 < rho := hap.trans_le hrho
  have haone : 0 < 1 + a := by positivity
  have hrhoone : 0 < 1 + rho := by positivity
  have hratio : a / (1 + a) ≤ rho / (1 + rho) := by
    apply (div_le_div_iff₀ haone hrhoone).2
    change ((1 : ℝ) / 16) * (1 + rho) ≤ rho * (1 + (1 : ℝ) / 16)
    nlinarith
  have hpow6 : a ^ 6 ≤ rho ^ 6 := pow_le_pow_left₀ ha0 hrho 6
  have hratio0 : 0 ≤ a / (1 + a) := div_nonneg ha0 haone.le
  have hratio_rho0 : 0 ≤ rho / (1 + rho) := div_nonneg hrho0 hrhoone.le
  have hpow4 : (a / (1 + a)) ^ 4 ≤ (rho / (1 + rho)) ^ 4 :=
    pow_le_pow_left₀ hratio0 hratio 4
  have hprod : a ^ 6 * (a / (1 + a)) ^ 4 ≤
      rho ^ 6 * (rho / (1 + rho)) ^ 4 :=
    mul_le_mul hpow6 hpow4 (pow_nonneg hratio0 4) (pow_nonneg hrho0 6)
  have hcoef0 : 0 ≤ 8 / (729 * Real.log 2) := by positivity
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  calc
    cStar = 8 * a ^ 10 / (729 * (1 + a) ^ 4 * Real.log 2) := by
      dsimp [a]
      unfold cStar
      norm_num [N]
      field_simp [hlog]
      norm_num
    _ = 8 / (729 * Real.log 2) *
        (a ^ 6 * (a / (1 + a)) ^ 4) := by
      field_simp [hlog, haone.ne']
    _ ≤ 8 / (729 * Real.log 2) *
        (rho ^ 6 * (rho / (1 + rho)) ^ 4) :=
      mul_le_mul_of_nonneg_left hprod hcoef0
    _ = 8 * rho ^ 10 / (729 * (1 + rho) ^ 4 * Real.log 2) := by
      field_simp [hlog, hrhoone.ne']

/-- **Theorem 6.2** (near-collision floor).
Two **distinct** contacts of one feasible kernel, both of full support on the
same connected `𝒮`, that are `δ_*`-close in total variation, both have
`ρ_HGR ≥ 1/16` and hence `I(X;Y) ≥ c_*`.

This drives Theorem 9.1's near/far dichotomy: clusters that nearly collide are
individually expensive, so `M = I(X;Y ∣ L)` pays for them. -/
theorem nearcollision_floor {S : Finset (α × β)} {w : α × β → ℝ} (hw : Feasible S w)
    (hS : IsConnected S) {q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) (hne : q ≠ r)
    (hclose : TV q r ≤ deltaStar) :
    1 / 16 ≤ rhoHGR q ∧ 1 / 16 ≤ rhoHGR r ∧ cStar ≤ Ixy q ∧ cStar ≤ Ixy r := by
  have hqs : support q = S := contact_support_eq hw hS hq
  have hrs : support r = S := contact_support_eq hw hS hr
  have hclose' : tvDist q r ≤ deltaStar := by simpa [TV, tvDist] using hclose
  have htvsym : tvDist r q = tvDist q r := by
    unfold tvDist
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    rw [abs_sub_comm]
  have hclose_rev : tvDist r q ≤ deltaStar := by rw [htvsym]; exact hclose'
  have hqgt : 1 / 16 < rhoHGR q :=
    rhoHGR_gt_one_sixteen_of_contacts hw hq hr hqs hrs hne hclose'
  have hrgt : 1 / 16 < rhoHGR r :=
    rhoHGR_gt_one_sixteen_of_contacts hw hr hq hrs hqs hne.symm hclose_rev
  have hqpos : 0 < rhoHGR q := (by norm_num : (0 : ℝ) < 1 / 16).trans hqgt
  have hrpos : 0 < rhoHGR r := (by norm_num : (0 : ℝ) < 1 / 16).trans hrgt
  have hIq := Ixy_ge_hgr_floor hw hq hqpos
  have hIr := Ixy_ge_hgr_floor hw hr hrpos
  have hcq : cStar ≤ Ixy q := (cStar_le_hgr_floor hqgt.le).trans hIq
  have hcr : cStar ≤ Ixy r := (cStar_le_hgr_floor hrgt.le).trans hIr
  exact ⟨hqgt.le, hrgt.le, hcq, hcr⟩

/-! ## Improved Hellinger floor

The historical TV/clipping argument above remains available.  The improved
proof uses squared Hellinger distance, exact secant moments, and the same HGR
singular-pair and contact-hypercontractivity API.
-/

/-- Squared Hellinger distance on a finite alphabet. -/
noncomputable def hellingerSq {ω : Type*} [Fintype ω]
    (P Q : ω → ℝ) : ℝ :=
  ∑ a, (Real.sqrt (P a) - Real.sqrt (Q a)) ^ 2

lemma hellingerSq_nonneg {ω : Type*} [Fintype ω] (P Q : ω → ℝ) :
    0 ≤ hellingerSq P Q := by
  unfold hellingerSq
  exact Finset.sum_nonneg fun a _ => sq_nonneg _

lemma hellingerSq_comm {ω : Type*} [Fintype ω] (P Q : ω → ℝ) :
    hellingerSq P Q = hellingerSq Q P := by
  unfold hellingerSq
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- `h²(P,Q) = 2(1-BC(P,Q))` for probability laws. -/
lemma hellingerSq_eq_two_mul_one_sub_BC {ω : Type*} [Fintype ω]
    {P Q : ω → ℝ} (hP : IsPMF P) (hQ : IsPMF Q) :
    hellingerSq P Q = 2 * (1 - BC P Q) := by
  have hsumP : ∑ a, P a = 1 := by simpa [mass] using hP.total
  have hsumQ : ∑ a, Q a = 1 := by simpa [mass] using hQ.total
  unfold hellingerSq BC
  calc
    (∑ a, (Real.sqrt (P a) - Real.sqrt (Q a)) ^ 2) =
        ∑ a, (P a + Q a - 2 * Real.sqrt (P a * Q a)) := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        (Real.sqrt (P a) - Real.sqrt (Q a)) ^ 2 =
            Real.sqrt (P a) ^ 2 + Real.sqrt (Q a) ^ 2 -
              2 * (Real.sqrt (P a) * Real.sqrt (Q a)) := by ring
        _ = P a + Q a - 2 * Real.sqrt (P a * Q a) := by
          rw [Real.sqrt_mul (hP.nonneg a), Real.sq_sqrt (hP.nonneg a),
            Real.sq_sqrt (hQ.nonneg a)]
    _ = (∑ a, P a) + (∑ a, Q a) -
          2 * ∑ a, Real.sqrt (P a * Q a) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 * (1 - ∑ a, Real.sqrt (P a * Q a)) := by
      rw [hsumP, hsumQ]
      ring

private lemma BC_le_BC_mX {q r : α × β → ℝ}
    (hq : IsPMF q) (hr : IsPMF r) :
    BC q r ≤ BC (mX q) (mX r) := by
  unfold BC
  rw [Fintype.sum_prod_type]
  calc
    (∑ x, ∑ y, Real.sqrt (q (x, y) * r (x, y))) =
        ∑ x, ∑ y, Real.sqrt (q (x, y)) * Real.sqrt (r (x, y)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [Real.sqrt_mul (hq.nonneg (x, y))]
    _ ≤ ∑ x, Real.sqrt (mX q x) * Real.sqrt (mX r x) := by
      apply Finset.sum_le_sum
      intro x _
      have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset β)
        (fun y => hq.nonneg (x, y)) (fun y => hr.nonneg (x, y))
      simpa [mX_eq_sum] using hcs
    _ = ∑ x, Real.sqrt (mX q x * mX r x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Real.sqrt_mul ((isPMF_push hq).nonneg x)]

private lemma BC_le_BC_mY {q r : α × β → ℝ}
    (hq : IsPMF q) (hr : IsPMF r) :
    BC q r ≤ BC (mY q) (mY r) := by
  unfold BC
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ y, ∑ x, Real.sqrt (q (x, y) * r (x, y))) =
        ∑ y, ∑ x, Real.sqrt (q (x, y)) * Real.sqrt (r (x, y)) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      rw [Real.sqrt_mul (hq.nonneg (x, y))]
    _ ≤ ∑ y, Real.sqrt (mY q y) * Real.sqrt (mY r y) := by
      apply Finset.sum_le_sum
      intro y _
      have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset α)
        (fun x => hq.nonneg (x, y)) (fun x => hr.nonneg (x, y))
      simpa [mY_eq_sum] using hcs
    _ = ∑ y, Real.sqrt (mY q y * mY r y) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Real.sqrt_mul ((isPMF_push hq).nonneg y)]

/-- Squared Hellinger distance contracts under the `X` marginal. -/
lemma hellingerSq_mX_le {q r : α × β → ℝ} (hq : IsPMF q) (hr : IsPMF r) :
    hellingerSq (mX q) (mX r) ≤ hellingerSq q r := by
  rw [hellingerSq_eq_two_mul_one_sub_BC (isPMF_push hq) (isPMF_push hr),
    hellingerSq_eq_two_mul_one_sub_BC hq hr]
  linarith [BC_le_BC_mX hq hr]

/-- Squared Hellinger distance contracts under the `Y` marginal. -/
lemma hellingerSq_mY_le {q r : α × β → ℝ} (hq : IsPMF q) (hr : IsPMF r) :
    hellingerSq (mY q) (mY r) ≤ hellingerSq q r := by
  rw [hellingerSq_eq_two_mul_one_sub_BC (isPMF_push hq) (isPMF_push hr),
    hellingerSq_eq_two_mul_one_sub_BC hq hr]
  linarith [BC_le_BC_mY hq hr]

/-- The pointwise cube-root estimate (6.3) of the improved proof. -/
lemma abs_rpow_one_third_sub_one_cube_le_sqrt_sub_one_sq
    {t : ℝ} (ht : 0 ≤ t) :
    |t ^ ((1 : ℝ) / 3) - 1| ^ 3 ≤ (Real.sqrt t - 1) ^ 2 := by
  let s : ℝ := t ^ ((1 : ℝ) / 6)
  have hs : 0 ≤ s := Real.rpow_nonneg ht _
  have hthird : t ^ ((1 : ℝ) / 3) = s ^ 2 := by
    dsimp [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    norm_num
  have hhalf : Real.sqrt t = s ^ 3 := by
    rw [Real.sqrt_eq_rpow]
    dsimp [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    norm_num
  rw [hthird, hhalf]
  rcases le_total 1 s with hs1 | hs1
  · rw [abs_of_nonneg (by nlinarith : 0 ≤ s ^ 2 - 1)]
    have hnonneg : 0 ≤ (s - 1) ^ 2 * (3 * s ^ 2 + 4 * s + 2) := by
      positivity
    nlinarith
  · rw [abs_of_nonpos (by nlinarith [sq_nonneg s] : s ^ 2 - 1 ≤ 0)]
    have hnonneg : 0 ≤ s ^ 2 * (s - 1) ^ 2 * (2 * s ^ 2 + 4 * s + 3) := by
      positivity
    nlinarith

private lemma weighted_ratio_root_cube_le_hellinger
    {ω : Type*} [Fintype ω] {m n : ω → ℝ}
    (hm : IsPMF m) (hn : IsPMF n) (i : ω) :
    m i * |(n i / m i) ^ ((1 : ℝ) / 3) - 1| ^ (3 : ℝ) ≤
      (Real.sqrt (m i) - Real.sqrt (n i)) ^ 2 := by
  by_cases hmi : m i = 0
  · simp [hmi]
  · have hmpos : 0 < m i := lt_of_le_of_ne (hm.nonneg i) (Ne.symm hmi)
    have hn0 : 0 ≤ n i := hn.nonneg i
    have hscalar := abs_rpow_one_third_sub_one_cube_le_sqrt_sub_one_sq
      (div_nonneg hn0 hmpos.le)
    rw [Real.rpow_ofNat]
    calc
      m i * |(n i / m i) ^ ((1 : ℝ) / 3) - 1| ^ 3 ≤
          m i * (Real.sqrt (n i / m i) - 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hscalar hmpos.le
      _ = (Real.sqrt (m i) - Real.sqrt (n i)) ^ 2 := by
        rw [Real.sqrt_div hn0]
        have hsqrt : 0 < Real.sqrt (m i) := Real.sqrt_pos.2 hmpos
        field_simp [hsqrt.ne']
        nlinarith [Real.sq_sqrt hmpos.le, Real.sq_sqrt hn0]

private lemma ratio_root_smallness_hellinger {q r : α × β → ℝ}
    (hq : IsPMF q) (hr : IsPMF r) :
    moment (mX q) 3
        (fun x => (mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1) ≤
        hellingerSq q r ∧
    moment (mY q) 3
        (fun y => (mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1) ≤
        hellingerSq q r := by
  have hX : moment (mX q) 3
      (fun x => (mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1) ≤
      hellingerSq (mX q) (mX r) := by
    unfold moment hellingerSq
    exact Finset.sum_le_sum fun x _ =>
      weighted_ratio_root_cube_le_hellinger (isPMF_push hq) (isPMF_push hr) x
  have hY : moment (mY q) 3
      (fun y => (mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1) ≤
      hellingerSq (mY q) (mY r) := by
    unfold moment hellingerSq
    exact Finset.sum_le_sum fun y _ =>
      weighted_ratio_root_cube_le_hellinger (isPMF_push hq) (isPMF_push hr) y
  exact ⟨hX.trans (hellingerSq_mX_le hq hr),
    hY.trans (hellingerSq_mY_le hq hr)⟩

/-- The quantitative heart of the improved HGR argument:
`h²(q,q_X tensor q_Y) >= rho^6/(1+rho^2)^2`. -/
private theorem hellingerSq_product_ge_hgr {S : Finset (α × β)}
    {w : α × β → ℝ} (hw : Feasible S w)
    {q : α × β → ℝ} (hq : IsContact S w q)
    (hrho : 0 < rhoHGR q) :
    rhoHGR q ^ 6 / (1 + rhoHGR q ^ 2) ^ 2 ≤
      hellingerSq q (fun z => mX q z.1 * mY q z.2) := by
  rcases exists_hgr_singular_pair hw hq hrho with
    ⟨f, g, hf0, hg0, hf2, hg2, hcorr, hrelf, hrelg⟩
  let Q : α × β → ℝ := fun z => mX q z.1 * mY q z.2
  let E4 : ℝ := ∑ z, q z * f z.1 ^ 2 * g z.2 ^ 2
  let EQ4 : ℝ := ∑ z, Q z * f z.1 ^ 2 * g z.2 ^ 2
  let cross : ℝ := ∑ z,
    Real.sqrt (q z) * Real.sqrt (Q z) * f z.1 ^ 2 * g z.2 ^ 2
  let second : ℝ := ∑ z,
    (Real.sqrt (q z) + Real.sqrt (Q z)) ^ 2 * f z.1 ^ 2 * g z.2 ^ 2
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  have hQ : IsPMF Q := product_isPMF hqX hqY
  have hinv0 : 0 ≤ (rhoHGR q)⁻¹ := (inv_pos.mpr hrho).le
  have hf3 : moment (mX q) 3 f ≤ (rhoHGR q)⁻¹ ^ 3 :=
    singular_f_moment_three_le hw hq hrho hf2 hg2 hrelf
  have hg3 : moment (mY q) 3 g ≤ (rhoHGR q)⁻¹ ^ 3 :=
    singular_g_moment_three_le hw hq hrho hf2 hg2 hrelg
  let nf : ℝ := normThree (mX q) f
  let ng : ℝ := normThree (mY q) g
  have hnf0 : 0 ≤ nf := normThree_nonneg hqX.nonneg f
  have hng0 : 0 ≤ ng := normThree_nonneg hqY.nonneg g
  have hnf3 : nf ^ 3 = moment (mX q) 3 f := by
    simpa [nf] using normThree_cube hqX.nonneg f
  have hng3 : ng ^ 3 = moment (mY q) 3 g := by
    simpa [ng] using normThree_cube hqY.nonneg g
  have hnf : nf ≤ (rhoHGR q)⁻¹ := by
    apply (pow_le_pow_iff_left₀ hnf0 hinv0 (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [hnf3]
    exact hf3
  have hng : ng ≤ (rhoHGR q)⁻¹ := by
    apply (pow_le_pow_iff_left₀ hng0 hinv0 (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [hng3]
    exact hg3
  have hE4_nonneg : 0 ≤ E4 := by
    dsimp [E4]
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg (mul_nonneg (hq.1.nonneg z) (sq_nonneg _)) (sq_nonneg _)
  have hE4 : E4 ≤ (rhoHGR q)⁻¹ ^ 4 := by
    have hhc := contact_hypercontractive hw hq
      (f := fun x => f x ^ 2) (g := fun y => g y ^ 2)
      (fun x => sq_nonneg _) (fun y => sq_nonneg _)
    have hhc_all : E4 ≤ nf ^ 2 * ng ^ 2 := by
      have hsupp := sum_eq_sum_support hq.2.1
        (fun z => f z.1 ^ 2 * g z.2 ^ 2)
      rw [show E4 = ∑ z ∈ S, q z * f z.1 ^ 2 * g z.2 ^ 2 by
        simpa [E4, mul_assoc] using hsupp]
      have hpowf : ∀ x, (f x ^ 2) ^ ((3 : ℝ) / 2) = |f x| ^ (3 : ℝ) := by
        intro x
        rw [show f x ^ 2 = |f x| ^ (2 : ℝ) by rw [Real.rpow_two, sq_abs],
          ← Real.rpow_mul (abs_nonneg _)]
        norm_num
      have hpowg : ∀ y, (g y ^ 2) ^ ((3 : ℝ) / 2) = |g y| ^ (3 : ℝ) := by
        intro y
        rw [show g y ^ 2 = |g y| ^ (2 : ℝ) by rw [Real.rpow_two, sq_abs],
          ← Real.rpow_mul (abs_nonneg _)]
        norm_num
      simp_rw [hpowf, hpowg] at hhc
      have hnf2 : (moment (mX q) 3 f) ^ ((2 : ℝ) / 3) = nf ^ 2 := by
        dsimp [nf, normThree]
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (moment_nonneg hqX.nonneg 3 f)]
        norm_num
      have hng2 : (moment (mY q) 3 g) ^ ((2 : ℝ) / 3) = ng ^ 2 := by
        dsimp [ng, normThree]
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (moment_nonneg hqY.nonneg 3 g)]
        norm_num
      have hhc' : (∑ z ∈ S, q z * f z.1 ^ 2 * g z.2 ^ 2) ≤
          (moment (mX q) 3 f) ^ ((2 : ℝ) / 3) *
            (moment (mY q) 3 g) ^ ((2 : ℝ) / 3) := by
        simpa [moment] using hhc
      rw [hnf2, hng2] at hhc'
      exact hhc'
    calc
      E4 ≤ nf ^ 2 * ng ^ 2 := hhc_all
      _ ≤ ((rhoHGR q)⁻¹) ^ 2 * ((rhoHGR q)⁻¹) ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ hnf0 hnf 2) (pow_le_pow_left₀ hng0 hng 2)
          (sq_nonneg ng) (sq_nonneg _)
      _ = (rhoHGR q)⁻¹ ^ 4 := by ring
  have hEQ4 : EQ4 = 1 := by
    dsimp [EQ4, Q]
    rw [Fintype.sum_prod_type]
    calc
      (∑ x, ∑ y, (mX q x * mY q y) * f x ^ 2 * g y ^ 2) =
          ∑ x, (mX q x * f x ^ 2) * (∑ y, mY q y * g y ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = (∑ x, mX q x * f x ^ 2) *
          (∑ y, mY q y * g y ^ 2) := by rw [Finset.sum_mul]
      _ = 1 := by rw [hf2, hg2]; norm_num
  have hcross_nonneg : 0 ≤ cross := by
    dsimp [cross]
    exact Finset.sum_nonneg fun z _ => by positivity
  have hcross_sq : cross ^ 2 ≤ E4 * EQ4 := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (s := (Finset.univ : Finset (α × β)))
      (r := fun z => Real.sqrt (q z) * Real.sqrt (Q z) *
        f z.1 ^ 2 * g z.2 ^ 2)
      (f := fun z => q z * f z.1 ^ 2 * g z.2 ^ 2)
      (g := fun z => Q z * f z.1 ^ 2 * g z.2 ^ 2)
      (fun z _ =>
        mul_nonneg (mul_nonneg (hq.1.nonneg z) (sq_nonneg _)) (sq_nonneg _))
      (fun z _ =>
        mul_nonneg (mul_nonneg (hQ.nonneg z) (sq_nonneg _)) (sq_nonneg _))
      (fun z _ => by
        have heq :
          (Real.sqrt (q z) * Real.sqrt (Q z) * f z.1 ^ 2 * g z.2 ^ 2) ^ 2 =
              (Real.sqrt (q z) ^ 2 * f z.1 ^ 2 * g z.2 ^ 2) *
                (Real.sqrt (Q z) ^ 2 * f z.1 ^ 2 * g z.2 ^ 2) := by ring
        have heq' :
            (Real.sqrt (Q z) ^ 2 * f z.1 ^ 2 * g z.2 ^ 2) =
              Q z * f z.1 ^ 2 * g z.2 ^ 2 := by
          rw [Real.sq_sqrt (hQ.nonneg z)]
        rw [heq, Real.sq_sqrt (hq.1.nonneg z), heq'])
    simpa [cross, E4, EQ4] using hcs
  have hcross : cross ≤ (rhoHGR q)⁻¹ ^ 2 := by
    have hbound_sq : cross ^ 2 ≤ ((rhoHGR q)⁻¹ ^ 2) ^ 2 := by
      rw [hEQ4, mul_one] at hcross_sq
      exact hcross_sq.trans (hE4.trans_eq (by ring))
    exact (pow_le_pow_iff_left₀ hcross_nonneg (sq_nonneg _)
      (by norm_num : (2 : ℕ) ≠ 0)).mp hbound_sq
  have hsecond_expand : second = E4 + EQ4 + 2 * cross := by
    calc
      second = ∑ z, (q z * f z.1 ^ 2 * g z.2 ^ 2 +
          Q z * f z.1 ^ 2 * g z.2 ^ 2 +
          2 * (Real.sqrt (q z) * Real.sqrt (Q z) *
            f z.1 ^ 2 * g z.2 ^ 2)) := by
        dsimp [second]
        apply Finset.sum_congr rfl
        intro z _
        calc
          (Real.sqrt (q z) + Real.sqrt (Q z)) ^ 2 *
              f z.1 ^ 2 * g z.2 ^ 2 =
              (Real.sqrt (q z) ^ 2 + Real.sqrt (Q z) ^ 2 +
                2 * (Real.sqrt (q z) * Real.sqrt (Q z))) *
                  f z.1 ^ 2 * g z.2 ^ 2 := by ring
          _ = q z * f z.1 ^ 2 * g z.2 ^ 2 +
              Q z * f z.1 ^ 2 * g z.2 ^ 2 +
              2 * (Real.sqrt (q z) * Real.sqrt (Q z) *
                f z.1 ^ 2 * g z.2 ^ 2) := by
            rw [Real.sq_sqrt (hq.1.nonneg z), Real.sq_sqrt (hQ.nonneg z)]
            ring
      _ = E4 + EQ4 + 2 * cross := by
        dsimp [E4, EQ4, cross]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsecond : second ≤ ((rhoHGR q)⁻¹ ^ 2 + 1) ^ 2 := by
    rw [hsecond_expand, hEQ4]
    nlinarith
  have hsecond_nonneg : 0 ≤ second := by
    dsimp [second]
    exact Finset.sum_nonneg fun z _ => by positivity
  have hQfg : ∑ z, Q z * f z.1 * g z.2 = 0 := by
    dsimp [Q]
    rw [Fintype.sum_prod_type]
    calc
      (∑ x, ∑ y, (mX q x * mY q y) * f x * g y) =
          ∑ x, (mX q x * f x) * (∑ y, mY q y * g y) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = 0 := by rw [hg0]; simp
  have hfactor_sum :
      (∑ z, (Real.sqrt (q z) - Real.sqrt (Q z)) *
        (Real.sqrt (q z) + Real.sqrt (Q z)) * f z.1 * g z.2) =
        rhoHGR q := by
    calc
      _ = ∑ z, (q z * f z.1 * g z.2 - Q z * f z.1 * g z.2) := by
        apply Finset.sum_congr rfl
        intro z _
        calc
          (Real.sqrt (q z) - Real.sqrt (Q z)) *
              (Real.sqrt (q z) + Real.sqrt (Q z)) * f z.1 * g z.2 =
              (Real.sqrt (q z) ^ 2 - Real.sqrt (Q z) ^ 2) *
                f z.1 * g z.2 := by ring
          _ = q z * f z.1 * g z.2 - Q z * f z.1 * g z.2 := by
            rw [Real.sq_sqrt (hq.1.nonneg z), Real.sq_sqrt (hQ.nonneg z)]
            ring
      _ = (∑ z, q z * f z.1 * g z.2) -
          ∑ z, Q z * f z.1 * g z.2 := by rw [Finset.sum_sub_distrib]
      _ = rhoHGR q := by rw [hcorr, hQfg, sub_zero]
  have hcs_main : rhoHGR q ^ 2 ≤ hellingerSq q Q * second := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (s := (Finset.univ : Finset (α × β)))
      (r := fun z => (Real.sqrt (q z) - Real.sqrt (Q z)) *
        (Real.sqrt (q z) + Real.sqrt (Q z)) * f z.1 * g z.2)
      (f := fun z => (Real.sqrt (q z) - Real.sqrt (Q z)) ^ 2)
      (g := fun z => (Real.sqrt (q z) + Real.sqrt (Q z)) ^ 2 *
        f z.1 ^ 2 * g z.2 ^ 2)
      (fun z _ => sq_nonneg _) (fun z _ => by positivity)
      (fun z _ => by ring_nf; exact le_rfl)
    rw [hfactor_sum] at hcs
    simpa [hellingerSq, second] using hcs
  have hcs_bound : rhoHGR q ^ 2 ≤
      hellingerSq q Q * ((rhoHGR q)⁻¹ ^ 2 + 1) ^ 2 := by
    exact hcs_main.trans (mul_le_mul_of_nonneg_left hsecond
      (hellingerSq_nonneg q Q))
  have hscaled : rhoHGR q ^ 6 ≤
      hellingerSq q Q * (1 + rhoHGR q ^ 2) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hcs_bound (pow_nonneg hrho.le 4)
    field_simp [hrho.ne'] at hmul
    nlinarith
  apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < 1 + rhoHGR q ^ 2))).2
  simpa [mul_comm] using hscaled

private lemma product_absCont (q : α × β → ℝ) (hq : IsPMF q) :
    AbsCont q (fun z => mX q z.1 * mY q z.2) := by
  intro z hzero
  by_contra hqz
  have hqpos : 0 < q z := lt_of_le_of_ne (hq.nonneg z) (Ne.symm hqz)
  have hxle : q z ≤ mX q z.1 := by
    rw [mX_eq_sum]
    exact Finset.single_le_sum (fun y _ => hq.nonneg (z.1, y)) (Finset.mem_univ z.2)
  have hyle : q z ≤ mY q z.2 := by
    rw [mY_eq_sum]
    exact Finset.single_le_sum (fun x _ => hq.nonneg (x, z.2)) (Finset.mem_univ z.1)
  have hxpos := hqpos.trans_le hxle
  have hypos := hqpos.trans_le hyle
  exact (mul_ne_zero hxpos.ne' hypos.ne') hzero

private lemma KL_self_eq_zero {ω : Type*} [Fintype ω] (P : ω → ℝ) :
    KL P P = 0 := by
  unfold KL
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : P a = 0
  · simp [ha]
  · rw [div_self ha, lg]
    norm_num

private lemma BC_product_pos {q : α × β → ℝ} (hq : IsPMF q) :
    0 < BC q (fun z => mX q z.1 * mY q z.2) := by
  obtain ⟨z, hz⟩ : ∃ z, 0 < q z := by
    have hsum_eq : ∑ z, q z = 1 := by simpa [mass] using hq.total
    have hsum : 0 < ∑ z, q z := by rw [hsum_eq]; norm_num
    rcases (Finset.sum_pos_iff_of_nonneg
      (fun z _ => hq.nonneg z)).mp hsum with ⟨z, _, hz⟩
    exact ⟨z, hz⟩
  have hxle : q z ≤ mX q z.1 := by
    rw [mX_eq_sum]
    exact Finset.single_le_sum (fun y _ => hq.nonneg (z.1, y)) (Finset.mem_univ z.2)
  have hyle : q z ≤ mY q z.2 := by
    rw [mY_eq_sum]
    exact Finset.single_le_sum (fun x _ => hq.nonneg (x, z.2)) (Finset.mem_univ z.1)
  unfold BC
  apply Finset.sum_pos'
  · intro a _
    exact Real.sqrt_nonneg _
  · refine ⟨z, Finset.mem_univ z, Real.sqrt_pos.2 ?_⟩
    exact mul_pos hz (mul_pos (hz.trans_le hxle) (hz.trans_le hyle))

private lemma hellinger_floor_to_Ixy {q : α × β → ℝ} (hq : IsPMF q)
    {c : ℝ} (hc0 : 0 ≤ c) (hc2 : c < 2)
    (hc : c ≤ hellingerSq q (fun z => mX q z.1 * mY q z.2)) :
    -2 * lg (1 - c / 2) ≤ Ixy q := by
  let Q : α × β → ℝ := fun z => mX q z.1 * mY q z.2
  have hQ : IsPMF Q := product_isPMF (isPMF_push hq) (isPMF_push hq)
  have hac : AbsCont q Q := product_absCont q hq
  have hBCpos : 0 < BC q Q := by simpa [Q] using BC_product_pos hq
  have hargpos : 0 < 1 - c / 2 := by linarith
  have hBCle : BC q Q ≤ 1 - c / 2 := by
    have hid := hellingerSq_eq_two_mul_one_sub_BC hq hQ
    change c ≤ hellingerSq q Q at hc
    linarith
  have hlog : lg (BC q Q) ≤ lg (1 - c / 2) := by
    rw [lg_eq_log_div, lg_eq_log_div]
    exact div_le_div_of_nonneg_right (Real.log_le_log hBCpos hBCle)
      (Real.log_pos one_lt_two).le
  have hreverse : -2 * lg (1 - c / 2) ≤ -2 * lg (BC q Q) :=
    mul_le_mul_of_nonpos_left hlog (by norm_num)
  have hbh := bhattacharyya_le hq hQ hq
    (fun _ h => h) hac
  rw [KL_self_eq_zero q, zero_add] at hbh
  rw [Ixy_eq_KL_product hq]
  exact hreverse.trans hbh

/-- **Theorem 6.1 (improved)**: the Hellinger HGR information floor. -/
theorem Ixy_ge_hgr_floor_hellinger_pos {S : Finset (α × β)}
    {w : α × β → ℝ} (hw : Feasible S w)
    {q : α × β → ℝ} (hq : IsContact S w q)
    (hrho : 0 < rhoHGR q) :
    -2 * lg
        (1 - rhoHGR q ^ 6 /
          (2 * (1 + rhoHGR q ^ 2) ^ 2)) ≤ Ixy q := by
  let c : ℝ := rhoHGR q ^ 6 / (1 + rhoHGR q ^ 2) ^ 2
  have hrho_le : rhoHGR q ≤ 1 := rhoHGR_le_one hq.1
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hrho6 : rhoHGR q ^ 6 ≤ 1 := pow_le_one₀ hrho.le hrho_le
  have hdenpos : 0 < (1 + rhoHGR q ^ 2) ^ 2 := by positivity
  have hone_den : 1 ≤ (1 + rhoHGR q ^ 2) ^ 2 := by nlinarith [sq_nonneg (rhoHGR q)]
  have hc1 : c ≤ 1 := by
    apply (div_le_one₀ hdenpos).2
    exact hrho6.trans hone_den
  have hc2 : c < 2 := hc1.trans_lt (by norm_num)
  have hc := hellingerSq_product_ge_hgr hw hq hrho
  have hfloor := hellinger_floor_to_Ixy hq.1 hc0 hc2 (by simpa [c] using hc)
  have hrewrite :
      rhoHGR q ^ 6 / (1 + rhoHGR q ^ 2) ^ 2 / 2 =
        rhoHGR q ^ 6 / (2 * (1 + rhoHGR q ^ 2) ^ 2) := by
    rw [div_div]
    congr 1
    ring
  simpa [c, hrewrite] using hfloor

theorem rhoHGR_nonneg {q : α × β → ℝ} (hq : IsPMF q) :
    0 ≤ rhoHGR q := by
  let I := {fg : (α → ℝ) × (β → ℝ) //
      (∑ x, mX q x * fg.1 x = 0) ∧ (∑ y, mY q y * fg.2 y = 0) ∧
      (∑ x, mX q x * fg.1 x ^ 2 = 1) ∧ (∑ y, mY q y * fg.2 y ^ 2 = 1)}
  cases isEmpty_or_nonempty I with
  | inl hempty =>
      letI := hempty
      simp [rhoHGR, I]
  | inr hnonempty =>
      letI := hnonempty
      let fg : I := Classical.choice hnonempty
      have hpos := correlation_le_rhoHGR hq fg.2.1 fg.2.2.1
        fg.2.2.2.1 fg.2.2.2.2
      have hf0 : ∑ x, mX q x * (-fg.1.1 x) = 0 := by
        calc
          ∑ x, mX q x * (-fg.1.1 x) = -(∑ x, mX q x * fg.1.1 x) := by
            simp_rw [mul_neg, Finset.sum_neg_distrib]
          _ = 0 := by rw [fg.2.1]; norm_num
      have hf2 : ∑ x, mX q x * (-fg.1.1 x) ^ 2 = 1 := by
        simpa only [neg_sq] using fg.2.2.2.1
      have hneg := correlation_le_rhoHGR hq hf0 fg.2.2.1 hf2 fg.2.2.2.2
      have hcorr :
          (∑ z, q z * (-fg.1.1 z.1) * fg.1.2 z.2) =
            -(∑ z, q z * fg.1.1 z.1 * fg.1.2 z.2) := by
        calc
          ∑ z, q z * (-fg.1.1 z.1) * fg.1.2 z.2 =
              ∑ z, -(q z * fg.1.1 z.1 * fg.1.2 z.2) := by
                apply Finset.sum_congr rfl
                intro z _
                ring
          _ = -(∑ z, q z * fg.1.1 z.1 * fg.1.2 z.2) :=
            by simp
      rw [hcorr] at hneg
      linarith

private lemma Ixy_nonneg_floor {q : α × β → ℝ} (hq : IsPMF q) :
    0 ≤ Ixy q := by
  have h := MI_nonneg hq Prod.fst Prod.snd
  unfold MI Hvar at h
  have hid : (fun z : α × β => (z.1, z.2)) = id := by
    funext z
    exact Prod.eta z
  have hpush : push id q = q := by
    funext a
    unfold push
    apply Finset.sum_eq_single a
    · intro b hb hba
      have heq : b = a := by simpa using (Finset.mem_filter.mp hb).2
      exact (hba heq).elim
    · intro ha
      exact (ha (by simp)).elim
  rw [hid, hpush] at h
  simpa [Ixy] using h

/-- **Theorem 6.1 (improved, total form)**: the Hellinger HGR information
floor, including the degenerate zero-correlation case. -/
theorem Ixy_ge_hgr_floor_hellinger {S : Finset (α × β)}
    {w : α × β → ℝ} (hw : Feasible S w)
    {q : α × β → ℝ} (hq : IsContact S w q) :
    -2 * lg
        (1 - rhoHGR q ^ 6 /
          (2 * (1 + rhoHGR q ^ 2) ^ 2)) ≤ Ixy q := by
  by_cases hz : rhoHGR q = 0
  · simp [hz, Ixy_nonneg_floor hq.1]
  · exact Ixy_ge_hgr_floor_hellinger_pos hw hq
      (lt_of_le_of_ne (rhoHGR_nonneg hq.1) (Ne.symm hz))

private lemma value_eq_zero_of_weighted_sq_sum_eq_zero
    {ω : Type*} [Fintype ω] {m : ω → ℝ} (hm : ∀ i, 0 ≤ m i)
    {f : ω → ℝ} (hsum : ∑ i, m i * f i ^ 2 = 0)
    {i : ω} (hmi : m i ≠ 0) : f i = 0 := by
  have hterm : m i * f i ^ 2 = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hm j) (sq_nonneg _))).mp hsum
    exact Finset.mem_univ i
  have hmsq : f i ^ 2 = 0 := (mul_eq_zero.mp hterm).resolve_left hmi
  nlinarith [sq_nonneg (f i)]

/-- Parametric `q`-oriented exact-secant rigidity: two distinct contacts with
common support and squared Hellinger distance at most `η³` force HGR maximal
correlation at least `1/2 - η²` at the first contact. -/
theorem rho_le_rhoHGR_of_contacts_param
    (η : ℝ) (hη : 0 < η) (hη1 : 2 * η ^ 2 < 1)
    {S : Finset (α × β)} {w q r : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q) (hr : IsContact S w r)
    (hqs : support q = S) (hrs : support r = S) (hne : q ≠ r)
    (hclose : hellingerSq q r ≤ η ^ 3) :
    1 / 2 - η ^ 2 ≤ rhoHGR q := by
  let f : α → ℝ := fun x =>
    (mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1
  let g : β → ℝ := fun y =>
    (mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1
  let af : ℝ := normThree (mX q) f
  let ag : ℝ := normThree (mY q) g
  let a : ℝ := normTwo (mX q) f
  let b : ℝ := normTwo (mY q) g
  let A : ℝ := ∑ x, mX q x * f x ^ 2
  let B : ℝ := ∑ y, mY q y * g y ^ 2
  let R : ℝ := ∑ z, q z * f z.1 * g z.2
  let Efg2 : ℝ := ∑ z, q z * f z.1 * g z.2 ^ 2
  let Ef2g : ℝ := ∑ z, q z * f z.1 ^ 2 * g z.2
  let E4 : ℝ := ∑ z, q z * f z.1 ^ 2 * g z.2 ^ 2
  let μf : ℝ := weightedMean (mX q) f
  let μg : ℝ := weightedMean (mY q) g
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (hqX.nonneg x) (sq_nonneg _)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg (hqY.nonneg y) (sq_nonneg _)
  have hE40 : 0 ≤ E4 := by
    dsimp [E4]
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg (mul_nonneg (hq.1.nonneg z) (sq_nonneg _)) (sq_nonneg _)
  have hsmall := ratio_root_smallness_hellinger hq.1 hr.1
  have haf0 : 0 ≤ af := normThree_nonneg hqX.nonneg f
  have hag0 : 0 ≤ ag := normThree_nonneg hqY.nonneg g
  have hafcube : af ^ 3 = moment (mX q) 3 f :=
    normThree_cube hqX.nonneg f
  have hagcube : ag ^ 3 = moment (mY q) 3 g :=
    normThree_cube hqY.nonneg g
  have haf3 : af ^ 3 ≤ η ^ 3 := by
    rw [hafcube]
    exact hsmall.1.trans hclose
  have hag3 : ag ^ 3 ≤ η ^ 3 := by
    rw [hagcube]
    exact hsmall.2.trans hclose
  have haf_le : af ≤ η := by
    exact (pow_le_pow_iff_left₀ haf0 hη.le
      (by norm_num : (3 : ℕ) ≠ 0)).mp haf3
  have hag_le : ag ≤ η := by
    exact (pow_le_pow_iff_left₀ hag0 hη.le
      (by norm_num : (3 : ℕ) ≠ 0)).mp hag3
  have ha0 : 0 ≤ a := normTwo_nonneg hqX.nonneg f
  have hb0 : 0 ≤ b := normTwo_nonneg hqY.nonneg g
  have ha_le : a ≤ η := (normTwo_le_normThree hqX f).trans haf_le
  have hb_le : b ≤ η := (normTwo_le_normThree hqY g).trans hag_le
  have ha_sq : a ^ 2 = A := by
    rw [normTwo_sq hqX.nonneg, moment_two_eq hqX.nonneg]
  have hb_sq : b ^ 2 = B := by
    rw [normTwo_sq hqY.nonneg, moment_two_eq hqY.nonneg]
  have hA_le : A ≤ η ^ 2 := by
    rw [← ha_sq]
    exact pow_le_pow_left₀ ha0 ha_le 2
  have hB_le : B ≤ η ^ 2 := by
    rw [← hb_sq]
    exact pow_le_pow_left₀ hb0 hb_le 2
  have hAB_le : A + B ≤ 2 * η ^ 2 := by linarith
  have hAB_lt_one : A + B < 1 := by
    exact hAB_le.trans_lt hη1
  have hsec :
      (∀ x, mX q x * f x =
        2 * (∑ y, q (x, y) * g y) + ∑ y, q (x, y) * g y ^ 2) ∧
      (∀ y, mY q y * g y =
        2 * (∑ x, q (x, y) * f x) + ∑ x, q (x, y) * f x ^ 2) := by
    simpa [f, g] using secant_expanded_equations hq hr hqs hrs
  have hmeanf : μf = 2 * μg + B := by
    calc
      μf = ∑ x, mX q x * f x := rfl
      _ = ∑ x, (2 * (∑ y, q (x, y) * g y) +
          ∑ y, q (x, y) * g y ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        exact hsec.1 x
      _ = 2 * (∑ z, q z * g z.2) + ∑ z, q z * g z.2 ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          Fintype.sum_prod_type, Fintype.sum_prod_type]
      _ = 2 * μg + B := by
        rw [← sum_push_mul Prod.snd q g,
          ← sum_push_mul Prod.snd q (fun y => g y ^ 2)]
        rfl
  have hmeang : μg = 2 * μf + A := by
    have hfirst : (∑ y, ∑ x, q (x, y) * f x) =
        ∑ z, q z * f z.1 := by
      calc
        (∑ y, ∑ x, q (x, y) * f x) =
            ∑ x, ∑ y, q (x, y) * f x := Finset.sum_comm
        _ = ∑ z, q z * f z.1 := by rw [Fintype.sum_prod_type]
    have hsecond : (∑ y, ∑ x, q (x, y) * f x ^ 2) =
        ∑ z, q z * f z.1 ^ 2 := by
      calc
        (∑ y, ∑ x, q (x, y) * f x ^ 2) =
            ∑ x, ∑ y, q (x, y) * f x ^ 2 := Finset.sum_comm
        _ = ∑ z, q z * f z.1 ^ 2 := by rw [Fintype.sum_prod_type]
    calc
      μg = ∑ y, mY q y * g y := rfl
      _ = ∑ y, (2 * (∑ x, q (x, y) * f x) +
          ∑ x, q (x, y) * f x ^ 2) := by
        apply Finset.sum_congr rfl
        intro y _
        exact hsec.2 y
      _ = 2 * (∑ z, q z * f z.1) + ∑ z, q z * f z.1 ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfirst, hsecond]
      _ = 2 * μf + A := by
        rw [← sum_push_mul Prod.fst q f,
          ← sum_push_mul Prod.fst q (fun x => f x ^ 2)]
        rfl
  have hμf : μf = -(2 * A + B) / 3 := by linarith
  have hμg : μg = -(A + 2 * B) / 3 := by linarith
  have hA_mixed : A = 2 * R + Efg2 := by
    have hfirst : (∑ x, f x * (∑ y, q (x, y) * g y)) =
        ∑ z, q z * f z.1 * g z.2 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    have hsecond : (∑ x, f x * (∑ y, q (x, y) * g y ^ 2)) =
        ∑ z, q z * f z.1 * g z.2 ^ 2 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    calc
      A = ∑ x, f x * (mX q x * f x) := by
        dsimp [A]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = ∑ x, f x * (2 * (∑ y, q (x, y) * g y) +
          ∑ y, q (x, y) * g y ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hsec.1 x]
      _ = 2 * R + Efg2 := by
        dsimp [R, Efg2]
        rw [show (∑ x, f x *
            (2 * (∑ y, q (x, y) * g y) + ∑ y, q (x, y) * g y ^ 2)) =
            ∑ x, (2 * (f x * (∑ y, q (x, y) * g y)) +
              f x * (∑ y, q (x, y) * g y ^ 2)) by
          apply Finset.sum_congr rfl
          intro x _
          ring]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfirst, hsecond]
  have hB_mixed : B = 2 * R + Ef2g := by
    have hfirst : (∑ y, g y * (∑ x, q (x, y) * f x)) =
        ∑ z, q z * f z.1 * g z.2 := by
      calc
        (∑ y, g y * (∑ x, q (x, y) * f x)) =
            ∑ y, ∑ x, q (x, y) * f x * g y := by
              apply Finset.sum_congr rfl
              intro y _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              ring
        _ = ∑ x, ∑ y, q (x, y) * f x * g y := Finset.sum_comm
        _ = ∑ z, q z * f z.1 * g z.2 := by rw [Fintype.sum_prod_type]
    have hsecond : (∑ y, g y * (∑ x, q (x, y) * f x ^ 2)) =
        ∑ z, q z * f z.1 ^ 2 * g z.2 := by
      calc
        (∑ y, g y * (∑ x, q (x, y) * f x ^ 2)) =
            ∑ y, ∑ x, q (x, y) * f x ^ 2 * g y := by
              apply Finset.sum_congr rfl
              intro y _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              ring
        _ = ∑ x, ∑ y, q (x, y) * f x ^ 2 * g y := Finset.sum_comm
        _ = ∑ z, q z * f z.1 ^ 2 * g z.2 := by rw [Fintype.sum_prod_type]
    calc
      B = ∑ y, g y * (mY q y * g y) := by
        dsimp [B]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = ∑ y, g y * (2 * (∑ x, q (x, y) * f x) +
          ∑ x, q (x, y) * f x ^ 2) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [hsec.2 y]
      _ = 2 * R + Ef2g := by
        dsimp [R, Ef2g]
        rw [show (∑ y, g y *
            (2 * (∑ x, q (x, y) * f x) + ∑ x, q (x, y) * f x ^ 2)) =
            ∑ y, (2 * (g y * (∑ x, q (x, y) * f x)) +
              g y * (∑ x, q (x, y) * f x ^ 2)) by
          apply Finset.sum_congr rfl
          intro y _
          ring]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfirst, hsecond]
  have hratio := contact_ratio_eq hq hr hqs hrs
  have hratio_fg : ∀ z, r z = q z * (f z.1 + 1) ^ 2 * (g z.2 + 1) ^ 2 := by
    intro z
    simpa [f, g] using hratio z
  have hmass_expanded :
      1 + 2 * μf + A + 2 * μg + 4 * R +
          2 * Ef2g + B + 2 * Efg2 + E4 = 1 := by
    have hmass : ∑ z, q z * (f z.1 + 1) ^ 2 * (g z.2 + 1) ^ 2 = 1 := by
      calc
        ∑ z, q z * (f z.1 + 1) ^ 2 * (g z.2 + 1) ^ 2 =
            ∑ z, r z := by
              apply Finset.sum_congr rfl
              intro z _
              exact (hratio_fg z).symm
        _ = 1 := by simpa [mass] using hr.1.total
    have hpoint : ∀ z,
        q z * (f z.1 + 1) ^ 2 * (g z.2 + 1) ^ 2 =
          q z + 2 * (q z * f z.1) + q z * f z.1 ^ 2 +
          2 * (q z * g z.2) + 4 * (q z * f z.1 * g z.2) +
          2 * (q z * f z.1 ^ 2 * g z.2) + q z * g z.2 ^ 2 +
          2 * (q z * f z.1 * g z.2 ^ 2) +
          q z * f z.1 ^ 2 * g z.2 ^ 2 := by
      intro z
      ring
    have hexpand :
        (∑ z, q z * (f z.1 + 1) ^ 2 * (g z.2 + 1) ^ 2) =
          (∑ z, q z) + 2 * (∑ z, q z * f z.1) +
          (∑ z, q z * f z.1 ^ 2) + 2 * (∑ z, q z * g z.2) +
          4 * (∑ z, q z * f z.1 * g z.2) +
          2 * (∑ z, q z * f z.1 ^ 2 * g z.2) +
          (∑ z, q z * g z.2 ^ 2) +
          2 * (∑ z, q z * f z.1 * g z.2 ^ 2) +
          ∑ z, q z * f z.1 ^ 2 * g z.2 ^ 2 := by
      simp_rw [hpoint]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hexpand] at hmass
    rw [← sum_push_mul Prod.fst q f,
      ← sum_push_mul Prod.fst q (fun x => f x ^ 2),
      ← sum_push_mul Prod.snd q g,
      ← sum_push_mul Prod.snd q (fun y => g y ^ 2)] at hmass
    rw [show (∑ z, q z) = 1 by simpa [mass] using hq.1.total] at hmass
    simpa [μf, μg, weightedMean, A, B, R, Efg2, Ef2g, E4] using hmass
  have hR_identity : 4 * R = A + B + E4 := by
    nlinarith [hmass_expanded, hmeanf, hmeang, hA_mixed, hB_mixed]
  have hABpos : 0 < A + B := by
    by_contra hnot
    have hABnonpos : A + B ≤ 0 := le_of_not_gt hnot
    have hAz : A = 0 := by linarith
    have hBz : B = 0 := by linarith
    apply hne
    funext z
    by_cases hz : z ∈ S
    · have hqmem : z ∈ support q := by simpa [hqs] using hz
      have hqne : q z ≠ 0 := by simpa [support] using hqmem
      have hqpos : 0 < q z := lt_of_le_of_ne (hq.1.nonneg z) (Ne.symm hqne)
      have hxpos : 0 < mX q z.1 := by
        have hxle : q z ≤ mX q z.1 := by
          rw [mX_eq_sum]
          exact Finset.single_le_sum (fun y _ => hq.1.nonneg (z.1, y))
            (Finset.mem_univ z.2)
        exact hqpos.trans_le hxle
      have hypos : 0 < mY q z.2 := by
        have hyle : q z ≤ mY q z.2 := by
          rw [mY_eq_sum]
          exact Finset.single_le_sum (fun x _ => hq.1.nonneg (x, z.2))
            (Finset.mem_univ z.1)
        exact hqpos.trans_le hyle
      have hfz : f z.1 = 0 :=
        value_eq_zero_of_weighted_sq_sum_eq_zero hqX.nonneg
          (by simpa [A] using hAz) hxpos.ne'
      have hgz : g z.2 = 0 :=
        value_eq_zero_of_weighted_sq_sum_eq_zero hqY.nonneg
          (by simpa [B] using hBz) hypos.ne'
      have hzratio := hratio_fg z
      rw [hfz, hgz] at hzratio
      norm_num at hzratio
      exact hzratio.symm
    · rw [hq.2.1 z hz, hr.2.1 z hz]

  let Γ : ℝ := R - μf * μg
  have hR_lower : (A + B) / 4 ≤ R := by
    nlinarith only [hR_identity, hE40]
  have hμ_product : μf * μg ≤ (A + B) ^ 2 / 4 := by
    rw [hμf, hμg]
    nlinarith only [sq_nonneg (A - B)]
  have hΓ_lower : (A + B) * (1 - A - B) / 4 ≤ Γ := by
    dsimp [Γ]
    nlinarith only [hR_lower, hμ_product]
  have hΓpos : 0 < Γ := by
    have hprod : 0 < (A + B) * (1 - A - B) :=
      mul_pos hABpos (by linarith only [hAB_lt_one])
    have hdiv : 0 < (A + B) * (1 - A - B) / 4 :=
      div_pos hprod (by norm_num)
    exact hdiv.trans_le hΓ_lower
  let f₀ : α → ℝ := centered (mX q) f
  let g₀ : β → ℝ := centered (mY q) g
  let a₀ : ℝ := normTwo (mX q) f₀
  let b₀ : ℝ := normTwo (mY q) g₀
  have ha₀0 : 0 ≤ a₀ := normTwo_nonneg hqX.nonneg f₀
  have hb₀0 : 0 ≤ b₀ := normTwo_nonneg hqY.nonneg g₀
  have hf₀mean : weightedMean (mX q) f₀ = 0 := by
    simpa [f₀] using weightedMean_centered_eq_zero hqX f
  have hg₀mean : weightedMean (mY q) g₀ = 0 := by
    simpa [g₀] using weightedMean_centered_eq_zero hqY g
  have ha₀sq : a₀ ^ 2 = A - μf ^ 2 := by
    have h := normTwo_centered_sq hqX f
    rw [ha_sq] at h
    simpa [a₀, f₀, μf] using h
  have hb₀sq : b₀ ^ 2 = B - μg ^ 2 := by
    have h := normTwo_centered_sq hqY g
    rw [hb_sq] at h
    simpa [b₀, g₀, μg] using h
  have ha₀sq_sum : a₀ ^ 2 = ∑ x, mX q x * f₀ x ^ 2 := by
    rw [normTwo_sq hqX.nonneg, moment_two_eq hqX.nonneg]
  have hb₀sq_sum : b₀ ^ 2 = ∑ y, mY q y * g₀ y ^ 2 := by
    rw [normTwo_sq hqY.nonneg, moment_two_eq hqY.nonneg]
  have hΓ_joint : ∑ z, q z * f₀ z.1 * g₀ z.2 = Γ := by
    have hpoint : ∀ z,
        q z * f₀ z.1 * g₀ z.2 =
          q z * f z.1 * g z.2 - μg * (q z * f z.1) -
            μf * (q z * g z.2) + μf * μg * q z := by
      intro z
      dsimp [f₀, g₀, centered, μf, μg]
      ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    rw [← sum_push_mul Prod.fst q f, ← sum_push_mul Prod.snd q g,
      show (∑ z, q z) = 1 by simpa [mass] using hq.1.total]
    dsimp [R, Γ, μf, μg, weightedMean]
    ring
  have ha₀pos : 0 < a₀ := by
    by_contra hnot
    have ha₀z : a₀ = 0 := le_antisymm (le_of_not_gt hnot) ha₀0
    have hsqzero : ∑ x, mX q x * f₀ x ^ 2 = 0 := by
      rw [← ha₀sq_sum, ha₀z]
      norm_num
    have hjointzero : ∑ z, q z * f₀ z.1 * g₀ z.2 = 0 := by
      apply Finset.sum_eq_zero
      intro z _
      by_cases hqz : q z = 0
      · simp [hqz]
      · have hqpos : 0 < q z :=
          lt_of_le_of_ne (hq.1.nonneg z) (Ne.symm hqz)
        have hxle : q z ≤ mX q z.1 := by
          rw [mX_eq_sum]
          exact Finset.single_le_sum (fun y _ => hq.1.nonneg (z.1, y))
            (Finset.mem_univ z.2)
        have hfz : f₀ z.1 = 0 :=
          value_eq_zero_of_weighted_sq_sum_eq_zero hqX.nonneg hsqzero
            (hqpos.trans_le hxle).ne'
        simp [hfz]
    rw [hΓ_joint] at hjointzero
    linarith
  have hb₀pos : 0 < b₀ := by
    by_contra hnot
    have hb₀z : b₀ = 0 := le_antisymm (le_of_not_gt hnot) hb₀0
    have hsqzero : ∑ y, mY q y * g₀ y ^ 2 = 0 := by
      rw [← hb₀sq_sum, hb₀z]
      norm_num
    have hjointzero : ∑ z, q z * f₀ z.1 * g₀ z.2 = 0 := by
      apply Finset.sum_eq_zero
      intro z _
      by_cases hqz : q z = 0
      · simp [hqz]
      · have hqpos : 0 < q z :=
          lt_of_le_of_ne (hq.1.nonneg z) (Ne.symm hqz)
        have hyle : q z ≤ mY q z.2 := by
          rw [mY_eq_sum]
          exact Finset.single_le_sum (fun x _ => hq.1.nonneg (x, z.2))
            (Finset.mem_univ z.1)
        have hgz : g₀ z.2 = 0 :=
          value_eq_zero_of_weighted_sq_sum_eq_zero hqY.nonneg hsqzero
            (hqpos.trans_le hyle).ne'
        simp [hgz]
    rw [hΓ_joint] at hjointzero
    linarith
  have ha₀sq_le : a₀ ^ 2 ≤ A := by
    nlinarith only [ha₀sq, sq_nonneg μf]
  have hb₀sq_le : b₀ ^ 2 ≤ B := by
    nlinarith only [hb₀sq, sq_nonneg μg]
  have hab_upper : a₀ * b₀ ≤ (A + B) / 2 := by
    nlinarith only [ha₀sq_le, hb₀sq_le, sq_nonneg (a₀ - b₀)]
  let fn : α → ℝ := fun x => f₀ x / a₀
  let gn : β → ℝ := fun y => g₀ y / b₀
  have hfn0 : ∑ x, mX q x * fn x = 0 := by
    calc
      ∑ x, mX q x * fn x = weightedMean (mX q) f₀ / a₀ := by
        dsimp [fn, weightedMean]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hf₀mean, zero_div]
  have hgn0 : ∑ y, mY q y * gn y = 0 := by
    calc
      ∑ y, mY q y * gn y = weightedMean (mY q) g₀ / b₀ := by
        dsimp [gn, weightedMean]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = 0 := by rw [hg₀mean, zero_div]
  have hfn2 : ∑ x, mX q x * fn x ^ 2 = 1 := by
    calc
      ∑ x, mX q x * fn x ^ 2 =
          (∑ x, mX q x * f₀ x ^ 2) / a₀ ^ 2 := by
        dsimp [fn]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        field_simp [ha₀pos.ne']
      _ = 1 := by rw [← ha₀sq_sum]; field_simp [ha₀pos.ne']
  have hgn2 : ∑ y, mY q y * gn y ^ 2 = 1 := by
    calc
      ∑ y, mY q y * gn y ^ 2 =
          (∑ y, mY q y * g₀ y ^ 2) / b₀ ^ 2 := by
        dsimp [gn]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro y _
        field_simp [hb₀pos.ne']
      _ = 1 := by rw [← hb₀sq_sum]; field_simp [hb₀pos.ne']
  have hcorr_norm :
      (∑ z, q z * fn z.1 * gn z.2) = Γ / (a₀ * b₀) := by
    dsimp [fn, gn]
    calc
      (∑ z, q z * (f₀ z.1 / a₀) * (g₀ z.2 / b₀)) =
          ∑ z, (q z * f₀ z.1 * g₀ z.2) / (a₀ * b₀) := by
        apply Finset.sum_congr rfl
        intro z _
        field_simp [ha₀pos.ne', hb₀pos.ne']
      _ = (∑ z, q z * f₀ z.1 * g₀ z.2) / (a₀ * b₀) := by
        rw [Finset.sum_div]
      _ = Γ / (a₀ * b₀) := by rw [hΓ_joint]
  have habpos : 0 < a₀ * b₀ := mul_pos ha₀pos hb₀pos
  have hcorr_lower : (1 - A - B) / 2 ≤ Γ / (a₀ * b₀) := by
    apply (le_div_iff₀ habpos).2
    calc
      (1 - A - B) / 2 * (a₀ * b₀) ≤
          (1 - A - B) / 2 * ((A + B) / 2) :=
        mul_le_mul_of_nonneg_left hab_upper (by linarith [hAB_lt_one])
      _ = (A + B) * (1 - A - B) / 4 := by ring
      _ ≤ Γ := hΓ_lower
  have hwitness := correlation_le_rhoHGR hq.1 hfn0 hgn0 hfn2 hgn2
  rw [hcorr_norm] at hwitness
  calc
    1 / 2 - η ^ 2 ≤ (1 - A - B) / 2 := by linarith [hAB_le]
    _ ≤ Γ / (a₀ * b₀) := hcorr_lower
    _ ≤ rhoHGR q := hwitness

private theorem rho1771_le_rhoHGR_of_contacts
    {S : Finset (α × β)} {w q r : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q) (hr : IsContact S w r)
    (hqs : support q = S) (hrs : support r = S) (hne : q ≠ r)
    (hclose : hellingerSq q r ≤ delta1771) :
    rho1771 ≤ rhoHGR q := by
  rw [rho1771_eq]
  exact rho_le_rhoHGR_of_contacts_param eta1771 eta1771_pos
    (by norm_num [eta1771_eq]) hw hq hr hqs hrs hne
    (by simpa only [delta1771_eq] using hclose)

private lemma hgr_hellinger_fraction_mono {a b : ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) :
    a ^ 6 / (1 + a ^ 2) ^ 2 ≤ b ^ 6 / (1 + b ^ 2) ^ 2 := by
  have hb0 : 0 ≤ b := ha0.trans hab
  have hda : 0 < 1 + a ^ 2 := by positivity
  have hdb : 0 < 1 + b ^ 2 := by positivity
  have hcross : a ^ 3 * (1 + b ^ 2) ≤ b ^ 3 * (1 + a ^ 2) := by
    have hfactor :
        b ^ 3 * (1 + a ^ 2) - a ^ 3 * (1 + b ^ 2) =
          (b - a) * (b ^ 2 + a * b + a ^ 2 + a ^ 2 * b ^ 2) := by
      ring
    apply sub_nonneg.mp
    rw [hfactor]
    exact mul_nonneg (sub_nonneg.mpr hab) (by positivity)
  have hratio : a ^ 3 / (1 + a ^ 2) ≤ b ^ 3 / (1 + b ^ 2) :=
    (div_le_div_iff₀ hda hdb).2 hcross
  have hratio_a0 : 0 ≤ a ^ 3 / (1 + a ^ 2) := by positivity
  have hsq := pow_le_pow_left₀ hratio_a0 hratio 2
  calc
    a ^ 6 / (1 + a ^ 2) ^ 2 = (a ^ 3 / (1 + a ^ 2)) ^ 2 := by
      field_simp [hda.ne']
    _ ≤ (b ^ 3 / (1 + b ^ 2)) ^ 2 := hsq
    _ = b ^ 6 / (1 + b ^ 2) ^ 2 := by
      field_simp [hdb.ne']

/-- **Theorem 6.2 (improved)**: distinct Hellinger-near contacts on one
connected support have the exact HGR and information floors used by the
`1771` ledger. -/
theorem nearcollision_floor_hellinger
    {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) (hS : IsConnected S)
    {q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) (hne : q ≠ r)
    (hnear : hellingerSq q r ≤ delta1771) :
    rho1771 ≤ rhoHGR q ∧
    rho1771 ≤ rhoHGR r ∧
    infoFloor1771 ≤ Ixy q ∧
    infoFloor1771 ≤ Ixy r := by
  have hqs : support q = S := contact_support_eq hw hS hq
  have hrs : support r = S := contact_support_eq hw hS hr
  have hqR := rho1771_le_rhoHGR_of_contacts
    hw hq hr hqs hrs hne hnear
  have hnear_rev : hellingerSq r q ≤ delta1771 := by
    rw [hellingerSq_comm]
    exact hnear
  have hrR := rho1771_le_rhoHGR_of_contacts
    hw hr hq hrs hqs hne.symm hnear_rev
  have hqpos : 0 < rhoHGR q := rho1771_pos.trans_le hqR
  have hrpos : 0 < rhoHGR r := rho1771_pos.trans_le hrR
  have hchi_q : chi1771 ≤
      rhoHGR q ^ 6 / (1 + rhoHGR q ^ 2) ^ 2 := by
    rw [chi1771_eq]
    exact hgr_hellinger_fraction_mono rho1771_pos.le hqR
  have hchi_r : chi1771 ≤
      rhoHGR r ^ 6 / (1 + rhoHGR r ^ 2) ^ 2 := by
    rw [chi1771_eq]
    exact hgr_hellinger_fraction_mono rho1771_pos.le hrR
  have hhell_q := hellingerSq_product_ge_hgr hw hq hqpos
  have hhell_r := hellingerSq_product_ge_hgr hw hr hrpos
  have hIq := hellinger_floor_to_Ixy hq.1 chi1771_pos.le chi1771_lt_two
    (hchi_q.trans hhell_q)
  have hIr := hellinger_floor_to_Ixy hr.1 chi1771_pos.le chi1771_lt_two
    (hchi_r.trans hhell_r)
  exact ⟨hqR, hrR, by simpa [infoFloor1771] using hIq,
    by simpa [infoFloor1771] using hIr⟩

end stoch_to_det
