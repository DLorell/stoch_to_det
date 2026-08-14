import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Scalar core of the all-label shared-race bound

This file formalizes the elementary one-variable end of the direct
C less than 96 argument. The probability-law and simplex
change-of-variables layers are intentionally kept separate.
-/

namespace stoch_to_det
namespace SharedRace

open Set
open scoped Interval Real

noncomputable def logTwo : ℝ := Real.log 2

local notation "L" => logTwo

lemma two_thirds_lt_L : (2 / 3 : ℝ) < L := by
  unfold logTwo
  nlinarith [Real.log_two_gt_d9]

lemma L_lt_one : L < 1 := by
  unfold logTwo
  nlinarith [Real.log_two_lt_d9]

lemma L_pos : 0 < L := lt_trans (by norm_num : (0 : ℝ) < 2 / 3) two_thirds_lt_L

/-- The supporting-line inequality for `log`, with an arbitrary positive
base point. -/
lemma log_le_tangent {z t : ℝ} (hz : 0 < z) (ht : 0 < t) :
    Real.log z ≤ Real.log t + z / t - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hz ht)
  rw [Real.log_div hz.ne' ht.ne'] at h
  linarith

/-- The exponential form of the log tangent used after normalizing by the
minimum race clock. -/
lemma log_le_exp_tangent {z a : ℝ} (hz : 0 < z) :
    Real.log z ≤ a + Real.exp (-a) * z - 1 := by
  have h := log_le_tangent hz (Real.exp_pos a)
  rw [Real.log_exp] at h
  have hdiv : z / Real.exp a = Real.exp (-a) * z := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    ring
  rwa [hdiv] at h

/-- Integrated form of the log tangent: a unit upper bound for the normalized
moment and mean `logTwo` for the tangent point imply the desired logarithmic
expectation bound. -/
lemma integral_log_le_logTwo_of_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (z a : Ω → ℝ)
    (hz : ∀ᵐ ω ∂μ, 0 < z ω)
    (hlog : MeasureTheory.Integrable (fun ω => Real.log (z ω)) μ)
    (haInt : MeasureTheory.Integrable a μ)
    (hmInt : MeasureTheory.Integrable (fun ω => Real.exp (-a ω) * z ω) μ)
    (ha : (∫ ω, a ω ∂μ) = L)
    (hm : (∫ ω, Real.exp (-a ω) * z ω ∂μ) ≤ 1) :
    (∫ ω, Real.log (z ω) ∂μ) ≤ L := by
  have hrhs : MeasureTheory.Integrable
      (fun ω => a ω + Real.exp (-a ω) * z ω - 1) μ :=
    (haInt.add hmInt).sub (MeasureTheory.integrable_const 1)
  have hpoint : ∀ᵐ ω ∂μ,
      Real.log (z ω) ≤ a ω + Real.exp (-a ω) * z ω - 1 := by
    filter_upwards [hz] with ω hω
    exact log_le_exp_tangent hω
  calc
    (∫ ω, Real.log (z ω) ∂μ) ≤
        ∫ ω, (a ω + Real.exp (-a ω) * z ω - 1) ∂μ :=
      MeasureTheory.integral_mono_ae hlog hrhs hpoint
    _ = (∫ ω, a ω ∂μ) +
          (∫ ω, Real.exp (-a ω) * z ω ∂μ) - 1 := by
      rw [MeasureTheory.integral_sub
        (f := fun ω => a ω + Real.exp (-a ω) * z ω)
        (g := fun _ => (1 : ℝ))
        (haInt.add hmInt) (MeasureTheory.integrable_const 1),
        MeasureTheory.integral_add haInt hmInt]
      simp
    _ ≤ L := by rw [ha]; linarith

/-- The weighted AM--GM inequality in the exact form used by the proof. -/
lemma rpow_one_sub_le_affine {r x : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hx : 0 ≤ x) :
    x ^ (1 - r) ≤ r + (1 - r) * x := by
  have h := Real.geom_mean_le_arith_mean2_weighted
    hr0 (sub_nonneg.mpr hr1) (by norm_num : (0 : ℝ) ≤ 1) hx (by ring)
  simpa using h

/-- The elementary power integral used after weighted AM--GM. -/
lemma integral_rpow_zero_one {a : ℝ} (ha : -1 < a) :
    (∫ x : ℝ in 0..1, x ^ a) = 1 / (a + 1) := by
  rw [integral_rpow (Or.inl ha)]
  have ha0 : 0 < a + 1 := by linarith
  simp [Real.zero_rpow ha0.ne']

/-- Weighted AM--GM bounds the rational integral occurring in the scalar
beta--gamma estimate by the elementary power integral. -/
lemma integral_sq_div_affine_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫ x : ℝ in 0..1, (x / (r + (1 - r) * x)) ^ 2) ≤ 1 / (1 + 2 * r) := by
  have hr0' : 0 ≤ r := hr0.le
  have hden_pos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < r + (1 - r) * x := by
    intro x hx
    have hxr : 0 ≤ (1 - r) * x :=
      mul_nonneg (sub_nonneg.mpr hr1) hx.1
    linarith
  have hleft : IntervalIntegrable
      (fun x : ℝ => (x / (r + (1 - r) * x)) ^ 2) MeasureTheory.volume 0 1 := by
    have hcont : ContinuousOn
        (fun x : ℝ => (x / (r + (1 - r) * x)) ^ 2) (Icc 0 1) := by
      have hxcont : ContinuousOn (fun x : ℝ => x) (Icc 0 1) :=
        continuous_id.continuousOn
      have hdencont : ContinuousOn
          (fun x : ℝ => r + (1 - r) * x) (Icc 0 1) :=
        continuous_const.continuousOn.add
          (continuous_const.continuousOn.mul hxcont)
      exact (hxcont.div hdencont (fun x hx => (hden_pos x hx).ne')).pow 2
    have hcont' : ContinuousOn
        (fun x : ℝ => (x / (r + (1 - r) * x)) ^ 2) [[0, 1]] := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcont
    exact hcont'.intervalIntegrable
  have hright : IntervalIntegrable (fun x : ℝ => x ^ (2 * r))
      MeasureTheory.volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow (Or.inl (mul_nonneg (by norm_num) hr0'))
  have hpoint : ∀ x ∈ Ioo (0 : ℝ) 1,
      (x / (r + (1 - r) * x)) ^ 2 ≤ x ^ (2 * r) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx0' : 0 ≤ x := hx0.le
    have hx1 : x ≤ 1 := hx.2.le
    have hden : 0 < r + (1 - r) * x := hden_pos x ⟨hx0', hx1⟩
    have hamgm := rpow_one_sub_le_affine hr0' hr1 hx0'
    have hxrpow : 0 ≤ x ^ r := Real.rpow_nonneg hx0' r
    have hmul := mul_le_mul_of_nonneg_left hamgm hxrpow
    have hprod : x ^ r * x ^ (1 - r) = x := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hratio : x / (r + (1 - r) * x) ≤ x ^ r := by
      apply (div_le_iff₀ hden).2
      exact hprod.symm.trans_le hmul
    have hratio0 : 0 ≤ x / (r + (1 - r) * x) :=
      div_nonneg hx0' hden.le
    calc
      (x / (r + (1 - r) * x)) ^ 2 ≤ (x ^ r) ^ 2 :=
        (sq_le_sq₀ hratio0 hxrpow).2 hratio
      _ = x ^ (2 * r) := by
        rw [← Real.rpow_mul_natCast hx0' r 2]
        congr 1
        ring
  calc
    (∫ x : ℝ in 0..1, (x / (r + (1 - r) * x)) ^ 2) ≤
        ∫ x : ℝ in 0..1, x ^ (2 * r) :=
      intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hleft hright hpoint
    _ = 1 / (2 * r + 1) := integral_rpow_zero_one (by nlinarith)
    _ = 1 / (1 + 2 * r) := by ring

/-- The final rational expression produced by the beta--gamma estimates. -/
noncomputable def scalarUpper (p : ℝ) : ℝ :=
  let q := 1 - p
  let D := 1 + L * q
  let r := p * (1 - L) / D
  1 / D + q / (D ^ 2 * (1 + 2 * r))

/-- The constant check at the end of the scalar proof. -/
lemma L_mul_three_sub_two_L_gt_one : 1 < L * (3 - 2 * L) := by
  have hhalf : (1 / 2 : ℝ) < L := by
    linarith [two_thirds_lt_L]
  nlinarith [L_lt_one]

/-- The final algebraic estimate for the Beta-to-Gamma scalar bound. -/
theorem scalarUpper_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    scalarUpper p ≤ 1 := by
  let q : ℝ := 1 - p
  let D : ℝ := 1 + L * q
  let r : ℝ := p * (1 - L) / D
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hL0 : 0 < L := L_pos
  have hL1 : L < 1 := L_lt_one
  have hD : 0 < D := by dsimp [D]; nlinarith
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hcore : 1 < L * D * (1 + 2 * r) := by
    have hDr : D * (1 + 2 * r) = 1 + L + p * (2 - 3 * L) := by
      have hcancel : D * (p * (1 - L) / D) = p * (1 - L) := by
        field_simp [hD.ne']
      calc
        D * (1 + 2 * r) =
            D + 2 * (D * (p * (1 - L) / D)) := by
              change D * (1 + 2 * (p * (1 - L) / D)) =
                D + 2 * (D * (p * (1 - L) / D))
              ring
        _ = D + 2 * (p * (1 - L)) := by rw [hcancel]
        _ = 1 + L + p * (2 - 3 * L) := by
          dsimp [D, q]
          ring
    have hbase : 3 - 2 * L ≤ D * (1 + 2 * r) := by
      rw [hDr]
      nlinarith [two_thirds_lt_L]
    nlinarith [L_mul_three_sub_two_L_gt_one, mul_le_mul_of_nonneg_left hbase hL0.le]
  have hone : 0 < 1 + 2 * r := by nlinarith
  have hinv : 1 / (D * (1 + 2 * r)) ≤ L := by
    apply (div_le_iff₀ (mul_pos hD hone)).2
    nlinarith [hcore]
  have hqd : 0 ≤ q / D := div_nonneg hq hD.le
  have hmul := mul_le_mul_of_nonneg_left hinv hqd
  have hfactor :
      q / (D ^ 2 * (1 + 2 * r)) =
        (q / D) * (1 / (D * (1 + 2 * r))) := by
    field_simp [hD.ne', hone.ne']
  have hlast : 1 / D + (q / D) * L = 1 := by
    dsimp [D]
    field_simp [hD.ne']
  change 1 / D + q / (D ^ 2 * (1 + 2 * r)) ≤ 1
  rw [hfactor]
  calc
    1 / D + (q / D) * (1 / (D * (1 + 2 * r))) ≤
        1 / D + (q / D) * L := by
          simpa [add_comm] using add_le_add_left hmul (1 / D)
    _ = 1 := hlast

/-- Abstract assembly of the one-coordinate estimate.  The two hypotheses are
the winner and loser exponential-moment bounds; all remaining work is the
scalar calculation in `scalarUpper_le_one`. -/
theorem coordinateContribution_le {p winner loser : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hwinner : winner ≤ 1 / (1 + L * (1 - p)))
    (hloser : loser ≤
      p / ((1 + L * (1 - p)) ^ 2 *
        (1 + 2 * (p * (1 - L) / (1 + L * (1 - p)))))) :
    p * winner + (1 - p) * loser ≤ p := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hsum :
      p * winner + (1 - p) * loser ≤
        p * (1 / (1 + L * (1 - p))) +
          (1 - p) *
            (p / ((1 + L * (1 - p)) ^ 2 *
              (1 + 2 * (p * (1 - L) / (1 + L * (1 - p)))))) :=
    add_le_add
      (mul_le_mul_of_nonneg_left hwinner hp0)
      (mul_le_mul_of_nonneg_left hloser hq)
  have hscalar := scalarUpper_le_one hp0 hp1
  have hmul : p * scalarUpper p ≤ p := by
    simpa using mul_le_mul_of_nonneg_left hscalar hp0
  calc
    p * winner + (1 - p) * loser ≤
        p * (1 / (1 + L * (1 - p))) +
          (1 - p) *
            (p / ((1 + L * (1 - p)) ^ 2 *
              (1 + 2 * (p * (1 - L) / (1 + L * (1 - p)))))) := hsum
    _ = p * scalarUpper p := by
      unfold scalarUpper
      dsimp only
      ring
    _ ≤ p := hmul

end SharedRace
end stoch_to_det
