import stoch_to_det.SharedRace.BetaGamma
import stoch_to_det.SharedRace.LoserIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The loser-coordinate Möbius substitution

This file formalizes the one-dimensional change of variables

`x = p v / (p v + 1 - v)`

which sends a uniform `v ∈ [0,1]` to the density

`p / (p + (1-p)x)^2`.
-/

namespace stoch_to_det
namespace SharedRace

open MeasureTheory Set
open scoped Interval

local notation "L" => SharedRace.logTwo

/-- Forward Möbius map from the uniform coordinate to the loser coordinate. -/
noncomputable def mobius (p v : ℝ) : ℝ :=
  p * v / (p * v + 1 - v)

/-- Density induced by `mobius p` on `[0,1]`. -/
noncomputable def mobiusDensity (p x : ℝ) : ℝ :=
  p / (p + (1 - p) * x) ^ 2

/-- Derivative of the forward Möbius map. -/
noncomputable def mobiusDeriv (p v : ℝ) : ℝ :=
  p / (p * v + 1 - v) ^ 2

/-- Exponent appearing in the loser-cell shape-two beta moment. -/
noncomputable def loserExponent (p x : ℝ) : ℝ :=
  L * ((p - x) / (p + (1 - p) * x))

/-- The loser-coordinate integrand before inserting the Möbius density. -/
noncomputable def loserBetaIntegrand (k : ℕ) (p x : ℝ) : ℝ :=
  x ^ 2 * SharedRace.betaTwoExpMoment k (loserExponent p x)

/-- The loser-coordinate integrand in the degenerate `k = 2` shape-two
branch, where the scaled beta variable is identically two. -/
noncomputable def loserDegenerateIntegrand (p x : ℝ) : ℝ :=
  x ^ 2 * Real.exp (2 * loserExponent p x)

private lemma forwardDen_pos {p v : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < p * v + 1 - v := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1.le
  have hv' : 0 ≤ 1 - v := sub_nonneg.mpr hv.2
  have hprod : 0 ≤ (1 - p) * (1 - v) := mul_nonneg hq hv'
  nlinarith

private lemma densityDen_pos {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < p + (1 - p) * x := by
  exact add_pos_of_pos_of_nonneg hp0
    (mul_nonneg (sub_nonneg.mpr hp1.le) hx.1)

lemma mobius_mem_Icc {p v : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    mobius p v ∈ Icc (0 : ℝ) 1 := by
  have hden := forwardDen_pos hp0 hp1 hv
  constructor
  · exact div_nonneg (mul_nonneg hp0.le hv.1) hden.le
  · rw [mobius, div_le_one hden]
    linarith [hv.2]

private lemma hasDerivAt_mobius {p v : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (mobius p) (mobiusDeriv p v) v := by
  have hden := forwardDen_pos hp0 hp1 hv
  have hnum : HasDerivAt (fun y : ℝ => p * y) p v := hasDerivAt_const_mul p
  have hdenDeriv : HasDerivAt (fun y : ℝ => p * y + 1 - y) (p - 1) v := by
    convert ((hasDerivAt_const_mul p).add_const 1).sub (hasDerivAt_id v) using 1
    all_goals rfl
  unfold mobius mobiusDeriv
  convert hnum.div hdenDeriv hden.ne' using 1
  all_goals first
    | rfl
    | (field_simp [hden.ne']; ring)

private lemma continuousOn_mobiusDeriv {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn (mobiusDeriv p) (Icc (0 : ℝ) 1) := by
  unfold mobiusDeriv
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro v hv
  exact pow_ne_zero _ (forwardDen_pos hp0 hp1 hv).ne'

private lemma continuousOn_mobiusDensity {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn (mobiusDensity p) (Icc (0 : ℝ) 1) := by
  unfold mobiusDensity
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro x hx
  exact pow_ne_zero _ (densityDen_pos hp0 hp1 hx).ne'

private lemma continuous_betaTwoExpMoment (k : ℕ) :
    Continuous (SharedRace.betaTwoExpMoment k) := by
  unfold SharedRace.betaTwoExpMoment
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold SharedRace.betaTwoDensity
  fun_prop

private lemma continuousOn_loserExponent {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn (loserExponent p) (Icc (0 : ℝ) 1) := by
  unfold loserExponent
  apply continuousOn_const.mul
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  exact (densityDen_pos hp0 hp1 hx).ne'

private lemma loserExponent_lt_one {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    loserExponent p x < 1 := by
  have hden := densityDen_pos hp0 hp1 hx
  have hratio : (p - x) / (p + (1 - p) * x) ≤ 1 := by
    rw [div_le_one hden]
    have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1.le
    nlinarith [mul_nonneg hq hx.1]
  have hL0 := SharedRace.L_pos
  have hL1 := SharedRace.L_lt_one
  unfold loserExponent
  nlinarith [mul_le_mul_of_nonneg_left hratio hL0.le]

private lemma continuousOn_loserBetaIntegrand (k : ℕ) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn (loserBetaIntegrand k p) (Icc (0 : ℝ) 1) := by
  unfold loserBetaIntegrand
  exact (continuousOn_id.pow 2).mul
    ((continuous_betaTwoExpMoment k).continuousOn.comp
      (continuousOn_loserExponent hp0 hp1) (fun _ _ => Set.mem_univ _))

private lemma continuousOn_loserDegenerateIntegrand {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn (loserDegenerateIntegrand p) (Icc (0 : ℝ) 1) := by
  have hexponent : ContinuousOn (fun x : ℝ => 2 * loserExponent p x)
      (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul (continuousOn_loserExponent hp0 hp1)
  unfold loserDegenerateIntegrand
  exact (continuousOn_id.pow 2).mul
    (Real.continuous_exp.continuousOn.comp hexponent
      (fun _ _ => Set.mem_univ _))

private lemma continuousOn_loserGammaIntegrand {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn
      (fun x : ℝ =>
        mobiusDensity p x * x ^ 2 * (1 - loserExponent p x)⁻¹ ^ 2)
      (Icc (0 : ℝ) 1) := by
  have hbase : ContinuousOn (fun x : ℝ => 1 - loserExponent p x)
      (Icc (0 : ℝ) 1) :=
    continuousOn_const.sub (continuousOn_loserExponent hp0 hp1)
  have hinv : ContinuousOn (fun x : ℝ => (1 - loserExponent p x)⁻¹)
      (Icc (0 : ℝ) 1) := by
    apply hbase.inv₀
    intro x hx
    exact (sub_pos.mpr (loserExponent_lt_one hp0 hp1 hx)).ne'
  exact ((continuousOn_mobiusDensity hp0 hp1).mul
    (continuousOn_id.pow 2)).mul (hinv.pow 2)

/-- Möbius change of variables for any integrand continuous on `[0,1]`. -/
theorem integral_comp_mobius {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Icc (0 : ℝ) 1)) :
    (∫ v : ℝ in 0..1, F (mobius p v)) =
      ∫ x : ℝ in 0..1, mobiusDensity p x * F x := by
  have himage : mobius p '' Icc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    rcases hx with ⟨v, hv, rfl⟩
    exact mobius_mem_Icc hp0 hp1 hv
  have hdensity : ContinuousOn (mobiusDensity p) (mobius p '' Icc (0 : ℝ) 1) := by
    unfold mobiusDensity
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    exact pow_ne_zero _ (densityDen_pos hp0 hp1 (himage hx)).ne'
  have hG : ContinuousOn (fun x : ℝ => mobiusDensity p x * F x)
      (mobius p '' Icc (0 : ℝ) 1) :=
    hdensity.mul (hF.mono himage)
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := mobius p) (f' := mobiusDeriv p)
    (g := fun x : ℝ => mobiusDensity p x * F x)
    (fun v hv => hasDerivAt_mobius hp0 hp1 (by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hv))
    (by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        continuousOn_mobiusDeriv hp0 hp1)
    (by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hG)
  have hzero : mobius p 0 = 0 := by simp [mobius]
  have hone : mobius p 1 = 1 := by
    unfold mobius
    field_simp [hp0.ne']
    ring
  have hcancel (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      (mobiusDensity p (mobius p v) * F (mobius p v)) * mobiusDeriv p v =
        F (mobius p v) := by
    have hforward := forwardDen_pos hp0 hp1 hv
    have hdensity := densityDen_pos hp0 hp1 (mobius_mem_Icc hp0 hp1 hv)
    unfold mobiusDensity mobiusDeriv mobius
    field_simp [hp0.ne', hforward.ne', hdensity.ne']
    ring
  calc
    (∫ v : ℝ in 0..1, F (mobius p v)) =
        ∫ v : ℝ in 0..1,
          ((fun x : ℝ => mobiusDensity p x * F x) ∘ mobius p) v *
            mobiusDeriv p v := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hv' : v ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hv
      exact (hcancel v hv').symm
    _ = ∫ x : ℝ in mobius p 0..mobius p 1, mobiusDensity p x * F x := hsub
    _ = ∫ x : ℝ in 0..1, mobiusDensity p x * F x := by rw [hzero, hone]

/-- The literal loser beta-moment integral after the Möbius substitution. -/
theorem loserBetaIntegral_changeOfVariables (k : ℕ) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ v : ℝ in 0..1, loserBetaIntegrand k p (mobius p v)) =
      ∫ x : ℝ in 0..1,
        p / (p + (1 - p) * x) ^ 2 * x ^ 2 *
          SharedRace.betaTwoExpMoment k
            (L * ((p - x) / (p + (1 - p) * x))) := by
  simpa [mobiusDensity, loserBetaIntegrand, loserExponent, mul_assoc] using
    integral_comp_mobius hp0 hp1 (continuousOn_loserBetaIntegrand k hp0 hp1)

/-- The literal `k = 2` degenerate loser integral after the Möbius
substitution. -/
theorem loserDegenerateIntegral_changeOfVariables {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ v : ℝ in 0..1, loserDegenerateIntegrand p (mobius p v)) =
      ∫ x : ℝ in 0..1,
        p / (p + (1 - p) * x) ^ 2 * x ^ 2 *
          Real.exp (2 * (L * ((p - x) / (p + (1 - p) * x)))) := by
  simpa [mobiusDensity, loserDegenerateIntegrand, loserExponent, mul_assoc] using
    integral_comp_mobius hp0 hp1 (continuousOn_loserDegenerateIntegrand hp0 hp1)

/-- The clock-ready integrated loser bound.  It combines the literal
shape-two beta moment, the Möbius density, the beta--gamma comparison, and
the rational coordinate integral. -/
theorem integratedLoserBetaExpMoment_le (k : ℕ) (hk : 3 ≤ k) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ v : ℝ in 0..1, loserBetaIntegrand k p (mobius p v)) ≤
      p /
        ((1 + L * (1 - p)) ^ 2 *
          (1 + 2 * (p * (1 - L) / (1 + L * (1 - p))))) := by
  rw [loserBetaIntegral_changeOfVariables k hp0 hp1]
  have hleft : IntervalIntegrable
      (fun x : ℝ =>
        mobiusDensity p x * x ^ 2 *
          SharedRace.betaTwoExpMoment k (loserExponent p x))
      volume 0 1 := by
    have hcont := (continuousOn_mobiusDensity hp0 hp1).mul
      (continuousOn_loserBetaIntegrand k hp0 hp1)
    change ContinuousOn
      (fun x : ℝ => mobiusDensity p x * loserBetaIntegrand k p x)
      (Icc (0 : ℝ) 1) at hcont
    have hcont' : ContinuousOn
        (fun x : ℝ =>
          mobiusDensity p x * x ^ 2 *
            SharedRace.betaTwoExpMoment k (loserExponent p x))
        [[(0 : ℝ), 1]] := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        loserBetaIntegrand, mul_assoc] using hcont
    exact hcont'.intervalIntegrable
  have hright : IntervalIntegrable
      (fun x : ℝ =>
        mobiusDensity p x * x ^ 2 * (1 - loserExponent p x)⁻¹ ^ 2)
      volume 0 1 := by
    have hcont : ContinuousOn
        (fun x : ℝ =>
          mobiusDensity p x * x ^ 2 * (1 - loserExponent p x)⁻¹ ^ 2)
        [[(0 : ℝ), 1]] := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        continuousOn_loserGammaIntegrand hp0 hp1
    exact hcont.intervalIntegrable
  calc
    (∫ x : ℝ in 0..1,
        p / (p + (1 - p) * x) ^ 2 * x ^ 2 *
          SharedRace.betaTwoExpMoment k
            (L * ((p - x) / (p + (1 - p) * x)))) ≤
        ∫ x : ℝ in 0..1,
          p / (p + (1 - p) * x) ^ 2 * x ^ 2 *
            (1 - L * ((p - x) / (p + (1 - p) * x)))⁻¹ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (by simpa [mobiusDensity, loserExponent, mul_assoc] using hleft)
        (by simpa [mobiusDensity, loserExponent, mul_assoc] using hright)
      intro x hx
      have hbeta := SharedRace.loserBetaExpMoment_le k hk
        (loserExponent_lt_one hp0 hp1 hx)
      have hcoeff : 0 ≤ p / (p + (1 - p) * x) ^ 2 * x ^ 2 := by
        positivity
      exact mul_le_mul_of_nonneg_left hbeta hcoeff
    _ ≤ _ := SharedRace.loserMobiusGammaIntegral_le hp0 hp1

/-- The clock-ready integrated loser bound for the degenerate `k = 2`
shape-two branch. -/
theorem integratedLoserDegenerateExpMoment_le {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ v : ℝ in 0..1, loserDegenerateIntegrand p (mobius p v)) ≤
      p /
        ((1 + L * (1 - p)) ^ 2 *
          (1 + 2 * (p * (1 - L) / (1 + L * (1 - p))))) := by
  rw [loserDegenerateIntegral_changeOfVariables hp0 hp1]
  have hleft : IntervalIntegrable
      (fun x : ℝ =>
        mobiusDensity p x * x ^ 2 * Real.exp (2 * loserExponent p x))
      volume 0 1 := by
    have hcont := (continuousOn_mobiusDensity hp0 hp1).mul
      (continuousOn_loserDegenerateIntegrand hp0 hp1)
    change ContinuousOn
      (fun x : ℝ => mobiusDensity p x * loserDegenerateIntegrand p x)
      (Icc (0 : ℝ) 1) at hcont
    have hcont' : ContinuousOn
        (fun x : ℝ =>
          mobiusDensity p x * x ^ 2 * Real.exp (2 * loserExponent p x))
        [[(0 : ℝ), 1]] := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        loserDegenerateIntegrand, mul_assoc] using hcont
    exact hcont'.intervalIntegrable
  have hright : IntervalIntegrable
      (fun x : ℝ =>
        mobiusDensity p x * x ^ 2 * (1 - loserExponent p x)⁻¹ ^ 2)
      volume 0 1 := by
    have hcont : ContinuousOn
        (fun x : ℝ =>
          mobiusDensity p x * x ^ 2 * (1 - loserExponent p x)⁻¹ ^ 2)
        [[(0 : ℝ), 1]] := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        continuousOn_loserGammaIntegrand hp0 hp1
    exact hcont.intervalIntegrable
  calc
    (∫ x : ℝ in 0..1,
        p / (p + (1 - p) * x) ^ 2 * x ^ 2 *
          Real.exp (2 * (L * ((p - x) / (p + (1 - p) * x))))) ≤
        ∫ x : ℝ in 0..1,
          p / (p + (1 - p) * x) ^ 2 * x ^ 2 *
            (1 - L * ((p - x) / (p + (1 - p) * x)))⁻¹ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (by simpa [mobiusDensity, loserExponent, mul_assoc] using hleft)
        (by simpa [mobiusDensity, loserExponent, mul_assoc] using hright)
      intro x hx
      have hbeta : Real.exp (2 * loserExponent p x) ≤
          (1 - loserExponent p x)⁻¹ ^ 2 := by
        simpa [mul_comm] using SharedRace.loserBetaExpMoment_two_le
          (loserExponent_lt_one hp0 hp1 hx)
      have hcoeff : 0 ≤ p / (p + (1 - p) * x) ^ 2 * x ^ 2 := by
        positivity
      exact mul_le_mul_of_nonneg_left hbeta hcoeff
    _ ≤ _ := SharedRace.loserMobiusGammaIntegral_le hp0 hp1

end SharedRace
end stoch_to_det
